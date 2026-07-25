// SPDX-License-Identifier: MPL-2.0

use std::collections::BTreeSet as Set;
use std::error::Error;
use std::fmt::{Debug, Display};

use crate::internal::{Id, Incompatibility, State};
use crate::observer::NoopSolverObserver;
use crate::{
    Map, Package, PubGrubError, Set as PackageSet, SolverEvent, SolverObserver, Term, VersionSet,
};
use log::{debug, info};

/// Statistics on how often a package conflicted with other packages.
#[derive(Debug, Default, Clone)]
pub struct PackageResolutionStatistics {
    // We track these fields separately but currently don't expose them separately to keep the
    // stable API slim. Please be encouraged to try different combinations of them and report if
    // you find better metrics that should be exposed.
    //
    // Say we have packages A and B, A having higher priority than B. We first decide A and then B,
    // and then find B to conflict with A. We call be B "affected" and A "culprit" since the
    // decisions for B is being rejected due to the decision we made for A earlier.
    //
    // If B is rejected due to its dependencies conflicting with A, we increase
    // `dependencies_affected` for B and for `dependencies_culprit` A. If B is rejected in unit
    // through an incompatibility with B, we increase `unit_propagation_affected` for B and for
    // `unit_propagation_culprit` A.
    unit_propagation_affected: u32,
    unit_propagation_culprit: u32,
    dependencies_affected: u32,
    dependencies_culprit: u32,
}

impl PackageResolutionStatistics {
    /// The number of conflicts this package was involved in.
    ///
    /// Processing packages with a high conflict count earlier usually speeds up resolution.
    ///
    /// Whenever a package is part of the root cause incompatibility of a conflict, we increase its
    /// count by one. Since the structure of the incompatibilities may change, this count too may
    /// change in the future.
    pub fn conflict_count(&self) -> u32 {
        self.unit_propagation_affected
            + self.unit_propagation_culprit
            + self.dependencies_affected
            + self.dependencies_culprit
    }
}

/// The resolved dependencies and their versions.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SelectedDependencies<P: Package, V>(Map<P, V>);

/// All locally maximal solutions returned by [`resolve_maximal_solutions`].
pub type MaximalSolutions<P, V> = Vec<SelectedDependencies<P, V>>;

impl<P: Package, V> SelectedDependencies<P, V> {
    /// Iterate over the resolved dependencies and their versions.
    pub fn iter(&self) -> impl Iterator<Item = (&P, &V)> {
        self.0.iter()
    }

    /// Get the version of a specific dependencies.
    pub fn get(&self, package: &P) -> Option<&V> {
        self.0.get(package)
    }
}

impl<P: Package, V> FromIterator<(P, V)> for SelectedDependencies<P, V> {
    fn from_iter<I: IntoIterator<Item = (P, V)>>(iter: I) -> Self {
        Self(Map::from_iter(iter))
    }
}

impl<P: Package, V> IntoIterator for SelectedDependencies<P, V> {
    type Item = (P, V);
    type IntoIter = <Map<P, V> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

struct SolverState<DP: DependencyProvider> {
    state: State<DP>,
    conflict_tracker: Map<Id<DP::P>, PackageResolutionStatistics>,
    added_dependencies: Map<Id<DP::P>, Set<DP::V>>,
    next: Id<DP::P>,
}

impl<DP: DependencyProvider> SolverState<DP> {
    fn new(package: DP::P, version: DP::V) -> Self {
        let state = State::init(package, version);
        let next = state.root_package;
        Self {
            state,
            conflict_tracker: Map::default(),
            added_dependencies: Map::default(),
            next,
        }
    }

    fn add_solution_exclusion(
        &mut self,
        terms: impl IntoIterator<Item = (DP::P, Term<DP::VS>)>,
    ) -> bool {
        let Some(next) = self.state.add_solution_exclusion(terms) else {
            return false;
        };
        self.next = next;
        true
    }

    fn run_until_solution<O>(
        &mut self,
        dependency_provider: &DP,
        observer: &mut O,
    ) -> Result<SelectedDependencies<DP::P, DP::V>, PubGrubError<DP>>
    where
        O: SolverObserver<DP::P, DP::VS, DP::M>,
    {
        loop {
            dependency_provider
                .should_cancel()
                .map_err(PubGrubError::ErrorInShouldCancel)?;

            info!(
                "unit_propagation: {:?} = '{}'",
                &self.next, self.state.package_store[self.next]
            );
            let satisfier_causes = self
                .state
                .unit_propagation_with_observer(self.next, observer)?;
            for (affected, incompat) in satisfier_causes {
                self.conflict_tracker
                    .entry(affected)
                    .or_default()
                    .unit_propagation_affected += 1;
                for (conflict_package, _) in self.state.incompatibility_store[incompat].iter() {
                    if conflict_package == affected {
                        continue;
                    }
                    self.conflict_tracker
                        .entry(conflict_package)
                        .or_default()
                        .unit_propagation_culprit += 1;
                }
            }

            debug!(
                "Partial solution after unit propagation: {}",
                self.state
                    .partial_solution
                    .display(&self.state.package_store)
            );

            let Some((highest_priority_pkg, term_intersection)) = self
                .state
                .partial_solution
                .pick_highest_priority_pkg(|p, r| {
                    dependency_provider.prioritize(
                        &self.state.package_store[p],
                        r,
                        self.conflict_tracker.entry(p).or_default(),
                    )
                })
            else {
                return Ok(SelectedDependencies(
                    self.state
                        .partial_solution
                        .extract_solution()
                        .map(|(p, v)| (self.state.package_store[p].clone(), v))
                        .collect(),
                ));
            };
            self.next = highest_priority_pkg;
            observer.on_event(SolverEvent::PackageChoice {
                package: &self.state.package_store[self.next],
                allowed: term_intersection,
            });

            let decision = dependency_provider
                .choose_version(&self.state.package_store[self.next], term_intersection)
                .map_err(|source| PubGrubError::ErrorChoosingVersion {
                    package: self.state.package_store[self.next].clone(),
                    source,
                })?;

            info!(
                "DP chose: {:?} = '{}' @ {:?}",
                &self.next, self.state.package_store[self.next], decision
            );

            let version = match decision {
                None => {
                    observer.on_event(SolverEvent::NoVersion {
                        package: &self.state.package_store[self.next],
                        allowed: term_intersection,
                    });
                    let incompatibility = Incompatibility::no_versions(
                        self.next,
                        Term::Positive(term_intersection.clone()),
                    );
                    self.state.add_incompatibility(incompatibility);
                    continue;
                }
                Some(version) => version,
            };
            observer.on_event(SolverEvent::VersionChoice {
                package: &self.state.package_store[self.next],
                version: &version,
                allowed: term_intersection,
            });

            if !term_intersection.contains(&version) {
                panic!(
                    "`choose_version` picked an incompatible version for package {}, {} is not in {}",
                    self.state.package_store[self.next], version, term_intersection
                );
            }

            let is_new_dependency = self
                .added_dependencies
                .entry(self.next)
                .or_default()
                .insert(version.clone());

            if is_new_dependency {
                let package = self.next;
                let dependencies = dependency_provider
                    .get_dependencies(&self.state.package_store[package], &version)
                    .map_err(|source| PubGrubError::ErrorRetrievingDependencies {
                        package: self.state.package_store[package].clone(),
                        version: version.clone(),
                        source,
                    })?;

                let dependencies = match dependencies {
                    Dependencies::Unavailable(reason) => {
                        self.state
                            .add_incompatibility(Incompatibility::custom_version(
                                package, version, reason,
                            ));
                        continue;
                    }
                    Dependencies::Available(dependencies) => dependencies,
                };
                let incompatibilities = dependency_provider
                    .get_incompatibilities(&self.state.package_store[package], &version)
                    .map_err(|source| PubGrubError::ErrorRetrievingDependencies {
                        package: self.state.package_store[package].clone(),
                        version: version.clone(),
                        source,
                    })?;

                match self.state.add_package_version_dependencies(
                    package,
                    version.clone(),
                    dependencies,
                    incompatibilities,
                ) {
                    Some(conflict) => {
                        self.conflict_tracker
                            .entry(package)
                            .or_default()
                            .dependencies_affected += 1;
                        for (incompat_package, _) in
                            self.state.incompatibility_store[conflict].iter()
                        {
                            if incompat_package == package {
                                continue;
                            }
                            self.conflict_tracker
                                .entry(incompat_package)
                                .or_default()
                                .dependencies_culprit += 1;
                        }
                    }
                    None => observer.on_event(SolverEvent::Decision {
                        package: &self.state.package_store[package],
                        version: &version,
                        decision_level: self.state.partial_solution.current_decision_level().0,
                    }),
                }
            } else {
                info!(
                    "add_decision (not first time): {:?} = '{}' @ {}",
                    &self.next, self.state.package_store[self.next], version
                );
                self.state
                    .partial_solution
                    .add_decision(self.next, version.clone());
                observer.on_event(SolverEvent::Decision {
                    package: &self.state.package_store[self.next],
                    version: &version,
                    decision_level: self.state.partial_solution.current_decision_level().0,
                });
            }
        }
    }
}
/// Finds a set of packages satisfying dependency bounds for a given package + version pair.
///
/// It consists in efficiently finding a set of packages and versions
/// that satisfy all the constraints of a given project dependencies.
/// In addition, when that is not possible,
/// PubGrub tries to provide a very human-readable and clear
/// explanation as to why that failed.
/// Below is an example of explanation present in
/// the introductory blog post about PubGrub
/// (Although this crate is not yet capable of building formatting quite this nice.)
///
/// ```txt
/// Because dropdown >=2.0.0 depends on icons >=2.0.0 and
///   root depends on icons <2.0.0, dropdown >=2.0.0 is forbidden.
///
/// And because menu >=1.1.0 depends on dropdown >=2.0.0,
///   menu >=1.1.0 is forbidden.
///
/// And because menu <1.1.0 depends on dropdown >=1.0.0 <2.0.0
///   which depends on intl <4.0.0, every version of menu
///   requires intl <4.0.0.
///
/// So, because root depends on both menu >=1.0.0 and intl >=5.0.0,
///   version solving failed.
/// ```
///
/// Is generic over an implementation of [DependencyProvider] which represents where the dependency constraints come from.
/// The associated types on the DependencyProvider allow flexibility for the representation of
/// package names, version requirements, version numbers, and other things.
/// See its documentation for more details.
/// For simple cases [OfflineDependencyProvider](crate::OfflineDependencyProvider) may be sufficient.
///
/// ## API
///
/// ```
/// # use std::convert::Infallible;
/// # use pubgrub::{resolve, OfflineDependencyProvider, PubGrubError, Ranges};
/// #
/// # type NumVS = Ranges<u32>;
/// #
/// # fn try_main() -> Result<(), PubGrubError<OfflineDependencyProvider<&'static str, NumVS>>> {
/// #     let dependency_provider = OfflineDependencyProvider::<&str, NumVS>::new();
/// #     let package = "root";
/// #     let version = 1u32;
/// let solution = resolve(&dependency_provider, package, version)?;
/// #     Ok(())
/// # }
/// # fn main() {
/// #     assert!(matches!(try_main(), Err(PubGrubError::NoSolution(_))));
/// # }
/// ```
///
/// The call to [resolve] for a given package at a given version
/// will compute the set of packages and versions needed
/// to satisfy the dependencies of that package and version pair.
/// If there is no solution, the reason will be provided as clear as possible.
#[cold]
pub fn resolve<DP: DependencyProvider>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
) -> Result<SelectedDependencies<DP::P, DP::V>, PubGrubError<DP>> {
    resolve_with_observer(
        dependency_provider,
        package,
        version,
        &mut NoopSolverObserver,
    )
}

/// Finds a set of packages satisfying dependency bounds and reports the path taken by the solver.
///
/// Unlike the derivation tree returned for an unsatisfiable resolution, observer events describe
/// one concrete solver run. In particular, they can explain when a version was excluded by
/// propagation or discarded by backtracking even if a different solver path could select it.
#[cold]
pub fn resolve_with_observer<DP, O>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    observer: &mut O,
) -> Result<SelectedDependencies<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    let mut solver = SolverState::new(package, version.into());
    let solution = solver.run_until_solution(dependency_provider, observer)?;
    observer.on_event(SolverEvent::Solution);
    Ok(solution)
}

/// Finds every solution in which no maximized package can be upgraded while all other selected
/// package versions remain fixed.
///
/// `strictly_higher` must return the version set strictly greater than its argument. The package
/// iterator defines both the user-visible solution coordinates and the packages considered for
/// upgrades. Other coordinates are held fixed while checking an individual upgrade; packages
/// outside that projection may change and do not make two projected solutions distinct.
///
/// Enumeration may be exponential in the number of independent choices. The dependency
/// provider's [`should_cancel`](DependencyProvider::should_cancel) hook remains active throughout
/// both enumeration and maximality checks.
#[cold]
pub fn resolve_maximal_solutions<DP, I, F>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    maximized_packages: I,
    strictly_higher: F,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    I: IntoIterator<Item = DP::P>,
    F: Fn(&DP::V) -> DP::VS,
{
    resolve_maximal_solutions_with_observer(
        dependency_provider,
        package,
        version,
        maximized_packages,
        strictly_higher,
        &mut NoopSolverObserver,
    )
}

/// Finds every single-package-maximal solution and reports each retained solution's actual solver
/// path.
///
/// [`SolverEvent::Solution`] is emitted once for every returned solution. Intermediate events
/// between two solution events belong to the continued enumeration path. Maximality probes expose
/// start/finish boundaries so observers can report dynamically discovered work, while their
/// internal decisions and derivations remain excluded from the retained solution trace.
#[cold]
pub fn resolve_maximal_solutions_with_observer<DP, I, F, O>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    maximized_packages: I,
    strictly_higher: F,
    observer: &mut O,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    I: IntoIterator<Item = DP::P>,
    F: Fn(&DP::V) -> DP::VS,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    let root_version = version.into();
    let mut seen = PackageSet::default();
    let maximized_packages: Vec<_> = maximized_packages
        .into_iter()
        .filter(|candidate| candidate != &package)
        .filter(|candidate| seen.insert(candidate.clone()))
        .collect();
    let mut solver = SolverState::new(package.clone(), root_version.clone());
    let mut solutions = Vec::new();
    let mut run = 0;

    loop {
        run += 1;
        observer.on_event(SolverEvent::EnumerationRunStarted { run });
        let run_result = solver.run_until_solution(dependency_provider, observer);
        observer.on_event(SolverEvent::EnumerationRunFinished { run });
        let solution = match run_result {
            Ok(solution) => solution,
            Err(PubGrubError::NoSolution(reason)) if solutions.is_empty() => {
                return Err(PubGrubError::NoSolution(reason));
            }
            Err(PubGrubError::NoSolution(_)) => return Ok(solutions),
            Err(error) => return Err(error),
        };

        if maximized_packages.is_empty() {
            observer.on_event(SolverEvent::Solution);
            return Ok(vec![solution]);
        }

        let upgradeable = find_upgradeable_package(
            dependency_provider,
            &package,
            &root_version,
            &solution,
            &maximized_packages,
            &strictly_higher,
            observer,
        )?;

        let exclusion = match upgradeable {
            Some(upgradeable) => solution
                .iter()
                .filter(|(selected, _)| maximized_packages.contains(selected))
                .map(|(selected, version)| {
                    let versions = if selected == &upgradeable {
                        strictly_higher(version).complement()
                    } else {
                        DP::VS::singleton(version.clone())
                    };
                    (selected.clone(), Term::Positive(versions))
                })
                .collect::<Vec<_>>(),
            None => {
                observer.on_event(SolverEvent::Solution);
                let exclusion = solution
                    .iter()
                    .filter(|(selected, _)| maximized_packages.contains(selected))
                    .map(|(selected, version)| {
                        (
                            selected.clone(),
                            Term::Positive(DP::VS::singleton(version.clone())),
                        )
                    })
                    .collect();
                solutions.push(solution);
                exclusion
            }
        };

        if !solver.add_solution_exclusion(exclusion) {
            return Ok(solutions);
        }
    }
}

fn find_upgradeable_package<DP, F, O>(
    dependency_provider: &DP,
    root_package: &DP::P,
    root_version: &DP::V,
    solution: &SelectedDependencies<DP::P, DP::V>,
    maximized_packages: &[DP::P],
    strictly_higher: &F,
    observer: &mut O,
) -> Result<Option<DP::P>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    F: Fn(&DP::V) -> DP::VS,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    for candidate in maximized_packages {
        let Some(current) = solution.get(candidate) else {
            continue;
        };
        let mut probe = SolverState::new(root_package.clone(), root_version.clone());
        let root_term = || {
            (
                root_package.clone(),
                Term::Positive(DP::VS::singleton(root_version.clone())),
            )
        };

        for (selected, version) in solution.iter() {
            if selected == root_package
                || selected == candidate
                || !maximized_packages.contains(selected)
            {
                continue;
            }
            probe.add_solution_exclusion([
                root_term(),
                (
                    selected.clone(),
                    Term::Negative(DP::VS::singleton(version.clone())),
                ),
            ]);
        }
        probe.add_solution_exclusion([
            root_term(),
            (candidate.clone(), Term::Negative(strictly_higher(current))),
        ]);

        observer.on_event(SolverEvent::MaximalityProbeStarted { package: candidate });
        let result = probe.run_until_solution(dependency_provider, &mut NoopSolverObserver);
        observer.on_event(SolverEvent::MaximalityProbeFinished { package: candidate });
        match result {
            Ok(_) => return Ok(Some(candidate.clone())),
            Err(PubGrubError::NoSolution(_)) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(None)
}

/// The dependencies of a package with their version ranges.
///
/// There is a difference in semantics between an empty [DependencyConstraints] and
/// [Dependencies::Unavailable]:
/// The former means the package has no dependency and it is a known fact,
/// while the latter means they could not be fetched by the [DependencyProvider].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DependencyConstraints<P, VS>(Vec<(P, VS)>);

/// One term in a provider-supplied incompatibility clause.
///
/// A positive term is true only when the package is selected in the given
/// range. A negative term is also true when the package is not selected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncompatibilityConstraintTerm<P, VS> {
    /// The package must be selected in the given range for the term to hold.
    Positive(P, VS),
    /// The term holds when the package is absent or outside the given range.
    Negative(P, VS),
}

/// A clause that must not be satisfied together with the package version whose
/// metadata returned it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IncompatibilityConstraint<P, VS, M> {
    /// Additional terms; the declaring package/version is inserted automatically.
    pub terms: Vec<IncompatibilityConstraintTerm<P, VS>>,
    /// Human-readable reason retained in derivation reports.
    pub reason: M,
}

/// Provider-supplied incompatibility clauses for one package version.
pub type IncompatibilityConstraints<P, VS, M> = Vec<IncompatibilityConstraint<P, VS, M>>;

/// Backwards compatibility: Serialize as map.
#[cfg(feature = "serde")]
impl<P: Package + serde::Serialize, VS: serde::Serialize> serde::Serialize
    for DependencyConstraints<P, VS>
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        Map::from_iter(self.0.iter().map(|(p, v)| (p, v))).serialize(serializer)
    }
}

/// Backwards compatibility: Deserialize as map.
#[cfg(feature = "serde")]
impl<'de, P: Package + serde::Deserialize<'de>, VS: serde::Deserialize<'de>> serde::Deserialize<'de>
    for DependencyConstraints<P, VS>
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Self::from_iter(Map::deserialize(deserializer)?))
    }
}

impl<P, VS> DependencyConstraints<P, VS> {
    /// Iterate over each dependency in order.
    pub fn iter(&self) -> impl Iterator<Item = &(P, VS)> {
        self.0.iter()
    }
}

impl<P, VS> Default for DependencyConstraints<P, VS> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<P, VS> FromIterator<(P, VS)> for DependencyConstraints<P, VS> {
    fn from_iter<T: IntoIterator<Item = (P, VS)>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<P, VS> IntoIterator for DependencyConstraints<P, VS> {
    type Item = (P, VS);
    type IntoIter = <Vec<(P, VS)> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// An enum used by [DependencyProvider] that holds information about package dependencies.
/// For each [Package] there is a set of versions allowed as a dependency.
#[derive(Clone)]
pub enum Dependencies<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Package dependencies are unavailable with the reason why they are missing.
    Unavailable(M),
    /// Container for all available package versions.
    Available(DependencyConstraints<P, VS>),
}

/// Trait that allows the algorithm to retrieve available packages and their dependencies.
/// An implementor needs to be supplied to the [resolve] function.
pub trait DependencyProvider {
    /// How this provider stores the name of the packages.
    type P: Package;

    /// How this provider stores the versions of the packages.
    ///
    /// A common choice is [`SemanticVersion`][crate::version::SemanticVersion].
    type V: Debug + Display + Clone + Ord;

    /// How this provider stores the version requirements for the packages.
    /// The requirements must be able to process the same kind of version as this dependency provider.
    ///
    /// A common choice is [`Ranges`][version_ranges::Ranges].
    type VS: VersionSet<V = Self::V>;

    /// The type returned from `prioritize`. The resolver does not care what type this is
    /// as long as it can pick a largest one and clone it.
    ///
    /// [`Reverse`](std::cmp::Reverse) can be useful if you want to pick the package with
    /// the fewest versions that match the outstanding constraint.
    type Priority: Ord + Clone;

    /// Type for custom incompatibilities.
    ///
    /// There are reasons in user code outside pubgrub that can cause packages or versions
    /// to be unavailable. Examples:
    /// * The version would require building the package, but builds are disabled.
    /// * The package is not available in the cache, but internet access has been disabled.
    /// * The package uses a legacy format not supported anymore.
    ///
    /// The intended use is to track them in an enum and assign them to this type. You can also
    /// assign [`String`] as placeholder.
    type M: Eq + Clone + Debug + Display;

    /// The kind of error returned from these methods.
    ///
    /// Returning this signals that resolution should fail with this error.
    type Err: Error + 'static;

    /// Determine the order in which versions are chosen for packages.
    ///
    /// Decisions are always made for the highest priority package first. The order of decisions
    /// determines which solution is chosen and can drastically change the performances of the
    /// solver. If there is a conflict between two package versions, decisions will be backtracked
    /// until the lower priority package version is discarded preserving the higher priority
    /// package. Usually, you want to decide more certain packages (e.g. those with a single version
    /// constraint) and packages with more conflicts first.
    ///
    /// The `package_conflicts_counts` argument provides access to some other heuristics that
    /// are production users have found useful. Although the exact meaning/efficacy of those
    /// arguments may change.
    ///
    /// The function is called once for each new package and then cached until we detect a
    /// (potential) change to `range`, otherwise it is cached, assuming that the priority only
    /// depends on the arguments to this function.
    ///
    /// If two packages have the same priority, PubGrub will bias toward a breadth first search.
    fn prioritize(
        &self,
        package: &Self::P,
        range: &Self::VS,
        // TODO(konsti): Are we always refreshing the priorities when `PackageResolutionStatistics`
        // changed for a package?
        package_conflicts_counts: &PackageResolutionStatistics,
    ) -> Self::Priority;

    /// Once the resolver has found the highest `Priority` package from all potential valid
    /// packages, it needs to know what version of that package to use. The most common pattern
    /// is to select the largest version that the range contains.
    fn choose_version(
        &self,
        package: &Self::P,
        range: &Self::VS,
    ) -> Result<Option<Self::V>, Self::Err>;

    /// Retrieves the package dependencies.
    /// Return [Dependencies::Unavailable] if its dependencies are unavailable.
    #[allow(clippy::type_complexity)]
    fn get_dependencies(
        &self,
        package: &Self::P,
        version: &Self::V,
    ) -> Result<Dependencies<Self::P, Self::VS, Self::M>, Self::Err>;

    /// Retrieves conditional incompatibilities declared by this package
    /// version. The current package/version is automatically included as a
    /// positive term in every returned clause.
    #[allow(clippy::type_complexity)]
    fn get_incompatibilities(
        &self,
        _package: &Self::P,
        _version: &Self::V,
    ) -> Result<IncompatibilityConstraints<Self::P, Self::VS, Self::M>, Self::Err> {
        Ok(Vec::new())
    }

    /// This is called fairly regularly during the resolution,
    /// if it returns an Err then resolution will be terminated.
    /// This is helpful if you want to add some form of early termination like a timeout,
    /// or you want to add some form of user feedback if things are taking a while.
    /// If not provided the resolver will run as long as needed.
    fn should_cancel(&self) -> Result<(), Self::Err> {
        Ok(())
    }
}
