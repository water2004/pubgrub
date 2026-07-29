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

/// All Pareto-maximal solutions returned by [`resolve_maximal_solutions`].
pub type MaximalSolutions<P, V> = Vec<SelectedDependencies<P, V>>;

/// Caller-defined identity and precedence classes used by Pareto enumeration.
pub struct VersionOrdering<E, R, F> {
    same_version: E,
    same_precedence: R,
    strictly_higher: F,
}

/// A soft package-state condition used by minimal-change solution enumeration.
///
/// A solution which satisfies a strict superset of these conditions changes a strict subset of
/// the caller's baseline state. Preferences are optimized by set inclusion, not by assigning
/// arbitrary numeric weights to packages.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct PackagePreference<P: Package, VS: VersionSet> {
    package: P,
    preferred: Term<VS>,
}

impl<P: Package, VS: VersionSet> PackagePreference<P, VS> {
    /// Prefer selecting this package inside the supplied version set.
    pub fn selected(package: P, versions: VS) -> Self {
        Self {
            package,
            preferred: Term::Positive(versions),
        }
    }

    /// Prefer leaving this package absent from the solution.
    pub fn absent(package: P) -> Self {
        Self {
            package,
            preferred: Term::Negative(VS::full()),
        }
    }
}

impl<E, R, F> VersionOrdering<E, R, F> {
    /// Construct identity, equal-precedence, and strictly-higher version-set mappings.
    pub fn new(same_version: E, same_precedence: R, strictly_higher: F) -> Self {
        Self {
            same_version,
            same_precedence,
            strictly_higher,
        }
    }
}

type DominatingSolutionResult<DP> = Result<
    Option<SelectedDependencies<<DP as DependencyProvider>::P, <DP as DependencyProvider>::V>>,
    PubGrubError<DP>,
>;

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

/// Finds the complete Pareto front of the selected package versions.
///
/// `same_version` maps a selected provider version to representations that are the same selectable
/// realization. `same_precedence` maps it to every representation with the same ordering rank, and
/// `strictly_higher` maps it to the set of versions that count as an upgrade. A realization is
/// retained when its rank vector is Pareto-maximal; distinct `same_version` classes at the same
/// maximal rank are all returned. Packages outside the projection may change and do not make two
/// projected solutions distinct.
///
/// For every selected version, both equivalence sets must contain that version, `same_version` must
/// be a subset of `same_precedence`, and `same_precedence` must be disjoint from
/// `strictly_higher`. The solver validates these conditions so an invalid ordering cannot make
/// enumeration repeat a solution forever.
///
/// Each retained point excludes the complete region it dominates, rather than only its exact
/// projection. Enumeration is therefore driven by the size and shape of the Pareto and co-Pareto
/// fronts instead of visiting the Cartesian product of independent dominated choices. The
/// dependency provider's [`should_cancel`](DependencyProvider::should_cancel) hook remains active
/// throughout both enumeration and maximality checks.
#[cold]
pub fn resolve_maximal_solutions<DP, I, E, R, F>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    maximized_packages: I,
    version_ordering: VersionOrdering<E, R, F>,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    I: IntoIterator<Item = DP::P>,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
{
    resolve_maximal_solutions_with_observer(
        dependency_provider,
        package,
        version,
        maximized_packages,
        version_ordering,
        &mut NoopSolverObserver,
    )
}

/// Finds the complete Pareto front and reports each retained solution's actual solver path.
///
/// [`SolverEvent::Solution`] is emitted once for every returned solution. Intermediate events
/// between two solution events belong to the continued enumeration path. A successful maximality
/// probe becomes the path of the improved candidate; a failed probe does not. Probe boundaries and
/// outcomes let stateful observers commit or roll back the enclosed events accordingly.
#[cold]
pub fn resolve_maximal_solutions_with_observer<DP, I, E, R, F, O>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    maximized_packages: I,
    version_ordering: VersionOrdering<E, R, F>,
    observer: &mut O,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    I: IntoIterator<Item = DP::P>,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
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
    let version_ordering = BorrowedVersionOrdering {
        same_version: &version_ordering.same_version,
        same_precedence: &version_ordering.same_precedence,
        strictly_higher: &version_ordering.strictly_higher,
    };

    enumerate_maximal_solutions_with_constraints(
        dependency_provider,
        &package,
        &root_version,
        &maximized_packages,
        &version_ordering,
        &[],
        observer,
    )
}

/// Finds every standard Pareto-minimal change set and, within each equal change set, retains the
/// Pareto-maximal projected versions.
///
/// Each [`PackagePreference`] describes one fact from the caller's baseline state. A solution is
/// discarded when another feasible solution satisfies a strict superset of its preferences. This
/// is the set-inclusion definition of minimal change: no package preference can be restored without
/// losing another one that the solution already preserves. Incomparable minimal change sets are all
/// returned.
///
/// Version maximization is secondary and is performed only among solutions with exactly the same
/// satisfied preference set. It therefore cannot upgrade an otherwise preservable package merely
/// to obtain a newer solution. The same identity, precedence, and strict-upgrade callbacks used by
/// [`resolve_maximal_solutions`] define this secondary Pareto front.
#[cold]
pub fn resolve_minimal_change_solutions<DP, PI, MI, E, R, F>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    preferences: PI,
    maximized_packages: MI,
    version_ordering: VersionOrdering<E, R, F>,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    PI: IntoIterator<Item = PackagePreference<DP::P, DP::VS>>,
    MI: IntoIterator<Item = DP::P>,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
{
    resolve_minimal_change_solutions_with_observer(
        dependency_provider,
        package,
        version,
        preferences,
        maximized_packages,
        version_ordering,
        &mut NoopSolverObserver,
    )
}

/// Minimal-change solution enumeration with observer events for every returned solver path.
///
/// Preference-front feasibility work emits enumeration and maximality-probe boundaries, while the
/// decision and derivation events retained by the observer come from the secondary version solve
/// which produced each returned solution. This keeps path diagnostics aligned with actual output.
#[cold]
pub fn resolve_minimal_change_solutions_with_observer<DP, PI, MI, E, R, F, O>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
    preferences: PI,
    maximized_packages: MI,
    version_ordering: VersionOrdering<E, R, F>,
    observer: &mut O,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    PI: IntoIterator<Item = PackagePreference<DP::P, DP::VS>>,
    MI: IntoIterator<Item = DP::P>,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    let root_version = version.into();
    let preferences = preferences
        .into_iter()
        .filter(|preference| preference.package != package)
        .filter(|preference| {
            preference.preferred != Term::any() && preference.preferred != Term::empty()
        })
        .collect::<Vec<_>>();
    let mut seen = PackageSet::default();
    let maximized_packages = maximized_packages
        .into_iter()
        .filter(|candidate| candidate != &package)
        .filter(|candidate| seen.insert(candidate.clone()))
        .collect::<Vec<_>>();
    let version_ordering = BorrowedVersionOrdering {
        same_version: &version_ordering.same_version,
        same_precedence: &version_ordering.same_precedence,
        strictly_higher: &version_ordering.strictly_higher,
    };
    let mut preference_solver = SolverState::new(package.clone(), root_version.clone());
    let mut solutions = Vec::new();
    let mut run = 0;

    loop {
        run += 1;
        observer.on_event(SolverEvent::EnumerationRunStarted { run });
        let result =
            preference_solver.run_until_solution(dependency_provider, &mut NoopSolverObserver);
        observer.on_event(SolverEvent::EnumerationRunFinished { run });
        let mut solution = match result {
            Ok(solution) => solution,
            Err(PubGrubError::NoSolution(reason)) if solutions.is_empty() => {
                return Err(PubGrubError::NoSolution(reason));
            }
            Err(PubGrubError::NoSolution(_)) => return Ok(solutions),
            Err(error) => return Err(error),
        };

        loop {
            let Some(improved) = find_preference_dominating_solution(
                dependency_provider,
                &package,
                &root_version,
                &solution,
                &preferences,
                observer,
            )?
            else {
                break;
            };
            solution = improved;
        }

        let satisfaction = preference_satisfaction::<DP>(&solution, &preferences);
        let fixed_preferences = preferences
            .iter()
            .zip(&satisfaction)
            .map(|(preference, satisfied)| {
                (
                    preference.package.clone(),
                    if *satisfied {
                        preference.preferred.clone()
                    } else {
                        preference.preferred.negate()
                    },
                )
            })
            .collect::<Vec<_>>();
        solutions.extend(enumerate_maximal_solutions_with_constraints(
            dependency_provider,
            &package,
            &root_version,
            &maximized_packages,
            &version_ordering,
            &fixed_preferences,
            observer,
        )?);

        let dominated_preference_region = preferences
            .iter()
            .zip(&satisfaction)
            .filter(|(_, satisfied)| !**satisfied)
            .map(|(preference, _)| (preference.package.clone(), preference.preferred.negate()))
            .collect::<Vec<_>>();
        if !preference_solver.add_solution_exclusion(dominated_preference_region) {
            return Ok(solutions);
        }
    }
}

fn enumerate_maximal_solutions_with_constraints<DP, E, R, F, O>(
    dependency_provider: &DP,
    root_package: &DP::P,
    root_version: &DP::V,
    maximized_packages: &[DP::P],
    version_ordering: &BorrowedVersionOrdering<'_, E, R, F>,
    required_terms: &[(DP::P, Term<DP::VS>)],
    observer: &mut O,
) -> Result<MaximalSolutions<DP::P, DP::V>, PubGrubError<DP>>
where
    DP: DependencyProvider,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    let mut solver = SolverState::new(root_package.clone(), root_version.clone());
    force_terms(&mut solver, root_package, root_version, required_terms);
    let mut solutions = Vec::new();
    let mut run = 0;

    loop {
        run += 1;
        observer.on_event(SolverEvent::EnumerationRunStarted { run });
        let run_result = solver.run_until_solution(dependency_provider, observer);
        observer.on_event(SolverEvent::EnumerationRunFinished { run });
        let mut solution = match run_result {
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

        loop {
            validate_version_ordering(&solution, maximized_packages, version_ordering)?;
            let context = DominatingContext {
                root_package,
                root_version,
                maximized_packages,
                ordering: version_ordering,
                required_terms,
            };
            let Some(dominating) =
                find_dominating_solution(dependency_provider, &solution, &context, observer)?
            else {
                break;
            };
            solution = dominating;
        }

        observer.on_event(SolverEvent::Solution);
        let exact_exclusion = solution
            .iter()
            .filter(|(selected, _)| maximized_packages.contains(selected))
            .map(|(selected, version)| {
                (
                    selected.clone(),
                    Term::Positive((version_ordering.same_version)(version)),
                )
            })
            .collect::<Vec<_>>();
        solutions.push(solution);

        if !solver.add_solution_exclusion(exact_exclusion) {
            return Ok(solutions);
        }
        let retained = solutions.last().expect("a solution was just retained");
        for (lower_package, lower_version) in retained
            .iter()
            .filter(|(selected, _)| maximized_packages.contains(selected))
        {
            let not_lower = (version_ordering.same_precedence)(lower_version)
                .union(&(version_ordering.strictly_higher)(lower_version));
            let lower = not_lower.complement();
            let dominated = retained
                .iter()
                .filter(|(selected, _)| maximized_packages.contains(selected))
                .map(|(selected, version)| {
                    if selected == lower_package {
                        (selected.clone(), Term::Positive(lower.clone()))
                    } else {
                        (
                            selected.clone(),
                            Term::Negative((version_ordering.strictly_higher)(version)),
                        )
                    }
                })
                .collect::<Vec<_>>();
            if !dominated.is_empty() {
                solver.add_solution_exclusion(dominated);
            }
        }
    }
}

fn preference_satisfaction<DP: DependencyProvider>(
    solution: &SelectedDependencies<DP::P, DP::V>,
    preferences: &[PackagePreference<DP::P, DP::VS>],
) -> Vec<bool> {
    preferences
        .iter()
        .map(|preference| match solution.get(&preference.package) {
            Some(version) => preference.preferred.contains(version),
            None => matches!(preference.preferred, Term::Negative(_)),
        })
        .collect()
}

fn find_preference_dominating_solution<DP, O>(
    dependency_provider: &DP,
    root_package: &DP::P,
    root_version: &DP::V,
    solution: &SelectedDependencies<DP::P, DP::V>,
    preferences: &[PackagePreference<DP::P, DP::VS>],
    observer: &mut O,
) -> DominatingSolutionResult<DP>
where
    DP: DependencyProvider,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    let satisfaction = preference_satisfaction::<DP>(solution, preferences);
    let preserved = preferences
        .iter()
        .zip(&satisfaction)
        .filter(|(_, satisfied)| **satisfied)
        .map(|(preference, _)| (preference.package.clone(), preference.preferred.clone()))
        .collect::<Vec<_>>();
    for (preference, satisfied) in preferences.iter().zip(&satisfaction) {
        if *satisfied {
            continue;
        }
        let mut probe = SolverState::new(root_package.clone(), root_version.clone());
        force_terms(&mut probe, root_package, root_version, &preserved);
        force_terms(
            &mut probe,
            root_package,
            root_version,
            &[(preference.package.clone(), preference.preferred.clone())],
        );
        observer.on_event(SolverEvent::PreferenceProbeStarted {
            package: &preference.package,
        });
        let result = probe.run_until_solution(dependency_provider, &mut NoopSolverObserver);
        let probe_result = match &result {
            Ok(_) => crate::MaximalityProbeResult::Improved,
            Err(PubGrubError::NoSolution(_)) => crate::MaximalityProbeResult::NoImprovement,
            Err(_) => crate::MaximalityProbeResult::Error,
        };
        observer.on_event(SolverEvent::PreferenceProbeFinished {
            package: &preference.package,
            result: probe_result,
        });
        match result {
            Ok(solution) => return Ok(Some(solution)),
            Err(PubGrubError::NoSolution(_)) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(None)
}

fn force_terms<DP: DependencyProvider>(
    solver: &mut SolverState<DP>,
    root_package: &DP::P,
    root_version: &DP::V,
    required_terms: &[(DP::P, Term<DP::VS>)],
) {
    let root_term = || {
        (
            root_package.clone(),
            Term::Positive(DP::VS::singleton(root_version.clone())),
        )
    };
    for (package, required) in required_terms {
        if required == &Term::any() {
            continue;
        }
        if required == &Term::empty() {
            solver.add_solution_exclusion([root_term()]);
            continue;
        }
        solver.add_solution_exclusion([root_term(), (package.clone(), required.negate())]);
    }
}

struct BorrowedVersionOrdering<'a, E, R, F> {
    same_version: &'a E,
    same_precedence: &'a R,
    strictly_higher: &'a F,
}

fn validate_version_ordering<DP, E, R, F>(
    solution: &SelectedDependencies<DP::P, DP::V>,
    maximized_packages: &[DP::P],
    ordering: &BorrowedVersionOrdering<'_, E, R, F>,
) -> Result<(), PubGrubError<DP>>
where
    DP: DependencyProvider,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
{
    for (package, version) in solution
        .iter()
        .filter(|(package, _)| maximized_packages.contains(package))
    {
        let equivalent = (ordering.same_version)(version);
        let same_precedence = (ordering.same_precedence)(version);
        let higher = (ordering.strictly_higher)(version);
        let reason = if !equivalent.contains(version) {
            Some("same_version must contain the selected version")
        } else if !same_precedence.contains(version) {
            Some("same_precedence must contain the selected version")
        } else if !equivalent.subset_of(&same_precedence) {
            Some("same_version must be a subset of same_precedence")
        } else if higher.contains(version) {
            Some("strictly_higher must not contain the selected version")
        } else if !same_precedence.is_disjoint(&higher) {
            Some("same_precedence and strictly_higher must be disjoint")
        } else {
            None
        };
        if let Some(reason) = reason {
            return Err(PubGrubError::InvalidVersionOrdering {
                package: package.clone(),
                version: version.clone(),
                reason,
            });
        }
    }
    Ok(())
}

struct DominatingContext<'a, DP: DependencyProvider, E, R, F> {
    root_package: &'a DP::P,
    root_version: &'a DP::V,
    maximized_packages: &'a [DP::P],
    ordering: &'a BorrowedVersionOrdering<'a, E, R, F>,
    required_terms: &'a [(DP::P, Term<DP::VS>)],
}

fn find_dominating_solution<DP, E, R, F, O>(
    dependency_provider: &DP,
    solution: &SelectedDependencies<DP::P, DP::V>,
    context: &DominatingContext<'_, DP, E, R, F>,
    observer: &mut O,
) -> DominatingSolutionResult<DP>
where
    DP: DependencyProvider,
    E: Fn(&DP::V) -> DP::VS,
    R: Fn(&DP::V) -> DP::VS,
    F: Fn(&DP::V) -> DP::VS,
    O: SolverObserver<DP::P, DP::VS, DP::M>,
{
    for candidate in context.maximized_packages {
        if solution.get(candidate).is_none() {
            continue;
        }
        let mut probe =
            SolverState::new(context.root_package.clone(), context.root_version.clone());
        force_terms(
            &mut probe,
            context.root_package,
            context.root_version,
            context.required_terms,
        );
        let root_term = || {
            (
                context.root_package.clone(),
                Term::Positive(DP::VS::singleton(context.root_version.clone())),
            )
        };

        for (selected, version) in solution.iter() {
            if selected == context.root_package || !context.maximized_packages.contains(selected) {
                continue;
            }
            let required = if selected == candidate {
                (context.ordering.strictly_higher)(version)
            } else {
                (context.ordering.same_precedence)(version).union(&(context
                    .ordering
                    .strictly_higher)(
                    version
                ))
            };
            probe.add_solution_exclusion([
                root_term(),
                (selected.clone(), Term::Negative(required)),
            ]);
        }

        observer.on_event(SolverEvent::MaximalityProbeStarted { package: candidate });
        let result = probe.run_until_solution(dependency_provider, observer);
        let probe_result = match &result {
            Ok(_) => crate::MaximalityProbeResult::Improved,
            Err(PubGrubError::NoSolution(_)) => crate::MaximalityProbeResult::NoImprovement,
            Err(_) => crate::MaximalityProbeResult::Error,
        };
        observer.on_event(SolverEvent::MaximalityProbeFinished {
            package: candidate,
            result: probe_result,
        });
        match result {
            Ok(solution) => return Ok(Some(solution)),
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
