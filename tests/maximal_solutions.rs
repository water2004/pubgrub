use std::collections::BTreeSet;

use pubgrub::{
    OfflineDependencyProvider, PackagePreference, Ranges, SolverEvent, SolverObserver,
    VersionOrdering, resolve_factored_preference_solutions, resolve_maximal_solutions,
    resolve_maximal_solutions_for_preference_decisions, resolve_maximal_solutions_with_observer,
    resolve_minimal_change_solutions, resolve_minimal_change_solutions_with_observer,
};

type Provider = OfflineDependencyProvider<&'static str, Ranges<u32>>;

fn projected(
    solutions: impl IntoIterator<Item = pubgrub::SelectedDependencies<&'static str, u32>>,
) -> BTreeSet<(u32, u32)> {
    solutions
        .into_iter()
        .map(|solution| {
            (
                *solution.get(&"a").expect("a must be selected"),
                *solution.get(&"b").expect("b must be selected"),
            )
        })
        .collect()
}

#[derive(Default)]
struct PreferenceProbeCounter {
    impossible_started: usize,
}

impl SolverObserver<&'static str, Ranges<u32>, String> for PreferenceProbeCounter {
    fn on_event(&mut self, event: SolverEvent<'_, &'static str, Ranges<u32>, String>) {
        if let SolverEvent::PreferenceProbeStarted { package } = event {
            if *package == "impossible" {
                self.impossible_started += 1;
            }
        }
    }

    fn captures_derivation_trees(&self) -> bool {
        false
    }
}

#[test]
fn failed_preference_is_not_retried_while_the_preserved_set_only_grows() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, []);
    provider.add_dependencies("b", 1u32, []);
    provider.add_dependencies("c", 1u32, []);

    let mut observer = PreferenceProbeCounter::default();
    let solutions = resolve_minimal_change_solutions_with_observer(
        &provider,
        "root",
        1u32,
        [
            PackagePreference::selected("impossible", Ranges::singleton(1u32)),
            PackagePreference::selected("b", Ranges::singleton(1u32)),
            PackagePreference::selected("c", Ranges::singleton(1u32)),
        ],
        ["b", "c"],
        ordering(),
        &mut observer,
    )
    .unwrap();

    assert_eq!(observer.impossible_started, 1);
    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"b"), Some(&1));
    assert_eq!(solutions[0].get(&"c"), Some(&1));
}

#[test]
fn independent_preference_fronts_are_returned_as_a_product_of_factors() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, []);
    provider.add_dependencies("a1", 1u32, [("gate-a", Ranges::singleton(1u32))]);
    provider.add_dependencies("a2", 1u32, [("gate-a", Ranges::singleton(2u32))]);
    provider.add_dependencies("b1", 1u32, [("gate-b", Ranges::singleton(1u32))]);
    provider.add_dependencies("b2", 1u32, [("gate-b", Ranges::singleton(2u32))]);
    for gate in ["gate-a", "gate-b"] {
        provider.add_dependencies(gate, 1u32, []);
        provider.add_dependencies(gate, 2u32, []);
    }

    let factored = resolve_factored_preference_solutions(
        &provider,
        "root",
        1u32,
        vec![
            vec![
                PackagePreference::selected("a1", Ranges::singleton(1u32)),
                PackagePreference::selected("a2", Ranges::singleton(1u32)),
            ],
            vec![
                PackagePreference::selected("b1", Ranges::singleton(1u32)),
                PackagePreference::selected("b2", Ranges::singleton(1u32)),
            ],
        ],
    )
    .unwrap();

    assert_eq!(factored.common(), []);
    assert_eq!(factored.factors().len(), 2);
    assert!(
        factored
            .factors()
            .iter()
            .all(|factor| factor.alternatives().len() == 2)
    );
    assert_eq!(factored.complete_assignment_count(), Some(4));

    let decisions = factored.decisions_for(&[0, 1]).unwrap();
    let solutions = resolve_maximal_solutions_for_preference_decisions(
        &provider,
        "root",
        1u32,
        decisions,
        std::iter::empty::<&'static str>(),
        ordering(),
    )
    .unwrap();
    assert_eq!(solutions.len(), 1);
    let selected_a = ["a1", "a2"]
        .into_iter()
        .filter(|package| solutions[0].get(package).is_some())
        .count();
    let selected_b = ["b1", "b2"]
        .into_iter()
        .filter(|package| solutions[0].get(package).is_some())
        .count();
    assert_eq!((selected_a, selected_b), (1, 1));
}

fn enumerate(provider: &Provider) -> BTreeSet<(u32, u32)> {
    projected(
        resolve_maximal_solutions(
            provider,
            "root",
            1u32,
            ["a", "b"],
            VersionOrdering::new(
                |version: &u32| Ranges::singleton(*version),
                |version: &u32| Ranges::singleton(*version),
                |version: &u32| Ranges::strictly_higher_than(*version),
            ),
        )
        .unwrap(),
    )
}

type NumericOrdering =
    VersionOrdering<fn(&u32) -> Ranges<u32>, fn(&u32) -> Ranges<u32>, fn(&u32) -> Ranges<u32>>;

fn same_numeric_version(version: &u32) -> Ranges<u32> {
    Ranges::singleton(*version)
}

fn higher_numeric_versions(version: &u32) -> Ranges<u32> {
    Ranges::strictly_higher_than(*version)
}

fn ordering() -> NumericOrdering {
    VersionOrdering::new(
        same_numeric_version,
        same_numeric_version,
        higher_numeric_versions,
    )
}

#[test]
fn minimal_change_preserves_an_installed_version_instead_of_upgrading_it() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full())]);
    provider.add_dependencies("a", 1u32, []);
    provider.add_dependencies("a", 2u32, []);

    let solutions = resolve_minimal_change_solutions(
        &provider,
        "root",
        1u32,
        [PackagePreference::selected("a", Ranges::singleton(1u32))],
        ["a"],
        ordering(),
    )
    .unwrap();

    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"a"), Some(&1));
}

#[test]
fn incomparable_minimal_change_sets_are_all_returned() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("choice", Ranges::full())]);
    provider.add_dependencies(
        "choice",
        1u32,
        [
            ("a", Ranges::singleton(1u32)),
            ("b", Ranges::singleton(2u32)),
        ],
    );
    provider.add_dependencies(
        "choice",
        2u32,
        [
            ("a", Ranges::singleton(2u32)),
            ("b", Ranges::singleton(1u32)),
        ],
    );
    provider.add_dependencies(
        "choice",
        3u32,
        [
            ("a", Ranges::singleton(2u32)),
            ("b", Ranges::singleton(2u32)),
        ],
    );
    for package in ["a", "b"] {
        provider.add_dependencies(package, 1u32, []);
        provider.add_dependencies(package, 2u32, []);
    }

    let solutions = resolve_minimal_change_solutions(
        &provider,
        "root",
        1u32,
        [
            PackagePreference::selected("a", Ranges::singleton(1u32)),
            PackagePreference::selected("b", Ranges::singleton(1u32)),
        ],
        ["a", "b"],
        ordering(),
    )
    .unwrap();

    assert_eq!(projected(solutions), BTreeSet::from([(1, 2), (2, 1)]));
}

#[test]
fn absence_preference_avoids_an_unnecessary_new_package() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("choice", Ranges::full())]);
    provider.add_dependencies("choice", 1u32, []);
    provider.add_dependencies("choice", 2u32, [("addon", Ranges::singleton(1u32))]);
    provider.add_dependencies("addon", 1u32, []);

    let solutions = resolve_minimal_change_solutions(
        &provider,
        "root",
        1u32,
        [PackagePreference::absent("addon")],
        ["choice", "addon"],
        ordering(),
    )
    .unwrap();

    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"choice"), Some(&1));
    assert_eq!(solutions[0].get(&"addon"), None);
}

#[test]
fn versions_are_maximized_only_after_the_change_set_is_fixed() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::strictly_higher_than(1u32))]);
    for version in 1u32..=3 {
        provider.add_dependencies("a", version, []);
    }

    let solutions = resolve_minimal_change_solutions(
        &provider,
        "root",
        1u32,
        [PackagePreference::selected("a", Ranges::singleton(1u32))],
        ["a"],
        ordering(),
    )
    .unwrap();

    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"a"), Some(&3));
}

#[test]
fn independent_packages_have_one_maximal_solution() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    for package in ["a", "b"] {
        provider.add_dependencies(package, 1u32, []);
        provider.add_dependencies(package, 2u32, []);
    }

    assert_eq!(enumerate(&provider), BTreeSet::from([(2, 2)]));
}

#[test]
fn upgrade_tradeoff_returns_both_maximal_solutions() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    provider.add_dependencies("a", 1u32, []);
    provider.add_dependencies("a", 2u32, [("b", Ranges::singleton(1u32))]);
    provider.add_dependencies("b", 1u32, []);
    provider.add_dependencies("b", 2u32, []);

    assert_eq!(enumerate(&provider), BTreeSet::from([(1, 2), (2, 1)]));
}

#[test]
fn a_coordinated_upgrade_dominates_the_lower_diagonal_solution() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    provider.add_dependencies("a", 1u32, [("b", Ranges::singleton(1u32))]);
    provider.add_dependencies("a", 2u32, [("b", Ranges::singleton(2u32))]);
    provider.add_dependencies("b", 1u32, []);
    provider.add_dependencies("b", 2u32, []);

    assert_eq!(enumerate(&provider), BTreeSet::from([(2, 2)]));
}

#[derive(Default)]
struct SolutionCounter {
    solutions: usize,
    runs_started: usize,
    runs_finished: usize,
    probes_started: usize,
    probes_finished: usize,
}

impl SolverObserver<&'static str, Ranges<u32>, String> for SolutionCounter {
    fn on_event(&mut self, event: SolverEvent<'_, &'static str, Ranges<u32>, String>) {
        match event {
            SolverEvent::Solution => self.solutions += 1,
            SolverEvent::EnumerationRunStarted { .. } => self.runs_started += 1,
            SolverEvent::EnumerationRunFinished { .. } => self.runs_finished += 1,
            SolverEvent::MaximalityProbeStarted { .. } => self.probes_started += 1,
            SolverEvent::MaximalityProbeFinished { .. } => self.probes_finished += 1,
            _ => {}
        }
    }

    fn captures_derivation_trees(&self) -> bool {
        false
    }
}

#[test]
fn observer_reports_only_retained_solutions() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    for package in ["a", "b"] {
        provider.add_dependencies(package, 1u32, []);
        provider.add_dependencies(package, 2u32, []);
    }

    let mut observer = SolutionCounter::default();
    let solutions = resolve_maximal_solutions_with_observer(
        &provider,
        "root",
        1u32,
        ["a", "b"],
        VersionOrdering::new(
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::strictly_higher_than(*version),
        ),
        &mut observer,
    )
    .unwrap();

    assert_eq!(projected(solutions), BTreeSet::from([(2, 2)]));
    assert_eq!(observer.solutions, 1);
    assert_eq!(observer.runs_started, 2);
    assert_eq!(observer.runs_started, observer.runs_finished);
    assert!(observer.probes_started > 0);
    assert_eq!(observer.probes_started, observer.probes_finished);
}

#[test]
fn packages_outside_the_projection_may_change_during_an_upgrade() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full())]);
    provider.add_dependencies("a", 1u32, [("internal-old", Ranges::singleton(1u32))]);
    provider.add_dependencies("a", 2u32, [("internal-new", Ranges::singleton(1u32))]);
    provider.add_dependencies("internal-old", 1u32, []);
    provider.add_dependencies("internal-new", 1u32, []);

    let solutions = resolve_maximal_solutions(
        &provider,
        "root",
        1u32,
        ["a"],
        VersionOrdering::new(
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::strictly_higher_than(*version),
        ),
    )
    .unwrap();

    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"a"), Some(&2));
}

#[test]
fn equivalent_provider_versions_do_not_multiply_projected_solutions() {
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Realization {
        version: u32,
        source: u32,
    }

    impl std::fmt::Display for Realization {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "{} from {}", self.version, self.source)
        }
    }

    type RealizationProvider = OfflineDependencyProvider<&'static str, Ranges<Realization>>;
    let mut provider = RealizationProvider::new();
    let root = Realization {
        version: 1,
        source: 0,
    };
    provider.add_dependencies(
        "root",
        root.clone(),
        [("a", Ranges::full()), ("b", Ranges::full())],
    );
    for package in ["a", "b"] {
        for source in 1..=3 {
            provider.add_dependencies(package, Realization { version: 1, source }, []);
        }
    }

    let solutions = resolve_maximal_solutions(
        &provider,
        "root",
        root,
        ["a", "b"],
        VersionOrdering::new(
            |selected: &Realization| {
                Ranges::between(
                    Realization {
                        version: selected.version,
                        source: 0,
                    },
                    Realization {
                        version: selected.version + 1,
                        source: 0,
                    },
                )
            },
            |selected: &Realization| {
                Ranges::between(
                    Realization {
                        version: selected.version,
                        source: 0,
                    },
                    Realization {
                        version: selected.version + 1,
                        source: 0,
                    },
                )
            },
            |selected: &Realization| {
                Ranges::higher_than(Realization {
                    version: selected.version + 1,
                    source: 0,
                })
            },
        ),
    )
    .unwrap();

    assert_eq!(solutions.len(), 1);
}

#[test]
fn distinct_realizations_at_the_same_maximal_precedence_are_all_returned() {
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct Realization {
        precedence: u32,
        source: u32,
    }

    impl std::fmt::Display for Realization {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(formatter, "{} from {}", self.precedence, self.source)
        }
    }

    type RealizationProvider = OfflineDependencyProvider<&'static str, Ranges<Realization>>;
    let mut provider = RealizationProvider::new();
    let root = Realization {
        precedence: 0,
        source: 0,
    };
    provider.add_dependencies("root", root.clone(), [("a", Ranges::full())]);
    for source in 1..=3 {
        provider.add_dependencies(
            "a",
            Realization {
                precedence: 1,
                source,
            },
            [],
        );
    }

    let solutions = resolve_maximal_solutions(
        &provider,
        "root",
        root,
        ["a"],
        VersionOrdering::new(
            |selected: &Realization| Ranges::singleton(selected.clone()),
            |selected: &Realization| {
                Ranges::between(
                    Realization {
                        precedence: selected.precedence,
                        source: 0,
                    },
                    Realization {
                        precedence: selected.precedence + 1,
                        source: 0,
                    },
                )
            },
            |selected: &Realization| {
                Ranges::higher_than(Realization {
                    precedence: selected.precedence + 1,
                    source: 0,
                })
            },
        ),
    )
    .unwrap();
    let sources: BTreeSet<_> = solutions
        .iter()
        .map(|solution| solution.get(&"a").unwrap().source)
        .collect();

    assert_eq!(sources, BTreeSet::from([1, 2, 3]));
}

#[test]
fn invalid_strictly_higher_callback_is_rejected_instead_of_repeating() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full())]);
    provider.add_dependencies("a", 1u32, []);

    let error = resolve_maximal_solutions(
        &provider,
        "root",
        1u32,
        ["a"],
        VersionOrdering::new(
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::singleton(*version),
            |version: &u32| Ranges::higher_than(*version),
        ),
    )
    .unwrap_err();

    assert!(matches!(
        error,
        pubgrub::PubGrubError::InvalidVersionOrdering {
            package: "a",
            version: 1,
            ..
        }
    ));
}

#[test]
fn pareto_enumeration_matches_every_three_by_three_feasibility_relation() {
    let all_points: Vec<_> = (1u32..=3)
        .flat_map(|a| (1u32..=3).map(move |b| (a, b)))
        .collect();

    for feasible_bits in 1u16..(1 << all_points.len()) {
        let feasible: BTreeSet<_> = all_points
            .iter()
            .enumerate()
            .filter(|(index, _)| feasible_bits & (1 << index) != 0)
            .map(|(_, point)| *point)
            .collect();
        let expected: BTreeSet<_> = feasible
            .iter()
            .copied()
            .filter(|point| {
                !feasible.iter().any(|other| {
                    other.0 >= point.0
                        && other.1 >= point.1
                        && (other.0 > point.0 || other.1 > point.1)
                })
            })
            .collect();

        let mut provider = Provider::new();
        provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
        for a in 1u32..=3 {
            let allowed_b = feasible
                .iter()
                .filter(|point| point.0 == a)
                .fold(Ranges::empty(), |versions, point| {
                    versions.union(&Ranges::singleton(point.1))
                });
            provider.add_dependencies("a", a, [("b", allowed_b)]);
        }
        for b in 1u32..=3 {
            provider.add_dependencies("b", b, []);
        }

        assert_eq!(
            enumerate(&provider),
            expected,
            "wrong Pareto front for feasible relation {feasible:?}"
        );
    }
}
