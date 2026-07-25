use std::collections::BTreeSet;

use pubgrub::{
    OfflineDependencyProvider, Ranges, SolverEvent, SolverObserver, resolve_maximal_solutions,
    resolve_maximal_solutions_with_observer,
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

fn enumerate(provider: &Provider) -> BTreeSet<(u32, u32)> {
    projected(
        resolve_maximal_solutions(provider, "root", 1u32, ["a", "b"], |version| {
            Ranges::strictly_higher_than(*version)
        })
        .unwrap(),
    )
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
fn disconnected_diagonal_solutions_are_both_locally_maximal() {
    let mut provider = Provider::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    provider.add_dependencies("a", 1u32, [("b", Ranges::singleton(1u32))]);
    provider.add_dependencies("a", 2u32, [("b", Ranges::singleton(2u32))]);
    provider.add_dependencies("b", 1u32, []);
    provider.add_dependencies("b", 2u32, []);

    assert_eq!(enumerate(&provider), BTreeSet::from([(1, 1), (2, 2)]));
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
        |version| Ranges::strictly_higher_than(*version),
        &mut observer,
    )
    .unwrap();

    assert_eq!(projected(solutions), BTreeSet::from([(2, 2)]));
    assert_eq!(observer.solutions, 1);
    assert!(observer.runs_started > 0);
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

    let solutions = resolve_maximal_solutions(&provider, "root", 1u32, ["a"], |version| {
        Ranges::strictly_higher_than(*version)
    })
    .unwrap();

    assert_eq!(solutions.len(), 1);
    assert_eq!(solutions[0].get(&"a"), Some(&2));
}
