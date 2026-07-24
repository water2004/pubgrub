use pubgrub::{
    DerivationTree, OfflineDependencyProvider, Ranges, SolverEvent, SolverObserver, resolve,
    resolve_with_observer,
};

#[derive(Debug, PartialEq, Eq)]
enum RecordedEvent {
    PackageChoice(String),
    VersionChoice(String, u32),
    Decision(String, u32, u32),
    NoVersion(String),
    Derivation {
        package: String,
        packages: Vec<String>,
        allowed_two_before: Option<bool>,
        allowed_two_after: bool,
    },
    Conflict(Vec<String>),
    Backtrack {
        from_level: u32,
        to_level: u32,
        packages: Vec<String>,
    },
    Solution,
}

#[derive(Default)]
struct Recorder {
    events: Vec<RecordedEvent>,
}

fn cause_packages(cause: &DerivationTree<&'static str, Ranges<u32>, String>) -> Vec<String> {
    let mut packages: Vec<_> = cause
        .packages()
        .into_iter()
        .map(|package| (*package).to_string())
        .collect();
    packages.sort();
    packages
}

impl SolverObserver<&'static str, Ranges<u32>, String> for Recorder {
    fn on_event(&mut self, event: SolverEvent<'_, &'static str, Ranges<u32>, String>) {
        match event {
            SolverEvent::PackageChoice { package, .. } => self
                .events
                .push(RecordedEvent::PackageChoice((*package).to_string())),
            SolverEvent::VersionChoice {
                package, version, ..
            } => self.events.push(RecordedEvent::VersionChoice(
                (*package).to_string(),
                *version,
            )),
            SolverEvent::Decision {
                package,
                version,
                decision_level,
            } => self.events.push(RecordedEvent::Decision(
                (*package).to_string(),
                *version,
                decision_level,
            )),
            SolverEvent::NoVersion { package, .. } => self
                .events
                .push(RecordedEvent::NoVersion((*package).to_string())),
            SolverEvent::Derivation {
                package,
                previous,
                current,
                cause,
            } => self.events.push(RecordedEvent::Derivation {
                package: (*package).to_string(),
                packages: cause_packages(cause),
                allowed_two_before: previous.map(|term| term.contains(&2)),
                allowed_two_after: current.contains(&2),
            }),
            SolverEvent::Conflict { cause } => self
                .events
                .push(RecordedEvent::Conflict(cause_packages(cause))),
            SolverEvent::Backtrack {
                from_level,
                to_level,
                cause,
            } => self.events.push(RecordedEvent::Backtrack {
                from_level,
                to_level,
                packages: cause_packages(cause),
            }),
            SolverEvent::Solution => self.events.push(RecordedEvent::Solution),
            _ => {}
        }
    }
}

#[test]
fn observer_records_choices_without_changing_the_solution() {
    let mut provider = OfflineDependencyProvider::<&str, Ranges<u32>>::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full())]);
    provider.add_dependencies("a", 1u32, []);

    let expected = resolve(&provider, "root", 1u32).unwrap();
    let mut recorder = Recorder::default();
    let actual = resolve_with_observer(&provider, "root", 1u32, &mut recorder).unwrap();

    assert_eq!(actual, expected);
    let choices: Vec<_> = recorder
        .events
        .iter()
        .filter(|event| {
            matches!(
                event,
                RecordedEvent::PackageChoice(_)
                    | RecordedEvent::VersionChoice(_, _)
                    | RecordedEvent::NoVersion(_)
                    | RecordedEvent::Solution
            )
        })
        .collect();
    assert_eq!(
        choices,
        [
            &RecordedEvent::PackageChoice("root".to_string()),
            &RecordedEvent::VersionChoice("root".to_string(), 1),
            &RecordedEvent::PackageChoice("a".to_string()),
            &RecordedEvent::VersionChoice("a".to_string(), 1),
            &RecordedEvent::Solution,
        ]
    );
}

#[test]
fn observer_records_when_no_version_is_available() {
    let mut provider = OfflineDependencyProvider::<&str, Ranges<u32>>::new();
    provider.add_dependencies("root", 1u32, [("missing", Ranges::full())]);

    let mut recorder = Recorder::default();
    assert!(resolve_with_observer(&provider, "root", 1u32, &mut recorder).is_err());
    assert!(
        recorder
            .events
            .contains(&RecordedEvent::NoVersion("missing".to_string()))
    );
}

#[test]
fn observer_retains_the_actual_reason_a_newer_version_was_discarded() {
    let mut provider = OfflineDependencyProvider::<&str, Ranges<u32>>::new();
    provider.add_dependencies(
        "root",
        1u32,
        [("a", Ranges::full()), ("b", Ranges::singleton(1u32))],
    );
    provider.add_dependencies("a", 2u32, [("b", Ranges::singleton(2u32))]);
    provider.add_dependencies("a", 1u32, [("b", Ranges::singleton(1u32))]);
    provider.add_dependencies("b", 2u32, []);
    provider.add_dependencies("b", 1u32, []);

    let mut recorder = Recorder::default();
    let solution = resolve_with_observer(&provider, "root", 1u32, &mut recorder).unwrap();

    assert_eq!(solution.get(&"a"), Some(&1));
    assert!(
        recorder
            .events
            .contains(&RecordedEvent::VersionChoice("a".to_string(), 2))
    );
    let a_two_decision_level = recorder
        .events
        .iter()
        .find_map(|event| match event {
            RecordedEvent::Decision(package, 2, decision_level) if package == "a" => {
                Some(*decision_level)
            }
            _ => None,
        })
        .expect("a 2 was committed before it was backtracked");
    assert!(recorder.events.iter().any(|event| {
        matches!(
            event,
            RecordedEvent::Backtrack {
                from_level,
                to_level,
                packages,
            } if from_level > to_level
                && a_two_decision_level > *to_level
                && a_two_decision_level <= *from_level
                && packages == &["a".to_string(), "b".to_string()]
        )
    }));
    assert!(recorder.events.iter().any(|event| {
        matches!(
            event,
            RecordedEvent::Derivation {
                package,
                packages,
                ..
            }
                if package == "a"
                    && packages == &["a".to_string(), "b".to_string()]
        )
    }));
}

#[test]
fn observer_explains_a_version_excluded_before_it_was_chosen() {
    let mut provider = OfflineDependencyProvider::<&str, Ranges<u32>>::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    provider.add_dependencies("a", 2u32, []);
    provider.add_dependencies("a", 1u32, []);
    provider.add_dependencies("b", 1u32, [("a", Ranges::singleton(1u32))]);

    let mut recorder = Recorder::default();
    let solution = resolve_with_observer(&provider, "root", 1u32, &mut recorder).unwrap();

    assert_eq!(solution.get(&"a"), Some(&1));
    assert!(
        !recorder
            .events
            .contains(&RecordedEvent::VersionChoice("a".to_string(), 2))
    );
    assert!(
        !recorder
            .events
            .iter()
            .any(|event| matches!(event, RecordedEvent::Decision(package, 2, _) if package == "a"))
    );
    assert!(recorder.events.iter().any(|event| {
        matches!(
            event,
            RecordedEvent::Derivation {
                package,
                packages,
                allowed_two_before: Some(true),
                allowed_two_after: false,
            } if package == "a"
                && packages == &["a".to_string(), "b".to_string()]
        )
    }));
}
