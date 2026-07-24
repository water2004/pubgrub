use pubgrub::{
    OfflineDependencyProvider, Ranges, SolverEvent, SolverObserver, resolve, resolve_with_observer,
};

#[derive(Debug, PartialEq, Eq)]
enum RecordedEvent {
    PackageChoice(String),
    VersionChoice(String, u32),
    NoVersion(String),
    Solution,
}

#[derive(Default)]
struct Recorder {
    events: Vec<RecordedEvent>,
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
            SolverEvent::NoVersion { package, .. } => self
                .events
                .push(RecordedEvent::NoVersion((*package).to_string())),
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
    assert_eq!(
        recorder.events,
        [
            RecordedEvent::PackageChoice("root".to_string()),
            RecordedEvent::VersionChoice("root".to_string(), 1),
            RecordedEvent::PackageChoice("a".to_string()),
            RecordedEvent::VersionChoice("a".to_string(), 1),
            RecordedEvent::Solution,
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
