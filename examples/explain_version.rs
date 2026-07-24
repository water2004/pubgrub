// SPDX-License-Identifier: MPL-2.0

use pubgrub::{
    DerivationTree, External, OfflineDependencyProvider, Ranges, SolverEvent, SolverObserver,
    resolve_with_observer,
};

type Cause = DerivationTree<&'static str, Ranges<u32>, String>;

struct ExplainVersion {
    package: &'static str,
    version: u32,
    exclusion: Option<Cause>,
}

impl SolverObserver<&'static str, Ranges<u32>, String> for ExplainVersion {
    fn on_event(&mut self, event: SolverEvent<'_, &'static str, Ranges<u32>, String>) {
        let SolverEvent::Derivation {
            package,
            previous,
            current,
            cause,
        } = event
        else {
            return;
        };

        let was_allowed = previous.is_none_or(|term| term.contains(&self.version));
        if *package == self.package && was_allowed && !current.contains(&self.version) {
            self.exclusion = Some(cause.clone());
        }
    }
}

fn print_external_facts(cause: &Cause) {
    match cause {
        DerivationTree::External(external) => match external {
            External::NotRoot(package, version) => {
                println!("  {package} {version} is not the root package");
            }
            External::NoVersions(package, versions) => {
                println!("  no version of {package} exists in {versions}");
            }
            External::FromDependencyOf(package, versions, dependency, required) => {
                println!("  {package} {versions} requires {dependency} {required}");
            }
            External::Custom(package, versions, message) => {
                println!("  {package} {versions} is unavailable: {message}");
            }
        },
        DerivationTree::Derived(derived) => {
            print_external_facts(&derived.cause1);
            print_external_facts(&derived.cause2);
        }
    }
}

fn main() {
    let mut provider = OfflineDependencyProvider::<&str, Ranges<u32>>::new();
    provider.add_dependencies("root", 1u32, [("a", Ranges::full()), ("b", Ranges::full())]);
    provider.add_dependencies("a", 2u32, []);
    provider.add_dependencies("a", 1u32, []);
    provider.add_dependencies("b", 1u32, [("a", Ranges::singleton(1u32))]);

    let mut observer = ExplainVersion {
        package: "a",
        version: 2,
        exclusion: None,
    };
    let solution = resolve_with_observer(&provider, "root", 1u32, &mut observer).unwrap();

    assert_eq!(solution.get(&"a"), Some(&1));
    println!("a 2 was excluded during the successful solve because:");
    print_external_facts(
        observer
            .exclusion
            .as_ref()
            .expect("the observer should retain the excluding derivation"),
    );
}
