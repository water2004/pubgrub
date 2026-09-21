# PubGrub

[![guide](https://img.shields.io/badge/guide-pubgrub-pink?logo=read-the-docs)][guide]
[![docs.rs](https://img.shields.io/badge/docs.rs-pubgrub-yellow)][docs]
[![crates.io](https://img.shields.io/crates/v/pubgrub.svg?logo=rust)][crates]

PubGrub is a high performance version resolution algorithm with good error
messages, it finds a set of packages and versions that satisfy all the
constraints of a set of packages and their transitive dependencies. This rust
implementation is used by [uv][uv] and as designated replacement for cargo's
solver, while other PubGrub implementations are used by [dart][medium-pubgrub],
[bundler][bundler] and [poetry][poetry].

This rust implementation of PubGrub is highly flexible. It is generic over the
package type (including virtual packages), the version format and version set
used, the user controls package and version prioritization (including highest
and lowest version solving) and the error rendering can be customized.

## Getting started

The best way to get started with PubGrub are the [guide][guide] and the
algorithm's [introductory blog post][medium-pubgrub]. There are also some
runnable examples in the [examples](./examples) folder. More details are
available in the [stable API documentation][docs] and the [development API
documentation][docs-dev] from dev branch.

## The PubGrub Algorithm

PubGrub was introduced in 2018 in a [blog post][medium-pubgrub] by Natalie
Weizenbaum, who developed it for the dart package manager. Algorithmically, it
is a SAT solver using conflict-driven clause learning. A detailed explanation of
the algorithm is [available on GitHub][github-pubgrub], and complemented by our
[internals guide][guide-internals]. The foundation of the algorithm is based on
Answer Set Programming (ASP), and the book "[Answer Set Solving in
Practice][potassco-book]" by Martin Gebser, Roland Kaminski, Benjamin Kaufmann
and Torsten Schaub.

## Error messages

While traditional SAT solvers can find a solution fast, they don't provide an
understable explanation when they didn't find a solution. PubGrub is both very
fast and can explain errors more clearly than the alternatives.

An error message from the blog post:

```txt
Because dropdown >=2.0.0 depends on icons >=2.0.0 and
  root depends on icons <2.0.0, dropdown >=2.0.0 is forbidden.

And because menu >=1.1.0 depends on dropdown >=2.0.0,
  menu >=1.1.0 is forbidden.

And because menu <1.1.0 depends on dropdown >=1.0.0 <2.0.0
  which depends on intl <4.0.0, every version of menu
  requires intl <4.0.0.

So, because root depends on both menu >=1.0.0 and intl >=5.0.0,
  version solving failed.
```

Two examples from uv:

```
  × No solution found when resolving dependencies:
  ╰─▶ Because project[extra2] depends on sortedcontainers==2.4.0 and project[extra1] depends on sortedcontainers==2.3.0, we can conclude that project[extra1] and project[extra2] are incompatible.
      And because your project requires project[extra1] and project[extra2], we can conclude that your project's requirements are unsatisfiable.
```

```
  × No solution found when resolving dependencies for split (included: dummy[extra2], dummysub[extra1]; excluded: dummy[extra1], dummysub[extra2]):
  ╰─▶ Because dummy[extra2] depends on proxy1[extra2] and only proxy1[extra2]==0.1.0 is available, we can conclude that dummy[extra2] depends on proxy1[extra2]==0.1.0. (1)

    Because proxy1[extra1]==0.1.0 depends on anyio==4.1.0 and proxy1[extra2]==0.1.0 depends on anyio==4.2.0, we can conclude that proxy1[extra1]==0.1.0 and proxy1[extra2]==0.1.0 are incompatible.
    And because we know from (1) that dummy[extra2] depends on proxy1[extra2]==0.1.0, we can conclude that dummy[extra2] and proxy1[extra1]==0.1.0 are incompatible.
    And because only proxy1[extra1]==0.1.0 is available and dummysub[extra1] depends on proxy1[extra1], we can conclude that dummysub[extra1] and dummy[extra2] are incompatible.
    And because your workspace requires dummy[extra2] and dummysub[extra1], we can conclude that your workspace's requirements are unsatisfiable.
```

## Explaining a successful resolution

An unsatisfiable derivation tree proves that no solution exists. It does not
explain why one particular version was skipped in a successful resolution.
Use `resolve_with_observer` when that distinction matters. Its typed events
describe the actual path taken by the solver:

- `VersionChoice` records a version proposed by the dependency provider.
- `Decision` records that the proposal was committed to the partial solution.
- `Derivation` records when propagation narrowed a package's allowed versions.
- `Conflict` and `Backtrack` retain the incompatibility trees used by conflict
  resolution.

`Term::contains` lets an observer detect the exact derivation that changed a
target version from allowed to excluded. The event's derivation tree can then
be cloned and rendered with application-specific package names and messages,
without parsing logs or running a second counterfactual solve. See the runnable
[`explain_version`](./examples/explain_version.rs) example.

## Enumerating Pareto-maximal solutions

`resolve_maximal_solutions` enumerates the complete Pareto front of the
requested packages: there is no other feasible solution in which every selected
requested package stays equivalent or moves higher and at least one moves
strictly higher. The requested package list is also the solution projection;
solver-internal or otherwise unlisted packages may change and do not create a
distinct result.

Absence is a first-class, backtrackable package state. Presence and absence are
incomparable in the version order: dominance compares solutions with the same
projected package support. Thus optional installation choices are retained, but
no result may violate a dependency disjunction by silently treating all
undecided alternatives as absent.

The enumerator grows each candidate along non-decreasing projected coordinates
until it reaches a Pareto point. It then excludes the whole region dominated by
that point. Independent lower versions therefore do not create a Cartesian
product of locally maximality checks.

Use `resolve_maximal_solutions_with_observer` when the application also needs
the real derivation path for each result. It continues one enumeration session
and emits `SolverEvent::Solution` once per retained point. Feasibility probes
have typed start/finish boundaries and outcomes. A successful probe becomes the
new retained path; a failed probe can be rolled back by a stateful observer.
Enumeration clauses have their own `ExcludedSolution` reason, so they cannot
be mistaken for provider dependency metadata.

The caller supplies the packages to maximize and three version-set functions:
the same selectable realization, every realization at the same ordering
precedence, and every strictly higher version. This lets applications choose
whether multiple sources are one realization while still returning distinct
realizations that share a Pareto rank. The solver validates containment and
disjointness between these sets before adding enumeration clauses.

The Pareto or co-Pareto front can still be large;
`DependencyProvider::should_cancel` is checked throughout enumeration.

For factored results, use `resolve_factored_preference_solutions` followed by
`resolve_factored_maximal_solutions_for_preference_decisions`. These APIs require
a finite, stable provider universe and accept flat projections, not
caller-guessed partitions. The solver discovers the complete candidate closure,
propagates fixed domains and partitions residual incompatibility hyperedges,
including non-projected intermediate packages. Before enumerating version
factors it also proves frontier-invariant states with dominance-pruned queries,
then reduces the graph again. Already satisfied shared dependencies no longer
join independent optional consumers. Unproved dependencies remain coupled.
The representation stores local alternatives rather than their Cartesian
product; `resolve_for_preference_and_package_decisions_with_observer` verifies
the final choices together in the original graph.

## Provider-defined incompatibilities

Some package metadata cannot be represented as a list of ordinary dependency
edges. A provider can return conditional clauses from
`DependencyProvider::get_incompatibilities`:

```rust
IncompatibilityConstraint {
    terms: vec![IncompatibilityConstraintTerm::Positive(other, versions)],
    reason: MyReason::Conflict,
}
```

The selected declaring package/version is inserted as a positive term
automatically. Positive terms express combinations that cannot coexist;
negative terms express conditional requirements. These clauses are added to
the active solver state when the declaring version is chosen, so their
metadata is retained in conflict learning and the original derivation tree.
They are not a post-processing explanation pass.

## Contributing

Discussion and development happens here on GitHub and on our
[Zulip stream](https://rust-lang.zulipchat.com/#narrow/stream/260232-t-cargo.2FPubGrub).
Please join in!

Remember to always be considerate of others, who may have different native
languages, cultures and experiences. We want everyone to feel welcomed, let us
know with a private message on Zulip if you don't feel that way.

[uv]: https://docs.astral.sh/uv/reference/internals/resolver
[bundler]: https://bundler.io/blog/2023/01/31/bundler-v2-4.html
[poetry]: https://github.com/sdispater/mixology
[crates]: https://crates.io/crates/pubgrub
[guide]: https://pubgrub-rs-guide.pages.dev
[guide-internals]: https://pubgrub-rs-guide.pages.dev/internals/intro.html
[docs]: https://docs.rs/pubgrub
[docs-dev]: https://pubgrub-rs.github.io/pubgrub/pubgrub/
[medium-pubgrub]: https://medium.com/@nex3/pubgrub-2fb6470504f
[github-pubgrub]: https://github.com/dart-lang/pub/blob/master/doc/solver.md
[potassco-book]: https://potassco.org/book/
