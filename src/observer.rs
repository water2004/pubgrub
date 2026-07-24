// SPDX-License-Identifier: MPL-2.0

//! Observe the decisions and derivations made during dependency resolution.
//!
//! These events expose the actual path taken by the solver. This makes it possible to explain why
//! a version was skipped in a successful resolution, where an unsatisfiable derivation tree from a
//! separate counterfactual solve would answer a different question.
//!
//! [`SolverEvent::VersionChoice`] is a proposal made by the dependency provider, while
//! [`SolverEvent::Decision`] means that proposal was committed to the partial solution. A committed
//! decision may later be discarded by [`SolverEvent::Backtrack`]. For a version that was never
//! proposed, compare [`SolverEvent::Derivation::previous`] and
//! [`SolverEvent::Derivation::current`] with [`Term::contains`](crate::Term::contains) to find the
//! propagation step that excluded it.

use std::fmt::{Debug, Display};

use crate::{DerivationTree, Package, Term, VersionSet};

/// A structured event emitted while resolving dependencies.
///
/// Events describe the path taken by a specific solver run. They are not a proof that an
/// alternative solution does not exist.
#[derive(Debug)]
#[non_exhaustive]
pub enum SolverEvent<'a, P, VS, M>
where
    P: Package,
    VS: VersionSet,
    M: Eq + Clone + Debug + Display,
{
    /// The solver selected a package for its next version decision.
    PackageChoice {
        /// Package selected for the next decision.
        package: &'a P,
        /// Versions currently allowed for the package.
        allowed: &'a VS,
    },
    /// The dependency provider selected a version for a package.
    VersionChoice {
        /// Package for which a version was selected.
        package: &'a P,
        /// Version selected by the dependency provider.
        version: &'a VS::V,
        /// Versions allowed when the selection was made.
        allowed: &'a VS,
    },
    /// The solver committed a package version to the partial solution.
    Decision {
        /// Package whose version was committed.
        package: &'a P,
        /// Version committed to the partial solution.
        version: &'a VS::V,
        /// Decision level assigned to the package version.
        decision_level: u32,
    },
    /// The dependency provider found no version in the currently allowed set.
    NoVersion {
        /// Package for which no version was found.
        package: &'a P,
        /// Versions allowed when the lookup failed.
        allowed: &'a VS,
    },
    /// Unit propagation narrowed the versions allowed for a package.
    Derivation {
        /// Package whose allowed versions changed.
        package: &'a P,
        /// Allowed term before applying the derivation, if the package was already known.
        previous: Option<&'a Term<VS>>,
        /// Allowed term after applying the derivation.
        current: &'a Term<VS>,
        /// Incompatibility tree that caused the derivation.
        cause: &'a DerivationTree<P, VS, M>,
    },
    /// Unit propagation found an incompatibility satisfied by the partial solution.
    Conflict {
        /// Incompatibility tree that triggered conflict resolution.
        cause: &'a DerivationTree<P, VS, M>,
    },
    /// Conflict resolution discarded decisions and learned an incompatibility.
    Backtrack {
        /// Decision level before backtracking.
        from_level: u32,
        /// Decision level retained after backtracking.
        to_level: u32,
        /// Learned incompatibility that caused the backtrack.
        cause: &'a DerivationTree<P, VS, M>,
    },
    /// The solver found a complete solution.
    Solution,
}

/// Receives structured events from a solver run.
///
/// Implementations that only need package and version choices can return `false` from
/// [`captures_derivation_trees`](SolverObserver::captures_derivation_trees) to avoid constructing
/// intermediate derivation trees.
pub trait SolverObserver<P, VS, M>
where
    P: Package,
    VS: VersionSet,
    M: Eq + Clone + Debug + Display,
{
    /// Receive one event from the solver.
    fn on_event(&mut self, event: SolverEvent<'_, P, VS, M>);

    /// Whether the solver should construct and emit events containing derivation trees.
    fn captures_derivation_trees(&self) -> bool {
        true
    }
}

pub(crate) struct NoopSolverObserver;

impl<P, VS, M> SolverObserver<P, VS, M> for NoopSolverObserver
where
    P: Package,
    VS: VersionSet,
    M: Eq + Clone + Debug + Display,
{
    #[inline]
    fn on_event(&mut self, _event: SolverEvent<'_, P, VS, M>) {}

    #[inline]
    fn captures_derivation_trees(&self) -> bool {
        false
    }
}
