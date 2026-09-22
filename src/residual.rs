//! Exact finite-domain reduction before Pareto factor enumeration.
//!
//! Edges are residual incompatibilities, not the union of all metadata references. In particular,
//! a dependency already satisfied by every remaining value does not couple its consumers.

use crate::{
    Dependencies, DependencyProvider, IncompatibilityConstraintTerm, Map, Package, PubGrubError,
    Term, VersionSet,
};

#[derive(Clone)]
struct Domain<P, V> {
    package: P,
    values: Vec<Option<V>>,
}

type Clause<VS> = Vec<(usize, Term<VS>)>;

/// Finite provider clauses, shared by residual decomposition and substitution proofs.
pub(crate) struct ConstraintModel<P, VS: VersionSet> {
    ids: Map<P, usize>,
    domains: Vec<Domain<P, VS::V>>,
    clauses: Vec<Clause<VS>>,
    occurrences: Vec<Vec<usize>>,
}

pub(crate) struct Partition<P> {
    pub(crate) variable: Vec<Vec<P>>,
    fixed: Vec<P>,
}

impl<P> Partition<P> {
    pub(crate) fn into_components(mut self) -> Vec<Vec<P>> {
        if !self.fixed.is_empty() {
            self.variable.push(self.fixed);
        }
        self.variable
    }
}

pub(crate) fn components<DP: DependencyProvider>(
    provider: &DP,
    root: &DP::P,
    version: &DP::V,
    projected: &[DP::P],
    required: &[(DP::P, Term<DP::VS>)],
) -> Result<Vec<Vec<DP::P>>, PubGrubError<DP>> {
    let model = load(provider, root, projected, required)?;
    Ok(model
        .partition(provider, root, version, projected, required)?
        .into_components())
}

pub(crate) fn load<DP: DependencyProvider>(
    provider: &DP,
    root: &DP::P,
    projected: &[DP::P],
    required: &[(DP::P, Term<DP::VS>)],
) -> Result<ConstraintModel<DP::P, DP::VS>, PubGrubError<DP>> {
    let mut ids = Map::default();
    let mut domains = Vec::new();
    intern(root, &mut ids, &mut domains);
    for package in projected
        .iter()
        .chain(required.iter().map(|(package, _)| package))
    {
        intern(package, &mut ids, &mut domains);
    }
    let mut clauses = Vec::new();
    let mut index = 0;
    while index < domains.len() {
        provider
            .should_cancel()
            .map_err(PubGrubError::ErrorInShouldCancel)?;
        let package = domains[index].package.clone();
        let mut remaining = DP::VS::full();
        while let Some(candidate) =
            provider
                .choose_version(&package, &remaining)
                .map_err(|source| PubGrubError::ErrorChoosingVersion {
                    package: package.clone(),
                    source,
                })?
        {
            provider
                .should_cancel()
                .map_err(PubGrubError::ErrorInShouldCancel)?;
            remaining = remaining.intersection(&DP::VS::singleton(candidate.clone()).complement());
            domains[index].values.push(Some(candidate.clone()));
            let owner = (index, Term::Positive(DP::VS::singleton(candidate.clone())));
            let dependencies =
                provider
                    .get_dependencies(&package, &candidate)
                    .map_err(|source| PubGrubError::ErrorRetrievingDependencies {
                        package: package.clone(),
                        version: candidate.clone(),
                        source,
                    })?;
            match dependencies {
                Dependencies::Unavailable(_) => clauses.push(vec![owner.clone()]),
                Dependencies::Available(dependencies) => {
                    for (dependency, range) in dependencies {
                        let id = intern(&dependency, &mut ids, &mut domains);
                        clauses.push(normalize(vec![owner.clone(), (id, Term::Negative(range))]));
                    }
                    let incompatibilities = provider
                        .get_incompatibilities(&package, &candidate)
                        .map_err(|source| PubGrubError::ErrorRetrievingDependencies {
                            package: package.clone(),
                            version: candidate.clone(),
                            source,
                        })?;
                    for incompatibility in incompatibilities {
                        let mut clause = vec![owner.clone()];
                        for term in incompatibility.terms {
                            let (dependency, term) = match term {
                                IncompatibilityConstraintTerm::Positive(p, r) => {
                                    (p, Term::Positive(r))
                                }
                                IncompatibilityConstraintTerm::Negative(p, r) => {
                                    (p, Term::Negative(r))
                                }
                            };
                            let id = intern(&dependency, &mut ids, &mut domains);
                            clause.push((id, term));
                        }
                        clauses.push(normalize(clause));
                    }
                }
            }
        }
        index += 1;
    }
    let mut occurrences = vec![Vec::new(); domains.len()];
    for (index, clause) in clauses.iter().enumerate() {
        for (id, _) in clause {
            occurrences[*id].push(index);
        }
    }
    Ok(ConstraintModel {
        ids,
        domains,
        clauses,
        occurrences,
    })
}

impl<P: Package, VS: VersionSet> ConstraintModel<P, VS> {
    pub(crate) fn partition<DP: DependencyProvider<P = P, VS = VS, V = VS::V>>(
        &self,
        provider: &DP,
        root: &P,
        version: &VS::V,
        projected: &[P],
        required: &[(P, Term<VS>)],
    ) -> Result<Partition<P>, PubGrubError<DP>> {
        let ids = &self.ids;
        let clauses = &self.clauses;
        let mut domains = self.domains.clone();
        domains[ids[root]]
            .values
            .retain(|value| value.as_ref() == Some(version));
        for (package, term) in required {
            domains[ids[package]]
                .values
                .retain(|value| matches(term, value.as_ref()));
        }

        // Unit propagation on finite domains. On contradiction leave explanation construction to
        // the normal solver, which retains provider reasons and derivation events.
        loop {
            provider
                .should_cancel()
                .map_err(PubGrubError::ErrorInShouldCancel)?;
            if domains.iter().any(|domain| domain.values.is_empty()) {
                return Ok(Partition {
                    variable: vec![projected.to_vec()],
                    fixed: Vec::new(),
                });
            }
            let mut changed = false;
            for clause in clauses {
                let active = residual(clause, &domains);
                if let Some(active) = active {
                    if active.is_empty() {
                        return Ok(Partition {
                            variable: vec![projected.to_vec()],
                            fixed: Vec::new(),
                        });
                    }
                    if let [index] = active.as_slice() {
                        let (id, term) = &clause[*index];
                        let values = &mut domains[*id].values;
                        let before = values.len();
                        values.retain(|value| !matches(term, value.as_ref()));
                        changed |= before != values.len();
                    }
                }
            }
            if !changed {
                break;
            }
        }

        let mut parent = (0..domains.len()).collect::<Vec<_>>();
        for clause in clauses {
            if let Some(active) = residual(clause, &domains)
                && let Some(first) = active.first()
            {
                for index in active.iter().skip(1) {
                    let a = representative(&mut parent, clause[*first].0);
                    let b = representative(&mut parent, clause[*index].0);
                    parent[b] = a;
                }
            }
        }
        let mut groups: Vec<Vec<P>> = Vec::new();
        let mut group_ids = Map::default();
        let mut fixed = Vec::new();
        for package in projected {
            let id = ids[package];
            if domains[id].values.len() <= 1 {
                fixed.push(package.clone());
                continue;
            }
            let representative = representative(&mut parent, id);
            let group = *group_ids.entry(representative).or_insert_with(|| {
                groups.push(Vec::new());
                groups.len() - 1
            });
            groups[group].push(package.clone());
        }
        Ok(Partition {
            variable: groups,
            fixed,
        })
    }

    /// Lift an observed strict improvement to a cube of dominated assignments.
    ///
    /// Bound changed projected coordinates by their replacement values. For each clause touched by the
    /// substitution, either a replacement value already falsifies it, or retain one unchanged
    /// false term as a boundary guard. Consequently the same substitution is feasible for EVERY
    /// solution in this cube, independent of all unmentioned coordinates. Hidden provider
    /// packages may be replaced too, but never participate in the Pareto objective or remain as
    /// guards on arbitrary internal choices. At least one projected coordinate strictly improves.
    pub(crate) fn substitution_region<R: Fn(&VS::V) -> VS, F: Fn(&VS::V) -> VS>(
        &self,
        before: &crate::SelectedDependencies<P, VS::V>,
        after: &crate::SelectedDependencies<P, VS::V>,
        projected: &[P],
        same_precedence: &R,
        strictly_higher: &F,
        preferred: &P,
    ) -> Vec<(P, Term<VS>)> {
        // A fresh solve may gratuitously switch equal-rank artifacts in unrelated components.
        // Start with ONE strict improvement and close only over clauses needed to make that
        // substitution feasible. This avoids turning those unrelated switches into cube guards.
        let seed = std::iter::once(preferred)
            .chain(projected)
            .find(|package| {
                before
                    .get(package)
                    .zip(after.get(package))
                    .is_some_and(|(old, new)| strictly_higher(old).contains(new))
            })
            .expect("a dominance substitution must strictly improve a projected coordinate");
        let mut changed = vec![false; self.domains.len()];
        let projected_ids = projected
            .iter()
            .map(|package| self.ids[package])
            .collect::<crate::Set<_>>();
        let seed = self.ids[seed];
        changed[seed] = true;
        let mut pending = std::collections::VecDeque::from(self.occurrences[seed].clone());
        while let Some(index) = pending.pop_front() {
            let clause = &self.clauses[index];
            if clause.iter().any(|(id, term)| {
                changed[*id] && !matches(term, after.get(&self.domains[*id].package))
            }) {
                continue;
            }
            if clause.iter().any(|(id, term)| {
                !changed[*id]
                    && projected_ids.contains(id)
                    && !matches(term, before.get(&self.domains[*id].package))
            }) {
                continue;
            }
            let (id, _) = clause
                .iter()
                .filter(|(id, term)| {
                    !changed[*id] && !matches(term, after.get(&self.domains[*id].package))
                })
                .min_by_key(|(id, _)| (projected_ids.contains(id), self.occurrences[*id].len()))
                .expect(
                    "a feasible improved solution supplies a replacement for every violated clause",
                );
            changed[*id] = true;
            pending.extend(&self.occurrences[*id]);
        }
        let mut guards = projected
            .iter()
            .filter(|package| changed[self.ids[*package]])
            .map(|package| {
                let term = after.get(package).map_or_else(
                    || Term::Negative(VS::full()),
                    |version| {
                        // The replacement's feasibility does not depend on the old values of
                        // replaced coordinates. Cover their entire dominated ranges, not just
                        // this witness's concrete artifact identities.
                        let mut allowed = strictly_higher(version).complement();
                        if self.ids[package] == seed {
                            allowed = allowed.intersection(&same_precedence(version).complement());
                        }
                        Term::Positive(allowed)
                    },
                );
                (self.ids[package], term)
            })
            .collect::<Vec<_>>();
        for clause in &self.clauses {
            if !clause.iter().any(|(id, _)| changed[*id]) {
                continue;
            }
            if clause.iter().any(|(id, term)| {
                changed[*id] && !matches(term, after.get(&self.domains[*id].package))
            }) {
                continue;
            }
            let (id, term) = clause
                .iter()
                .find(|(id, term)| {
                    !changed[*id]
                        && projected_ids.contains(id)
                        && !matches(term, before.get(&self.domains[*id].package))
                })
                .expect("a feasible replacement must falsify every provider clause");
            guards.push((*id, term.negate()));
        }
        normalize(guards)
            .into_iter()
            .map(|(id, term)| (self.domains[id].package.clone(), term))
            .collect()
    }
}

fn intern<P: Package, V>(
    package: &P,
    ids: &mut Map<P, usize>,
    domains: &mut Vec<Domain<P, V>>,
) -> usize {
    *ids.entry(package.clone()).or_insert_with(|| {
        domains.push(Domain {
            package: package.clone(),
            values: vec![None],
        });
        domains.len() - 1
    })
}

fn normalize<VS: VersionSet>(clause: Clause<VS>) -> Clause<VS> {
    let mut merged: Clause<VS> = Vec::new();
    for (id, term) in clause {
        if let Some((_, existing)) = merged.iter_mut().find(|(existing, _)| *existing == id) {
            *existing = existing.intersection(&term);
        } else {
            merged.push((id, term));
        }
    }
    merged
}

fn matches<VS: VersionSet>(term: &Term<VS>, value: Option<&VS::V>) -> bool {
    value.map_or(matches!(term, Term::Negative(_)), |value| {
        term.contains(value)
    })
}

fn residual<P, VS: VersionSet>(
    clause: &Clause<VS>,
    domains: &[Domain<P, VS::V>],
) -> Option<Vec<usize>> {
    let mut active = Vec::new();
    for (index, (id, term)) in clause.iter().enumerate() {
        let values = &domains[*id].values;
        let matching = values
            .iter()
            .filter(|value| matches(term, value.as_ref()))
            .count();
        if matching == 0 {
            return None;
        }
        if matching < values.len() {
            active.push(index);
        }
    }
    Some(active)
}

fn representative(parent: &mut [usize], mut id: usize) -> usize {
    while parent[id] != id {
        parent[id] = parent[parent[id]];
        id = parent[id];
    }
    id
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Ranges, SelectedDependencies};

    // Check the pruning proof independently of front enumeration and its separator heuristic.
    // Enumerate all nonempty truth tables over two projected coordinates and a hidden one.
    #[test]
    fn substitution_regions_never_contain_a_pareto_point() {
        for optional in [false, true] {
            let second = if optional {
                [None, Some(1u32)]
            } else {
                [Some(1), Some(2)]
            };
            let points = [Some(1u32), Some(2)]
                .into_iter()
                .flat_map(|a| {
                    second
                        .into_iter()
                        .flat_map(move |b| [None, Some(1)].map(|hidden| [a, b, hidden]))
                })
                .collect::<Vec<_>>();
            let dominates = |a: &[Option<u32>; 3], b: &[Option<u32>; 3]| {
                (0..2).all(|i| a[i].is_some() == b[i].is_some() && a[i] >= b[i])
                    && (0..2).any(|i| a[i] > b[i])
            };
            let state = |v: Option<u32>| {
                v.map_or_else(
                    || Term::Negative(Ranges::full()),
                    |v| Term::Positive(Ranges::singleton(v)),
                )
            };
            for mask in 1usize..(1 << points.len()) {
                let feasible = points
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, p)| p)
                    .collect::<Vec<_>>();
                let mut clauses = points
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) == 0)
                    .map(|(_, point)| {
                        point
                            .iter()
                            .enumerate()
                            .map(|(id, v)| (id, state(*v)))
                            .collect()
                    })
                    .collect::<Vec<Clause<Ranges<u32>>>>();
                clauses.push(vec![(0, Term::Negative(Ranges::full()))]);
                if !optional {
                    clauses.push(vec![(1, Term::Negative(Ranges::full()))]);
                }
                let mut occurrences = vec![Vec::new(); 3];
                for (index, clause) in clauses.iter().enumerate() {
                    for (id, _) in clause {
                        occurrences[*id].push(index);
                    }
                }
                let model = ConstraintModel {
                    ids: (0usize..3).map(|i| (i, i)).collect(),
                    domains: (0usize..3)
                        .map(|package| Domain {
                            package,
                            values: Vec::new(),
                        })
                        .collect(),
                    clauses,
                    occurrences,
                };
                let assignment = |point: &[Option<u32>; 3]| {
                    point
                        .iter()
                        .enumerate()
                        .filter_map(|(id, value)| value.map(|v| (id, v)))
                        .collect::<SelectedDependencies<usize, u32>>()
                };
                for before in &feasible {
                    for after in feasible.iter().filter(|after| dominates(after, before)) {
                        let region = model.substitution_region(
                            &assignment(before),
                            &assignment(after),
                            &[0, 1],
                            &|v: &u32| Ranges::singleton(*v),
                            &|v: &u32| Ranges::strictly_higher_than(*v),
                            &0,
                        );
                        assert!(
                            region
                                .iter()
                                .all(|(id, term)| matches(term, before[*id].as_ref()))
                        );
                        for point in feasible.iter().filter(|point| {
                            region
                                .iter()
                                .all(|(id, term)| matches(term, point[*id].as_ref()))
                        }) {
                            assert!(
                                feasible.iter().any(|other| dominates(other, point)),
                                "pruned a maximal point: mask={mask}, point={point:?}, region={region:?}"
                            );
                        }
                    }
                }
            }
        }
    }
}
