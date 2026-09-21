//! Exact finite-domain reduction before Pareto factor enumeration.
//!
//! Edges are residual incompatibilities, not the union of all metadata references. In particular,
//! a dependency already satisfied by every remaining value does not couple its consumers.

use crate::{
    Dependencies, DependencyProvider, IncompatibilityConstraintTerm, Map, Package, PubGrubError,
    Term, VersionSet,
};

struct Domain<P, V> {
    package: P,
    values: Vec<Option<V>>,
}

type Clause<VS> = Vec<(usize, Term<VS>)>;

pub(crate) fn components<DP: DependencyProvider>(
    provider: &DP,
    root: &DP::P,
    version: &DP::V,
    projected: &[DP::P],
    required: &[(DP::P, Term<DP::VS>)],
) -> Result<Vec<Vec<DP::P>>, PubGrubError<DP>> {
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
            return Ok(vec![projected.to_vec()]);
        }
        let mut changed = false;
        for clause in &clauses {
            let active = residual(clause, &domains);
            if let Some(active) = active {
                if active.is_empty() {
                    return Ok(vec![projected.to_vec()]);
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
    for clause in &clauses {
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
    let mut groups: Vec<Vec<DP::P>> = Vec::new();
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
    if !fixed.is_empty() {
        groups.push(fixed);
    }
    Ok(groups)
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
