#!/usr/bin/env python3
"""Reproduce the C5 / K3 quotient-pushforward obstruction from
PROPOSITION_11_3_QUOTIENT_AUDIT.md.

Standard Python only. No third-party packages. The script checks the
*exact* free-decomposition definition for every induced subset, not
merely a convenient characterization of graph cliques.
"""
from itertools import combinations, permutations, product


def subsets(items):
    ordered = tuple(sorted(items))
    for size in range(len(ordered) + 1):
        for tup in combinations(ordered, size):
            yield frozenset(tup)


def graph_tuples(edges):
    return frozenset(t for e in edges for t in permutations(tuple(e), 2))


def model(vertices, edge_tuples, triples):
    return (frozenset(vertices), frozenset(edge_tuples), frozenset(triples))


def rels(model_):
    _, binary, ternary = model_
    return ((2, binary), (3, ternary))


def has_free_decomposition(model_, subset):
    for left in subsets(subset):
        for right in subsets(subset):
            if left == subset or right == subset or left | right != subset:
                continue
            if all(
                set(t) <= left or set(t) <= right
                for _, relation in rels(model_)
                for t in relation
                if set(t) <= subset
            ):
                return True
    return False


def irreducibles(model_):
    return tuple(s for s in subsets(model_[0])
                 if not has_free_decomposition(model_, s))


def homomorphism(src, target, mapping):
    for _, relation in rels(src):
        arity = len(next(iter(relation))) if relation else None
        trg = target[1] if arity == 2 else target[2] if arity == 3 else None
        if trg is None:
            # An empty source relation is automatically preserved.
            continue
        if any(tuple(mapping[x] for x in t) not in trg for t in relation):
            return False
    return True


def locally_exact(src, target, mapping, vertices):
    if len({mapping[x] for x in vertices}) != len(vertices):
        return False
    for arity, rel in rels(src):
        target_rel = target[1] if arity == 2 else target[2]
        for t in product(sorted(vertices), repeat=arity):
            if (t in rel) != (tuple(mapping[x] for x in t) in target_rel):
                return False
    return True


def homomorphism_embedding(src, target, mapping):
    return homomorphism(src, target, mapping) and all(
        locally_exact(src, target, mapping, s) for s in irreducibles(src)
    )


A = model(
    range(5),
    graph_tuples({frozenset((i, (i + 1) % 5)) for i in range(5)}),
    ()
)
B = model(
    range(3),
    graph_tuples({frozenset(e) for e in combinations(range(3), 2)}),
    permutations(range(3), 3)
)

f = {0: 0, 1: 1, 2: 2, 3: 0, 4: 1}
q = {0: 0, 1: 1, 2: 2, 3: 0, 4: 4}
Q = model(
    set(q.values()),
    (tuple(q[x] for x in t) for t in A[1]),
    (tuple(q[x] for x in t) for t in A[2])
)
g = {z: f[next(x for x in A[0] if q[x] == z)] for z in Q[0]}

assert all(g[q[x]] == f[x] for x in A[0])
assert set(q.values()) == Q[0]
assert len(Q[0]) == 4 and len(A[0]) == 5

assert homomorphism_embedding(A, B, f), "f must be a hom-embedding"
assert homomorphism_embedding(A, Q, q), "q must be a hom-embedding"
assert homomorphism(Q, B, g), "g must be a homomorphism"
assert not homomorphism_embedding(Q, B, g), (
    "g MUST fail to be a hom-embedding"
)

triangle = frozenset((0, 1, 2))
assert triangle in irreducibles(Q)
assert (0, 1, 2) not in Q[2]
assert tuple(g[x] for x in (0, 1, 2)) in B[2]

print("PASS: A→B and A→Q are homomorphism-embeddings.")
print("PASS: Q→B is a homomorphism but not a homomorphism-embedding.")
print("WITNESS: irreducible triangle {0,1,2}, missing ternary tuple.")
