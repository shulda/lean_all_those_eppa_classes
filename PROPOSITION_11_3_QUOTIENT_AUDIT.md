# Proposition 11.3 quotient audit: existential pushforward is insufficient

**Status:** mathematical/computational regression, **NOT** yet a Lean theorem.
This note records an obstruction to a tempting intermediate-quotient
shortcut. It does **not** challenge Proposition 11.3 or its published proof.

## The finite counterexample

Use a relational language with a symmetric irreflexive binary symbol
`E` and an additional ternary symbol `T`, and trivial Γ-action.
There are no functions, so all one-point closures are singletons.

- Source `A`: a graph 5-cycle on vertices `0,1,2,3,4`, with edges
  `01,12,23,34,40` and **empty** `T`.
- Target `B`: a complete graph on `0,1,2`, with `T` containing
  **all ordered triples of pairwise distinct vertices** (and no
  triples containing repetitions).
- Define the vertex map `f:A→B` by

  | source | 0 | 1 | 2 | 3 | 4 |
  |---|---:|---:|---:|---:|---:|
  | f | 0 | 1 | 2 | 0 | 1 |

  This is a graph proper colouring, hence an `E`-homomorphism;
  and `T` is empty in `A`, so `f` is a homomorphism as well.

**Why `f` is a homomorphism-embedding.** The only irreducible induced
substructures of `A` are its singletons and edges: every vertex set
of size at least three fails to be a clique of the 5-cycle and has
a free decomposition (there are no ternary tuples or functions).
On each singleton or edge, `f` is injective and preserves/reflects
all relation data. In particular, no triple of pairwise distinct
vertices is supported on one such piece.

Take the *local one-point-closure collapse* `q:A↠Q` identifying
`0` with `3`, while leaving `1,2,4` distinct. Write `u` for
the identified class `{0,3}`. Give `Q` the **existential
pushforward** interpretation of all relations of `A`:

- `Q` has vertices `u,1,2,4`.
- Its edges are `u1,12,2u,u4`.
- `T^Q` is empty.

Then `q` is a homomorphism-embedding for exactly the same
singleton/edge check as for `f`. In particular the first factor
of the proposed quotient is perfectly valid.

The descended vertex map is

  `g(u)=0, g(1)=1, g(2)=2, g(4)=1`,

and `f=g∘q`. It is a homomorphism, but **not a
homomorphism-embedding**: `{u,1,2}` is a triangle, hence an
irreducible induced substructure of `Q`. The tuple `(u,1,2)`
is **not** in `T^Q`, whereas `(0,1,2)` is in `T^B`.
Thus `g` fails relation reflection on this new irreducible
substructure.

## Exact lesson for the Lean construction

The generic existential pushforward built in
`StrongCompletionPushforward.lean` is still valuable: it provides
both *ordinary* homomorphisms and their correct Γ-components.
The source-side quotient map can also be a homomorphism-embedding,
as the unary-fibre lemmas seek to prove. But these facts **cannot**
by themselves establish that the descended map is a
homomorphism-embedding.

The intermediate Γ-structure must be **appropriately saturated
with relation data from B on newly irreducible configurations**.
In this toy example, adding the relevant ternary tuples to `Q`
repairs the displayed obstruction and does not alter the exact
restriction of `q` to the old singleton/edge irreducibles.
A general, audited saturation/extension construction is still
required, especially to preserve exact set-valued unary-function
fibres and Γ-language actions.

This is the remaining structural difficulty behind the
minimal-factorization step in Proposition 11.3; the abstract
kernel-defect and five-region lemmas do not bypass it.

## Independent finite sanity check

Enumerating all closed induced subsets and proper free
decompositions in this function-free example gives:

- `f:A→B`: homomorphism-embedding — **YES**.
- `q:A→Q`: homomorphism-embedding — **YES**.
- `g:Q→B`: homomorphism-embedding — **NO**.

This enumeration was an external finite check, not a Lean
formalization. It should eventually become a dedicated Lean
regression before claiming the full Proposition 11.3 is closed.
