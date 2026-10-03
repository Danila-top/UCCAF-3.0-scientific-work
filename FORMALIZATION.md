# UCCAF 3.0 — Lean 4 formalization

This branch is the first machine-checkable mathematical specification of the currently documented UCCAF 3.0 protocol.

## Formalized in phase 1

1. Score values are a subtype of rationals constrained by 0 <= score <= 100.
2. ResearchWork is a typed object containing id, title, IS, CS and P.
3. UCCI = (IS + 2 CS) / 2.
4. KSI = (IS + 2 CS + P) / 3.
5. MainBetter is an IS-only strict order.
6. MainSorted certifies that a ranking list is non-increasing in IS.
7. MasterTopN takes the first n entries of a certified ranking.

Lean proves:
- score lower and upper bounds by construction;
- UCCI is in [0, 150];
- KSI is in [0, 400/3];
- KSI(100,100,100) = 400/3;
- strict monotonicity of UCCI and KSI in IS;
- irreflexivity, transitivity and asymmetry of MainBetter;
- equivalence of MainBetter with the IS comparison;
- the main score depends on IS, not CS/P;
- MasterTopN has length at most n.

## Scientific boundary

These proofs establish properties of the chosen formal specification. They do not establish that IS/CS/P are empirically valid measures or that UCCAF is correct as an empirical evaluation methodology.

Next layers:
- deterministic tie-breaking;
- evidence and attribution;
- confidence and status;
- benchmark aggregation;
- exact Master Top-120 / Top-150 specification;
- evaluation consistency and invariance.
