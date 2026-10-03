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

## Formalized in phase 2 — evidence, attribution and deterministic ranking

- Evidence tiers E0–E5, reality classes and evaluation status are explicit datatypes.
- AttributionRecord stores the six causal-contribution buckets and carries a proof that they sum to 100%.
- MainBetterDet adds the deterministic tie-break IS descending, then id ascending.
- MainBetterDet is proved irreflexive, transitive and asymmetric.
- For distinct ids, MainBetterDet compares either direction, so equal-IS ties are resolvable.
- DeterministicallyRankedWorks requires both deterministic ordering and unique ids.
- Exact Top-120 and Top-150 lengths are proved under the natural list-length precondition.

## Formalized in phase 3 — uncertainty and hard-domain benchmark layer

- ScoreInterval stores low, point and high scores with machine-checked ordering.
- Interval width is proved non-negative.
- UncertaintyRecord binds point score, interval, confidence, evidence tier, breadth state, configuration id and calibration id.
- PostHumanEvidenceGate formalizes the baseline/configuration/IS interval/breadth/evidence/replication/status schema and proves point/interval consistency.
- HardDomain enumerates the 12 v3.0 hard-task domains D01–D12.
- BenchmarkObservation records domain, benchmark score, epistemic reality class, evidence tier and whether the score is estimated.
- BenchmarkMean is an explicit equal-weight aggregate over a finite set of benchmark observations.
- BenchmarkMean is proved to lie in [0,100].
- DomainCoverage records the versioned domain set and independence-map identifier; its size is bounded by the 12-domain registry.

## Scientific boundary

These proofs establish properties of the chosen formal specification. They do not establish that IS/CS/P are empirically valid measures or that UCCAF is correct as an empirical evaluation methodology.

The formalization deliberately keeps benchmark evidence separate from the primary IS ranking. It also keeps uncertainty, epistemic status, replication and configuration metadata explicit rather than silently converting benchmark performance or a single breakthrough into a general-intelligence claim.

## Next layers

- configuration identity as a structured, versioned object;
- explicit breadth gates B0–B4 and post-human eligibility predicates;
- measured/estimated/fictional benchmark separation with stronger invariants;
- benchmark batteries and domain-wise aggregation policies;
- score revision records and evaluator disagreement;
- executable validation tests and CI-side axiom/audit checks.
