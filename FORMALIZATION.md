# UCCAF 3.0 — Lean 4 formalization

This branch is the first machine-checkable mathematical specification of the currently documented UCCAF 3.0 protocol.

## Formalized in phase 1

1. Score is a subtype of rationals constrained by 0 <= score <= 100.
2. ISScore is a separate primary-intelligence subtype constrained by 0 <= IS <= 200, so provisional and ASI-level values above the 100% Human Swarm baseline are representable.
3. ResearchWork contains id, title, IS, CS and P, with IS using ISScore and CS/P using Score.
4. UCCI = (IS + 2 CS) / 2.
5. KSI = (IS + 2 CS + P) / 3.
6. MainBetter is an IS-only strict order.
7. MainSorted certifies that a ranking list is non-increasing in IS.
8. MasterTopN takes the first n entries of a certified ranking.

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
- ISScoreInterval provides the same interval logic on the 0–200 IS scale used by post-human gates.
- Interval width is proved non-negative.
- UncertaintyRecord binds point score, interval, confidence, evidence tier, breadth state, configuration id and calibration id.
- PostHumanEvidenceGate formalizes the baseline/configuration/IS interval/breadth/evidence/replication/status schema and proves point/interval consistency.
- HardDomain enumerates the 12 v3.0 hard-task domains D01–D12.
- BenchmarkObservation records domain, benchmark score, epistemic reality class, evidence tier and whether the score is estimated.
- BenchmarkMean is an explicit equal-weight aggregate over a finite set of benchmark observations.
- BenchmarkMean is proved to lie in [0,100].
- DomainCoverage records the versioned domain set and independence-map identifier; its size is bounded by the 12-domain registry.
- BreadthState.ofCount encodes B0=0, B1=1, B2=2, B3=3–4 and B4=5+ hard domains.
- BreadthAssessment separates independent-domain coverage from the primary specialization set.
- PostHumanTier encodes the protocol's current maximum IS bands: 100, 101, 120, 149 and 200.
- GateAssessment formalizes provisional, advanced, confirmed and ASI-extension eligibility predicates.

## Scientific boundary

These proofs establish properties of the chosen formal specification. They do not establish that IS/CS/P are empirically valid measures or that UCCAF is correct as an empirical evaluation methodology.

The formalization deliberately keeps benchmark evidence separate from the primary IS ranking. It also keeps uncertainty, epistemic status, replication and configuration metadata explicit rather than silently converting benchmark performance or a single breakthrough into a general-intelligence claim.

## Next layers

- structured configuration identity with model/version, tools, harness, topology, resources, memory and environment;
- benchmark batteries with explicit per-domain independence maps;
- measured/estimated/fictional benchmark separation with stronger invariants;
- score revision records and evaluator disagreement;
- executable validation tests and CI-side axiom/audit checks.
