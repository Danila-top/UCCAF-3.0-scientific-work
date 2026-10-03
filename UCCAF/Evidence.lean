import UCCAF.Model

namespace UCCAF

inductive EvidenceTier : Type
  | E0
  | E1
  | E2
  | E3
  | E4
  | E5
  deriving DecidableEq, Repr

inductive RealityClass : Type
  | Real
  | HistoricalProxy
  | BiologicalProxy
  | Biohybrid
  | Fiction
  deriving DecidableEq, Repr

inductive Confidence : Type
  | Low
  | Medium
  | High
  deriving DecidableEq, Repr

inductive EvaluationStatus : Type
  | HumanParity
  | Claimed
  | Provisional
  | Confirmed
  | Unreleased
  deriving DecidableEq, Repr

structure EvidenceRecord where
  tier : EvidenceTier
  reality : RealityClass
  confidence : Confidence
  status : EvaluationStatus
  deriving DecidableEq, Repr

structure AttributionRecord where
  outcomeId : Nat
  configurationId : Nat
  outcomeMetric : ℚ
  baseline : ℚ
  orchestrator : Score
  workers : Score
  tools : Score
  human : Score
  environment : Score
  underdetermined : Score
  balanced :
    (orchestrator : ℚ) +
      (workers : ℚ) +
      (tools : ℚ) +
      (human : ℚ) +
      (environment : ℚ) +
      (underdetermined : ℚ) = 100

def AttributionTotal (a : AttributionRecord) : ℚ :=
  (a.orchestrator : ℚ) +
    (a.workers : ℚ) +
    (a.tools : ℚ) +
    (a.human : ℚ) +
    (a.environment : ℚ) +
    (a.underdetermined : ℚ)

theorem AttributionTotal_eq_100 (a : AttributionRecord) :
    AttributionTotal a = 100 := by
  exact a.balanced

theorem AttributionTotal_nonnegative (a : AttributionRecord) :
    0 ≤ AttributionTotal a := by
  rw [AttributionTotal_eq_100]
  norm_num

end UCCAF
