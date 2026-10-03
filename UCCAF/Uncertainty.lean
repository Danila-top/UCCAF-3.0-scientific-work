import UCCAF.Evidence

namespace UCCAF

inductive BreadthState : Type
  | B0 | B1 | B2 | B3 | B4
  deriving DecidableEq, Repr

inductive ReplicationStatus : Type
  | None
  | Partial
  | Independent
  deriving DecidableEq, Repr

structure ScoreInterval where
  low : Score
  point : Score
  high : Score
  low_le_point : (low : ℚ) ≤ point
  point_le_high : (point : ℚ) ≤ high
  deriving DecidableEq, Repr

theorem ScoreInterval.low_le_high (i : ScoreInterval) :
    (i.low : ℚ) ≤ i.high := by
  exact le_trans i.low_le_point i.point_le_high

def ScoreInterval.width (i : ScoreInterval) : ℚ :=
  (i.high : ℚ) - i.low

theorem ScoreInterval.width_nonnegative (i : ScoreInterval) :
    0 ≤ i.width := by
  dsimp [ScoreInterval.width]
  linarith [i.low_le_high]

structure ISScoreInterval where
  low : ISScore
  point : ISScore
  high : ISScore
  low_le_point : (low : ℚ) ≤ point
  point_le_high : (point : ℚ) ≤ high
  deriving DecidableEq, Repr

theorem ISScoreInterval.low_le_high (i : ISScoreInterval) :
    (i.low : ℚ) ≤ i.high := by
  exact le_trans i.low_le_point i.point_le_high

def ISScoreInterval.width (i : ISScoreInterval) : ℚ :=
  (i.high : ℚ) - i.low

theorem ISScoreInterval.width_nonnegative (i : ISScoreInterval) :
    0 ≤ i.width := by
  dsimp [ISScoreInterval.width]
  linarith [i.low_le_high]

structure UncertaintyRecord where
  point : Score
  interval : ScoreInterval
  confidence : Confidence
  evidence : EvidenceTier
  breadth : BreadthState
  configurationId : String
  calibrationId : String
  point_matches_interval : interval.point = point
  deriving DecidableEq, Repr

structure PostHumanEvidenceGate where
  baselineVersion : String
  configurationId : String
  pointIS : ISScore
  interval : ISScoreInterval
  confidence : Confidence
  breadth : BreadthState
  evidence : EvidenceTier
  replication : ReplicationStatus
  status : EvaluationStatus
  point_matches_interval : interval.point = pointIS
  deriving DecidableEq, Repr

theorem PostHumanEvidenceGate.point_matches_interval'
    (g : PostHumanEvidenceGate) :
    (g.interval.point : ℚ) = g.pointIS := by
  exact congrArg (fun s : ISScore => (s : ℚ)) g.point_matches_interval

end UCCAF
