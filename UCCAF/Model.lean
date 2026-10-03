import UCCAF.Score

namespace UCCAF

abbrev ISScore := {x : ℚ // 0 ≤ x ∧ x ≤ 200}

namespace ISScore

theorem lower (s : ISScore) : 0 ≤ (s : ℚ) := s.property.1

theorem upper (s : ISScore) : (s : ℚ) ≤ 200 := s.property.2

end ISScore

structure ResearchWork where
  id : Nat
  title : String
  IS : ISScore
  CS : Score
  P : Score
  deriving DecidableEq, Repr

def MainScore (w : ResearchWork) : ℚ := w.IS
def ConsciousnessScore (w : ResearchWork) : ℚ := w.CS
def ProspectivenessScore (w : ResearchWork) : ℚ := w.P

end UCCAF
