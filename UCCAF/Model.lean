import UCCAF.Score

namespace UCCAF

structure ResearchWork where
  id : Nat
  title : String
  IS : Score
  CS : Score
  P : Score
  deriving DecidableEq, Repr

def MainScore (w : ResearchWork) : ℚ := w.IS
def ConsciousnessScore (w : ResearchWork) : ℚ := w.CS
def ProspectivenessScore (w : ResearchWork) : ℚ := w.P

end UCCAF
