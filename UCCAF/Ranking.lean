import UCCAF.Model
import UCCAF.Scoring

namespace UCCAF

def MainBetter (a b : ResearchWork) : Prop :=
  MainScore b < MainScore a

def MainSorted (xs : List ResearchWork) : Prop :=
  xs.Pairwise (fun a b => MainScore b ≤ MainScore a)

structure RankedWorks where
  items : List ResearchWork
  sorted : MainSorted items

def MasterTopN (r : RankedWorks) (n : Nat) : List ResearchWork :=
  r.items.take n

theorem MainBetter_irrefl (a : ResearchWork) :
    ¬ MainBetter a a := by
  exact lt_irrefl _

theorem MainBetter_trans {a b c : ResearchWork}
    (hab : MainBetter a b) (hbc : MainBetter b c) :
    MainBetter a c := by
  exact lt_trans hbc hab

theorem MainBetter_asymm {a b : ResearchWork}
    (hab : MainBetter a b) :
    ¬ MainBetter b a := by
  exact not_lt_of_ge (le_of_lt hab)

theorem MainScore_ignores_CS_P {a b : ResearchWork}
    (hIS : (a.IS : ℚ) = b.IS) :
    MainScore a = MainScore b := by
  exact hIS

theorem MainBetter_iff_IS {a b : ResearchWork} :
    MainBetter a b ↔ (b.IS : ℚ) < a.IS := by
  rfl

theorem MasterTopN_length_le (r : RankedWorks) (n : Nat) :
    (MasterTopN r n).length ≤ n := by
  simp [MasterTopN, List.length_take]

end UCCAF
