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

def MainBetterDet (a b : ResearchWork) : Prop :=
  MainBetter a b ∨ (MainScore a = MainScore b ∧ a.id < b.id)

def DeterministicSorted (xs : List ResearchWork) : Prop :=
  xs.Pairwise MainBetterDet

def UniqueIds (xs : List ResearchWork) : Prop :=
  (xs.map ResearchWork.id).Nodup

structure DeterministicallyRankedWorks where
  items : List ResearchWork
  sorted : DeterministicSorted items
  uniqueIds : UniqueIds items

def MasterTopN (r : RankedWorks) (n : Nat) : List ResearchWork :=
  r.items.take n

def MasterTopNDet (r : DeterministicallyRankedWorks) (n : Nat) : List ResearchWork :=
  r.items.take n

def MasterTop120 (r : RankedWorks) : List ResearchWork :=
  MasterTopN r 120

def MasterTop150 (r : RankedWorks) : List ResearchWork :=
  MasterTopN r 150

def MasterTop120Det (r : DeterministicallyRankedWorks) : List ResearchWork :=
  MasterTopNDet r 120

def MasterTop150Det (r : DeterministicallyRankedWorks) : List ResearchWork :=
  MasterTopNDet r 150

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

theorem MainBetterDet_irrefl (a : ResearchWork) :
    ¬ MainBetterDet a a := by
  intro h
  rcases h with h | h
  · exact MainBetter_irrefl a h
  · exact (Nat.lt_irrefl a.id) h.2

theorem MainBetterDet_trans {a b c : ResearchWork}
    (hab : MainBetterDet a b) (hbc : MainBetterDet b c) :
    MainBetterDet a c := by
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · exact Or.inl (MainBetter_trans hab hbc)
    · apply Or.inl
      dsimp [MainBetter] at hab ⊢
      rw [← hbc.1]
      exact hab
  · rcases hbc with hbc | hbc
    · apply Or.inl
      dsimp [MainBetter] at hbc ⊢
      rw [hab.1]
      exact hbc
    · exact Or.inr ⟨hab.1.trans hbc.1, Nat.lt_trans hab.2 hbc.2⟩

theorem MainBetterDet_asymm {a b : ResearchWork}
    (hab : MainBetterDet a b) :
    ¬ MainBetterDet b a := by
  intro hba
  rcases hab with hab | hab
  · rcases hba with hba | hba
    · exact MainBetter_asymm hab hba
    · exact (ne_of_lt hab) hba.1
  · rcases hba with hba | hba
    · exact (ne_of_lt hba) hab.1
    · exact (Nat.not_lt_of_ge (Nat.le_of_lt hab.2)) hba.2

theorem MasterTopN_length_le (r : RankedWorks) (n : Nat) :
    (MasterTopN r n).length ≤ n := by
  simp [MasterTopN, List.length_take]

theorem MasterTopNDet_length_le (r : DeterministicallyRankedWorks) (n : Nat) :
    (MasterTopNDet r n).length ≤ n := by
  simp [MasterTopNDet, List.length_take]

theorem MasterTopN_length_eq (r : RankedWorks) {n : Nat}
    (h : n ≤ r.items.length) :
    (MasterTopN r n).length = n := by
  simp [MasterTopN, h, Nat.min_eq_left]

theorem MasterTopNDet_length_eq (r : DeterministicallyRankedWorks) {n : Nat}
    (h : n ≤ r.items.length) :
    (MasterTopNDet r n).length = n := by
  simp [MasterTopNDet, h, Nat.min_eq_left]

theorem MasterTop120_length (r : RankedWorks)
    (h : 120 ≤ r.items.length) :
    (MasterTop120 r).length = 120 := by
  exact MasterTopN_length_eq r h

theorem MasterTop150_length (r : RankedWorks)
    (h : 150 ≤ r.items.length) :
    (MasterTop150 r).length = 150 := by
  exact MasterTopN_length_eq r h

theorem MasterTop120Det_length (r : DeterministicallyRankedWorks)
    (h : 120 ≤ r.items.length) :
    (MasterTop120Det r).length = 120 := by
  exact MasterTopNDet_length_eq r h

theorem MasterTop150Det_length (r : DeterministicallyRankedWorks)
    (h : 150 ≤ r.items.length) :
    (MasterTop150Det r).length = 150 := by
  exact MasterTopNDet_length_eq r h

end UCCAF
