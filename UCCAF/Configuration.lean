import UCCAF.Model

namespace UCCAF

structure ConfigurationIdentity where
  configurationId : String
  model : String
  modelVersion : String
  promptPolicy : String
  tools : List String
  harness : String
  memory : String
  topology : String
  agentCount : Option Nat
  resourceBudget : String
  environment : String
  benchmarkRevision : String
  evaluationDate : String
  deriving DecidableEq, Repr

def ConfigurationIdentity.isMultiAgent (c : ConfigurationIdentity) : Prop :=
  match c.agentCount with
  | some n => 1 < n
  | none => False

theorem ConfigurationIdentity.singleOrMulti (c : ConfigurationIdentity) :
    c.isMultiAgent ∨ c.agentCount = some 1 ∨ c.agentCount = none := by
  cases h : c.agentCount with
  | none =>
      exact Or.inr (Or.inr rfl)
  | some n =>
      by_cases hn : 1 < n
      · exact Or.inl hn
      · have : n ≤ 1 := Nat.le_of_not_gt hn
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with rfl | rfl
        · exact Or.inr (Or.inr (by simp))
        · exact Or.inr (Or.inl rfl)

end UCCAF
