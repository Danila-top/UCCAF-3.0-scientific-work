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


end UCCAF
