import UCCAF.Benchmark
import UCCAF.Uncertainty

namespace UCCAF

def BreadthState.ofCount : Nat → BreadthState
  | 0 => .B0
  | 1 => .B1
  | 2 => .B2
  | n + 3 =>
      if n + 3 ≤ 4 then .B3 else .B4

theorem BreadthState.ofCount_zero :
    BreadthState.ofCount 0 = .B0 := by
  rfl

theorem BreadthState.ofCount_one :
    BreadthState.ofCount 1 = .B1 := by
  rfl

theorem BreadthState.ofCount_two :
    BreadthState.ofCount 2 = .B2 := by
  rfl

theorem BreadthState.ofCount_three :
    BreadthState.ofCount 3 = .B3 := by
  rfl

theorem BreadthState.ofCount_four :
    BreadthState.ofCount 4 = .B3 := by
  rfl

theorem BreadthState.ofCount_five :
    BreadthState.ofCount 5 = .B4 := by
  rfl

structure BreadthAssessment where
  independentDomains : Finset HardDomain
  primarySpecialization : Finset HardDomain
  independenceMapId : String
  state : BreadthState
  state_is_derived : state = BreadthState.ofCount independentDomains.card
  deriving DecidableEq, Repr

def BreadthAssessment.outsidePrimaryCount (b : BreadthAssessment) : Nat :=
  (b.independentDomains \ b.primarySpecialization).card

theorem BreadthAssessment.b4_implies_five_domains (b : BreadthAssessment)
    (h : b.state = .B4) :
    5 ≤ b.independentDomains.card := by
  subst h
  by_cases hc : b.independentDomains.card ≤ 4
  · have : BreadthState.ofCount b.independentDomains.card ≠ .B4 := by
      rcases b.independentDomains.card with _ | _ | _ | _ | _ | n <;>
        simp [BreadthState.ofCount, Nat.succ_eq_add_one, hc, Nat.not_succ_le_self]
    exact False.elim (this b.state_is_derived)
  · exact Nat.le_of_lt_succ (Nat.lt_of_not_ge hc)

inductive PostHumanTier : Type
  | NoPostHuman
  | Provisional
  | AdvancedProvisional
  | Confirmed
  | ASIExtension
  deriving DecidableEq, Repr

def PostHumanTier.maxIS : PostHumanTier → ISScore
  | .NoPostHuman => ⟨100, by norm_num, by norm_num⟩
  | .Provisional => ⟨101, by norm_num, by norm_num⟩
  | .AdvancedProvisional => ⟨120, by norm_num, by norm_num⟩
  | .Confirmed => ⟨149, by norm_num, by norm_num⟩
  | .ASIExtension => ⟨200, by norm_num, by norm_num⟩

def EvidenceTier.atLeastE4 : EvidenceTier → Prop
  | .E4 => True
  | .E5 => True
  | _ => False

def EvidenceTier.atLeastE3 : EvidenceTier → Prop
  | .E3 => True
  | .E4 => True
  | .E5 => True
  | _ => False

structure GateAssessment where
  evidence : EvidenceTier
  breadth : BreadthAssessment
  keyResultIndependentlyVerified : Bool
  qualifiedDomains : Finset HardDomain
  independentReplication : Bool
  sustainedAutonomyReliability : Bool
  newValidatedAnchors : Bool
  qualifiedDomains_subset : qualifiedDomains ⊆ breadth.independentDomains
  deriving DecidableEq, Repr

def GateAssessment.provisionalEligible (g : GateAssessment) : Prop :=
  g.evidence.atLeastE4 ∧
    (g.breadth.state = .B2 ∨ g.breadth.state = .B3) ∧
    g.keyResultIndependentlyVerified = true

def GateAssessment.advancedEligible (g : GateAssessment) : Prop :=
  2 ≤ g.qualifiedDomains.card ∧
    g.breadth.state ≠ .B0 ∧
    g.breadth.state ≠ .B1 ∧
    g.keyResultIndependentlyVerified = true

def GateAssessment.confirmedEligible (g : GateAssessment) : Prop :=
  g.breadth.state = .B4 ∧
    5 ≤ g.breadth.independentDomains.card ∧
    3 ≤ g.breadth.outsidePrimaryCount ∧
    g.independentReplication = true ∧
    g.sustainedAutonomyReliability = true

def GateAssessment.asiExtensionEligible (g : GateAssessment) : Prop :=
  g.confirmedEligible ∧ g.newValidatedAnchors = true

def ISWithinTier (is : ISScore) (tier : PostHumanTier) : Prop :=
  (is : ℚ) ≤ tier.maxIS

theorem NoPostHuman_maxIS :
    (PostHumanTier.NoPostHuman.maxIS : ℚ) = 100 := by
  norm_num [PostHumanTier.maxIS]

theorem Provisional_maxIS :
    (PostHumanTier.Provisional.maxIS : ℚ) = 101 := by
  norm_num [PostHumanTier.maxIS]

theorem AdvancedProvisional_maxIS :
    (PostHumanTier.AdvancedProvisional.maxIS : ℚ) = 120 := by
  norm_num [PostHumanTier.maxIS]

theorem Confirmed_maxIS :
    (PostHumanTier.Confirmed.maxIS : ℚ) = 149 := by
  norm_num [PostHumanTier.maxIS]

theorem ASIExtension_maxIS :
    (PostHumanTier.ASIExtension.maxIS : ℚ) = 200 := by
  norm_num [PostHumanTier.maxIS]

end UCCAF
