import UCCAF.Evidence
import UCCAF.Uncertainty

namespace UCCAF

inductive HardDomain : Type
  | mathematics
  | fundamentalPhysics
  | quantumTechnology
  | engineering
  | softwareEngineering
  | cybersecurity
  | biologyMedicine
  | chemistryMaterials
  | aiResearch
  | astronomyCosmology
  | longHorizonAgency
  | societalInstitutionalReasoning
  deriving DecidableEq, Repr

structure BenchmarkObservation where
  id : Nat
  domain : HardDomain
  name : String
  score : Score
  reality : RealityClass
  evidence : EvidenceTier
  estimated : Bool
  deriving DecidableEq, Repr

def BenchmarkMean (xs : Finset BenchmarkObservation) : ℚ :=
  if h : xs.Nonempty then
    (∑ x in xs, (x.score : ℚ)) / xs.card
  else
    0

theorem BenchmarkMean_nonnegative (xs : Finset BenchmarkObservation) :
    0 ≤ BenchmarkMean xs := by
  classical
  by_cases h : xs.Nonempty
  · have hcard : (0 : ℚ) < xs.card := by
      exact_mod_cast h.card_pos
    have hsum : 0 ≤ ∑ x in xs, (x.score : ℚ) := by
      exact Finset.sum_nonneg (fun x hx => Score.lower x.score)
    rw [BenchmarkMean, dif_pos h]
    exact (div_nonneg hsum (le_of_lt hcard))
  · rw [BenchmarkMean, dif_neg h]
    norm_num

theorem BenchmarkMean_upper_bound (xs : Finset BenchmarkObservation) :
    BenchmarkMean xs ≤ 100 := by
  classical
  by_cases h : xs.Nonempty
  · have hcard : (0 : ℚ) < xs.card := by
      exact_mod_cast h.card_pos
    have hsum :
        (∑ x in xs, (x.score : ℚ)) ≤ ∑ x in xs, (100 : ℚ) := by
      exact Finset.sum_le_sum (fun x hx => Score.upper x.score)
    rw [BenchmarkMean, dif_pos h]
    apply (div_le_iff₀ hcard).2
    simpa using hsum
  · rw [BenchmarkMean, dif_neg h]
    norm_num

theorem BenchmarkMean_eq_of_singleton (x : BenchmarkObservation) :
    BenchmarkMean {x} = (x.score : ℚ) := by
  classical
  simp [BenchmarkMean]

structure DomainCoverage where
  domains : Finset HardDomain
  independenceMapId : String
  deriving DecidableEq, Repr

def DomainCoverage.count (c : DomainCoverage) : Nat :=
  c.domains.card

def DomainCoverage.contains (c : DomainCoverage) (d : HardDomain) : Prop :=
  d ∈ c.domains

theorem DomainCoverage.count_le_twelve (c : DomainCoverage) :
    c.count ≤ 12 := by
  dsimp [DomainCoverage.count]
  exact Finset.card_le_card (by
    intro d hd
    fin_cases d)

end UCCAF
