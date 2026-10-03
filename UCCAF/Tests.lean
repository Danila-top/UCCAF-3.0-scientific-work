import UCCAF.Gates
import UCCAF.Configuration

namespace UCCAF

def exampleIS101 : ISScore :=
  ⟨101, by norm_num, by norm_num⟩

theorem exampleIS101_above_human :
    (exampleIS101 : ℚ) > 100 := by
  norm_num [exampleIS101]

def exampleInterval : ISScoreInterval :=
  { low := ⟨95, by norm_num, by norm_num⟩
    point := exampleIS101
    high := ⟨110, by norm_num, by norm_num⟩
    low_le_point := by norm_num [exampleIS101]
    point_le_high := by norm_num [exampleIS101] }

theorem exampleInterval_width :
    exampleInterval.width = 15 := by
  norm_num [ISScoreInterval.width, exampleInterval, exampleIS101]

def exampleBenchmark : BenchmarkObservation :=
  { id := 1
    domain := .mathematics
    name := "Example benchmark"
    score := ⟨42, by norm_num, by norm_num⟩
    reality := .Real
    evidence := .E2
    estimated := true }

theorem singleton_benchmark_smoke :
    BenchmarkMean {exampleBenchmark} = 42 := by
  simpa using BenchmarkMean_eq_of_singleton exampleBenchmark

theorem breadth_smoke :
    BreadthState.ofCount 5 = .B4 := by
  rfl

theorem gate_maximum_smoke :
    (PostHumanTier.Provisional.maxIS : ℚ) = 101 := by
  exact Provisional_maxIS

end UCCAF
