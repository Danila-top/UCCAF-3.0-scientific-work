import Mathlib

namespace UCCAF

abbrev Score := {x : ℚ // 0 ≤ x ∧ x ≤ 100}

namespace Score

theorem lower (s : Score) : 0 ≤ (s : ℚ) := s.property.1
theorem upper (s : Score) : (s : ℚ) ≤ 100 := s.property.2

end Score
end UCCAF
