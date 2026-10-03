import UCCAF.Model

namespace UCCAF

def UCCI (is cs : Score) : ℚ :=
  (is + 2 * cs) / 2

def KSI (is cs p : Score) : ℚ :=
  (is + 2 * cs + p) / 3

theorem UCCI_nonnegative (is cs : Score) :
    0 ≤ UCCI is cs := by
  dsimp [UCCI]
  linarith [Score.lower is, Score.lower cs]

theorem UCCI_upper_bound (is cs : Score) :
    UCCI is cs ≤ 150 := by
  dsimp [UCCI]
  linarith [Score.upper is, Score.upper cs]

theorem KSI_nonnegative (is cs p : Score) :
    0 ≤ KSI is cs p := by
  dsimp [KSI]
  linarith [Score.lower is, Score.lower cs, Score.lower p]

theorem KSI_upper_bound (is cs p : Score) :
    KSI is cs p ≤ 400 / 3 := by
  dsimp [KSI]
  have h_is : (is : ℚ) ≤ 100 := Score.upper is
  have h_cs : (cs : ℚ) ≤ 100 := Score.upper cs
  have h_p : (p : ℚ) ≤ 100 := Score.upper p
  have h_2cs : (2 : ℚ) * (cs : ℚ) ≤ 2 * 100 :=
    mul_le_mul_of_nonneg_left h_cs (by norm_num)
  have h_sum :
      (is : ℚ) + 2 * (cs : ℚ) + (p : ℚ) ≤ 100 + 2 * 100 + 100 :=
    add_le_add (add_le_add h_is h_2cs) h_p
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 3)).2
  norm_num at h_sum ⊢
  exact h_sum

theorem KSI_all_100 :
    KSI ⟨100, by norm_num, by norm_num⟩
        ⟨100, by norm_num, by norm_num⟩
        ⟨100, by norm_num, by norm_num⟩ = 400 / 3 := by
  norm_num [KSI]

theorem UCCI_strictMono_IS {is₁ is₂ cs : Score}
    (h : (is₁ : ℚ) < is₂) :
    UCCI is₁ cs < UCCI is₂ cs := by
  dsimp [UCCI]
  linarith

theorem KSI_strictMono_IS {is₁ is₂ cs p : Score}
    (h : (is₁ : ℚ) < is₂) :
    KSI is₁ cs p < KSI is₂ cs p := by
  dsimp [KSI]
  linarith

end UCCAF
