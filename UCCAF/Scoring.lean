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
    KSI is cs p ≤ 100 := by
  dsimp [KSI]
  linarith [Score.upper is, Score.upper cs, Score.upper p]

theorem KSI_all_100 :
    KSI ⟨100, by norm_num, by norm_num⟩
        ⟨100, by norm_num, by norm_num⟩
        ⟨100, by norm_num, by norm_num⟩ = 100 := by
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
