import EllipseCongruence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# 导读例 0.1 的具体旋转角

不仅核验正切比值，还求出 cos θ、sin θ，并证明对每一个实点，
讲义中的 forward normalization 正好等于通常的旋转公式。
-/
namespace SpectralExample

noncomputable section

def rotationAngle : ℝ := Real.arctan (1 / 2)

/-- 角度采用 arctan 的主值，确实位于第一象限。 -/
theorem rotationAngle_bounds : 0 < rotationAngle ∧ rotationAngle < Real.pi / 2 := by
  constructor
  · have h := Real.arctan_lt_arctan (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [Real.arctan_zero, rotationAngle] using h
  · exact Real.arctan_lt_pi_div_two (1 / 2)

/-- 对应余弦和正弦是 2/√5、1/√5。 -/
theorem rotationAngle_cos_sin :
    Real.cos rotationAngle = 2 * normalization ∧
    Real.sin rotationAngle = normalization := by
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ) ^ 2) = Real.sqrt 5 / 2 := by
    have hr : (1 + (1 / 2 : ℝ) ^ 2) = 5 / 4 := by norm_num
    have hfour : Real.sqrt (4 : ℝ) = 2 := by
      calc
        _ = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 := Real.sqrt_sq (by norm_num)
    rw [hr, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 5) 4, hfour]
  constructor
  · unfold rotationAngle
    rw [Real.cos_arctan, hsqrt, div_div_eq_mul_div]
    unfold normalization
    ring
  · unfold rotationAngle
    rw [Real.sin_arctan, hsqrt, div_div_eq_mul_div]
    unfold normalization
    ring

/-- 该点映射对于任意输入点都等于角度 arctan(1/2) 的旋转。 -/
theorem forward_is_rotation (p : Point) :
    forward normalization p =
      (Real.cos rotationAngle * p.1 - Real.sin rotationAngle * p.2,
       Real.sin rotationAngle * p.1 + Real.cos rotationAngle * p.2) := by
  rw [rotationAngle_cos_sin.1, rotationAngle_cos_sin.2]
  apply Prod.ext <;> simp only [forward] <;> ring

end
end SpectralExample

#print axioms SpectralExample.rotationAngle_bounds
#print axioms SpectralExample.rotationAngle_cos_sin
#print axioms SpectralExample.forward_is_rotation
