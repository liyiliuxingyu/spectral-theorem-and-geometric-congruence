import Example21

/-!
# 例 2.4：不选特征向量的正负号，也能投影

复用例 2.1 的 `Mat2`、`A`、矩阵乘法、矩阵作用及欧氏内积 `dot`。
所有系数都是精确的实有理数。先核验投影矩阵的多项式表达式，
再证明对称性、幂等性、像空间正交、任意向量分解及特征直线。
这些断言共同明确了“正交投影”的含义，不依赖默认积空间范数。
-/

namespace SpectralExample.Example24

open SpectralExample.Example21

noncomputable section

def scaleMatrix (t : ℝ) (B : Mat2) : Mat2 :=
  ⟨t * B.a, t * B.b, t * B.c, t * B.d⟩

def addMatrix (B C : Mat2) : Mat2 :=
  ⟨B.a + C.a, B.b + C.b, B.c + C.c, B.d + C.d⟩

def subtractMatrix (B C : Mat2) : Mat2 :=
  ⟨B.a - C.a, B.b - C.b, B.c - C.c, B.d - C.d⟩

def zeroMatrix : Mat2 := ⟨0, 0, 0, 0⟩

def P6 : Mat2 := ⟨4 / 5, 2 / 5, 2 / 5, 1 / 5⟩
def P1 : Mat2 := ⟨1 / 5, -2 / 5, -2 / 5, 4 / 5⟩
def e : Point := (1, 0)

private theorem mat_ext {B C : Mat2}
    (ha : B.a = C.a) (hb : B.b = C.b)
    (hc : B.c = C.c) (hd : B.d = C.d) : B = C := by
  cases B
  cases C
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

/-- P₆=(A-I)/5：右侧表示逐项除以 5。 -/
theorem P6_polynomial : P6 = scaleMatrix (1 / 5) (subtractMatrix A I) := by
  apply mat_ext <;> norm_num [P6, scaleMatrix, subtractMatrix, A, I]

/-- 另一特征方向的投影是补投影 I-P₆。 -/
theorem P1_complement : P1 = subtractMatrix I P6 := by
  apply mat_ext <;> norm_num [P1, subtractMatrix, I, P6]

/-- 两个矩阵分别对称、幂等，即欧氏内积下的正交投影判据。 -/
theorem orthogonal_projection_identities :
    transpose P6 = P6 ∧ multiply P6 P6 = P6 ∧
    transpose P1 = P1 ∧ multiply P1 P1 = P1 := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;>
    apply mat_ext <;> norm_num [multiply, P6, P1]

/-- 不同特征方向的投影连续作用，无论顺序，都得到零。 -/
theorem mutually_annihilating :
    multiply P6 P1 = zeroMatrix ∧ multiply P1 P6 = zeroMatrix := by
  constructor <;> apply mat_ext <;> norm_num [multiply, P6, P1, zeroMatrix]

theorem projections_sum_to_identity : addMatrix P6 P1 = I := by
  apply mat_ext <;> norm_num [addMatrix, P6, P1, I]

/-- 两投影确实关于所用的实欧氏内积自伴。 -/
theorem projections_self_adjoint (p q : Point) :
    dot (applyMatrix P6 p) q = dot p (applyMatrix P6 q) ∧
    dot (applyMatrix P1 p) q = dot p (applyMatrix P1 q) := by
  constructor <;> simp only [dot, applyMatrix, P6, P1] <;> ring

/-- 任意两个投影像正交，而不只是题目中选定的一对向量。 -/
theorem orthogonal_ranges (p q : Point) :
    dot (applyMatrix P6 p) (applyMatrix P1 q) = 0 := by
  simp only [dot, applyMatrix, P6, P1]
  ring

/-- 每个实向量都分成两投影给出的分量。 -/
theorem vector_decomposition (p : Point) :
    ((applyMatrix P6 p).1 + (applyMatrix P1 p).1,
     (applyMatrix P6 p).2 + (applyMatrix P1 p).2) = p := by
  apply Prod.ext <;> simp only [applyMatrix, P6, P1] <;> ring

/-- P₆ 的像全在特征值 6 的方向上；P₁ 的像全在特征值 1 的方向上。 -/
theorem images_are_eigenvectors (p : Point) :
    applyMatrix A (applyMatrix P6 p) =
      (6 * (applyMatrix P6 p).1, 6 * (applyMatrix P6 p).2) ∧
    applyMatrix A (applyMatrix P1 p) = applyMatrix P1 p := by
  constructor <;> apply Prod.ext <;> simp only [applyMatrix, A, P6, P1] <;> ring

/-- P₆ 恰好固定特征直线 x=2y 上的点。 -/
theorem P6_fixed_iff (p : Point) :
    applyMatrix P6 p = p ↔ p.1 = 2 * p.2 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    change (4 / 5 : ℝ) * p.1 + (2 / 5 : ℝ) * p.2 = p.1 at hfirst
    linarith
  · intro h
    apply Prod.ext <;> simp only [applyMatrix, P6] <;> linarith only [h]

/-- P₁ 恰好固定另一条特征直线 y=-2x 上的点。 -/
theorem P1_fixed_iff (p : Point) :
    applyMatrix P1 p = p ↔ p.2 = -2 * p.1 := by
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    change (1 / 5 : ℝ) * p.1 + (-2 / 5 : ℝ) * p.2 = p.1 at hfirst
    linarith
  · intro h
    apply Prod.ext <;> simp only [applyMatrix, P1] <;> linarith only [h]

/-- 矩阵的谱分解：两个互相垂直的分量分别乘 6 和 1。 -/
theorem spectral_decomposition : A = addMatrix (scaleMatrix 6 P6) P1 := by
  apply mat_ext <;> norm_num [A, addMatrix, scaleMatrix, P6, P1]

/-- 作用两次，乘数分别变为 36 和 1。 -/
theorem squared_spectral_decomposition :
    multiply A A = addMatrix (scaleMatrix 36 P6) P1 := by
  apply mat_ext <;> norm_num [multiply, A, addMatrix, scaleMatrix, P6, P1]

theorem components_of_e :
    applyMatrix P6 e = (4 / 5, 2 / 5) ∧
    applyMatrix P1 e = (1 / 5, -2 / 5) := by
  constructor <;> apply Prod.ext <;> norm_num [applyMatrix, P6, P1, e]

theorem components_of_e_sum_and_orthogonal :
    ((applyMatrix P6 e).1 + (applyMatrix P1 e).1,
     (applyMatrix P6 e).2 + (applyMatrix P1 e).2) = e ∧
    dot (applyMatrix P6 e) (applyMatrix P1 e) = 0 :=
  ⟨vector_decomposition e, orthogonal_ranges e e⟩

/-- 按谱投影分解计算 A²e，得到讲义中的 (29,14)。 -/
theorem A_squared_e : applyMatrix (multiply A A) e = (29, 14) := by
  rw [squared_spectral_decomposition]
  apply Prod.ext <;> norm_num [applyMatrix, addMatrix, scaleMatrix, P6, P1, e]

/-- 直接连续作用两次，与上面的矩阵平方计算一致。 -/
theorem A_applied_twice_e : applyMatrix A (applyMatrix A e) = (29, 14) := by
  apply Prod.ext <;> norm_num [applyMatrix, A, e]

end
end SpectralExample.Example24

#print axioms SpectralExample.Example24.P6_polynomial
#print axioms SpectralExample.Example24.P1_complement
#print axioms SpectralExample.Example24.orthogonal_projection_identities
#print axioms SpectralExample.Example24.mutually_annihilating
#print axioms SpectralExample.Example24.projections_sum_to_identity
#print axioms SpectralExample.Example24.projections_self_adjoint
#print axioms SpectralExample.Example24.orthogonal_ranges
#print axioms SpectralExample.Example24.vector_decomposition
#print axioms SpectralExample.Example24.images_are_eigenvectors
#print axioms SpectralExample.Example24.P6_fixed_iff
#print axioms SpectralExample.Example24.P1_fixed_iff
#print axioms SpectralExample.Example24.spectral_decomposition
#print axioms SpectralExample.Example24.squared_spectral_decomposition
#print axioms SpectralExample.Example24.components_of_e
#print axioms SpectralExample.Example24.components_of_e_sum_and_orthogonal
#print axioms SpectralExample.Example24.A_squared_e
#print axioms SpectralExample.Example24.A_applied_twice_e
