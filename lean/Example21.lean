import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 例 2.1 的实矩阵与具体对应点

这是针对讲义例 2.1 的独立计算核验，不以一般谱定理为前提。
2×2 实矩阵用四个实数构成的结构表示，作用于实数对。
距离明确采用欧氏距离，避免把积空间的默认度量误作欧氏距离。
-/
namespace SpectralExample.Example21

noncomputable section

abbrev Point := ℝ × ℝ

structure Mat2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def transpose (B : Mat2) : Mat2 := ⟨B.a, B.c, B.b, B.d⟩

def multiply (B C : Mat2) : Mat2 :=
  ⟨B.a * C.a + B.b * C.c, B.a * C.b + B.b * C.d,
   B.c * C.a + B.d * C.c, B.c * C.b + B.d * C.d⟩

def applyMatrix (B : Mat2) (p : Point) : Point :=
  (B.a * p.1 + B.b * p.2, B.c * p.1 + B.d * p.2)

def determinant (B : Mat2) : ℝ := B.a * B.d - B.b * B.c

def I : Mat2 := ⟨1, 0, 0, 1⟩
def A : Mat2 := ⟨5, 2, 2, 2⟩
def D : Mat2 := ⟨6, 0, 0, 1⟩
def Q (r : ℝ) : Mat2 := ⟨2 * r, -r, r, 2 * r⟩
def r : ℝ := 1 / Real.sqrt 5

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
def distanceSquared (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
def euclideanDistance (p q : Point) : ℝ := Real.sqrt (distanceSquared p q)
def qA (p : Point) : ℝ := 5 * p.1 ^ 2 + 4 * p.1 * p.2 + 2 * p.2 ^ 2
def qD (p : Point) : ℝ := 6 * p.1 ^ 2 + p.2 ^ 2

private theorem mat_ext {B C : Mat2}
    (ha : B.a = C.a) (hb : B.b = C.b) (hc : B.c = C.c) (hd : B.d = C.d) :
    B = C := by
  cases B
  cases C
  cases ha
  cases hb
  cases hc
  cases hd
  rfl

theorem normalization_sq : r ^ 2 = 1 / 5 := by
  unfold r
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- 展开 det(A - lamI)，而不是把特征多项式作为未经核验的输入。 -/
theorem characteristic_polynomial (lam : ℝ) :
    determinant ⟨5 - lam, 2, 2, 2 - lam⟩ = (lam - 6) * (lam - 1) := by
  simp only [determinant]
  ring

theorem characteristic_roots (lam : ℝ) :
    determinant ⟨5 - lam, 2, 2, 2 - lam⟩ = 0 ↔ lam = 6 ∨ lam = 1 := by
  rw [characteristic_polynomial, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by rw [h]; ring)
    · exact Or.inr (by rw [h]; ring)

/-- 特征值 6 的整个特征向量方程，允许零向量。 -/
theorem eigenvalue_six_equation (p : Point) :
    applyMatrix A p = (6 * p.1, 6 * p.2) ↔ p.1 = 2 * p.2 := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    change 5 * p.1 + 2 * p.2 = 6 * p.1 at h₁
    linarith
  · intro h
    apply Prod.ext <;> simp only [applyMatrix, A]
    · nlinarith only [h]
    · nlinarith only [h]

/-- 特征值 1 的整个特征向量方程，允许零向量。 -/
theorem eigenvalue_one_equation (p : Point) :
    applyMatrix A p = p ↔ p.2 = -2 * p.1 := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    change 5 * p.1 + 2 * p.2 = p.1 at h₁
    linarith
  · intro h
    apply Prod.ext <;> simp only [applyMatrix, A]
    · nlinarith only [h]
    · nlinarith only [h]

/-- 两个明确的单位特征方向；单位长度同时保证它们不是零向量。 -/
theorem normalized_eigenvectors :
    applyMatrix A (2 * r, r) = (6 * (2 * r), 6 * r) ∧
    applyMatrix A (-r, 2 * r) = (-r, 2 * r) ∧
    dot (2 * r, r) (2 * r, r) = 1 ∧
    dot (-r, 2 * r) (-r, 2 * r) = 1 ∧
    dot (2 * r, r) (-r, 2 * r) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Prod.ext <;> simp only [applyMatrix, A] <;> ring
  · apply Prod.ext <;> simp only [applyMatrix, A] <;> ring
  · calc
      _ = 5 * r ^ 2 := by simp only [dot]; ring
      _ = 1 := by rw [normalization_sq]; norm_num
  · calc
      _ = 5 * r ^ 2 := by simp only [dot]; ring
      _ = 1 := by rw [normalization_sq]; norm_num
  · simp only [dot]
    ring

private theorem rscale : 5 * r ^ 2 = 1 := by rw [normalization_sq]; norm_num

theorem real_transpose_mul : multiply (transpose (Q r)) (Q r) = I := by
  apply mat_ext
  · calc
      _ = 5 * r ^ 2 := by simp only [multiply, transpose, Q]; ring
      _ = 1 := rscale
  · simp only [multiply, transpose, Q, I]; ring
  · simp only [multiply, transpose, Q, I]; ring
  · calc
      _ = 5 * r ^ 2 := by simp only [multiply, transpose, Q]; ring
      _ = 1 := rscale

theorem real_mul_transpose : multiply (Q r) (transpose (Q r)) = I := by
  apply mat_ext
  · calc
      _ = 5 * r ^ 2 := by simp only [multiply, transpose, Q]; ring
      _ = 1 := rscale
  · simp only [multiply, transpose, Q, I]; ring
  · simp only [multiply, transpose, Q, I]; ring
  · calc
      _ = 5 * r ^ 2 := by simp only [multiply, transpose, Q]; ring
      _ = 1 := rscale

theorem real_diagonalizes :
    multiply (transpose (Q r)) (multiply A (Q r)) = D := by
  apply mat_ext
  · calc
      _ = 6 * (5 * r ^ 2) := by simp only [multiply, transpose, Q, A]; ring
      _ = 6 := by rw [rscale]; ring
  · simp only [multiply, transpose, Q, A, D]; ring
  · simp only [multiply, transpose, Q, A, D]; ring
  · calc
      _ = 5 * r ^ 2 := by simp only [multiply, transpose, Q, A]; ring
      _ = 1 := rscale

theorem determinant_Q : determinant (Q r) = 1 := by
  calc
    _ = 5 * r ^ 2 := by simp only [determinant, Q]; ring
    _ = 1 := rscale

theorem quadratic_standard_form (p : Point) :
    qA (applyMatrix (Q r) p) = qD p := by
  calc
    _ = (5 * r ^ 2) * qD p := by simp only [qA, qD, applyMatrix, Q]; ring
    _ = _ := by rw [rscale]; ring

theorem arbitrary_points_distance (p q : Point) :
    distanceSquared (applyMatrix (Q r) p) (applyMatrix (Q r) q) =
      distanceSquared p q := by
  calc
    _ = (5 * r ^ 2) * distanceSquared p q := by
      simp only [distanceSquared, applyMatrix, Q]
      ring
    _ = _ := by rw [rscale]; ring

/-- 例题所取的两点及其在实矩阵 Q 作用下的像。 -/
def P : Point := (1 / Real.sqrt 6, 0)
def R : Point := (0, 1)

theorem sample_points_on_standard :
    qD P = 1 ∧ qD R = 1 := by
  have h : (1 / Real.sqrt (6 : ℝ)) ^ 2 = 1 / 6 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  constructor
  · simp only [qD, P, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    rw [h]
    norm_num
  · norm_num [qD, R]

theorem sample_point_images :
    applyMatrix (Q r) P = (2 * r / Real.sqrt 6, r / Real.sqrt 6) ∧
    applyMatrix (Q r) R = (-r, 2 * r) := by
  constructor
  · apply Prod.ext <;> simp only [applyMatrix, Q, P] <;> ring
  · apply Prod.ext <;> simp only [applyMatrix, Q, R] <;> ring

/-- 与纸本完全相同的坐标写法；将 √5 和 √6 的乘积合为 √30。 -/
theorem sample_radical_image :
    applyMatrix (Q r) P = (2 / Real.sqrt 30, 1 / Real.sqrt 30) := by
  have h : Real.sqrt 30 = Real.sqrt 5 * Real.sqrt 6 := by
    calc
      Real.sqrt 30 = Real.sqrt (5*6) := by norm_num
      _ = _ := Real.sqrt_mul (by norm_num) _
  rw [sample_point_images.1, h]
  apply Prod.ext <;> simp only [r, div_eq_mul_inv, mul_inv_rev] <;> ring

theorem sample_points_on_original :
    qA (applyMatrix (Q r) P) = 1 ∧ qA (applyMatrix (Q r) R) = 1 := by
  constructor
  · rw [quadratic_standard_form]; exact sample_points_on_standard.1
  · rw [quadratic_standard_form]; exact sample_points_on_standard.2

theorem sample_squared_distance :
    distanceSquared P R = 7 / 6 ∧
    distanceSquared (applyMatrix (Q r) P) (applyMatrix (Q r) R) = 7 / 6 := by
  have h : (1 / Real.sqrt (6 : ℝ)) ^ 2 = 1 / 6 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
    norm_num
  have hd : distanceSquared P R = 7 / 6 := by
    simp only [distanceSquared, P, R, sub_zero]
    rw [h]
    norm_num
  exact ⟨hd, by rw [arbitrary_points_distance, hd]⟩

theorem sample_euclidean_distance :
    euclideanDistance P R = Real.sqrt (7 / 6) ∧
    euclideanDistance (applyMatrix (Q r) P) (applyMatrix (Q r) R) =
      Real.sqrt (7 / 6) := by
  exact ⟨congrArg Real.sqrt sample_squared_distance.1,
    congrArg Real.sqrt sample_squared_distance.2⟩

end
end SpectralExample.Example21

#print axioms SpectralExample.Example21.characteristic_polynomial
#print axioms SpectralExample.Example21.characteristic_roots
#print axioms SpectralExample.Example21.eigenvalue_six_equation
#print axioms SpectralExample.Example21.eigenvalue_one_equation
#print axioms SpectralExample.Example21.normalized_eigenvectors
#print axioms SpectralExample.Example21.real_transpose_mul
#print axioms SpectralExample.Example21.real_mul_transpose
#print axioms SpectralExample.Example21.real_diagonalizes
#print axioms SpectralExample.Example21.determinant_Q
#print axioms SpectralExample.Example21.quadratic_standard_form
#print axioms SpectralExample.Example21.arbitrary_points_distance
#print axioms SpectralExample.Example21.sample_points_on_standard
#print axioms SpectralExample.Example21.sample_point_images
#print axioms SpectralExample.Example21.sample_points_on_original
#print axioms SpectralExample.Example21.sample_squared_distance
#print axioms SpectralExample.Example21.sample_euclidean_distance

#print axioms SpectralExample.Example21.sample_radical_image
