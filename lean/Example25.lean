import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 例 2.5：正定单位椭圆如何决定二次型与真正的特征多项式

点用实数对表示，距离明确是欧氏距离。Sym2 表示 [[a,b],[b,c]]；
Mat2 表示任意实二阶矩阵。Orthogonal 同时展开 QᵀQ=I 与 QQᵀ=I。
最终同谱结论是 Mathlib 的 Matrix.charpoly 相等，保留根的重数。
本文件只负责已消去平移后的反向论证；不以正交共轭充当同谱的定义。
-/
open scoped Matrix

namespace SpectralExample.Example25

noncomputable section

abbrev Point := ℝ × ℝ

structure Sym2 where
  a : ℝ
  b : ℝ
  c : ℝ

structure Mat2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def qForm (A : Sym2) (p : Point) : ℝ :=
  A.a * p.1 ^ 2 + 2 * A.b * p.1 * p.2 + A.c * p.2 ^ 2

def applyMatrix (Q : Mat2) (p : Point) : Point :=
  (Q.a * p.1 + Q.b * p.2, Q.c * p.1 + Q.d * p.2)

def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)
def transpose (Q : Mat2) : Mat2 := ⟨Q.a, Q.c, Q.b, Q.d⟩
def distanceSquared (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2
def euclideanDistance (p q : Point) : ℝ := Real.sqrt (distanceSquared p q)

def PositiveDefinite (A : Sym2) : Prop :=
  ∀ p : Point, p ≠ (0, 0) → 0 < qForm A p

/-- 列、行分别单位正交，正是 QᵀQ=QQᵀ=I 的六个实坐标等式。 -/
def Orthogonal (Q : Mat2) : Prop :=
  Q.a ^ 2 + Q.c ^ 2 = 1 ∧ Q.b ^ 2 + Q.d ^ 2 = 1 ∧ Q.a * Q.b + Q.c * Q.d = 0 ∧
  Q.a ^ 2 + Q.b ^ 2 = 1 ∧ Q.c ^ 2 + Q.d ^ 2 = 1 ∧ Q.a * Q.c + Q.b * Q.d = 0

def trace (A : Sym2) : ℝ := A.a + A.c
def determinant (A : Sym2) : ℝ := A.a * A.c - A.b ^ 2
def matDet (Q : Mat2) : ℝ := Q.a * Q.d - Q.b * Q.c

def congruence (Q : Mat2) (B : Sym2) : Sym2 :=
  ⟨B.a * Q.a ^ 2 + 2 * B.b * Q.a * Q.c + B.c * Q.c ^ 2,
   B.a * Q.a * Q.b + B.b * (Q.a * Q.d + Q.b * Q.c) + B.c * Q.c * Q.d,
   B.a * Q.b ^ 2 + 2 * B.b * Q.b * Q.d + B.c * Q.d ^ 2⟩

def symMatrix (A : Sym2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A.a, A.b; A.b, A.c]

def matMatrix (Q : Mat2) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Q.a, Q.b; Q.c, Q.d]

/-- 此处“同谱”直接指真正特征多项式相等，因而保留代数重数。 -/
def SameSpectrum (A B : Sym2) : Prop := (symMatrix A).charpoly = (symMatrix B).charpoly

private theorem sym_ext {A B : Sym2}
    (ha : A.a = B.a) (hb : A.b = B.b) (hc : A.c = B.c) : A = B := by
  cases A
  cases B
  cases ha
  cases hb
  cases hc
  rfl

theorem qForm_scale (A : Sym2) (t : ℝ) (p : Point) :
    qForm A (scale t p) = t ^ 2 * qForm A p := by
  simp only [qForm, scale]
  ring

theorem applyMatrix_scale (Q : Mat2) (t : ℝ) (p : Point) :
    applyMatrix Q (scale t p) = scale t (applyMatrix Q p) := by
  apply Prod.ext <;> simp only [applyMatrix, scale] <;> ring

theorem orthogonal_inverse_left (Q : Mat2) (hQ : Orthogonal Q) (p : Point) :
    applyMatrix (transpose Q) (applyMatrix Q p) = p := by
  rcases hQ with ⟨hc1, hc2, hc3, _, _, _⟩
  apply Prod.ext
  · calc
      _ = (Q.a ^ 2 + Q.c ^ 2) * p.1 + (Q.a * Q.b + Q.c * Q.d) * p.2 := by
        simp only [applyMatrix, transpose]; ring
      _ = p.1 := by rw [hc1, hc3]; ring
  · calc
      _ = (Q.a * Q.b + Q.c * Q.d) * p.1 + (Q.b ^ 2 + Q.d ^ 2) * p.2 := by
        simp only [applyMatrix, transpose]; ring
      _ = p.2 := by rw [hc2, hc3]; ring

theorem orthogonal_inverse_right (Q : Mat2) (hQ : Orthogonal Q) (p : Point) :
    applyMatrix Q (applyMatrix (transpose Q) p) = p := by
  rcases hQ with ⟨_, _, _, hr1, hr2, hr3⟩
  apply Prod.ext
  · calc
      _ = (Q.a ^ 2 + Q.b ^ 2) * p.1 + (Q.a * Q.c + Q.b * Q.d) * p.2 := by
        simp only [applyMatrix, transpose]; ring
      _ = p.1 := by rw [hr1, hr3]; ring
  · calc
      _ = (Q.a * Q.c + Q.b * Q.d) * p.1 + (Q.c ^ 2 + Q.d ^ 2) * p.2 := by
        simp only [applyMatrix, transpose]; ring
      _ = p.2 := by rw [hr2, hr3]; ring

theorem orthogonal_surjective (Q : Mat2) (hQ : Orthogonal Q) :
    Function.Surjective (applyMatrix Q) := by
  intro p
  exact ⟨applyMatrix (transpose Q) p, orthogonal_inverse_right Q hQ p⟩

theorem orthogonal_preserves_distanceSquared (Q : Mat2) (hQ : Orthogonal Q)
    (p r : Point) :
    distanceSquared (applyMatrix Q p) (applyMatrix Q r) = distanceSquared p r := by
  rcases hQ with ⟨hc1, hc2, hc3, _, _, _⟩
  calc
    _ = (Q.a ^ 2 + Q.c ^ 2) * (p.1 - r.1) ^ 2 +
        2 * (Q.a * Q.b + Q.c * Q.d) * (p.1 - r.1) * (p.2 - r.2) +
        (Q.b ^ 2 + Q.d ^ 2) * (p.2 - r.2) ^ 2 := by
      simp only [distanceSquared, applyMatrix]; ring
    _ = distanceSquared p r := by rw [hc1, hc2, hc3]; simp [distanceSquared]

theorem orthogonal_preserves_distance (Q : Mat2) (hQ : Orthogonal Q)
    (p r : Point) :
    euclideanDistance (applyMatrix Q p) (applyMatrix Q r) = euclideanDistance p r := by
  unfold euclideanDistance
  rw [orthogonal_preserves_distanceSquared Q hQ p r]

/-- 正定源二次型的单位水平映入，已决定所有向量上的二次型；目标无需预设正定。 -/
theorem unit_level_determines_form (A B : Sym2) (Q : Mat2)
    (hA : PositiveDefinite A)
    (hlevel : ∀ p, qForm A p = 1 → qForm B (applyMatrix Q p) = 1) :
    ∀ p, qForm B (applyMatrix Q p) = qForm A p := by
  intro p
  by_cases hp : p = (0, 0)
  · subst p
    simp [qForm, applyMatrix]
  · have hpos : 0 < qForm A p := hA p hp
    have hne : qForm A p ≠ 0 := ne_of_gt hpos
    let t : ℝ := 1 / Real.sqrt (qForm A p)
    have ht : t ^ 2 = 1 / qForm A p := by
      dsimp [t]
      rw [div_pow, Real.sq_sqrt (le_of_lt hpos)]
      norm_num
    have hnorm : t ^ 2 * qForm A p = 1 := by
      rw [ht]
      calc
        _ = qForm A p / qForm A p := by ring
        _ = 1 := div_self hne
    have hunit : qForm A (scale t p) = 1 := by rw [qForm_scale, hnorm]
    have himage := hlevel (scale t p) hunit
    rw [applyMatrix_scale, qForm_scale] at himage
    have htne : t ^ 2 ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hnorm
      norm_num at hnorm
    exact mul_left_cancel₀ htne (himage.trans hnorm.symm)

/-- 极化的二阶坐标版本：e1、e2、e1+e2 三个值读出全部对称系数。 -/
theorem polarization_coefficients (A B : Sym2)
    (h : ∀ p, qForm A p = qForm B p) : A = B := by
  have h1 := h (1, 0)
  have h2 := h (0, 1)
  have h3 := h (1, 1)
  simp only [qForm] at h1 h2 h3
  apply sym_ext
  · nlinarith only [h1]
  · nlinarith only [h1, h2, h3]
  · nlinarith only [h2]

/-- 显式的 Qᵀ B Q 系数与代入后的二次型一致。 -/
theorem qForm_congruence (Q : Mat2) (B : Sym2) (p : Point) :
    qForm (congruence Q B) p = qForm B (applyMatrix Q p) := by
  simp only [qForm, congruence, applyMatrix]
  ring

theorem level_implies_congruence (A B : Sym2) (Q : Mat2)
    (hA : PositiveDefinite A)
    (hlevel : ∀ p, qForm A p = 1 → qForm B (applyMatrix Q p) = 1) :
    A = congruence Q B := by
  apply polarization_coefficients
  intro p
  rw [qForm_congruence]
  exact (unit_level_determines_form A B Q hA hlevel p).symm

theorem trace_congruence (Q : Mat2) (B : Sym2) (hQ : Orthogonal Q) :
    trace (congruence Q B) = trace B := by
  rcases hQ with ⟨_, _, _, hr1, hr2, hr3⟩
  calc
    _ = B.a * (Q.a ^ 2 + Q.b ^ 2) +
        2 * B.b * (Q.a * Q.c + Q.b * Q.d) +
        B.c * (Q.c ^ 2 + Q.d ^ 2) := by
      simp only [trace, congruence]; ring
    _ = trace B := by rw [hr1, hr2, hr3]; simp [trace]

theorem orthogonal_det_sq (Q : Mat2) (hQ : Orthogonal Q) :
    matDet Q ^ 2 = 1 := by
  rcases hQ with ⟨hc1, hc2, hc3, _, _, _⟩
  calc
    _ = (Q.a ^ 2 + Q.c ^ 2) * (Q.b ^ 2 + Q.d ^ 2) -
        (Q.a * Q.b + Q.c * Q.d) ^ 2 := by simp only [matDet]; ring
    _ = 1 := by rw [hc1, hc2, hc3]; norm_num

theorem determinant_congruence (Q : Mat2) (B : Sym2) (hQ : Orthogonal Q) :
    determinant (congruence Q B) = determinant B := by
  calc
    _ = determinant B * matDet Q ^ 2 := by
      simp only [determinant, congruence, matDet]; ring
    _ = determinant B := by rw [orthogonal_det_sq Q hQ]; ring

/-- 真实的实对称矩阵，非形式上的系数列表。 -/
theorem symMatrix_symmetric (A : Sym2) : (symMatrix A).transpose = symMatrix A := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- 直接从 Mathlib 的 det(XI-A) 定义展开，不另定义“同谱”替代品。 -/
theorem symMatrix_charpoly (A : Sym2) :
    (symMatrix A).charpoly =
      Polynomial.X ^ 2 - Polynomial.C (trace A) * Polynomial.X +
        Polynomial.C (determinant A) := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two,
    symMatrix, trace, determinant, map_add, map_sub, map_mul, map_pow]
  ring

theorem unit_level_implies_charpoly (A B : Sym2) (Q : Mat2)
    (hA : PositiveDefinite A) (hQ : Orthogonal Q)
    (hlevel : ∀ p, qForm A p = 1 → qForm B (applyMatrix Q p) = 1) :
    (symMatrix A).charpoly = (symMatrix B).charpoly := by
  have hcong := level_implies_congruence A B Q hA hlevel
  have htr : trace A = trace B := by rw [hcong, trace_congruence Q B hQ]
  have hdet : determinant A = determinant B := by rw [hcong, determinant_congruence Q B hQ]
  rw [symMatrix_charpoly, symMatrix_charpoly, htr, hdet]

/-- 坐标结构的“正交”推出通常实矩阵的两侧正交恒等式。 -/
theorem matMatrix_orthogonal (Q : Mat2) (hQ : Orthogonal Q) :
    (matMatrix Q).transpose * matMatrix Q = 1 ∧
    matMatrix Q * (matMatrix Q).transpose = 1 := by
  rcases hQ with ⟨hc1, hc2, hc3, hr1, hr2, hr3⟩
  constructor
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, matMatrix, Matrix.transpose_apply] <;>
      nlinarith only [hc1, hc2, hc3]
  · funext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, matMatrix, Matrix.transpose_apply] <;>
      nlinarith only [hr1, hr2, hr3]

/-- 系数版合同与 Mathlib 的实矩阵合同完全一致。 -/
theorem symMatrix_congruence (Q : Mat2) (B : Sym2) :
    symMatrix (congruence Q B) =
      (matMatrix Q).transpose * symMatrix B * matMatrix Q := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, matMatrix, symMatrix, congruence,
      Matrix.transpose_apply] <;> ring

end
end SpectralExample.Example25

#print axioms SpectralExample.Example25.orthogonal_inverse_left
#print axioms SpectralExample.Example25.orthogonal_inverse_right
#print axioms SpectralExample.Example25.orthogonal_surjective
#print axioms SpectralExample.Example25.orthogonal_preserves_distanceSquared
#print axioms SpectralExample.Example25.orthogonal_preserves_distance
#print axioms SpectralExample.Example25.unit_level_determines_form
#print axioms SpectralExample.Example25.polarization_coefficients
#print axioms SpectralExample.Example25.qForm_congruence
#print axioms SpectralExample.Example25.level_implies_congruence
#print axioms SpectralExample.Example25.trace_congruence
#print axioms SpectralExample.Example25.orthogonal_det_sq
#print axioms SpectralExample.Example25.determinant_congruence
#print axioms SpectralExample.Example25.symMatrix_symmetric
#print axioms SpectralExample.Example25.symMatrix_charpoly
#print axioms SpectralExample.Example25.unit_level_implies_charpoly
#print axioms SpectralExample.Example25.matMatrix_orthogonal
#print axioms SpectralExample.Example25.symMatrix_congruence
