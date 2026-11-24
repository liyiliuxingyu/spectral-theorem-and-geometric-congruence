import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Orthogonal finite coordinates, without importing Mathlib's Matrix hierarchy

Every index set below is an arbitrary finite type. Scalars are real numbers.
Rows AND columns are assumed orthonormal explicitly; this file does not claim
that one of these hypotheses has been derived from the other. Matrix-vector
multiplication, transpose and matrix multiplication are defined by finite sums.

The main results prove transpose two-sided inverses, preservation of the
Euclidean distance, and a distance-preserving equivalence of common quadratic
level sets from either A Q = Q D or Qᵀ A Q = D. No existence part of the spectral
theorem is assumed to have been proved here, and A,D need not be symmetric.
-/

namespace OrthogonalCoordinates

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Vec (ι : Type*) := ι → ℝ
abbrev Mat (ι : Type*) := ι → ι → ℝ

noncomputable def dot (x y : Vec ι) : ℝ := ∑ i, x i * y i
noncomputable def mv (M : Mat ι) (x : Vec ι) : Vec ι := fun i => ∑ j, M i j * x j
noncomputable def mm (M N : Mat ι) : Mat ι := fun i j => ∑ k, M i k * N k j
def transpose (M : Mat ι) : Mat ι := fun i j => M j i
def identity : Mat ι := fun i j => if i = j then 1 else 0

/-- Unit, pairwise-orthogonal columns, including the equal-index case. -/
def ColumnsOrthonormal (Q : Mat ι) : Prop :=
  ∀ j k, ∑ i, Q i j * Q i k = if j = k then 1 else 0

/-- Unit, pairwise-orthogonal rows, including the equal-index case. -/
def RowsOrthonormal (Q : Mat ι) : Prop :=
  ∀ i k, ∑ j, Q i j * Q k j = if i = k then 1 else 0

noncomputable def distanceSquared (x y : Vec ι) : ℝ := dot (fun i => x i - y i) (fun i => x i - y i)
/-- The ordinary coordinate Euclidean distance; not a product-space default metric. -/
noncomputable def euclideanDistance (x y : Vec ι) : ℝ := Real.sqrt (distanceSquared x y)
noncomputable def quadratic (A : Mat ι) (x : Vec ι) : ℝ := dot x (mv A x)
def Level (A : Mat ι) (c : ℝ) := {x : Vec ι // quadratic A x = c}

theorem mv_identity (x : Vec ι) : mv identity x = x := by
  funext i
  simp [mv, identity]

omit [DecidableEq ι] in
theorem mv_mm (M N : Mat ι) (x : Vec ι) : mv (mm M N) x = mv M (mv N x) := by
  funext i
  simp only [mv, mm, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem transpose_mul_self (Q : Mat ι) (hc : ColumnsOrthonormal Q) :
    mm (transpose Q) Q = identity := by
  funext j k
  exact hc j k

theorem self_mul_transpose (Q : Mat ι) (hr : RowsOrthonormal Q) :
    mm Q (transpose Q) = identity := by
  funext i k
  exact hr i k

theorem transpose_after (Q : Mat ι) (hc : ColumnsOrthonormal Q) (x : Vec ι) :
    mv (transpose Q) (mv Q x) = x := by
  rw [← mv_mm, transpose_mul_self Q hc, mv_identity]

theorem transpose_before (Q : Mat ι) (hr : RowsOrthonormal Q) (x : Vec ι) :
    mv Q (mv (transpose Q) x) = x := by
  rw [← mv_mm, self_mul_transpose Q hr, mv_identity]

omit [DecidableEq ι] in
theorem dot_adjoint (Q : Mat ι) (x y : Vec ι) :
    dot (mv Q x) y = dot x (mv (transpose Q) y) := by
  simp only [dot, mv, transpose, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_preserved (Q : Mat ι) (hc : ColumnsOrthonormal Q) (x y : Vec ι) :
    dot (mv Q x) (mv Q y) = dot x y := by
  rw [dot_adjoint, transpose_after Q hc]

omit [DecidableEq ι] in
theorem mv_sub (Q : Mat ι) (x y : Vec ι) :
    mv Q (fun i => x i - y i) = fun i => mv Q x i - mv Q y i := by
  funext i
  simp only [mv, mul_sub, Finset.sum_sub_distrib]

omit [DecidableEq ι] in
theorem distanceSquared_nonneg (x y : Vec ι) : 0 ≤ distanceSquared x y := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

theorem distanceSquared_preserved (Q : Mat ι) (hc : ColumnsOrthonormal Q) (x y : Vec ι) :
    distanceSquared (mv Q x) (mv Q y) = distanceSquared x y := by
  unfold distanceSquared
  rw [← mv_sub, dot_preserved Q hc]

theorem distance_preserved (Q : Mat ι) (hc : ColumnsOrthonormal Q) (x y : Vec ι) :
    euclideanDistance (mv Q x) (mv Q y) = euclideanDistance x y := by
  unfold euclideanDistance
  rw [distanceSquared_preserved Q hc]

/-- The full coordinate equivalence uses both orthonormality assumptions. -/
noncomputable def coordinateEquiv (Q : Mat ι)
    (hc : ColumnsOrthonormal Q) (hr : RowsOrthonormal Q) : Vec ι ≃ Vec ι where
  toFun := mv Q
  invFun := mv (transpose Q)
  left_inv := transpose_after Q hc
  right_inv := transpose_before Q hr

/-- A Q = Q D entails the quadratic identity by preservation of the inner product. -/
theorem quadratic_of_intertwining (A D Q : Mat ι) (hc : ColumnsOrthonormal Q)
    (h : mm A Q = mm Q D) (x : Vec ι) : quadratic A (mv Q x) = quadratic D x := by
  unfold quadratic
  have hx : mv A (mv Q x) = mv Q (mv D x) := by
    rw [← mv_mm, h, mv_mm]
  rw [hx, dot_preserved Q hc]

omit [DecidableEq ι] in
/-- Qᵀ A Q = D also entails the quadratic identity directly. -/
theorem quadratic_of_conjugacy (A D Q : Mat ι)
    (h : mm (mm (transpose Q) A) Q = D) (x : Vec ι) :
    quadratic A (mv Q x) = quadratic D x := by
  unfold quadratic
  rw [dot_adjoint]
  have hx : mv (transpose Q) (mv A (mv Q x)) = mv D x := by
    rw [← mv_mm, ← mv_mm, h]
  rw [hx]

/-- General transfer lemma: a common quadratic level set equivalence. -/
noncomputable def levelEquiv (A D Q : Mat ι)
    (hc : ColumnsOrthonormal Q) (hr : RowsOrthonormal Q)
    (hquad : ∀ x, quadratic A (mv Q x) = quadratic D x) (c : ℝ) :
    Level D c ≃ Level A c where
  toFun x := ⟨mv Q x.val, by rw [hquad, x.property]⟩
  invFun y := ⟨mv (transpose Q) y.val, by
    rw [← hquad, transpose_before Q hr, y.property]⟩
  left_inv x := by
    apply Subtype.ext
    exact transpose_after Q hc x.val
  right_inv y := by
    apply Subtype.ext
    exact transpose_before Q hr y.val

/-- The level equivalence preserves the actual (square-root) Euclidean distance. -/
theorem levelEquiv_distance (A D Q : Mat ι)
    (hc : ColumnsOrthonormal Q) (hr : RowsOrthonormal Q)
    (hquad : ∀ x, quadratic A (mv Q x) = quadratic D x) (c : ℝ)
    (x y : Level D c) :
    euclideanDistance (levelEquiv A D Q hc hr hquad c x).val
        (levelEquiv A D Q hc hr hquad c y).val = euclideanDistance x.val y.val := by
  exact distance_preserved Q hc x.val y.val

/-- End-to-end theorem with the A Q = Q D hypothesis. -/
theorem intertwining_level_congruence (A D Q : Mat ι)
    (hc : ColumnsOrthonormal Q) (hr : RowsOrthonormal Q)
    (h : mm A Q = mm Q D) (c : ℝ) :
    ∃ e : Level D c ≃ Level A c, ∀ x y,
      euclideanDistance (e x).val (e y).val = euclideanDistance x.val y.val := by
  exact ⟨levelEquiv A D Q hc hr (quadratic_of_intertwining A D Q hc h) c,
    levelEquiv_distance A D Q hc hr (quadratic_of_intertwining A D Q hc h) c⟩

/-- End-to-end theorem with Qᵀ A Q = D. -/
theorem conjugacy_level_congruence (A D Q : Mat ι)
    (hc : ColumnsOrthonormal Q) (hr : RowsOrthonormal Q)
    (h : mm (mm (transpose Q) A) Q = D) (c : ℝ) :
    ∃ e : Level D c ≃ Level A c, ∀ x y,
      euclideanDistance (e x).val (e y).val = euclideanDistance x.val y.val := by
  exact ⟨levelEquiv A D Q hc hr (quadratic_of_conjugacy A D Q h) c,
    levelEquiv_distance A D Q hc hr (quadratic_of_conjugacy A D Q h) c⟩

end OrthogonalCoordinates

#print axioms OrthogonalCoordinates.transpose_mul_self
#print axioms OrthogonalCoordinates.coordinateEquiv
#print axioms OrthogonalCoordinates.distance_preserved
#print axioms OrthogonalCoordinates.intertwining_level_congruence
#print axioms OrthogonalCoordinates.conjugacy_level_congruence
