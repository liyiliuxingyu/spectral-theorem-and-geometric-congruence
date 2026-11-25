import SpectralCongruence
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Equal characteristic polynomials imply orthogonal similarity in dimension two

The hypothesis below is genuine equality of Mathlib's characteristic polynomials.
A common diagonal form is proved, not assumed: equality of characteristic
polynomials gives equality of traces and determinants; the spectral theorem
then gives two eigenvalue pairs with the same sum and product. The pairs are
proved equal up to swapping, including repeated eigenvalues. No positive-
definiteness hypothesis is needed for orthogonal similarity or level isometry.
When the two forms are positive definite, their unit levels are the ellipses.
-/

noncomputable section
open Matrix
open scoped Matrix BigOperators

namespace SpectralExample.EllipseForward

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ
abbrev Space := EuclideanSpace ℝ (Fin 2)

def Orthogonal (Q : Mat) : Prop := Q.transpose * Q = 1 ∧ Q * Q.transpose = 1

lemma eigenmatrix_orthogonal {A : Mat} (hA : A.IsHermitian) :
    Orthogonal (hA.eigenvectorUnitary : Mat) := by
  constructor
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      unitary.coe_mul_star_self hA.eigenvectorUnitary

lemma real_spectral_decomposition {A : Mat} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Mat) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Mat).transpose := by
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
    RCLike.ofReal_real_eq_id, id_eq] using hA.spectral_theorem

lemma real_spectral_diagonalization {A : Mat} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Mat).transpose * A *
      (hA.eigenvectorUnitary : Mat) = diagonal hA.eigenvalues := by
  simpa only [Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
    RCLike.ofReal_real_eq_id, id_eq] using hA.star_mul_self_mul_eq_diagonal

lemma trace_eq_eigenvalue_sum {A : Mat} (hA : A.IsHermitian) :
    A.trace = hA.eigenvalues 0 + hA.eigenvalues 1 := by
  calc
    A.trace = ((hA.eigenvectorUnitary : Mat) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Mat).transpose).trace :=
      congrArg Matrix.trace (real_spectral_decomposition hA)
    _ = hA.eigenvalues 0 + hA.eigenvalues 1 := by
      rw [Matrix.trace_mul_cycle, (eigenmatrix_orthogonal hA).1,
        Matrix.one_mul, Matrix.trace_diagonal]
      simp [Fin.sum_univ_two]

/-- The counting-multiplicity step: two real eigenvalue pairs must match or swap. -/
theorem charpoly_eq_eigenvalues_match {A B : Mat}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hchar : A.charpoly = B.charpoly) :
    (hA.eigenvalues 0 = hB.eigenvalues 0 ∧ hA.eigenvalues 1 = hB.eigenvalues 1) ∨
    (hA.eigenvalues 0 = hB.eigenvalues 1 ∧ hA.eigenvalues 1 = hB.eigenvalues 0) := by
  have ht : A.trace = B.trace := by
    rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, hchar]
  have hd : A.det = B.det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hchar]
  have hs : hA.eigenvalues 0 + hA.eigenvalues 1 =
      hB.eigenvalues 0 + hB.eigenvalues 1 :=
    (trace_eq_eigenvalue_sum hA).symm.trans (ht.trans (trace_eq_eigenvalue_sum hB))
  have hp : hA.eigenvalues 0 * hA.eigenvalues 1 =
      hB.eigenvalues 0 * hB.eigenvalues 1 := by
    simpa [Fin.prod_univ_two] using
      hA.det_eq_prod_eigenvalues.symm.trans (hd.trans hB.det_eq_prod_eigenvalues)
  have hz : (hA.eigenvalues 0 - hB.eigenvalues 0) *
      (hA.eigenvalues 0 - hB.eigenvalues 1) = 0 := by
    nlinarith [congrArg (fun t : ℝ => hA.eigenvalues 0 * t) hs]
  rcases mul_eq_zero.mp hz with hzero | hzero
  · left
    exact ⟨sub_eq_zero.mp hzero, by linarith⟩
  · right
    exact ⟨sub_eq_zero.mp hzero, by linarith⟩

lemma orthogonal_mul {Q R : Mat} (hQ : Orthogonal Q) (hR : Orthogonal R) :
    Orthogonal (Q * R) := by
  constructor
  · simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q.transpose Q R, hQ.1, Matrix.one_mul, hR.1]
  · simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc R R.transpose Q.transpose, hR.2, Matrix.one_mul, hQ.2]

lemma orthogonal_transpose {Q : Mat} (hQ : Orthogonal Q) : Orthogonal Q.transpose := by
  exact ⟨by simpa using hQ.2, by simpa using hQ.1⟩

def swapMatrix : Mat := !![0, 1; 1, 0]

lemma swapMatrix_orthogonal : Orthogonal swapMatrix := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]

lemma matched_diagonals_orthogonally_similar (a b : Fin 2 → ℝ)
    (h : (a 0 = b 0 ∧ a 1 = b 1) ∨ (a 0 = b 1 ∧ a 1 = b 0)) :
    ∃ P : Mat, Orthogonal P ∧ P.transpose * diagonal a * P = diagonal b := by
  rcases h with h | h
  · refine ⟨1, ⟨by simp, by simp⟩, ?_⟩
    have hab : a = b := by funext i; fin_cases i <;> simp [h.1, h.2]
    simp [hab]
  · refine ⟨swapMatrix, swapMatrix_orthogonal, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.transpose_apply, h.1, h.2]

/-- Genuine charpoly equality, including multiplicities, implies orthogonal similarity. -/
theorem charpoly_eq_implies_orthogonal_similarity (A B : Mat)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hchar : A.charpoly = B.charpoly) :
    ∃ Q : Mat, Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧ Q.transpose * A * Q = B := by
  have hHA : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hHB : B.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  obtain ⟨P, hP, hdiag⟩ := matched_diagonals_orthogonally_similar
    hHA.eigenvalues hHB.eigenvalues (charpoly_eq_eigenvalues_match hHA hHB hchar)
  let U : Mat := hHA.eigenvectorUnitary
  let V : Mat := hHB.eigenvectorUnitary
  let Q : Mat := U * P * V.transpose
  have hQ : Orthogonal Q := orthogonal_mul
    (orthogonal_mul (eigenmatrix_orthogonal hHA) hP)
    (orthogonal_transpose (eigenmatrix_orthogonal hHB))
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  calc
    Q.transpose * A * Q = V * (P.transpose * (U.transpose * A * U) * P) *
      V.transpose := by
        simp only [Q, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = V * diagonal hHB.eigenvalues * V.transpose := by
      rw [show U.transpose * A * U = diagonal hHA.eigenvalues from
        real_spectral_diagonalization hHA, hdiag]
    _ = B := (real_spectral_decomposition hHB).symm


/-- A coordinate swap is an isometry for the actual Euclidean two-norm. -/
def coordinateSwap : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

lemma coordinateSwap_zero (u : Space) : coordinateSwap u 0 = u 1 := by
  change u (Equiv.swap (0 : Fin 2) 1 0) = u 1
  exact congrArg u (Equiv.swap_apply_left 0 1)

lemma coordinateSwap_one (u : Space) : coordinateSwap u 1 = u 0 := by
  change u (Equiv.swap (0 : Fin 2) 1 1) = u 0
  exact congrArg u (Equiv.swap_apply_right 0 1)

/-- Restrict a proved Euclidean linear isometry to equal-value quadratic levels. -/
def diagonalLevelTransport (a b : Fin 2 → ℝ) (e : Space ≃ₗᵢ[ℝ] Space)
    (hvalue : ∀ u, SpectralBook.diagonalValue a (e u) = SpectralBook.diagonalValue b u)
    (c : ℝ) : SpectralBook.DiagonalLevel b c ≃ᵢ SpectralBook.DiagonalLevel a c where
  toFun u := ⟨e u.val, by rw [hvalue, u.property]⟩
  invFun v := ⟨e.symm v.val, by
    rw [← hvalue, LinearIsometryEquiv.apply_symm_apply, v.property]⟩
  left_inv u := by
    apply Subtype.ext
    exact e.symm_apply_apply u.val
  right_inv v := by
    apply Subtype.ext
    exact e.apply_symm_apply v.val
  isometry_toFun := by
    intro u v
    exact e.isometry u.val v.val

/-- Equal charpolys imply congruence of every real quadratic level set.
For positive definite A,B and c=1, this is congruence of the unit ellipses. -/
theorem charpoly_eq_implies_level_isometry (A B : Mat)
    (hA : A.transpose = A) (hB : B.transpose = B)
    (hchar : A.charpoly = B.charpoly) (c : ℝ) :
    Nonempty (SpectralBook.QuadraticLevel B c ≃ᵢ SpectralBook.QuadraticLevel A c) := by
  have hHA : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hHB : B.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hB
  rcases charpoly_eq_eigenvalues_match hHA hHB hchar with hsame | hswap
  · have hvalue : ∀ u : Space,
        SpectralBook.diagonalValue hHA.eigenvalues ((LinearIsometryEquiv.refl ℝ Space) u) =
          SpectralBook.diagonalValue hHB.eigenvalues u := by
      intro u
      simp [SpectralBook.diagonalValue, Fin.sum_univ_two, hsame.1, hsame.2]
    exact ⟨((SpectralBook.spectralLevelIsometry hHB c).symm.trans
      (diagonalLevelTransport hHA.eigenvalues hHB.eigenvalues
        (LinearIsometryEquiv.refl ℝ Space) hvalue c)).trans
      (SpectralBook.spectralLevelIsometry hHA c)⟩
  · have hvalue : ∀ u : Space,
        SpectralBook.diagonalValue hHA.eigenvalues (coordinateSwap u) =
          SpectralBook.diagonalValue hHB.eigenvalues u := by
      intro u
      simp only [SpectralBook.diagonalValue, Fin.sum_univ_two,
        coordinateSwap_zero, coordinateSwap_one, hswap.1, hswap.2]
      exact add_comm _ _
    exact ⟨((SpectralBook.spectralLevelIsometry hHB c).symm.trans
      (diagonalLevelTransport hHA.eigenvalues hHB.eigenvalues coordinateSwap hvalue c)).trans
      (SpectralBook.spectralLevelIsometry hHA c)⟩

end SpectralExample.EllipseForward

#print axioms SpectralExample.EllipseForward.charpoly_eq_eigenvalues_match
#print axioms SpectralExample.EllipseForward.charpoly_eq_implies_orthogonal_similarity

#print axioms SpectralExample.EllipseForward.charpoly_eq_implies_level_isometry
