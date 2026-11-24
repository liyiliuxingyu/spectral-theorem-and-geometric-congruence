import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
# Theorem 2.1: finite real symmetric spectral theorem

Checked upstream API: Mathlib v4.19.0, commit
c44e0c8ee63ca166450922a373c7409c5d26b00b.
The key imported results are `Matrix.IsHermitian.eigenvectorBasis`,
`mulVec_eigenvectorBasis`, `star_mul_self_mul_eq_diagonal`, and `spectral_theorem`.

This file derives the real orthogonal form of mathlib's Hermitian spectral theorem.
It states the existence of real eigenvalues, an orthonormal eigenbasis, and a
matrix whose columns are this basis, with both orthogonality identities and both
diagonalization formulas. The matrix can have any finite index type, including
`Fin m` for every natural number m; no distinct-eigenvalue or positivity
hypothesis is imposed.
-/

open scoped Matrix

namespace SpectralBook

/-- A square real matrix is Hermitian exactly when its transpose equals itself. -/
theorem real_isHermitian_iff_transpose_eq
    {n : Type*} (A : Matrix n n ℝ) :
    A.IsHermitian ↔ A.transpose = A := by
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

/--
**Theorem 2.1.** Every finite real symmetric matrix has real eigenvalues and a
complete orthonormal eigenbasis. Its basis matrix is orthogonal and diagonalizes
A. All vector, orthogonality, and diagonalization assertions are explicit.
-/
theorem real_symmetric_spectral_theorem
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose = A) :
    ∃ (evals : n → ℝ) (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
      (Q : Matrix n n ℝ),
      (∀ i j, Q i j = (b j : n → ℝ) i) ∧
      (∀ j, A *ᵥ (b j : n → ℝ) = evals j • (b j : n → ℝ)) ∧
      Q.transpose * Q = 1 ∧
      Q * Q.transpose = 1 ∧
      Q.transpose * A * Q = Matrix.diagonal evals ∧
      A = Q * Matrix.diagonal evals * Q.transpose := by
  have hH : A.IsHermitian := (real_isHermitian_iff_transpose_eq A).mpr hA
  refine ⟨hH.eigenvalues, hH.eigenvectorBasis,
    (hH.eigenvectorUnitary : Matrix n n ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact hH.eigenvectorUnitary_apply i j
  · intro j
    exact hH.mulVec_eigenvectorBasis j
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (unitary.coe_star_mul_self hH.eigenvectorUnitary)
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (unitary.coe_mul_star_self hH.eigenvectorUnitary)
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using
      hH.star_mul_self_mul_eq_diagonal
  · simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
      RCLike.ofReal_real_eq_id, id_eq] using hH.spectral_theorem

/-- The familiar `QᵀQ = I`, `QᵀAQ = diag evals` corollary in every matrix size. -/
theorem real_symmetric_orthogonal_diagonalization
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.transpose = A) :
    ∃ (Q : Matrix n n ℝ) (evals : n → ℝ),
      Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧
      Q.transpose * A * Q = Matrix.diagonal evals ∧
      A = Q * Matrix.diagonal evals * Q.transpose := by
  obtain ⟨evals, b, Q, _, _, hQtQ, hQQt, hdiag, hAeq⟩ :=
    real_symmetric_spectral_theorem A hA
  exact ⟨Q, evals, hQtQ, hQQt, hdiag, hAeq⟩

end SpectralBook

#print axioms SpectralBook.real_symmetric_spectral_theorem
#print axioms SpectralBook.real_symmetric_orthogonal_diagonalization
