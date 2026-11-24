import Mathlib.LinearAlgebra.Matrix.Spectrum

/-!
# 谱定理与几何全等：任意有限维实对称矩阵

本文件使用 Mathlib 已证明的谱定理。空间明确采用 `EuclideanSpace`，
其度量是欧氏二范数诱导的距离。没有把普通函数空间的默认范数当成二范数。
对每个实数 c，构造整个二次型等值集之间的 `IsometryEquiv`。
特征值可以为正、为负或为零；等值集也可以为空。
-/

noncomputable section

open Matrix
open scoped BigOperators Matrix

namespace SpectralBook

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- 实对称矩阵 A 的二次型 xᵀ A x，定义在真实欧氏空间上。 -/
def quadraticValue (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) : ℝ :=
  dotProduct (fun i => x i) (A *ᵥ fun i => x i)

/-- 在标准坐标中的对角二次型。 -/
def diagonalValue (evals : n → ℝ) (u : EuclideanSpace ℝ n) : ℝ :=
  ∑ i, evals i * (u i) ^ 2

/-- 谱定理所提供的正交特征基，作为从新坐标到旧坐标的线性等距同构。 -/
def spectralCoordinates {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    EuclideanSpace ℝ n ≃ₗᵢ[ℝ] EuclideanSpace ℝ n :=
  hA.eigenvectorBasis.repr.symm

/-- 谱定理中的正交矩阵；第 j 列是第 j 个单位特征向量。 -/
def coordinateMatrix {A : Matrix n n ℝ} (hA : A.IsHermitian) : Matrix n n ℝ :=
  hA.eigenvectorUnitary

theorem spectralCoordinates_apply {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (u : EuclideanSpace ℝ n) :
    (fun i => spectralCoordinates hA u i) = coordinateMatrix hA *ᵥ (fun i => u i) := by
  funext i
  change hA.eigenvectorBasis.repr.symm u i = _
  have hs := congrArg (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : n => ℝ) i)
    (hA.eigenvectorBasis.sum_repr_symm u)
  simp only [map_sum, map_smul, PiLp.projₗ_apply, WithLp.equiv_pi_apply, smul_eq_mul] at hs
  rw [← hs]
  simp only [coordinateMatrix, Matrix.mulVec, dotProduct,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem coordinateMatrix_diagonalizes {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (coordinateMatrix hA)ᵀ * A * coordinateMatrix hA = Matrix.diagonal hA.eigenvalues := by
  simpa [coordinateMatrix, Matrix.star_eq_conjTranspose, Function.comp_def] using
    hA.star_mul_self_mul_eq_diagonal

/-- 任意两点的真实欧氏距离都保持。 -/
theorem spectralCoordinates_preserves_distance {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (u v : EuclideanSpace ℝ n) :
    dist (spectralCoordinates hA u) (spectralCoordinates hA v) = dist u v :=
  (spectralCoordinates hA).dist_map u v

/-- 换元后的二次型与对角二次型逐点相同。 -/
theorem quadraticValue_spectralCoordinates {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (u : EuclideanSpace ℝ n) :
    quadraticValue A (spectralCoordinates hA u) = diagonalValue hA.eigenvalues u := by
  unfold quadraticValue
  rw [spectralCoordinates_apply]
  have hassoc := (Matrix.dotProduct_mulVec (fun i => u i)
    (coordinateMatrix hA)ᵀ (A *ᵥ (coordinateMatrix hA *ᵥ (fun i => u i)))).symm
  rw [Matrix.vecMul_transpose] at hassoc
  rw [hassoc, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    coordinateMatrix_diagonalizes]
  unfold dotProduct diagonalValue
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_diagonal]
  simp only [pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- 整个实二次型等值集。 -/
abbrev QuadraticLevel (A : Matrix n n ℝ) (c : ℝ) :=
  {x : EuclideanSpace ℝ n // quadraticValue A x = c}

/-- 整个实对角二次型等值集。 -/
abbrev DiagonalLevel (evals : n → ℝ) (c : ℝ) :=
  {u : EuclideanSpace ℝ n // diagonalValue evals u = c}

/-- 谱定理给出的等值集全等：双射及真正的欧氏距离保持一起打包。 -/
def spectralLevelIsometry {A : Matrix n n ℝ} (hA : A.IsHermitian) (c : ℝ) :
    DiagonalLevel hA.eigenvalues c ≃ᵢ QuadraticLevel A c where
  toFun u := ⟨spectralCoordinates hA u.val, by
    rw [quadraticValue_spectralCoordinates, u.property]⟩
  invFun x := ⟨(spectralCoordinates hA).symm x.val, by
    rw [← quadraticValue_spectralCoordinates hA,
      LinearIsometryEquiv.apply_symm_apply, x.property]⟩
  left_inv u := by
    apply Subtype.ext
    exact (spectralCoordinates hA).symm_apply_apply u.val
  right_inv x := by
    apply Subtype.ext
    exact (spectralCoordinates hA).apply_symm_apply x.val
  isometry_toFun := by
    intro u v
    exact (spectralCoordinates hA).isometry u.val v.val

theorem spectralLevelIsometry_preserves_distance {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) (u v : DiagonalLevel hA.eigenvalues c) :
    dist (spectralLevelIsometry hA c u) (spectralLevelIsometry hA c v) = dist u v :=
  (spectralLevelIsometry hA c).dist_eq u v

omit [DecidableEq n] in
/-- 用 Aᵀ=A 的通常表述：存在同一组 λ，使所有实水平 c 的图形全等。 -/
theorem real_symmetric_level_sets_congruent (A : Matrix n n ℝ) (hA : Aᵀ = A) :
    ∃ evals : n → ℝ, ∀ c : ℝ, Nonempty (DiagonalLevel evals c ≃ᵢ QuadraticLevel A c) := by
  classical
  have hH : A.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  exact ⟨hH.eigenvalues, fun c => ⟨spectralLevelIsometry hH c⟩⟩

end SpectralBook

#print axioms SpectralBook.quadraticValue_spectralCoordinates
#print axioms SpectralBook.spectralLevelIsometry
#print axioms SpectralBook.spectralLevelIsometry_preserves_distance
#print axioms SpectralBook.real_symmetric_level_sets_congruent
