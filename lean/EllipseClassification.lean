import Example25
import EllipseCenter
import EllipseForward

/-!
例 2.5 的双向判据。这里的全等是整个平面的刚体运动：允许平移、旋转或反射。
两条曲线的对应是对所有点的「当且仅当」，不是用几个抽样点判定全等。
同谱使用 Mathlib 的真实特征多项式，因此包括圆的二重特征值。
-/
open scoped Matrix
namespace SpectralExample.EllipseClassification
open SpectralExample.Example25

noncomputable section

def move (Q : Mat2) (b p : Point) : Point :=
  ((applyMatrix Q p).1 + b.1, (applyMatrix Q p).2 + b.2)

/-- 变换保持的是平面中任意两点的欧氏弦长，包括不在椭圆上的点。 -/
theorem move_preserves_distance (Q : Mat2) (hQ : Orthogonal Q) (b p r : Point) :
    euclideanDistance (move Q b p) (move Q b r) = euclideanDistance p r := by
  simpa [move, euclideanDistance, distanceSquared] using
    orthogonal_preserves_distance Q hQ p r

/-- 正交仿射变换是全平面的双射，所以逐点“当且仅当”确实给出整个曲线的对应。 -/
theorem move_bijective (Q : Mat2) (hQ : Orthogonal Q) (b : Point) :
    Function.Bijective (move Q b) := by
  constructor
  · intro p r he
    have hl : Function.LeftInverse (applyMatrix (transpose Q)) (applyMatrix Q) :=
      orthogonal_inverse_left Q hQ
    apply hl.injective
    apply Prod.ext
    · exact add_right_cancel (congrArg Prod.fst he : (applyMatrix Q p).1+b.1 = (applyMatrix Q r).1+b.1)
    · exact add_right_cancel (congrArg Prod.snd he : (applyMatrix Q p).2+b.2 = (applyMatrix Q r).2+b.2)
  · intro y
    obtain ⟨p,hp⟩ := orthogonal_surjective Q hQ (y.1-b.1,y.2-b.2)
    exact ⟨p, by simp [move, hp]⟩

/-- 用全平面的正交仿射变换刻画曲线的全等；正交性保证线性部分可逆。 -/
def RigidCongruent (A B : Sym2) : Prop :=
  ∃ (Q : Mat2) (b : Point), Orthogonal Q ∧
    ∀ p : Point, qForm A p = 1 ↔ qForm B (move Q b p) = 1

private theorem recover_entries {A B : Sym2} (h : symMatrix A = symMatrix B) : A = B := by
  have h₀ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
  have h₁ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  have h₂ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) h
  change A.a = B.a at h₀
  change A.b = B.b at h₁
  change A.c = B.c at h₂
  cases A; cases B
  cases h₀; cases h₁; cases h₂; rfl

private def pack (U : Matrix (Fin 2) (Fin 2) ℝ) : Mat2 :=
  ⟨U 0 0, U 0 1, U 1 0, U 1 1⟩

private theorem unpack (U : Matrix (Fin 2) (Fin 2) ℝ) : matMatrix (pack U) = U := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem pack_orthogonal (U : Matrix (Fin 2) (Fin 2) ℝ)
    (hc : U.transpose * U = 1) (hr : U * U.transpose = 1) : Orthogonal (pack U) := by
  have c (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hc
  have r (i j : Fin 2) := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using c 0 0
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using c 1 1
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two] using c 0 1
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using r 0 0
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two, pow_two] using r 1 1
  · simpa [pack, Matrix.mul_apply, Fin.sum_univ_two] using r 0 1

/-- 同谱的实对称矩阵，其单位等值集由一个全平面的正交变换对应。
这个方向实际上不要求正定。 -/
theorem rigidCongruent_of_sameSpectrum (A B : Sym2) (hs : SameSpectrum A B) :
    RigidCongruent A B := by
  obtain ⟨U, hc, hr, hcon⟩ :=
    EllipseForward.charpoly_eq_implies_orthogonal_similarity (symMatrix B) (symMatrix A)
      (symMatrix_symmetric B) (symMatrix_symmetric A) (Eq.symm hs)
  have he : congruence (pack U) B = A := by
    apply recover_entries
    rw [symMatrix_congruence, unpack]
    exact hcon
  refine ⟨pack U, (0,0), pack_orthogonal U hc hr, ?_⟩
  intro p
  have hp := qForm_congruence (pack U) B p
  rw [he] at hp
  simp [move, hp]

/-- 反向不能删除正定性或固定单位水平的条件。 -/
theorem sameSpectrum_of_rigidCongruent (A B : Sym2)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B) (h : RigidCongruent A B) :
    SameSpectrum A B := by
  obtain ⟨Q, b, hQ, hmap⟩ := h
  exact EllipseCenter.affine_unit_level_implies_charpoly A B Q b hA hB hQ
    (fun p hp => (hmap p).mp hp)

/-- 完整判据，特征值按代数重数计。 -/
theorem rigidCongruent_iff_sameSpectrum (A B : Sym2)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B) :
    RigidCongruent A B ↔ (symMatrix A).charpoly = (symMatrix B).charpoly :=
  ⟨sameSpectrum_of_rigidCongruent A B hA hB, rigidCongruent_of_sameSpectrum A B⟩

end
end SpectralExample.EllipseClassification

#print axioms SpectralExample.EllipseClassification.rigidCongruent_of_sameSpectrum
#print axioms SpectralExample.EllipseClassification.sameSpectrum_of_rigidCongruent
#print axioms SpectralExample.EllipseClassification.rigidCongruent_iff_sameSpectrum

#print axioms SpectralExample.EllipseClassification.move_preserves_distance
#print axioms SpectralExample.EllipseClassification.move_bijective
