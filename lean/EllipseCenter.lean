import Example25
import Mathlib.Tactic.FieldSimp

/-!
# 例 2.5：全等变换中的平移必须为零

这里直接使用正定二次型，不把“有界中心对称集合中心唯一”作为额外前提。
事实上，只需线性部分满射，并且仿射映射把源单位等值集映入目标单位等值集。

反证偏移 b 非零。取 Qv=b，并令 t=1/√qA(v)>0。
源等值集上的两个点 ±tv 映到 (1±t)b。二次齐次性给出
(1+t)² qB(b)=1=(1-t)² qB(b)，相减得到 t qB(b)=0，
与 t>0、qB(b)>0 矛盾。所有平方根和向量都在实数上。
-/

namespace SpectralExample.EllipseCenter

open SpectralExample.Example25

noncomputable section

private theorem qForm_scale (A : Sym2) (s : ℝ) (v : Point) :
    qForm A (s * v.1, s * v.2) = s ^ 2 * qForm A v := by
  simp only [qForm]
  ring

private theorem applyMatrix_scale (Q : Mat2) (s : ℝ) (v : Point) :
    applyMatrix Q (s * v.1, s * v.2) =
      (s * (applyMatrix Q v).1, s * (applyMatrix Q v).2) := by
  apply Prod.ext <;> simp only [applyMatrix] <;> ring

private theorem shifted_image (Q : Mat2) (b v : Point)
    (hv : applyMatrix Q v = b) (s : ℝ) :
    ((applyMatrix Q (s * v.1, s * v.2)).1 + b.1,
     (applyMatrix Q (s * v.1, s * v.2)).2 + b.2) =
      ((s + 1) * b.1, (s + 1) * b.2) := by
  rw [applyMatrix_scale, hv]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> ring

/-- 满射线性部分与两个正定单位等值集已足以排除非零平移。 -/
theorem surjective_affine_unit_level_forces_zero_offset
    (A B : Sym2) (Q : Mat2) (b : Point)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B)
    (hQ : Function.Surjective (applyMatrix Q))
    (hmap : ∀ p : Point, qForm A p = 1 →
      qForm B ((applyMatrix Q p).1 + b.1, (applyMatrix Q p).2 + b.2) = 1) :
    b = (0, 0) := by
  by_contra hb
  obtain ⟨v, hv⟩ := hQ b
  have hv0 : v ≠ (0, 0) := by
    intro hz
    apply hb
    rw [← hv, hz]
    simp [applyMatrix]
  have ha : 0 < qForm A v := hA v hv0
  let t : ℝ := 1 / Real.sqrt (qForm A v)
  have ht : 0 < t := by
    exact one_div_pos.mpr (Real.sqrt_pos.mpr ha)
  have hunit : t ^ 2 * qForm A v = 1 := by
    dsimp [t]
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt ha)]
    field_simp [ne_of_gt ha]
  have hplus : qForm A (t * v.1, t * v.2) = 1 := by
    rw [qForm_scale, hunit]
  have hminus : qForm A ((-t) * v.1, (-t) * v.2) = 1 := by
    rw [qForm_scale, neg_sq, hunit]
  have hplus_image := hmap (t * v.1, t * v.2) hplus
  have hminus_image := hmap ((-t) * v.1, (-t) * v.2) hminus
  rw [shifted_image Q b v hv t, qForm_scale] at hplus_image
  rw [shifted_image Q b v hv (-t), qForm_scale] at hminus_image
  have hzero : t * qForm B b = 0 := by
    nlinarith only [hplus_image, hminus_image]
  exact (ne_of_gt (mul_pos ht (hB b hb))) hzero

/-- 正交矩阵是满射，故欧氏刚体变换的平移部分必须为零。 -/
theorem affine_unit_level_forces_zero_offset
    (A B : Sym2) (Q : Mat2) (b : Point)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B) (hQ : Orthogonal Q)
    (hmap : ∀ p : Point, qForm A p = 1 →
      qForm B ((applyMatrix Q p).1 + b.1, (applyMatrix Q p).2 + b.2) = 1) :
    b = (0, 0) :=
  surjective_affine_unit_level_forces_zero_offset A B Q b hA hB
    (orthogonal_surjective Q hQ) hmap

/-- 消去平移后，单位等值集的对应决定整个二次型。 -/
theorem affine_unit_level_determines_form
    (A B : Sym2) (Q : Mat2) (b : Point)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B) (hQ : Orthogonal Q)
    (hmap : ∀ p : Point, qForm A p = 1 →
      qForm B ((applyMatrix Q p).1 + b.1, (applyMatrix Q p).2 + b.2) = 1) :
    b = (0, 0) ∧ ∀ p : Point, qForm B (applyMatrix Q p) = qForm A p := by
  have hb := affine_unit_level_forces_zero_offset A B Q b hA hB hQ hmap
  refine ⟨hb, unit_level_determines_form A B Q hA ?_⟩
  intro p hp
  simpa only [hb, Prod.fst, Prod.snd, add_zero] using hmap p hp

/-- 完整反向结论：允许平移的刚体对应也强迫真实特征多项式相同。 -/
theorem affine_unit_level_implies_charpoly
    (A B : Sym2) (Q : Mat2) (b : Point)
    (hA : PositiveDefinite A) (hB : PositiveDefinite B) (hQ : Orthogonal Q)
    (hmap : ∀ p : Point, qForm A p = 1 →
      qForm B ((applyMatrix Q p).1 + b.1, (applyMatrix Q p).2 + b.2) = 1) :
    (symMatrix A).charpoly = (symMatrix B).charpoly := by
  have hform := (affine_unit_level_determines_form A B Q b hA hB hQ hmap).2
  apply unit_level_implies_charpoly A B Q hA hQ
  intro p hp
  rw [hform p, hp]

end
end SpectralExample.EllipseCenter

#print axioms SpectralExample.EllipseCenter.surjective_affine_unit_level_forces_zero_offset
#print axioms SpectralExample.EllipseCenter.affine_unit_level_forces_zero_offset
#print axioms SpectralExample.EllipseCenter.affine_unit_level_determines_form
#print axioms SpectralExample.EllipseCenter.affine_unit_level_implies_charpoly
