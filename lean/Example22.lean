import EllipseCongruence

/-! # 例 2.2：不定二次型也能给出全等的等值集
将双曲线的标准坐标 (u,v) 旋转到 (x,y)。显式计算顶点和渐近线的像。
-/
namespace SpectralExample.Hyperbola

noncomputable section

abbrev Point := SpectralExample.Point
def r : ℝ := 1 / Real.sqrt 2
def standard (p : Point) : ℝ := 2*p.1^2 - 2*p.2^2
def original (p : Point) : ℝ := 4*p.1*p.2
def rotate (p : Point) : Point := (r*(p.1-p.2), r*(p.1+p.2))
def unrotate (p : Point) : Point := (r*(p.1+p.2), r*(p.2-p.1))

/-- 矩阵 [[0,2],[2,0]] 的正、负特征方向正是旋转矩阵的两条列方向。 -/
theorem eigenpairs :
    let B : Point → Point := fun p => (2*p.2, 2*p.1)
    B (r,r) = (2*r,2*r) ∧ B (-r,r) = ((-2)*(-r),(-2)*r) := by
  constructor <;> apply Prod.ext <;> dsimp <;> ring

private theorem r_sq : r^2 = 1/2 := by
  unfold r
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private theorem undo (p : Point) : unrotate (rotate p) = p := by
  apply Prod.ext <;> simp only [rotate, unrotate] <;> ring_nf <;> rw [r_sq] <;> ring

private theorem redo (p : Point) : rotate (unrotate p) = p := by
  apply Prod.ext <;> simp only [rotate, unrotate] <;> ring_nf <;> rw [r_sq] <;> ring

theorem standardForm (p : Point) : original (rotate p) = standard p := by
  simp only [original, rotate, standard]
  ring_nf
  rw [r_sq]
  ring

private theorem distance_eq (p q : Point) :
    euclideanDistance (rotate p) (rotate q) = euclideanDistance p q := by
  unfold euclideanDistance
  apply congrArg Real.sqrt
  simp only [distanceSquared, rotate]
  ring_nf
  rw [r_sq]
  ring

/-- 不要求 c 为正；同一个旋转在每个等值集上都给出保距双射。 -/
theorem levelCongruence (c : ℝ) :
    ∃ e : {p : Point // standard p = c} ≃ {p : Point // original p = c},
      (∀ p, (e p).val = rotate p.val) ∧
      ∀ p q, euclideanDistance (e p).val (e q).val = euclideanDistance p.val q.val := by
  let e : {p : Point // standard p = c} ≃ {p : Point // original p = c} :=
    { toFun := fun p => ⟨rotate p.val, (standardForm p.val).trans p.property⟩
      invFun := fun p => ⟨unrotate p.val, by rw [← standardForm, redo]; exact p.property⟩
      left_inv := fun p => Subtype.ext (undo p.val)
      right_inv := fun p => Subtype.ext (redo p.val) }
  exact ⟨e, fun _ => rfl, fun p q => distance_eq p.val q.val⟩

/-- 以到原点的最小距离刻画顶点，而不仅是列出曲线上两个点。 -/
theorem vertices (p : Point) (hp : standard p = 1) :
    1/2 ≤ distanceSquared p (0,0) ∧
      (distanceSquared p (0,0) = 1/2 ↔ p = (r,0) ∨ p = (-r,0)) := by
  change 2*p.1^2 - 2*p.2^2 = 1 at hp
  have hd : distanceSquared p (0,0) = p.1^2 + p.2^2 := by simp [distanceSquared]
  rw [hd]
  refine ⟨by linarith only [hp, sq_nonneg p.2], ?_⟩
  constructor
  · intro h
    have hz : p.2^2 = 0 := by linarith only [hp, h]
    have hy := (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp hz
    have hf : (p.1-r)*(p.1+r)=0 := by
      calc
        _ = p.1^2-r^2 := by ring
        _ = 0 := by linarith only [r_sq, h, hz]
    rcases mul_eq_zero.mp hf with hpos | hneg
    · exact Or.inl (Prod.ext (sub_eq_zero.mp hpos) hy)
    · exact Or.inr (Prod.ext (show p.1 = -r by linarith only [hneg]) hy)
  · rintro (h | h) <;> rw [h] <;> simp [r_sq]

theorem vertexImages :
    standard (r,0) = 1 ∧ standard (-r,0) = 1 ∧
    rotate (r,0) = (1/2,1/2) ∧ rotate (-r,0) = (-1/2,-1/2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · norm_num [standard, r_sq]
  · norm_num [standard, r_sq]
  · apply Prod.ext <;> simp only [rotate] <;> ring_nf <;> rw [r_sq]
  · apply Prod.ext <;> simp only [rotate] <;> ring_nf <;> rw [r_sq] <;> ring

/-- 二次型 4xy 的零等值集是两条坐标轴；
    用点的坐标判断两条直线在换元前后的对应关系。 -/
theorem axesCorrespond (p : Point) :
    ((rotate p).1 = 0 ↔ p.1 = p.2) ∧ ((rotate p).2 = 0 ↔ p.1 = -p.2) := by
  have hr : r ≠ 0 := by intro h; simpa [h] using r_sq
  simp [rotate, hr, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- 沿双曲线向无穷远走，另一坐标的绝对值趋于零。 -/
theorem axesAsymptotic (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ p : Point, original p = 1 →
      (M < |p.1| → |p.2| < ε) ∧ (M < |p.2| → |p.1| < ε) := by
  have hM : 0 < 1/ε := one_div_pos.mpr hε
  refine ⟨1/ε, hM, ?_⟩
  intro p hp
  change 4*p.1*p.2 = 1 at hp
  have hxy : p.1*p.2 = 1/4 := by linarith only [hp]
  have hprod : |p.1| * |p.2| = 1/4 := by rw [← abs_mul, hxy]; norm_num
  have aux (a b : ℝ) (hab : a*b = 1/4) (ha : 1/ε < a) : b < ε := by
    have hlt := (div_lt_iff₀ hε).mp ha
    by_contra hb
    have hmono := mul_le_mul_of_nonneg_left (le_of_not_gt hb) (le_of_lt (lt_trans hM ha))
    linarith only [hmono, hab, hlt]
  exact ⟨aux _ _ hprod, aux _ _ ((mul_comm _ _).trans hprod)⟩

/-- 任一非零横坐标或纵坐标都确实被曲线取到，极限估计并非空真。 -/
theorem unboundedBranches (t : ℝ) (ht : t ≠ 0) :
    original (t, 1/(4*t)) = 1 ∧ original (1/(4*t), t) = 1 := by
  have h4t : (4:ℝ)*t ≠ 0 := mul_ne_zero (by norm_num) ht
  have hx : (4*t)*(1/(4*t))=1 := by
    rw [one_div, mul_inv_cancel₀ h4t]
  refine ⟨hx, ?_⟩
  change 4*(1/(4*t))*t = 1
  calc
    _ = (4*t)*(1/(4*t)) := by ring
    _ = 1 := hx


end
end SpectralExample.Hyperbola

#print axioms SpectralExample.Hyperbola.standardForm
#print axioms SpectralExample.Hyperbola.levelCongruence
#print axioms SpectralExample.Hyperbola.vertices
#print axioms SpectralExample.Hyperbola.vertexImages
#print axioms SpectralExample.Hyperbola.axesCorrespond

#print axioms SpectralExample.Hyperbola.axesAsymptotic
#print axioms SpectralExample.Hyperbola.unboundedBranches

#print axioms SpectralExample.Hyperbola.eigenpairs
