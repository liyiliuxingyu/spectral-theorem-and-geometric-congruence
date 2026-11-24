import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 导读例 0.1：两条实椭圆全等

平面用实数对表示。距离显式定义为通常的欧氏距离，
不调用积空间的默认度量。Q₀ 将标准椭圆送到斜椭圆。
-/
namespace SpectralExample

noncomputable section

abbrev Point := ℝ × ℝ

/-- 斜椭圆的二次型。 -/
def qA (p : Point) : ℝ := 5 * p.1 ^ 2 + 4 * p.1 * p.2 + 2 * p.2 ^ 2

/-- 标准椭圆的二次型。 -/
def qD (p : Point) : ℝ := 6 * p.1 ^ 2 + p.2 ^ 2

/-- 欧氏距离平方；和两个坐标差分别平方。 -/
def distanceSquared (p q : Point) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- 两个点之间的欧氏距离。 -/
def euclideanDistance (p q : Point) : ℝ := Real.sqrt (distanceSquared p q)

/-- 先把归一化系数单列，方便把环恒等式与平方根分开验证。 -/
def forward (r : ℝ) (p : Point) : Point :=
  (r * (2 * p.1 - p.2), r * (p.1 + 2 * p.2))

/-- 转置矩阵给出的反向候选。 -/
def backward (r : ℝ) (p : Point) : Point :=
  (r * (2 * p.1 + p.2), r * (-p.1 + 2 * p.2))

private theorem scale (r : ℝ) (hr : r ^ 2 = 1 / 5) (t : ℝ) :
    (5 * r ^ 2) * t = t := by
  rw [hr]
  ring

/-- 后做转置，恢复两个坐标。 -/
theorem backward_forward (r : ℝ) (hr : r ^ 2 = 1 / 5) (p : Point) :
    backward r (forward r p) = p := by
  apply Prod.ext
  · change r * (2 * (r * (2 * p.1 - p.2)) + r * (p.1 + 2 * p.2)) = p.1
    calc
      _ = (5 * r ^ 2) * p.1 := by ring
      _ = _ := scale r hr _
  · change r * (-(r * (2 * p.1 - p.2)) + 2 * (r * (p.1 + 2 * p.2))) = p.2
    calc
      _ = (5 * r ^ 2) * p.2 := by ring
      _ = _ := scale r hr _

/-- 另一顺序同样恢复坐标，保证满射性。 -/
theorem forward_backward (r : ℝ) (hr : r ^ 2 = 1 / 5) (p : Point) :
    forward r (backward r p) = p := by
  apply Prod.ext
  · change r * (2 * (r * (2 * p.1 + p.2)) - r * (-p.1 + 2 * p.2)) = p.1
    calc
      _ = (5 * r ^ 2) * p.1 := by ring
      _ = _ := scale r hr _
  · change r * (r * (2 * p.1 + p.2) + 2 * (r * (-p.1 + 2 * p.2))) = p.2
    calc
      _ = (5 * r ^ 2) * p.2 := by ring
      _ = _ := scale r hr _

/-- 展开即为矩阵等式 Q₀ᵀ A₀ Q₀ = D₀ 的二次型版本。 -/
theorem qA_forward (r : ℝ) (hr : r ^ 2 = 1 / 5) (p : Point) :
    qA (forward r p) = qD p := by
  calc
    _ = (5 * r ^ 2) * qD p := by simp only [qA, qD, forward]; ring
    _ = _ := scale r hr _

/-- 正交性确保对任意两个点保距，先算平方。 -/
theorem distanceSquared_forward (r : ℝ) (hr : r ^ 2 = 1 / 5)
    (p q : Point) :
    distanceSquared (forward r p) (forward r q) = distanceSquared p q := by
  calc
    _ = (5 * r ^ 2) * distanceSquared p q := by
      simp only [distanceSquared, forward]
      ring
    _ = _ := scale r hr _

/-- 讲义所用的实归一化系数。 -/
def normalization : ℝ := 1 / Real.sqrt 5

theorem normalization_sq : normalization ^ 2 = 1 / 5 := by
  unfold normalization
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- 用任意共同等值常数定义两条曲线；讲义中取 1。 -/
def StandardLevel (c : ℝ) := { p : Point // qD p = c }
def OriginalLevel (c : ℝ) := { p : Point // qA p = c }

/-- 双射：逆方向先用转置恢复点，再检查它也落在正确的等值集。 -/
def levelEquiv (c : ℝ) : StandardLevel c ≃ OriginalLevel c where
  toFun p := ⟨forward normalization p.val, by
    rw [qA_forward normalization normalization_sq, p.property]⟩
  invFun p := ⟨backward normalization p.val, by
    calc
      qD (backward normalization p.val) =
          qA (forward normalization (backward normalization p.val)) :=
        (qA_forward normalization normalization_sq _).symm
      _ = qA p.val := by rw [forward_backward normalization normalization_sq]
      _ = c := p.property⟩
  left_inv p := by
    apply Subtype.ext
    exact backward_forward normalization normalization_sq p.val
  right_inv p := by
    apply Subtype.ext
    exact forward_backward normalization normalization_sq p.val

/-- 两个像的真实欧氏距离与原距离相同。 -/
theorem levelEquiv_preserves_distance (c : ℝ) (p q : StandardLevel c) :
    euclideanDistance (levelEquiv c p).val (levelEquiv c q).val =
      euclideanDistance p.val q.val := by
  change Real.sqrt
      (distanceSquared (forward normalization p.val) (forward normalization q.val)) =
    Real.sqrt (distanceSquared p.val q.val)
  rw [distanceSquared_forward normalization normalization_sq]

/-- 例 0.1 的结论：整条实椭圆之间存在保持欧氏距离的双射。 -/
theorem example01 :
    ∃ e : StandardLevel 1 ≃ OriginalLevel 1,
      ∀ p q, euclideanDistance (e p).val (e q).val = euclideanDistance p.val q.val :=
  ⟨levelEquiv 1, levelEquiv_preserves_distance 1⟩

/-- 标准椭圆的两端点及其显式像，用于对照讲义例 0.1。 -/
theorem longAxisEndpoints :
    qD (0, 1) = 1 ∧ qD (0, -1) = 1 ∧
    forward normalization (0, 1) = (-normalization, 2 * normalization) ∧
    forward normalization (0, -1) = (normalization, -2 * normalization) := by
  refine ⟨by norm_num [qD], by norm_num [qD], ?_, ?_⟩
  · apply Prod.ext <;> simp only [forward] <;> ring
  · apply Prod.ext <;> simp only [forward] <;> ring

/-- 标准椭圆到原点的最大半径为 1，达到该值的恰为一对长轴端点。 -/
theorem standardAxisExtrema (p : StandardLevel 1) :
    distanceSquared p.val (0, 0) ≤ 1 ∧
    (distanceSquared p.val (0, 0) = 1 ↔ p.val = (0, 1) ∨ p.val = (0, -1)) := by
  have hq := p.property
  change 6 * p.val.1 ^ 2 + p.val.2 ^ 2 = 1 at hq
  have hrad : distanceSquared p.val (0, 0) = p.val.1 ^ 2 + p.val.2 ^ 2 := by
    simp [distanceSquared]
  rw [hrad]
  constructor
  · linarith only [hq, sq_nonneg p.val.1]
  · constructor
    · intro h
      have hx2 : p.val.1 ^ 2 = 0 := by linarith only [hq, h]
      have hx : p.val.1 = 0 := (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).1 hx2
      have hy2 : p.val.2 ^ 2 = 1 := by linarith only [hq, hx2]
      have hy : (p.val.2 - 1) * (p.val.2 + 1) = 0 := by
        calc
          _ = p.val.2 ^ 2 - 1 := by ring
          _ = 0 := sub_eq_zero.mpr hy2
      rcases mul_eq_zero.mp hy with hp | hn
      · exact Or.inl (Prod.ext hx (sub_eq_zero.mp hp))
      · refine Or.inr (Prod.ext hx ?_)
        change p.val.2 = -1
        linarith only [hn]
    · rintro (h | h) <;> rw [h] <;> norm_num

/-- 斜椭圆上两个对应长轴端点的欧氏距离为 2。 -/
theorem originalLongAxisLength :
    euclideanDistance (forward normalization (0, 1)) (forward normalization (0, -1)) = 2 := by
  have hs : distanceSquared (0, 1) (0, -1) = (2 : ℝ)^2 := by
    norm_num [distanceSquared]
  unfold euclideanDistance
  rw [distanceSquared_forward normalization normalization_sq, hs]
  exact Real.sqrt_sq (by norm_num)

/-- 短半轴的归一化系数平方。 -/
theorem shortNormalization_sq : (1 / Real.sqrt (6 : ℝ)) ^ 2 = 1 / 6 := by
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

/-- 标准椭圆到原点的最小距离平方为 1/6，恰在一对短轴端点取得。 -/
theorem standardShortAxisExtrema (p : StandardLevel 1) :
    (1 : ℝ) / 6 ≤ distanceSquared p.val (0, 0) ∧
    (distanceSquared p.val (0, 0) = 1 / 6 ↔
      p.val = (1 / Real.sqrt 6, 0) ∨ p.val = (-1 / Real.sqrt 6, 0)) := by
  have hq := p.property
  change 6 * p.val.1 ^ 2 + p.val.2 ^ 2 = 1 at hq
  have hrad : distanceSquared p.val (0, 0) = p.val.1 ^ 2 + p.val.2 ^ 2 := by
    simp [distanceSquared]
  rw [hrad]
  constructor
  · linarith only [hq, sq_nonneg p.val.2]
  · constructor
    · intro h
      have hy2 : p.val.2 ^ 2 = 0 := by linarith only [hq, h]
      have hy : p.val.2 = 0 :=
        (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).1 hy2
      have hx2 : p.val.1 ^ 2 = 1 / 6 := by linarith only [h, hy2]
      have hfactor :
          (p.val.1 - 1 / Real.sqrt 6) * (p.val.1 + 1 / Real.sqrt 6) = 0 := by
        calc
          _ = p.val.1 ^ 2 - (1 / Real.sqrt 6) ^ 2 := by ring
          _ = 0 := by rw [hx2, shortNormalization_sq]; ring
      rcases mul_eq_zero.mp hfactor with hp | hn
      · exact Or.inl (Prod.ext (sub_eq_zero.mp hp) hy)
      · refine Or.inr (Prod.ext ?_ hy)
        change p.val.1 = -1 / Real.sqrt 6
        calc
          _ = -(1 / Real.sqrt (6 : ℝ)) := by linarith only [hn]
          _ = -1 / Real.sqrt 6 := by ring
    · rintro (h | h)
      · rw [h]
        simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
        exact shortNormalization_sq
      · rw [h]
        calc
          _ = (1 / Real.sqrt (6 : ℝ)) ^ 2 := by ring
          _ = 1 / 6 := shortNormalization_sq

/-- 两个短轴端点在标准椭圆上，其像正是 ±(2,1)/√30。 -/
theorem shortAxisEndpoints :
    qD (1 / Real.sqrt 6, 0) = 1 ∧ qD (-1 / Real.sqrt 6, 0) = 1 ∧
    forward normalization (1 / Real.sqrt 6, 0) =
      (2 / Real.sqrt 30, 1 / Real.sqrt 30) ∧
    forward normalization (-1 / Real.sqrt 6, 0) =
      (-2 / Real.sqrt 30, -1 / Real.sqrt 30) := by
  have hroot : Real.sqrt (5 : ℝ) * Real.sqrt 6 = Real.sqrt 30 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5) 6]
    norm_num
  have hcoef : normalization / Real.sqrt 6 = 1 / Real.sqrt 30 := by
    unfold normalization
    rw [div_div, hroot]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [qD, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    rw [shortNormalization_sq]
    norm_num
  · calc
      _ = 6 * (1 / Real.sqrt (6 : ℝ)) ^ 2 := by simp only [qD]; ring
      _ = 1 := by rw [shortNormalization_sq]; norm_num
  · apply Prod.ext
    · calc
        _ = 2 * (normalization / Real.sqrt 6) := by simp only [forward]; ring
        _ = 2 / Real.sqrt 30 := by rw [hcoef]; ring
    · calc
        _ = normalization / Real.sqrt 6 := by simp only [forward]; ring
        _ = 1 / Real.sqrt 30 := hcoef
  · apply Prod.ext
    · calc
        _ = -2 * (normalization / Real.sqrt 6) := by simp only [forward]; ring
        _ = -2 / Real.sqrt 30 := by rw [hcoef]; ring
    · calc
        _ = -(normalization / Real.sqrt 6) := by simp only [forward]; ring
        _ = -1 / Real.sqrt 30 := by rw [hcoef]; ring

/-- 斜椭圆上短轴两端点间的欧氏距离为 2/√6。 -/
theorem originalShortAxisLength :
    euclideanDistance (2 / Real.sqrt 30, 1 / Real.sqrt 30)
      (-2 / Real.sqrt 30, -1 / Real.sqrt 30) = 2 / Real.sqrt 6 := by
  have hp := shortAxisEndpoints.2.2.1
  have hn := shortAxisEndpoints.2.2.2
  rw [← hp, ← hn]
  have hs :
      distanceSquared (1 / Real.sqrt 6, 0) (-1 / Real.sqrt 6, 0) =
        (2 / Real.sqrt (6 : ℝ)) ^ 2 := by
    simp only [distanceSquared]
    ring
  unfold euclideanDistance
  rw [distanceSquared_forward normalization normalization_sq, hs]
  exact Real.sqrt_sq (div_nonneg (by norm_num) (Real.sqrt_nonneg 6))

end

end SpectralExample

#print axioms SpectralExample.example01

#print axioms SpectralExample.longAxisEndpoints

#print axioms SpectralExample.standardAxisExtrema

#print axioms SpectralExample.originalLongAxisLength

#print axioms SpectralExample.shortNormalization_sq

#print axioms SpectralExample.standardShortAxisExtrema

#print axioms SpectralExample.shortAxisEndpoints

#print axioms SpectralExample.originalShortAxisLength
