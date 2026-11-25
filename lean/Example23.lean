import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# 例 2.3：重特征值的实三维椭球

Vec3 用三个任意实数坐标表示；这里的长度明确是欧氏长度。
B 是 I + wwᵀ，其中 w=(1,1,1)。所有恒等式均在 ℝ 上核验。
不把三个抽查向量的计算代替整个特征空间的刻画。
-/
namespace SpectralExample.Example23

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ := p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2
def scale (t : ℝ) (p : Vec3) : Vec3 := (t * p.1, t * p.2.1, t * p.2.2)
def sumCoordinates (p : Vec3) : ℝ := p.1 + p.2.1 + p.2.2
def normSquared (p : Vec3) : ℝ := dot p p
def radius (p : Vec3) : ℝ := Real.sqrt (normSquared p)
def distanceSquared (p q : Vec3) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

def B (p : Vec3) : Vec3 :=
  (2 * p.1 + p.2.1 + p.2.2,
   p.1 + 2 * p.2.1 + p.2.2,
   p.1 + p.2.1 + 2 * p.2.2)

def qB (p : Vec3) : ℝ := dot p (B p)
def qD (p : Vec3) : ℝ := 4 * p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

def r3 : ℝ := 1 / Real.sqrt 3
def r2 : ℝ := 1 / Real.sqrt 2
def r6 : ℝ := 1 / Real.sqrt 6

def v1 : Vec3 := (r3, r3, r3)
def v2 : Vec3 := (r2, -r2, 0)
def v3 : Vec3 := (r6, r6, -2 * r6)

/-- 以 v1、v2、v3 为三列的实坐标变换。 -/
def fromCoordinates (p : Vec3) : Vec3 :=
  (r3 * p.1 + r2 * p.2.1 + r6 * p.2.2,
   r3 * p.1 - r2 * p.2.1 + r6 * p.2.2,
   r3 * p.1 - 2 * r6 * p.2.2)

/-- 同一个正交矩阵的转置：与三个单位方向作内积。 -/
def coordinates (p : Vec3) : Vec3 :=
  (r3 * (p.1 + p.2.1 + p.2.2),
   r2 * (p.1 - p.2.1),
   r6 * (p.1 + p.2.1 - 2 * p.2.2))

private theorem vec_ext {p q : Vec3}
    (hx : p.1 = q.1) (hy : p.2.1 = q.2.1) (hz : p.2.2 = q.2.2) : p = q :=
  Prod.ext hx (Prod.ext hy hz)

theorem r3_sq : r3 ^ 2 = 1 / 3 := by
  unfold r3
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem r2_sq : r2 ^ 2 = 1 / 2 := by
  unfold r2
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem r6_sq : r6 ^ 2 = 1 / 6 := by
  unfold r6
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

/-- B 确实是把 p 加上 (wᵀp)w；这将定义与 I+wwᵀ 接起来。 -/
theorem B_identity_rank_one (p : Vec3) :
    B p =
      (p.1 + sumCoordinates p, p.2.1 + sumCoordinates p, p.2.2 + sumCoordinates p) := by
  apply vec_ext <;> simp only [B, sumCoordinates] <;> ring

theorem quadratic_rank_one (p : Vec3) :
    qB p = normSquared p + (sumCoordinates p) ^ 2 := by
  simp only [qB, B, normSquared, dot, sumCoordinates]
  ring

/-- 特征值4的特征空间恰为直线 {(t,t,t):t∈ℝ}，包括零向量。 -/
theorem eigenspace_four (p : Vec3) :
    B p = scale 4 p ↔ ∃ t : ℝ, p = (t, t, t) := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg (fun q : Vec3 => q.2.1) h
    have hz := congrArg (fun q : Vec3 => q.2.2) h
    change 2 * p.1 + p.2.1 + p.2.2 = 4 * p.1 at hx
    change p.1 + 2 * p.2.1 + p.2.2 = 4 * p.2.1 at hy
    change p.1 + p.2.1 + 2 * p.2.2 = 4 * p.2.2 at hz
    refine ⟨p.1, vec_ext rfl ?_ ?_⟩
    · linarith only [hx, hy]
    · linarith only [hx, hz]
  · rintro ⟨t, h⟩
    rw [h]
    apply vec_ext <;> simp only [B, scale] <;> ring

/-- 特征值1的特征空间恰为与 w 垂直的平面 x+y+z=0。 -/
theorem eigenspace_one (p : Vec3) :
    B p = p ↔ sumCoordinates p = 0 := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    change 2 * p.1 + p.2.1 + p.2.2 = p.1 at hx
    unfold sumCoordinates
    linarith only [hx]
  · intro h
    rw [B_identity_rank_one]
    apply vec_ext <;> simp only [h, add_zero]

theorem eigenvectors :
    B v1 = scale 4 v1 ∧ B v2 = v2 ∧ B v3 = v3 := by
  refine ⟨?_, ?_, ?_⟩
  · apply vec_ext <;> simp only [B, scale, v1] <;> ring
  · apply vec_ext <;> simp only [B, v2] <;> ring
  · apply vec_ext <;> simp only [B, v3] <;> ring

/-- 三列互相正交而且均为单位向量；未作特征值相异的错误假设。 -/
theorem orthonormal_columns :
    dot v1 v1 = 1 ∧ dot v2 v2 = 1 ∧ dot v3 v3 = 1 ∧
    dot v1 v2 = 0 ∧ dot v1 v3 = 0 ∧ dot v2 v3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ = 3 * r3 ^ 2 := by simp only [dot, v1]; ring
      _ = 1 := by rw [r3_sq]; norm_num
  · calc
      _ = 2 * r2 ^ 2 := by simp only [dot, v2]; ring
      _ = 1 := by rw [r2_sq]; norm_num
  · calc
      _ = 6 * r6 ^ 2 := by simp only [dot, v3]; ring
      _ = 1 := by rw [r6_sq]; norm_num
  · simp only [dot, v1, v2]; ring
  · simp only [dot, v1, v3]; ring
  · simp only [dot, v2, v3]; ring

/-- 坐标变换的一侧逆恒等式，对任意实三维坐标成立。 -/
theorem coordinates_fromCoordinates (p : Vec3) :
    coordinates (fromCoordinates p) = p := by
  apply vec_ext
  · calc
      _ = (3 * r3 ^ 2) * p.1 := by simp only [coordinates, fromCoordinates]; ring
      _ = p.1 := by rw [r3_sq]; ring
  · calc
      _ = (2 * r2 ^ 2) * p.2.1 := by simp only [coordinates, fromCoordinates]; ring
      _ = p.2.1 := by rw [r2_sq]; ring
  · calc
      _ = (6 * r6 ^ 2) * p.2.2 := by simp only [coordinates, fromCoordinates]; ring
      _ = p.2.2 := by rw [r6_sq]; ring

/-- 另一侧逆恒等式，排除了只嵌入真子空间的可能。 -/
theorem fromCoordinates_coordinates (p : Vec3) :
    fromCoordinates (coordinates p) = p := by
  apply vec_ext
  · calc
      _ = r3 ^ 2 * (p.1 + p.2.1 + p.2.2) +
          r2 ^ 2 * (p.1 - p.2.1) + r6 ^ 2 * (p.1 + p.2.1 - 2 * p.2.2) := by
            simp only [coordinates, fromCoordinates]; ring
      _ = p.1 := by rw [r3_sq, r2_sq, r6_sq]; ring
  · calc
      _ = r3 ^ 2 * (p.1 + p.2.1 + p.2.2) -
          r2 ^ 2 * (p.1 - p.2.1) + r6 ^ 2 * (p.1 + p.2.1 - 2 * p.2.2) := by
            simp only [coordinates, fromCoordinates]; ring
      _ = p.2.1 := by rw [r3_sq, r2_sq, r6_sq]; ring
  · calc
      _ = r3 ^ 2 * (p.1 + p.2.1 + p.2.2) -
          2 * r6 ^ 2 * (p.1 + p.2.1 - 2 * p.2.2) := by
            simp only [coordinates, fromCoordinates]; ring
      _ = p.2.2 := by rw [r3_sq, r6_sq]; ring

theorem normSquared_fromCoordinates (p : Vec3) :
    normSquared (fromCoordinates p) = normSquared p := by
  calc
    _ = (3 * r3 ^ 2) * p.1 ^ 2 + (2 * r2 ^ 2) * p.2.1 ^ 2 +
        (6 * r6 ^ 2) * p.2.2 ^ 2 := by
          simp only [normSquared, dot, fromCoordinates]; ring
    _ = normSquared p := by
      rw [r3_sq, r2_sq, r6_sq]
      simp only [normSquared, dot]
      ring

/-- 任意两点的欧氏距离平方均保持，不依赖对若干点的抽查。 -/
theorem distanceSquared_fromCoordinates (p q : Vec3) :
    distanceSquared (fromCoordinates p) (fromCoordinates q) = distanceSquared p q := by
  calc
    _ = (3 * r3 ^ 2) * (p.1 - q.1) ^ 2 +
        (2 * r2 ^ 2) * (p.2.1 - q.2.1) ^ 2 +
        (6 * r6 ^ 2) * (p.2.2 - q.2.2) ^ 2 := by
          simp only [distanceSquared, fromCoordinates]; ring
    _ = distanceSquared p q := by
      rw [r3_sq, r2_sq, r6_sq]
      simp only [distanceSquared]
      ring

/-- 整个三维二次型的对角式，而非只在三个基向量上抽查。 -/
theorem diagonal_quadratic (p : Vec3) :
    qB (fromCoordinates p) = qD p := by
  calc
    _ = (12 * r3 ^ 2) * p.1 ^ 2 + (2 * r2 ^ 2) * p.2.1 ^ 2 +
        (6 * r6 ^ 2) * p.2.2 ^ 2 := by
          simp only [qB, dot, B, fromCoordinates]; ring
    _ = qD p := by
      rw [r3_sq, r2_sq, r6_sq]
      simp only [qD]
      ring

/-- 特征值1所在平面上的二次型恰是欧氏长度平方。 -/
theorem central_plane_form (p : Vec3) (hp : sumCoordinates p = 0) :
    qB p = normSquared p := by
  rw [quadratic_rank_one, hp]
  norm_num

/-- 在二维特征平面中，整个中央截面是单位圆，而非两条指定方向。 -/
theorem central_circle (s t : ℝ) :
    qB (fromCoordinates (0, s, t)) = s ^ 2 + t ^ 2 := by
  rw [diagonal_quadratic]
  simp only [qD, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add]

theorem form_on_axes (t : ℝ) :
    qB (scale t v1) = 4 * t ^ 2 ∧
    qB (scale t v2) = t ^ 2 ∧
    qB (scale t v3) = t ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = 12 * r3 ^ 2 * t ^ 2 := by simp only [qB, dot, B, scale, v1]; ring
      _ = 4 * t ^ 2 := by rw [r3_sq]; ring
  · calc
      _ = 2 * r2 ^ 2 * t ^ 2 := by simp only [qB, dot, B, scale, v2]; ring
      _ = t ^ 2 := by rw [r2_sq]; ring
  · calc
      _ = 6 * r6 ^ 2 * t ^ 2 := by simp only [qB, dot, B, scale, v3]; ring
      _ = t ^ 2 := by rw [r6_sq]; ring

private theorem square_one_roots (t : ℝ) :
    t ^ 2 = 1 ↔ t = 1 ∨ t = -1 := by
  constructor
  · intro h
    have hp : (t - 1) * (t + 1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hp with hpos | hneg
    · exact Or.inl (by linarith only [hpos])
    · exact Or.inr (by linarith only [hneg])
  · rintro (rfl | rfl) <;> norm_num

/-- 三条单位特征方向与椭球的全部交点参数。 -/
theorem axis_intersections (t : ℝ) :
    (qB (scale t v1) = 1 ↔ t = 1 / 2 ∨ t = -1 / 2) ∧
    (qB (scale t v2) = 1 ↔ t = 1 ∨ t = -1) ∧
    (qB (scale t v3) = 1 ↔ t = 1 ∨ t = -1) := by
  rw [(form_on_axes t).1, (form_on_axes t).2.1, (form_on_axes t).2.2]
  refine ⟨?_, square_one_roots t, square_one_roots t⟩
  constructor
  · intro h
    have hp : (t - 1 / 2) * (t + 1 / 2) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hp with hpos | hneg
    · exact Or.inl (by linarith only [hpos])
    · exact Or.inr (by linarith only [hneg])
  · rintro (rfl | rfl) <;> norm_num

theorem normSquared_scale (t : ℝ) (p : Vec3) :
    normSquared (scale t p) = t ^ 2 * normSquared p := by
  simp only [normSquared, dot, scale]
  ring

/-- 因为方向已经归一化，参数的绝对值正是实际欧氏长度。 -/
theorem radius_unit_scale (t : ℝ) (p : Vec3) (hp : normSquared p = 1) :
    radius (scale t p) = |t| := by
  unfold radius
  rw [normSquared_scale, hp, mul_one]
  exact Real.sqrt_sq_eq_abs t

/-- 半轴长度是实际欧氏长度 1/2、1、1，不只是方程系数的倒数。 -/
theorem semiaxis_lengths :
    radius (scale (1 / 2) v1) = 1 / 2 ∧
    radius (scale 1 v2) = 1 ∧ radius (scale 1 v3) = 1 := by
  have h1 : normSquared v1 = 1 := orthonormal_columns.1
  have h2 : normSquared v2 = 1 := orthonormal_columns.2.1
  have h3 : normSquared v3 = 1 := orthonormal_columns.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [radius_unit_scale (1 / 2) v1 h1]
    norm_num
  · rw [radius_unit_scale 1 v2 h2]
    norm_num
  · rw [radius_unit_scale 1 v3 h3]
    norm_num

end
end SpectralExample.Example23

#print axioms SpectralExample.Example23.B_identity_rank_one
#print axioms SpectralExample.Example23.quadratic_rank_one
#print axioms SpectralExample.Example23.eigenspace_four
#print axioms SpectralExample.Example23.eigenspace_one
#print axioms SpectralExample.Example23.eigenvectors
#print axioms SpectralExample.Example23.orthonormal_columns
#print axioms SpectralExample.Example23.coordinates_fromCoordinates
#print axioms SpectralExample.Example23.fromCoordinates_coordinates
#print axioms SpectralExample.Example23.normSquared_fromCoordinates
#print axioms SpectralExample.Example23.distanceSquared_fromCoordinates
#print axioms SpectralExample.Example23.diagonal_quadratic
#print axioms SpectralExample.Example23.central_plane_form
#print axioms SpectralExample.Example23.central_circle
#print axioms SpectralExample.Example23.form_on_axes
#print axioms SpectralExample.Example23.axis_intersections
#print axioms SpectralExample.Example23.semiaxis_lengths
