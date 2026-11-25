import Example21

/-!
例 2.5 的补充：任意三个不共线的平面点都可以用来定位。
这里使用欧氏弦长（直线距离）的平方；不用点积空间的默认乘积度量或弧长。
后一个结论只断言两个保距映射在三个标志点上吻合后必处处吻合，
将三个顶点对应起来的刚体运动的存在性，在讲义中由三边全等说明。
-/
namespace SpectralBook.ChordLandmarks

open SpectralExample.Example21

noncomputable section

/-- 三点是否共线由两条边向量的行列式判定。 -/
def orientedArea2 (o a b : Point) : ℝ :=
  (a.1 - o.1)*(b.2 - o.2) - (a.2 - o.2)*(b.1 - o.1)

private theorem subtract_distances {p q o a : Point}
    (ho : distanceSquared p o = distanceSquared q o)
    (ha : distanceSquared p a = distanceSquared q a) :
    (a.1-o.1)*(p.1-q.1) + (a.2-o.2)*(p.2-q.2) = 0 := by
  unfold distanceSquared at ho ha
  nlinarith only [ho, ha]

/-- 距三个不共线标志点的三个距离相同，推出两个候选点就是同一点。 -/
theorem determined_by_three {o a b p q : Point} (hind : orientedArea2 o a b ≠ 0)
    (ho : distanceSquared p o = distanceSquared q o)
    (ha : distanceSquared p a = distanceSquared q a)
    (hb : distanceSquared p b = distanceSquared q b) : p = q := by
  have hA := subtract_distances ho ha
  have hB := subtract_distances ho hb
  have hx : orientedArea2 o a b * (p.1-q.1) = 0 := by
    calc
      _ = ((a.1-o.1)*(p.1-q.1)+(a.2-o.2)*(p.2-q.2))*(b.2-o.2)
        - ((b.1-o.1)*(p.1-q.1)+(b.2-o.2)*(p.2-q.2))*(a.2-o.2) := by
          unfold orientedArea2; ring
      _ = _ := by rw [hA,hB]; ring
  have hy : orientedArea2 o a b * (p.2-q.2) = 0 := by
    calc
      _ = ((b.1-o.1)*(p.1-q.1)+(b.2-o.2)*(p.2-q.2))*(a.1-o.1)
        - ((a.1-o.1)*(p.1-q.1)+(a.2-o.2)*(p.2-q.2))*(b.1-o.1) := by
          unfold orientedArea2; ring
      _ = _ := by rw [hA,hB]; ring
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hind))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hind))

/-- 两个保弦长的实现，若在三个像不共线的参照点上一致，就在整个定义域上一致。 -/
theorem maps_agree_of_three {S : Type*} (f g : S → Point) (o a b : S)
    (h : ∀ x y, distanceSquared (f x) (f y) = distanceSquared (g x) (g y))
    (ho : f o = g o) (ha : f a = g a) (hb : f b = g b)
    (hind : orientedArea2 (f o) (f a) (f b) ≠ 0) : f = g := by
  funext x
  apply determined_by_three hind
  · simpa only [ho] using h x o
  · simpa only [ha] using h x a
  · simpa only [hb] using h x b

end
end SpectralBook.ChordLandmarks

#print axioms SpectralBook.ChordLandmarks.determined_by_three
#print axioms SpectralBook.ChordLandmarks.maps_agree_of_three
