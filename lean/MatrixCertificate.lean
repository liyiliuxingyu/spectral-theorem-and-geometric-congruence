import Std

/-! 导读例 0.1 的整数矩阵证书：这一文件只依赖 Lean 自带的标准库。 -/
namespace SpectralExample.IntegerCertificate

structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

def transpose (x : Mat2) : Mat2 := ⟨x.a, x.c, x.b, x.d⟩

def multiply (x y : Mat2) : Mat2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d,
   x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def M : Mat2 := ⟨2, -1, 1, 2⟩
def A : Mat2 := ⟨5, 2, 2, 2⟩
def fiveI : Mat2 := ⟨5, 0, 0, 5⟩
def fiveD : Mat2 := ⟨30, 0, 0, 5⟩

/-- MᵀM = 5I。 -/
theorem transpose_mul : multiply (transpose M) M = fiveI := by decide

/-- MMᵀ = 5I。 -/
theorem mul_transpose : multiply M (transpose M) = fiveI := by decide

/-- Mᵀ(A₀M) = 5D₀。 -/
theorem diagonalizes : multiply (transpose M) (multiply A M) = fiveD := by decide

end SpectralExample.IntegerCertificate

#print axioms SpectralExample.IntegerCertificate.transpose_mul
#print axioms SpectralExample.IntegerCertificate.mul_transpose
#print axioms SpectralExample.IntegerCertificate.diagonalizes
