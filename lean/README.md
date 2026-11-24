# 复验讲义中的 Lean 证明

使用 Lean 4.19.0、Lake 和与本目录锁文件匹配的 Mathlib。从工程根目录进入 `lean/` 后运行：

```sh
lean --version
lake exe cache get Mathlib.LinearAlgebra.Matrix.Spectrum Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan Mathlib.Data.Real.Sqrt Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Tactic.Ring Mathlib.Tactic.NormNum Mathlib.Tactic.Linarith
python3 check.py
```

首次使用需安装 Elan 或同版本 Lean 与 Lake，并能取得锁定仓库及 Mathlib 编译缓存。不要用 `lake update` 随意刷新依赖。已准备好配套依赖时，可直接运行最后一条命令。若已有本地编译器及完整、同版本的模块目录，也可执行：

```sh
LEAN_PATH=/path/to/matching/objects python3 check.py --lean /path/to/lean
```

脚本从本包的源文件重新产生临时 `.olean`，不会用旧版本的同名本地证明替代源码；检查结束后删除这些临时文件。运行中如遇 Lean 出错、警告、缺失目标、意外公理或 `sorryAx`，脚本返回非零。当前检查目标的名称固定在 [check.py](check.py) 中。只核验整数矩阵证书可运行 `python3 check.py --certificate-only`（不需要 Mathlib）。只核验下面的有限和推导可运行 `python3 check.py --coordinates-only`（需要 Mathlib，但该文件不导入矩阵谱定理）。

| 对照讲义 | 源文件及其职责 |
|---|---|
| 导读例 0.1 | [整数矩阵证书](MatrixCertificate.lean)核对三个矩阵恒等式；[椭圆全等](EllipseCongruence.lean)核对真实欧氏保距双射、长短轴端点的极值刻画、坐标像及两条轴的长度。 |
| 导读例 0.1 的转角 | [具体旋转角](RotationAngle.lean)核对第一象限主值 $\arctan(1/2)$ 的正弦、余弦，以及对任意点的旋转公式。 |
| 定理 2.1：特征基从哪里来 | [谱定理的实矩阵表述](SpectralTheorem.lean)从 Mathlib 的 Hermitian 矩阵谱定理得到实标准正交特征基、两个正交恒等式及对角分解。 |
| 定理 2.1：为什么是全等 | [从谱定理到等距同构](SpectralCongruence.lean)使用真实的欧氏空间 `EuclideanSpace ℝ n` 和等距同构 `≃ᵢ`。它把新坐标下的点送回原坐标，并对所有实数水平给出对应。 |
| 已知一个正交矩阵时的推导 | [有限和版本](OrthogonalCoordinates.lean)逐项证明转置是双侧逆、内积与欧氏距离不变。假设行和列标准正交，并给出 $AQ=QD$ 或 $Q^TAQ=D$；这一文件本身不证明这样的 $Q$ 存在。 |
| 例 2.1：椭圆 | [从系数到点对](Example21.lean)独立计算两个实特征值、归一化特征方向、正交矩阵和标准形，并核验指定两点及其像的距离。 |
| 例 2.2：双曲线 | [负特征值的实例](Example22.lean)核验 $4xy=2u^2-2v^2$ 的换元、全部等值集保距双射、顶点的极小性质与坐标以及渐近线。此文件复用导读的平面欧氏距离定义。 |

精确到目标的通过范围与未验证项见[接续状态](../接续状态.md)。Mathlib 定理的应用不是对讲义所用「球面取最大值、按维数归纳」证明的逐行翻译。
