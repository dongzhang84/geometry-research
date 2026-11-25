module

public import GeometryResearch.Orthocentric.Defs

/-!
# 棱切球四面体十一定理：定义

论文：D. Zhang, *Eleven Theorems on the Tetrahedron with a Midsphere*
（`docs/midsphere-theorems/midsphere_theorems.tex`）。

四个两两外切的球 Σᵢ（球心 Vᵢ，半径 tᵢ > 0）张成四面体，|VᵢVⱼ| = tᵢ + tⱼ；这正是有棱切球的
四面体，tᵢ 是从 Vᵢ 出发的切线长。Lean 中把切长记作 `r : Fin 4 → ℝ`，条件 `IsFourBall t r`。

与垂心四面体共用的一般定义（重心坐标 `bary`、按权重给点 `ofWeights`、面积平方 `S2`、等角共轭
`isogonal`、等截共轭 `isotomic`、`ConjDefined`、Fermat 点 `IsFermatPoint`，以及 G、O、R、Ω、
棱中点 `mid`）直接取自 `GeometryResearch.Orthocentric.Defs`，它们对任意四面体都有意义。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary S2 isogonal isotomic ConjDefined
  IsFermatPoint G O R Ω mid)

variable (t : Affine.Simplex ℝ E3 3) (r : Fin 4 → ℝ)

/-- 四球四面体：以 Vᵢ 为心、rᵢ > 0 为半径的四个球两两外切，即 |VᵢVⱼ| = rᵢ + rⱼ。 -/
def IsFourBall : Prop :=
  (∀ i, 0 < r i) ∧ ∀ i j, i ≠ j → dist (t.points i) (t.points j) = r i + r j

/-- 球 Σᵢ。 -/
def ball (i : Fin 4) : Sphere E3 := ⟨t.points i, r i⟩

/-- 切点 Tᵢⱼ：Σᵢ 与 Σⱼ 的切点，在棱 VᵢVⱼ 上、距 Vᵢ 为 rᵢ。 -/
def T (i j : Fin 4) : E3 := AffineMap.lineMap (t.points i) (t.points j) (r i / (r i + r j))

/-- s = Σ 1/rᵢ。 -/
def sInv : ℝ := ∑ i, 1 / r i

/-- Zeeman 点 Z = (1/rᵢ)（论文 Lemma 2.1；忠实性引理 `Z_mem_chord` 检查它在三条连线上）。 -/
def Z : E3 := ofWeights t (fun i => 1 / r i)

/-- 棱切球球心 M = (s/(2rᵢ) − 1/rᵢ²)（论文 Lemma 2.1；忠实性引理 `M_tangent` 检查棱切球与
六条棱相切于 Tᵢⱼ）。 -/
def M : E3 := ofWeights t (fun i => sInv r / (2 * r i) - 1 / r i ^ 2)

/-- 棱切球半径 ρ = |MT₀₁|。 -/
def ρ : ℝ := dist (M t r) (T t r 0 1)

/-- 棱切球 μ。 -/
def midsphere : Sphere E3 := ⟨M t r, ρ t r⟩

/-- 类似重心 K（重心坐标 Sᵢ²，Sᵢ 为面 i 的面积），即 G 的等角共轭。 -/
def K : E3 := ofWeights t (S2 t)

/-- Soddy 球：球心 S、带符号半径 ρₛ ≠ 0，与四个 Σᵢ 都相切，即 |SVᵢ|² = (ρₛ + rᵢ)²
（ρₛ > 0 外切；ρₛ < 0 表示半径 |ρₛ| 的球从外面包住 Σᵢ）。论文中曲率为 0 的「平面」情形不在此列。 -/
def IsSoddy (S : E3) (ρs : ℝ) : Prop :=
  ρs ≠ 0 ∧ ∀ i, dist S (t.points i) ^ 2 = (ρs + r i) ^ 2

/-- Soddy 球（S, ρₛ）与 Σᵢ 的切点：在直线 VᵢS 上、距 Vᵢ 为 rᵢ。 -/
def soddyPt (S : E3) (ρs : ℝ) (i : Fin 4) : E3 :=
  AffineMap.lineMap (t.points i) S (r i / (r i + ρs))

/-- Nᵢⱼ|ₖₗ：Tᵢⱼ 与 Tₖₗ 的中点。 -/
def N (i j k l : Fin 4) : E3 := midpoint ℝ (T t r i j) (T t r k l)

/-- 不含顶点 Vₗ 的那个面的内心（Mathlib 的 `incenter`）。论文的 I₀₁₂ 是 `Ipt t 3`。 -/
def Ipt (l : Fin 4) : E3 := (t.faceOpposite l).incenter

/-- 不含 Vₗ 的面的 Feuerbach 点，按论文 (5.1) 的重心坐标 (rⱼ(rₖ − rₘ)² : …)；
这里写成 rᵢ(Σ_F − rᵢ)² − 4Π_F，Σ_F、Π_F 为面上三个切长之和与积（与 rᵢ(rₖ − rₘ)² 相等）。
忠实性引理 `X11_faithful` 检查它同时在面的九点圆和内切圆上。论文的 X₁₁⁰¹² 是 `X11 t r 3`。 -/
def X11 (l : Fin 4) : E3 :=
  ofWeights t (fun i => if i = l then 0 else
    r i * (∑ j, r j - r l - r i) ^ 2 - 4 * (∏ j, r j) / r l)

/-- m₀₂ 到直线 V₁V₃ 的垂足。 -/
def foot02 : E3 :=
  (EuclideanGeometry.orthogonalProjection line[ℝ, t.points 1, t.points 3] (mid t 0 2) : E3)

/-- Σₖ、Σₗ 的外位似中心 E = (rₗVₖ − rₖVₗ)/(rₗ − rₖ)（rₖ ≠ rₗ）。 -/
def Eext (k l : Fin 4) : E3 := AffineMap.lineMap (t.points k) (t.points l) (-(r k) / (r l - r k))

/-- Möbius 意义下的「共球」：在一个球面上或一个平面上（论文的约定）。 -/
def MCospherical (S : Set E3) : Prop := Cospherical S ∨ Coplanar ℝ S

end GeometryResearch.Midsphere
