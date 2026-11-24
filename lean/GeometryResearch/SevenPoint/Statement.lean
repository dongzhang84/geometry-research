module

public import Mathlib

/-!
# 七点球定理：形式陈述（阶段 1）

论文：D. Zhang, *A Seven-Point Sphere of the Tetrahedron*, Zenodo 10.5281/zenodo.23572917，
Theorem 1（`docs/seven-point-sphere/seven_point_sphere.tex` 第 2 节）。

本文件只写定义和陈述；所有定理的**证明**暂时是 `sorry`，定义里没有 `sorry`。

空间取 `EuclideanSpace ℝ (Fin 3)`，点和向量是同一个类型。四面体是
`t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 3)) 3`，顶点 `t.points 0, …, t.points 3`
即论文的 V₀, …, V₃，取定顶点 V₀。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.SevenPoint

/-- 三维欧氏空间。 -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable (t : Affine.Simplex ℝ E3 3)

/-! ## 基本对象 -/

/-- 外心 O。 -/
def O : E3 := t.circumcenter

/-- 外接球半径 R。 -/
def R : ℝ := t.circumradius

/-- 重心 G（四个顶点的平均）。 -/
def G : E3 := Finset.univ.centroid ℝ t.points

/-- 取定的顶点 V₀。 -/
def V₀ : E3 := t.points 0

/-- V₀ 的对面 V₁V₂V₃（作为三角形）。`faceOpposite 0` 的第 j 个顶点是 `t.points (j+1)`。 -/
def face : Affine.Triangle ℝ E3 := t.faceOpposite 0

/-- 对面所在的平面。 -/
def facePlane : AffineSubspace ℝ E3 := affineSpan ℝ (Set.range (face t).points)

instance : Nonempty (facePlane t) :=
  ⟨⟨(face t).points 0, mem_affineSpan ℝ (Set.mem_range_self 0)⟩⟩

/-- 对面的外心 O′。 -/
def O' : E3 := (face t).circumcenter

/-! ## 七个点（论文 Table 1） -/

/-- 表 1 第 1 行：A，直线 V₀G 与外接球的第二个交点。 -/
def pointA : E3 := t.circumsphere.secondInter (V₀ t) (G t -ᵥ V₀ t)

/-- 表 1 第 2 行：B，对面所在平面关于外接球的极点（Mathlib 的 `Sphere.pole`：
球心在平面上的正交投影关于外接球的反演，即论文的 inv(O′)）。 -/
def pointB : E3 := t.circumsphere.pole (facePlane t)

/-- 表 1 第 3 行：C = 4G − 3V₀，即以 G 为中心、比 −3 的位似下 V₀ 的像（反补四面体的顶点）。 -/
def pointC : E3 := AffineMap.homothety (G t) (-3 : ℝ) (V₀ t)

/-- 表 1 第 4 行：H′，对面三角形的垂心（Mathlib 定义为三角形的 Monge 点）。 -/
def pointH' : E3 := (face t).orthocenter

/-- 表 1 第 5 行：E，G 关于外接球的反演点。 -/
def pointE : E3 := inversion (O t) (R t) (G t)

/-- 表 1 第 6 行：D = 4G − 3O，以 O 为中心、比 4 的位似下 G 的像。 -/
def pointD : E3 := AffineMap.homothety (O t) (4 : ℝ) (G t)

/-- 表 1 第 7 行：F = 4O′ − 3O，以 O 为中心、比 4 的位似下 O′ 的像。 -/
def pointF : E3 := AffineMap.homothety (O t) (4 : ℝ) (O' t)

/-- 七个点，顺序同论文表 1：A, B, C, H′, E, D, F。 -/
def sevenPoints : Fin 7 → E3 :=
  ![pointA t, pointB t, pointC t, pointH' t, pointE t, pointD t, pointF t]

/-- 球 s 与球 S(O, 2R) 正交：两球心距离的平方等于两半径平方之和。 -/
def OrthogonalToBigSphere (s : Sphere E3) : Prop :=
  dist s.center (O t) ^ 2 = s.radius ^ 2 + (2 * R t) ^ 2

/-! ## 忠实性引理：检查 A、B 的定义就是论文里的点 -/

/-- A 在外接球上。 -/
theorem pointA_mem_circumsphere : pointA t ∈ t.circumsphere := by
  sorry

/-- A 在直线 V₀G 上。 -/
theorem pointA_mem_line : pointA t ∈ line[ℝ, V₀ t, G t] := by
  sorry

/-- A 不是 V₀（直线 V₀G 与外接球确有第二个交点）。 -/
theorem pointA_ne_V₀ : pointA t ≠ V₀ t := by
  sorry

/-- 极点引理：若 O′ ≠ O，对面所在平面上的任意点 X 都满足 ⟪X − O, B − O⟫ = R²，
即 B 确实是该平面关于外接球的极点（与 O′ 不同方向的退化情形被排除）。 -/
theorem inner_pointB (hO' : O' t ≠ O t) {X : E3} (hX : X ∈ facePlane t) :
    ⟪X -ᵥ O t, pointB t -ᵥ O t⟫ = R t ^ 2 := by
  sorry

/-! ## 主定理 -/

/-- 主定理，Möbius 形式（论文 Theorem 1 的证明结构）：若 G ≠ O 且 O′ ≠ O，则存在不全为零的
(α, c)，使七个点 X 都满足 α‖X − O‖² − 2⟪c, X − O⟫ + 4αR² = 0。
α ≠ 0 时这是以 O + c/α 为心、与 S(O, 2R) 正交的球；α = 0 时这是过 O 的平面。 -/
theorem mobius_sphere (hG : G t ≠ O t) (hO' : O' t ≠ O t) :
    ∃ (α : ℝ) (c : E3), (α ≠ 0 ∨ c ≠ 0) ∧
      ∀ i, α * ‖sevenPoints t i -ᵥ O t‖ ^ 2 - 2 * ⟪c, sevenPoints t i -ᵥ O t⟫
        + 4 * α * R t ^ 2 = 0 := by
  sorry

/-- 主定理，非退化形式：若 O、G、O′、V₀ 不共面，则存在一个球 s，七个点都在 s 上，
s 与 S(O, 2R) 正交；并且在与 S(O, 2R) 正交的球中，经过这七个点的只有 s 一个。 -/
theorem seven_point_sphere (h : AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) :
    ∃ s : Sphere E3, (∀ i, sevenPoints t i ∈ s) ∧ OrthogonalToBigSphere t s ∧
      ∀ s' : Sphere E3, (∀ i, sevenPoints t i ∈ s') → OrthogonalToBigSphere t s' → s' = s := by
  sorry

/-- 平面形式：若 G ≠ O、O′ ≠ O，且 O、G、O′、V₀ 共面，则七个点在一个过 O 的平面上，
即存在非零向量 c，使七个点 X 都满足 ⟪c, X − O⟫ = 0。 -/
theorem seven_point_plane (hG : G t ≠ O t) (hO' : O' t ≠ O t)
    (h : ¬ AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) :
    ∃ c : E3, c ≠ 0 ∧ ∀ i, ⟪c, sevenPoints t i -ᵥ O t⟫ = 0 := by
  sorry

end GeometryResearch.SevenPoint
