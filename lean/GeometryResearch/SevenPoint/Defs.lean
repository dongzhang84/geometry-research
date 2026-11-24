module

public import Mathlib

/-!
# 七点球定理：定义

论文：D. Zhang, *A Seven-Point Sphere of the Tetrahedron*, Zenodo 10.5281/zenodo.23572917，
Theorem 1（`docs/seven-point-sphere/seven_point_sphere.tex` 第 2 节）。

本文件只有定义（四面体的基本对象和论文表 1 的七个点）；定理陈述和证明在 `Statement.lean`。

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

end GeometryResearch.SevenPoint
