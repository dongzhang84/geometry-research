module

public import Mathlib

/-!
# 垂心四面体五定理：定义

论文：D. Zhang, *Five Theorems on the Orthocentric Tetrahedron*, Zenodo 10.5281/zenodo.23579462
（`docs/orthocentric-theorems/orthocentric_theorems.tex`）。

空间取 `EuclideanSpace ℝ (Fin 3)`，四面体 `t : Affine.Simplex ℝ E3 3`，顶点 `t.points i`
即论文的 Vᵢ；论文的「面 i」是 Vᵢ 的对面 `t.faceOpposite i`。

Mathlib 里没有现成定义、需要自己定义的有：垂心四面体的条件、论文的参数 p 与 aᵢ、
极反演 ψ、重心坐标下的等角共轭与等截共轭、面积的平方、Fermat 点。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

/-- 三维欧氏空间。 -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable (t : Affine.Simplex ℝ E3 3)

/-! ## 垂心四面体 -/

/-- 垂心四面体：三对对棱都互相垂直（论文第 2 节的定义）。 -/
def IsOrthocentric : Prop :=
  ⟪t.points 0 - t.points 1, t.points 2 - t.points 3⟫ = 0 ∧
  ⟪t.points 0 - t.points 2, t.points 1 - t.points 3⟫ = 0 ∧
  ⟪t.points 0 - t.points 3, t.points 1 - t.points 2⟫ = 0

/-! ## 基本对象 -/

/-- 外心 O。 -/
def O : E3 := t.circumcenter

/-- 外接球半径 R。 -/
def R : ℝ := t.circumradius

/-- 外接球 Ω。 -/
def Ω : Sphere E3 := t.circumsphere

/-- 重心 G。 -/
def G : E3 := Finset.univ.centroid ℝ t.points

/-- 垂心 H，取为 Mathlib 的 Monge 点。论文：垂心四面体的四条高交于 H，H 与 Monge 点重合。
（忠实性引理 `H_mem_altitude` 检查 H 在四条高上。） -/
def H : E3 := t.mongePoint

/-- 面 i（顶点 Vᵢ 的对面）所在的平面。 -/
def facePlane (i : Fin 4) : AffineSubspace ℝ E3 :=
  affineSpan ℝ (Set.range (t.faceOpposite i).points)

instance (i : Fin 4) : Nonempty (facePlane t i) :=
  ⟨⟨(t.faceOpposite i).points 0, mem_affineSpan ℝ (Set.mem_range_self 0)⟩⟩

/-- 面 i 的重心 Gᵢ。 -/
def Gface (i : Fin 4) : E3 := t.faceOppositeCentroid i

/-- 从 Vᵢ 出发的高的垂足 Hᵢ（也是面 i 的垂心）。 -/
def Hfoot (i : Fin 4) : E3 := t.altitudeFoot i

/-- 棱 VᵢVⱼ 的中点 mᵢⱼ。 -/
def mid (i j : Fin 4) : E3 := midpoint ℝ (t.points i) (t.points j)

/-- 论文的参数 p = ⟪V₀ − H, V₁ − H⟫。论文第 2 节：垂心四面体中 ⟪Vᵢ − H, Vⱼ − H⟫（i ≠ j）
都相等，公共值记作 p（忠实性引理 `inner_eq_p` 检查这一点）。 -/
def p : ℝ := ⟪t.points 0 - H t, t.points 1 - H t⟫

/-- 论文的参数 aᵢ = ⟪H − Vᵢ, Hᵢ − Vᵢ⟫，即向量 VᵢH 与 VᵢHᵢ 的内积。 -/
def a (i : Fin 4) : ℝ := ⟪H t - t.points i, Hfoot t i - t.points i⟫

/-- 极反演 ψ(X) = H + p (X − H)/|X − H|²（论文第 2 节）。p 可以是负数，
所以这不是 Mathlib 的 `inversion`（后者的「幂」是 R² ≥ 0）。 -/
def ψ (X : E3) : E3 := H t + (p t / ‖X - H t‖ ^ 2) • (X - H t)

/-- 中点球的半径 r：六条棱的中点到 G 的距离（论文 Lemma 2.1(d)）。 -/
def rMid : ℝ := dist (mid t 0 1) (G t)

/-- 点 X 对中点球（球心 G、半径 r）的幂。 -/
def powMid (X : E3) : ℝ := dist X (G t) ^ 2 - rMid t ^ 2

/-! ## 重心坐标与共轭 -/

/-- 四面体的四个顶点构成三维空间的一组仿射基。 -/
def basis : AffineBasis (Fin 4) ℝ E3 :=
  ⟨t.points, t.independent,
    t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [finrank_euclideanSpace])⟩

/-- 点 X 的重心坐标（和为 1）。 -/
def bary (X : E3) : Fin 4 → ℝ := (basis t).coords X

/-- 以齐次重心坐标 (w₀ : w₁ : w₂ : w₃) 给出的点（要求 Σwᵢ ≠ 0）。 -/
def ofWeights (w : Fin 4 → ℝ) : E3 :=
  Finset.univ.affineCombination ℝ t.points (fun i => w i / ∑ j, w j)

/-- 面 i 面积的平方 Sᵢ²（由面的三个顶点用 Gram 行列式算出）。 -/
def S2 (i : Fin 4) : ℝ :=
  let u := (t.faceOpposite i).points 1 - (t.faceOpposite i).points 0
  let w := (t.faceOpposite i).points 2 - (t.faceOpposite i).points 0
  (‖u‖ ^ 2 * ‖w‖ ^ 2 - ⟪u, w⟫ ^ 2) / 4

/-- 等角共轭 P* = (S₀²/x₀ : … : S₃²/x₃)，x 为 P 的重心坐标（论文第 2 节）。 -/
def isogonal (P : E3) : E3 := ofWeights t (fun i => S2 t i / bary t P i)

/-- 等截共轭 Pᵗ = (1/x₀ : … : 1/x₃)（论文第 2 节）。 -/
def isotomic (P : E3) : E3 := ofWeights t (fun i => 1 / bary t P i)

/-- 点 P 的两种共轭都有定义：P 不在任何面所在平面上（重心坐标全不为 0），
且两种共轭的权重和都不为 0（共轭点不在无穷远）。 -/
def ConjDefined (P : E3) : Prop :=
  (∀ i, bary t P i ≠ 0) ∧ (∑ i, S2 t i / bary t P i ≠ 0) ∧ (∑ i, 1 / bary t P i ≠ 0)

/-! ## Fermat 点 -/

/-- Fermat–Torricelli 点：到四个顶点距离之和最小的点。 -/
def IsFermatPoint (F : E3) : Prop :=
  ∀ Y : E3, ∑ i, dist F (t.points i) ≤ ∑ i, dist Y (t.points i)

end GeometryResearch.Orthocentric
