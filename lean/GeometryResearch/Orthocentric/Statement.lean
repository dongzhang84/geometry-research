module

public import GeometryResearch.Orthocentric.Defs

/-!
# 垂心四面体五定理：形式陈述（阶段 1）

论文：D. Zhang, *Five Theorems on the Orthocentric Tetrahedron*, Zenodo 10.5281/zenodo.23579462。
定义见 `Defs.lean`。本文件只写陈述，所有**证明**暂时是 `sorry`。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

variable (t : Affine.Simplex ℝ E3 3)

/-! ## 忠实性引理：检查自定义的概念就是论文里的意思 -/

/-- 垂心四面体中，H（Monge 点）在四条高上，即 H 是四条高的公共点。 -/
theorem H_mem_altitude (ho : IsOrthocentric t) (i : Fin 4) : H t ∈ t.altitude i := by
  sorry

/-- 论文第 2 节：⟪Vᵢ − H, Vⱼ − H⟫（i ≠ j）都等于同一个数 p。 -/
theorem inner_eq_p (ho : IsOrthocentric t) {i j : Fin 4} (hij : i ≠ j) :
    ⟪t.points i - H t, t.points j - H t⟫ = p t := by
  sorry

/-- 论文 (2.1) 式：aᵢ = |HVᵢ|² − p。 -/
theorem a_eq (ho : IsOrthocentric t) (i : Fin 4) :
    a t i = ‖t.points i - H t‖ ^ 2 - p t := by
  sorry

/-- 论文第 2 节：极反演 ψ 把顶点 Vᵢ 映到高的垂足 Hᵢ。 -/
theorem ψ_point (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) (i : Fin 4) :
    ψ t (t.points i) = Hfoot t i := by
  sorry

/-- `ofWeights` 给出的点，重心坐标与权重成比例：这保证 `isogonal`、`isotomic`
确实是「重心坐标为 (S₀²/x₀ : …)、(1/x₀ : …) 的点」。 -/
theorem bary_ofWeights (w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0) (i : Fin 4) :
    bary t (ofWeights t w) i = w i / ∑ j, w j := by
  sorry

/-- Fermat 点存在（所以定理 5 不是空的）。 -/
theorem exists_fermatPoint : ∃ F, IsFermatPoint t F := by
  sorry

/-! ## 定理 1：十三点球 -/

/-- 定理 1（十三点球）：设 Σ 是经过顶点 Vᵢ 和对面九点圆的球。那么 Σ 还经过：
(i) 对面重心 Gᵢ 的极反演点 ψ(Gᵢ)；(ii) H 与 Vᵢ 的外接球对径点 Xᵢ 的中点；
(iii) H 与 Yᵢ 的中点，Yᵢ 是高线 VᵢH 与外接球的第二个交点。并且 H 对 Σ 的幂等于 (3/2)p。

「经过对面九点圆」写成：对面所在平面上、在面三角形的九点圆（Mathlib `ninePointCircle`）上的
点都在 Σ 上。Xᵢ = 2O − Vᵢ（以 O 为中心、比 −1 的位似），Yᵢ 用 Mathlib `secondInter`。 -/
theorem thirteen_point_sphere (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j)
    (i : Fin 4) (s : Sphere E3) (hV : t.points i ∈ s)
    (hN : ∀ X ∈ facePlane t i, X ∈ (t.faceOpposite i).ninePointCircle → X ∈ s) :
    ψ t (Gface t i) ∈ s ∧
    midpoint ℝ (H t) (AffineMap.homothety (O t) (-1 : ℝ) (t.points i)) ∈ s ∧
    midpoint ℝ (H t) ((Ω t).secondInter (t.points i) (H t -ᵥ t.points i)) ∈ s ∧
    s.power (H t) = 3 / 2 * p t := by
  sorry

/-- 经过 Vᵢ 和对面九点圆的球存在（所以定理 1 不是空的）。 -/
theorem exists_sphere_thirteen (i : Fin 4) :
    ∃ s : Sphere E3, t.points i ∈ s ∧
      ∀ X ∈ facePlane t i, X ∈ (t.faceOpposite i).ninePointCircle → X ∈ s := by
  sorry

/-! ## 定理 2、3：两条欧拉线上的共轭 -/

/-- 定理 2（欧拉线共轭平面）：四面体不是正四面体（O ≠ H），P 在欧拉线 OH 上且两种共轭都有定义，
则 P*、Pᵗ 与欧拉线共面。 -/
theorem euler_line_conjugate_plane (ho : IsOrthocentric t) (hOH : O t ≠ H t)
    {P : E3} (hP : P ∈ line[ℝ, O t, H t]) (hd : ConjDefined t P) :
    Coplanar ℝ ({O t, H t, isogonal t P, isotomic t P} : Set E3) := by
  sorry

/-- 定理 3（第二欧拉线上的共轭共线）：O 的两种共轭有定义且 O ≠ O*，P 在直线 OO* 上且两种共轭
都有定义，则 O、P*、Pᵗ 共线。 -/
theorem second_euler_line_collinear (ho : IsOrthocentric t) (hO : ConjDefined t (O t))
    (hOO : O t ≠ isogonal t (O t)) {P : E3} (hP : P ∈ line[ℝ, O t, isogonal t (O t)])
    (hd : ConjDefined t P) :
    Collinear ℝ ({O t, isogonal t P, isotomic t P} : Set E3) := by
  sorry

/-- 定理 3 的特例（P = O）：O、O*、Oᵗ 共线。 -/
theorem O_isogonal_isotomic_collinear (ho : IsOrthocentric t) (hO : ConjDefined t (O t))
    (hOO : O t ≠ isogonal t (O t)) :
    Collinear ℝ ({O t, isogonal t (O t), isotomic t (O t)} : Set E3) := by
  sorry

/-! ## 定理 4：七线共点 -/

/-- 论文定理 4 的点 X = H + λ(G − H)，λ = (4g² − R²)/(2g² + R²)，g = |HG|。 -/
def Xpt : E3 :=
  let g2 := dist (H t) (G t) ^ 2
  AffineMap.lineMap (H t) (G t) ((4 * g2 - R t ^ 2) / (2 * g2 + R t ^ 2))

/-- Aᵢ = ψ(Gᵢ)。 -/
def Apt (i : Fin 4) : E3 := ψ t (Gface t i)

/-- Bᵢ：直线 VᵢG 与外接球的第二个交点。 -/
def Bpt (i : Fin 4) : E3 := (Ω t).secondInter (t.points i) (G t -ᵥ t.points i)

/-- 定理 4（七线共点），四条弦 AᵢBᵢ 部分：X 在直线 AᵢBᵢ 上，且 ⟪XAᵢ, XBᵢ⟫ = X 对外接球的幂。
假设 ψ 在用到的点上有定义：H 不是顶点，且 Gᵢ ≠ H。 -/
theorem seven_lines_chord (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j)
    (hG : ∀ j, Gface t j ≠ H t) (i : Fin 4) :
    Xpt t ∈ line[ℝ, Apt t i, Bpt t i] ∧
      ⟪Apt t i - Xpt t, Bpt t i - Xpt t⟫ = (Ω t).power (Xpt t) := by
  sorry

/-- 定理 4（七线共点），三条直线 ψ(mᵢⱼ)ψ(mₖₗ) 部分（{i, j}、{k, l} 是一对对棱）：X 在这条直线上，
且 ⟪Xψ(mᵢⱼ), Xψ(mₖₗ)⟫ = X 对中点球的幂。假设 H 不是顶点，且棱中点都不等于 H。 -/
theorem seven_lines_midpoint (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j)
    (hm : ∀ a b, a ≠ b → mid t a b ≠ H t)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    Xpt t ∈ line[ℝ, ψ t (mid t i j), ψ t (mid t k l)] ∧
      ⟪ψ t (mid t i j) - Xpt t, ψ t (mid t k l) - Xpt t⟫ = powMid t (Xpt t) := by
  sorry

/-! ## 定理 5：Fermat 点的共线 -/

/-- 定理 5：F 是 Fermat 点，W 的重心坐标为 (a₀/d₀² : … : a₃/d₃²)，dᵢ = |FVᵢ|。
在论文第 6 节的假设下（F、H 都不是顶点，O 不在任何面所在平面上，F ≠ O，Σ aᵢ/dᵢ² ≠ 0），
F、O、W 共线。 -/
theorem fermat_collinear (ho : IsOrthocentric t) {F : E3} (hF : IsFermatPoint t F)
    (hFv : ∀ j, F ≠ t.points j) (hH : ∀ j, H t ≠ t.points j) (hO : ∀ j, bary t (O t) j ≠ 0)
    (hFO : F ≠ O t) (hW : ∑ j, a t j / dist F (t.points j) ^ 2 ≠ 0) :
    Collinear ℝ ({F, O t, ofWeights t (fun j => a t j / dist F (t.points j) ^ 2)} : Set E3) := by
  sorry

end GeometryResearch.Orthocentric
