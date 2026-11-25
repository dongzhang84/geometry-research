module

public import GeometryResearch.Midsphere.Defs

/-!
# 棱切球四面体十一定理：形式陈述

定义见 `Defs.lean`。所有陈述都假设 `IsFourBall t r`（四面体有棱切球，切长为 r）。
「共球」按论文的 Möbius 约定写成 `MCospherical`（在一个球面上或一个平面上）。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary S2 isogonal isotomic ConjDefined
  IsFermatPoint G O R Ω mid)

variable (t : Affine.Simplex ℝ E3 3) (r : Fin 4 → ℝ)

/-! ## 忠实性与存在性 -/

/-- Tᵢⱼ 在棱 VᵢVⱼ 上，且到 Vᵢ、Vⱼ 的距离分别为 rᵢ、rⱼ（即 Σᵢ 与 Σⱼ 的切点）。 -/
theorem T_spec (hfb : IsFourBall t r) {i j : Fin 4} (hij : i ≠ j) :
    T t r i j ∈ segment ℝ (t.points i) (t.points j) ∧
      dist (t.points i) (T t r i j) = r i ∧ dist (T t r i j) (t.points j) = r j := by
  sorry

/-- 棱切球：μ 经过六个切点，并在那里与棱相切（半径 MTᵢⱼ 垂直于棱）。 -/
theorem M_tangent (hfb : IsFourBall t r) {i j : Fin 4} (hij : i ≠ j) :
    T t r i j ∈ midsphere t r ∧ ⟪T t r i j - M t r, t.points j - t.points i⟫ = 0 := by
  sorry

/-- Zeeman 点在三条连线 TᵢⱼTₖₗ 上（{i, j}、{k, l} 为一对对棱）。 -/
theorem Z_mem_chord (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Z t r ∈ line[ℝ, T t r i j, T t r k l] := by
  sorry

/-- 类似重心是 G 的等角共轭；面积平方满足 Heron 公式 Sᵢ² = (Σr − rᵢ)·Πr/rᵢ。 -/
theorem K_spec (hfb : IsFourBall t r) :
    K t = isogonal t (G t) ∧ ∀ i, S2 t i = (∑ j, r j - r i) * (∏ j, r j) / r i := by
  sorry

/-- Feuerbach 点的忠实性：面不是等边三角形时，`X11` 同时在面的九点圆和内切圆上。 -/
theorem X11_faithful (hfb : IsFourBall t r) (l : Fin 4)
    (hne : ∃ i j, i ≠ l ∧ j ≠ l ∧ r i ≠ r j) :
    X11 t r l ∈ (t.faceOpposite l).ninePointCircle ∧
      dist (X11 t r l) (Ipt t l) = (t.faceOpposite l).inradius := by
  sorry

/-- Soddy 球存在：当两个曲率 s/2 ± 3√D 都不为 0（没有 Soddy 球退化为平面）时，有两个不同的
Soddy 球。（保证定理 1、3、9、10 不空。） -/
theorem exists_soddy (hfb : IsFourBall t r)
    (hplane : sInv r ^ 2 ≠ 3 * ∑ i, 1 / r i ^ 2) :
    ∃ S₁ ρ₁ S₂ ρ₂, IsSoddy t r S₁ ρ₁ ∧ IsSoddy t r S₂ ρ₂ ∧ (S₁, ρ₁) ≠ (S₂, ρ₂) := by
  sorry

/-- Soddy 球的刻画：任一满足 `IsSoddy` 的球，曲率 1/ρₛ 是 s/2 ± 3√D 之一，
D = (s² − 2Σ1/rᵢ²)/12 为 Descartes 判别式（论文 Lemma 2.1）。与 `exists_soddy` 合起来说明
`IsSoddy` 恰好刻画了论文的（非平面）Soddy 球。 -/
theorem soddy_curvature (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    let D := (sInv r ^ 2 - 2 * ∑ i, 1 / r i ^ 2) / 12
    1 / ρs = sInv r / 2 + 3 * √D ∨ 1 / ρs = sInv r / 2 - 3 * √D := by
  sorry

/-- Fermat 点存在。 -/
theorem exists_fermat : ∃ F, IsFermatPoint t F := by
  sorry

/-! ## 定理 1、2 -/

/-- 定理 1（中心平面）：G、O、K、M、Z 共面，且这个平面含有每个（非平面）Soddy 球的球心。 -/
theorem central_plane (hfb : IsFourBall t r) :
    Coplanar ℝ ({G t, O t, K t, M t r, Z t r} : Set E3) ∧
      ∀ S ρs, IsSoddy t r S ρs → Coplanar ℝ ({G t, O t, K t, M t r, Z t r, S} : Set E3) := by
  sorry

/-- 定理 2（GM 共轭平面）：G ≠ M，P 在直线 GM 上且两种共轭都有定义，则 P*、Pᵗ 与直线 GM 共面。 -/
theorem gm_conjugate_plane (hfb : IsFourBall t r) (hGM : G t ≠ M t r) {P : E3}
    (hP : P ∈ line[ℝ, G t, M t r]) (hd : ConjDefined t P) :
    Coplanar ℝ ({G t, M t r, isogonal t P, isotomic t P} : Set E3) := by
  sorry

/-! ## 定理 3：八点球 -/

/-- 定理 3（八点球）：σ₁、σ₂ 是两个不同的（非平面）Soddy 球，则 T₀₁、T₀₂、T₁₃、T₂₃、σ₁ 与 Σ₁、Σ₂ 的切点、
σ₂ 与 Σ₀、Σ₃ 的切点共球（或共面）。
论文指出 Soddy 球为平面时定理同样成立，这一情形未形式化（`IsSoddy` 要求 ρₛ ≠ 0）。 -/
theorem eight_point_sphere (hfb : IsFourBall t r) {S₁ S₂ : E3} {ρ₁ ρ₂ : ℝ}
    (h₁ : IsSoddy t r S₁ ρ₁) (h₂ : IsSoddy t r S₂ ρ₂) (hne : (S₁, ρ₁) ≠ (S₂, ρ₂)) :
    MCospherical ({T t r 0 1, T t r 0 2, T t r 1 3, T t r 2 3,
      soddyPt t r S₁ ρ₁ 1, soddyPt t r S₁ ρ₁ 2, soddyPt t r S₂ ρ₂ 0, soddyPt t r S₂ ρ₂ 3} :
        Set E3) := by
  sorry

/-! ## 定理 4：中心平面上的四点共圆 -/

/-- 定理 4：O、M、G 不共线，K ≠ M。A、B 是直线 OM 与外接球的交点，K′ 是 K 关于棱切球的反演点，
G′ 是 G 关于外接球的反演点。则 K′、G′、A、B 与 2O − G 共圆，且这个圆在中心平面上。 -/
theorem concyclic_four (hfb : IsFourBall t r) (hcol : ¬ Collinear ℝ ({O t, M t r, G t} : Set E3))
    (hKM : K t ≠ M t r) :
    let A := O t + (R t / ‖M t r - O t‖) • (M t r - O t)
    let B := O t - (R t / ‖M t r - O t‖) • (M t r - O t)
    let K' := inversion (M t r) (ρ t r) (K t)
    let G' := inversion (O t) (R t) (G t)
    let G2 := AffineMap.homothety (O t) (-1 : ℝ) (G t)
    Concyclic ({K', G', A, B, G2} : Set E3) ∧
      Coplanar ℝ ({G t, O t, K t, M t r, Z t r, K', G', A, B, G2} : Set E3) := by
  sorry

/-! ## 定理 5–7：三个五点球 -/

/-- 定理 5：面 012、123 都不是等边三角形，则 T₁₂、N₀₁|₂₃、N₀₂|₁₃、X₁₁⁰¹²、X₁₁¹²³ 共球（或共面）。 -/
theorem five_point_5 (hfb : IsFourBall t r) (h012 : ¬ (r 0 = r 1 ∧ r 1 = r 2))
    (h123 : ¬ (r 1 = r 2 ∧ r 2 = r 3)) :
    MCospherical ({T t r 1 2, N t r 0 1 2 3, N t r 0 2 1 3, X11 t r 3, X11 t r 0} : Set E3) := by
  sorry

/-- 定理 6：面 013 不是等边三角形，则 V₁、I₀₁₂、T₁₃、N₀₁|₂₃、X₁₁⁰¹³ 共球（或共面）。 -/
theorem five_point_6 (hfb : IsFourBall t r) (h013 : ¬ (r 0 = r 1 ∧ r 1 = r 3)) :
    MCospherical ({t.points 1, Ipt t 3, T t r 1 3, N t r 0 1 2 3, X11 t r 2} : Set E3) := by
  sorry

/-- 定理 7：I₀₁₂、I₀₂₃、m₀₂、m₀₂ 到直线 V₁V₃ 的垂足、T₁₃ 共球（或共面）。 -/
theorem five_point_7 (hfb : IsFourBall t r) :
    MCospherical ({Ipt t 3, Ipt t 1, mid t 0 2, foot02 t, T t r 1 3} : Set E3) := by
  sorry

/-! ## 定理 8、9：两个引理 -/

/-- 定理 8（位似引理）：{i, j}、{k, l} 为一对对棱，Γ 是过 Z、Nᵢₖ|ⱼₗ、Nᵢₗ|ⱼₖ 的圆（假设三点不共线），
E 是 Σₖ、Σₗ 的外位似中心（rₖ ≠ rₗ）。则 E 在 Γ 所在平面上，且 E 对 Γ 的幂等于 (rₗ/rₖ)·pow(E, Σₖ)。
（论文的「对 Σᵢ、Σⱼ 同样成立」由交换 {i, j} 与 {k, l} 得到：Γ 不变，因为 Tₐᵦ = Tᵦₐ。） -/
theorem homothety_lemma (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hrkl : r k ≠ r l)
    (hΓ : AffineIndependent ℝ ![Z t r, N t r i k j l, N t r i l j k]) :
    Eext t r k l ∈ affineSpan ℝ {Z t r, N t r i k j l, N t r i l j k} ∧
      (⟨_, hΓ⟩ : Affine.Triangle ℝ E3).circumsphere.power (Eext t r k l) =
        r l / r k * (ball t r k).power (Eext t r k l) := by
  sorry

/-- 定理 9（正交球引理）：{i, j}、{k, l} 为一对对棱，σ₁、σ₂ 为两个不同的 Soddy 球。经过 Tᵢⱼ 且
与 σ₁、σ₂ 都正交的球也经过 Tₖₗ。（Soddy 球为平面的情形未形式化。） -/
theorem orthogonal_sphere (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {S₁ S₂ : E3} {ρ₁ ρ₂ : ℝ}
    (h₁ : IsSoddy t r S₁ ρ₁) (h₂ : IsSoddy t r S₂ ρ₂) (hne : (S₁, ρ₁) ≠ (S₂, ρ₂))
    (s : Sphere E3) (hT : T t r i j ∈ s)
    (ho₁ : dist s.center S₁ ^ 2 = s.radius ^ 2 + ρ₁ ^ 2)
    (ho₂ : dist s.center S₂ ^ 2 = s.radius ^ 2 + ρ₂ ^ 2) :
    T t r k l ∈ s := by
  sorry

/-! ## 定理 10：Soddy 五点球 -/

/-- 定理 10（Soddy 五点球）：四面体不是正四面体（切长不全相等），{i, j}、{k, l} 为一对对棱，
σ 为一个 Soddy 球，M′ 为 M 关于 σ 的反演点。则 Z、Nᵢⱼ|ₖₗ、σ 与 Σₖ、Σₗ 的切点、M′ 共球（或共面）。（σ 为平面的情形未形式化。） -/
theorem soddy_five_point (hfb : IsFourBall t r) (hreg : ¬ ∀ i j, r i = r j)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    MCospherical ({Z t r, N t r i j k l, soddyPt t r S ρs k, soddyPt t r S ρs l,
      inversion S |ρs| (M t r)} : Set E3) := by
  sorry

/-! ## 定理 11：Fermat 线 -/

/-- 定理 11（Fermat 线）：Fermat 点 F 不是顶点，则 F、F*、M 共线。 -/
theorem fermat_line (hfb : IsFourBall t r) {F : E3} (hF : IsFermatPoint t F)
    (hFv : ∀ j, F ≠ t.points j) :
    Collinear ℝ ({F, isogonal t F, M t r} : Set E3) := by
  sorry

end GeometryResearch.Midsphere
