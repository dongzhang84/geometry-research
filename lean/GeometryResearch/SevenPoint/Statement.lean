module

public import GeometryResearch.SevenPoint.Defs
public import GeometryResearch.SevenPoint.Algebra
public import GeometryResearch.SevenPoint.Geometry

/-!
# 七点球定理：形式陈述与证明

论文：D. Zhang, *A Seven-Point Sphere of the Tetrahedron*, Zenodo 10.5281/zenodo.23572917，
Theorem 1。定义见 `Defs.lean`（阶段 1 审过的定义原样移入），代数核心见 `Algebra.lean`，
Mathlib 定义到向量公式的展开见 `Geometry.lean`。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.SevenPoint

variable (t : Affine.Simplex ℝ E3 3)

open _root_.GeometryResearch.SevenPoint.Algebra in
/-- 三个方程成立时，七个点（相对 O 的向量）都在 Σ(α, c) 上。 -/
theorem all_onSphere {α : ℝ} {c : E3} (h : Eqs (R t) α (v₀ t) (g t) (p t) c)
    (hG : G t ≠ O t) (hO' : O' t ≠ O t) (i : Fin 7) :
    OnSphere (R t) α c (sevenPoints t i - O t) := by
  have hg : g t ≠ 0 := sub_ne_zero.mpr hG
  have hp : p t ≠ 0 := sub_ne_zero.mpr hO'
  fin_cases i
  · change OnSphere (R t) α c (pointA t - O t); rw [pointA_sub]; exact onSphere_A h (inner_v₀ t)
  · change OnSphere (R t) α c (pointB t - O t); rw [pointB_sub]; exact onSphere_B h hp
  · change OnSphere (R t) α c (pointC t - O t); rw [pointC_sub]; exact onSphere_C h (inner_v₀ t)
  · change OnSphere (R t) α c (pointH' t - O t); rw [pointH'_sub]
    exact onSphere_H h (inner_v₀ t) (inner_s_p t)
  · change OnSphere (R t) α c (pointE t - O t); rw [pointE_sub]; exact onSphere_E h hg
  · change OnSphere (R t) α c (pointD t - O t); rw [pointD_sub]; exact onSphere_D h
  · change OnSphere (R t) α c (pointF t - O t); rw [pointF_sub]; exact onSphere_F h

/-! ## 忠实性引理：检查 A、B 的定义就是论文里的点 -/

/-- A 在外接球上。 -/
theorem pointA_mem_circumsphere : pointA t ∈ t.circumsphere :=
  (Sphere.secondInter_mem _).mpr (t.mem_circumsphere 0)

/-- A 在直线 V₀G 上。 -/
theorem pointA_mem_line : pointA t ∈ line[ℝ, V₀ t, G t] :=
  Sphere.secondInter_vsub_mem_affineSpan _ _ _

/-- A 不是 V₀（直线 V₀G 与外接球确有第二个交点）。 -/
theorem pointA_ne_V₀ : pointA t ≠ V₀ t := by
  intro h
  rw [pointA, Sphere.secondInter_eq_self_iff, t.circumsphere_center] at h
  have h' : ⟪g t - v₀ t, v₀ t⟫ = 0 := by
    have e1 : G t -ᵥ V₀ t = g t - v₀ t := by simp [g, v₀]
    rw [e1] at h; exact h
  exact (inner_g_sub_v₀_neg t).ne h'

/-- 极点引理：若 O′ ≠ O，对面所在平面上的任意点 X 都满足 ⟪X − O, B − O⟫ = R²，
即 B 确实是该平面关于外接球的极点（与 O′ 不同方向的退化情形被排除）。 -/
theorem inner_pointB (hO' : O' t ≠ O t) {X : E3} (hX : X ∈ facePlane t) :
    ⟪X -ᵥ O t, pointB t -ᵥ O t⟫ = R t ^ 2 := by
  have hp : p t ≠ 0 := sub_ne_zero.mpr hO'
  have hpp : ⟪p t, p t⟫ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  -- X − O′ 在平面的方向里，O − O′ 与之垂直
  have hmem := vsub_orthogonalProjection_mem_direction_orthogonal (facePlane t) (O t)
  rw [orthogonalProjection_O, vsub_eq_sub] at hmem
  have hdir : X - O' t ∈ (facePlane t).direction := by
    rw [← vsub_eq_sub]
    apply AffineSubspace.vsub_mem_direction hX
    rw [← orthogonalProjection_O]; exact (orthogonalProjection (facePlane t) (O t)).property
  have h0 : ⟪X - O' t, O t - O' t⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hdir hmem
  have hXp : ⟪X - O t, p t⟫ = ⟪p t, p t⟫ := by
    rw [show X - O t = (X - O' t) + p t by simp [p], inner_add_left,
      show p t = -(O t - O' t) by simp [p], inner_neg_right, h0]
    simp
  rw [vsub_eq_sub, vsub_eq_sub, pointB_sub, real_inner_smul_right, hXp]
  field_simp

/-! ## 主定理 -/

/-- 主定理，Möbius 形式（论文 Theorem 1 的证明结构）：若 G ≠ O 且 O′ ≠ O，则存在不全为零的
(α, c)，使七个点 X 都满足 α‖X − O‖² − 2⟪c, X − O⟫ + 4αR² = 0。
α ≠ 0 时这是以 O + c/α 为心、与 S(O, 2R) 正交的球；α = 0 时这是过 O 的平面。 -/
theorem mobius_sphere (hG : G t ≠ O t) (hO' : O' t ≠ O t) :
    ∃ (α : ℝ) (c : E3), (α ≠ 0 ∨ c ≠ 0) ∧
      ∀ i, α * ‖sevenPoints t i -ᵥ O t‖ ^ 2 - 2 * ⟪c, sevenPoints t i -ᵥ O t⟫
        + 4 * α * R t ^ 2 = 0 := by
  obtain ⟨α, c, hne, h⟩ := Algebra.exists_eqs finrank_euclideanSpace_fin (R t) (v₀ t) (g t) (p t)
  refine ⟨α, c, hne, fun i => ?_⟩
  have := all_onSphere t h hG hO' i
  unfold Algebra.OnSphere at this
  rwa [real_inner_self_eq_norm_sq] at this

/-- 主定理，非退化形式：若 O、G、O′、V₀ 不共面，则存在一个球 s，七个点都在 s 上，
s 与 S(O, 2R) 正交；并且在与 S(O, 2R) 正交的球中，经过这七个点的只有 s 一个。 -/
theorem seven_point_sphere (h : AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) :
    ∃ s : Sphere E3, (∀ i, sevenPoints t i ∈ s) ∧ OrthogonalToBigSphere t s ∧
      ∀ s' : Sphere E3, (∀ i, sevenPoints t i ∈ s') → OrthogonalToBigSphere t s' → s' = s := by
  -- 不共面蕴含 G ≠ O、O′ ≠ O
  have hG : G t ≠ O t := h.injective.ne (by decide : (1 : Fin 4) ≠ 0)
  have hO' : O' t ≠ O t := h.injective.ne (by decide : (2 : Fin 4) ≠ 0)
  have hg : g t ≠ 0 := sub_ne_zero.mpr hG
  have hp : p t ≠ 0 := sub_ne_zero.mpr hO'
  have hR : R t ≠ 0 := (R_pos t).ne'
  -- 取三个方程的非零解；不共面时 α ≠ 0，归一化为 α = 1
  obtain ⟨α, c, hne, hE⟩ := Algebra.exists_eqs finrank_euclideanSpace_fin (R t) (v₀ t) (g t) (p t)
  have hα : α ≠ 0 := by
    rintro rfl
    have hc : c = 0 := eq_zero_of_inner t h
      (by linarith [hE.eqG]) (by linarith [hE.eqP]) (by linarith [hE.eqV])
    exact hne.elim (fun h0 => h0 rfl) (fun h0 => h0 hc)
  set c₁ := α⁻¹ • c with hc₁
  have hE1 : Algebra.Eqs (R t) 1 (v₀ t) (g t) (p t) c₁ := hE.normalize hα
  -- α = 1 时：X 在 Σ(1, c₁) 上 ⇔ ‖x − c₁‖² = ‖c₁‖² − 4R²（x = X − O）
  have key : ∀ x : E3, Algebra.OnSphere (R t) 1 c₁ x →
      ‖x - c₁‖ ^ 2 = ‖c₁‖ ^ 2 - 4 * R t ^ 2 := by
    intro x hx
    unfold Algebra.OnSphere at hx
    rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq x, real_inner_comm c₁ x]
    linarith
  have hon := all_onSphere t hE1 hG hO'
  set ctr : E3 := c₁ + O t with hctr
  set rad : ℝ := ‖(pointA t - O t) - c₁‖ with hrad
  have hdist : ∀ X : E3, dist X ctr = ‖(X - O t) - c₁‖ := by
    intro X; rw [dist_eq_norm, hctr]; congr 1; abel
  have hradsq : rad ^ 2 = ‖c₁‖ ^ 2 - 4 * R t ^ 2 := key _ (hon 0)
  refine ⟨⟨ctr, rad⟩, ?_, ?_, ?_⟩
  · -- 七个点都在球上
    intro i
    rw [EuclideanGeometry.mem_sphere, hdist]
    change ‖(sevenPoints t i - O t) - c₁‖ = rad
    have h1 := key _ (hon i)
    rw [← hradsq] at h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  · -- 与 S(O, 2R) 正交
    change dist ctr (O t) ^ 2 = rad ^ 2 + (2 * R t) ^ 2
    rw [hradsq, dist_eq_norm, hctr, add_sub_cancel_right]
    ring
  · -- 唯一性
    intro s' hs' hort
    set c' := s'.center - O t with hc'
    -- s' 上的点都在 Σ(1, c') 上
    have hon' : ∀ i, Algebra.OnSphere (R t) 1 c' (sevenPoints t i - O t) := by
      intro i
      have hmem := hs' i
      rw [EuclideanGeometry.mem_sphere, dist_eq_norm] at hmem
      have hx : ‖(sevenPoints t i - O t) - c'‖ = s'.radius := by
        rw [← hmem, hc']; congr 1; abel
      unfold OrthogonalToBigSphere at hort
      rw [dist_eq_norm] at hort
      unfold Algebra.OnSphere
      have e := congrArg (· ^ 2) hx
      rw [@norm_sub_sq_real, ← real_inner_self_eq_norm_sq (sevenPoints t i - O t),
        real_inner_comm c' (sevenPoints t i - O t)] at e
      rw [← hc'] at hort
      nlinarith [e, hort]
    -- 由 E、B、C 三点反推出三个方程
    have hE4 := hon' 4
    have hB1 := hon' 1
    have hC2 := hon' 2
    change Algebra.OnSphere _ _ _ (pointE t - O t) at hE4
    change Algebra.OnSphere _ _ _ (pointB t - O t) at hB1
    change Algebra.OnSphere _ _ _ (pointC t - O t) at hC2
    rw [pointE_sub] at hE4
    rw [pointB_sub] at hB1
    rw [pointC_sub] at hC2
    have eG := Algebra.eqG_of_onSphere_E hg hR hE4
    have eP := Algebra.eqP_of_onSphere_B hp hR hB1
    have eV := Algebra.eqV_of_onSphere_C eG (inner_v₀ t) hC2
    -- c′ 与 c₁ 满足同样的三个方程，差与 g、p、v₀ 都垂直，所以相等
    have hcc : c' = c₁ := by
      have hd := eq_zero_of_inner t h (c := c' - c₁)
        (by rw [inner_sub_left]; linarith [hE1.eqG, eG])
        (by rw [inner_sub_left]; linarith [hE1.eqP, eP])
        (by rw [inner_sub_left]; linarith [hE1.eqV, eV])
      exact sub_eq_zero.mp hd
    have hcenter : s'.center = ctr := by
      rw [hctr, ← hcc, hc']; abel
    have hradius : s'.radius = rad := by
      have hmem := hs' 0
      rw [EuclideanGeometry.mem_sphere, hcenter, hdist] at hmem
      exact hmem.symm
    exact EuclideanGeometry.Sphere.ext hcenter hradius

/-- 平面形式：若 G ≠ O、O′ ≠ O，且 O、G、O′、V₀ 共面，则七个点在一个过 O 的平面上，
即存在非零向量 c，使七个点 X 都满足 ⟪c, X − O⟫ = 0。 -/
theorem seven_point_plane (hG : G t ≠ O t) (hO' : O' t ≠ O t)
    (h : ¬ AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) :
    ∃ c : E3, c ≠ 0 ∧ ∀ i, ⟪c, sevenPoints t i -ᵥ O t⟫ = 0 := by
  obtain ⟨c, hc0, h1, h2, h3⟩ := exists_orth t h
  have hE : Algebra.Eqs (R t) 0 (v₀ t) (g t) (p t) c := ⟨by simp [h1], by simp [h2], by simp [h3]⟩
  refine ⟨c, hc0, fun i => ?_⟩
  have := all_onSphere t hE hG hO' i
  unfold Algebra.OnSphere at this
  rw [vsub_eq_sub]
  linarith

end GeometryResearch.SevenPoint
