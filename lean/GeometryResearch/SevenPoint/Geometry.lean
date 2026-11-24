module

public import GeometryResearch.SevenPoint.Defs

/-!
# 七点球定理：几何包装

把 `Statement.lean` 里用 Mathlib 定义的对象，展开成以外心 O 为原点的向量公式，
供 `Algebra.lean` 使用。记 `v₀ = V₀ − O`、`g = G − O`、`p = O′ − O`。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.SevenPoint

variable (t : Affine.Simplex ℝ E3 3)

/-- 每个顶点到外心的距离都是 R。 -/
theorem norm_point_sub_O (i : Fin 4) : ‖t.points i - O t‖ = R t := by
  rw [← dist_eq_norm]; exact t.dist_circumcenter_eq_circumradius i

theorem inner_v₀ : ⟪V₀ t - O t, V₀ t - O t⟫ = R t ^ 2 := by
  rw [real_inner_self_eq_norm_sq]; exact congrArg (· ^ 2) (norm_point_sub_O t 0)

/-- 外接球半径为正。 -/
theorem R_pos : 0 < R t := t.circumradius_pos

/-- 重心公式：n + 1 个点的重心减去 q，等于各点减 q 的平均。 -/
theorem centroid_sub {n : ℕ} (pts : Fin (n + 1) → E3) (q : E3) :
    Finset.univ.centroid ℝ pts - q = (1 / (n + 1 : ℝ)) • ∑ i, (pts i - q) := by
  have h := Finset.univ.centroid_vsub_const (k := ℝ) (p := pts) (p₀ := q) Finset.univ_nonempty
  simp only [vsub_eq_sub] at h
  rw [h, Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (Finset.univ.sum_centroidWeights_eq_one_of_card_ne_zero ℝ (by simp))]
  simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum]
  norm_num

/-- 重心：G − O = (1/4) Σ (Vᵢ − O)。 -/
theorem G_sub_O : G t - O t = (1 / 4 : ℝ) • ∑ i, (t.points i - O t) := by
  rw [G, centroid_sub]; norm_num

/-- 对面的第 j 个顶点是 `t.points j.succ`（即 V₁、V₂、V₃）。 -/
theorem face_points (j : Fin 3) : (face t).points j = t.points j.succ := by
  simp [face, Affine.Simplex.faceOpposite_point_eq_point_succAbove]

/-- O′ 是 O 在对面所在平面上的正交投影。 -/
theorem orthogonalProjection_O : (orthogonalProjection (facePlane t) (O t) : E3) = O' t := by
  have h := (face t).orthogonalProjection_eq_circumcenter_of_dist_eq (p := O t) (r := R t)
    (fun j => by rw [face_points]; exact t.dist_circumcenter_eq_circumradius _)
  exact h

/-- 对面的每个顶点 Vᵢ（i = 1, 2, 3）满足 ⟪Vᵢ − O′, O′ − O⟫ = 0。 -/
theorem inner_face (j : Fin 3) : ⟪t.points j.succ - O' t, O' t - O t⟫ = 0 := by
  have hmem := vsub_orthogonalProjection_mem_direction_orthogonal (facePlane t) (O t)
  rw [orthogonalProjection_O, vsub_eq_sub] at hmem
  have hdir : t.points j.succ - O' t ∈ (facePlane t).direction := by
    rw [← vsub_eq_sub]
    apply AffineSubspace.vsub_mem_direction
    · rw [← face_points]; exact mem_affineSpan ℝ (Set.mem_range_self j)
    · rw [← orthogonalProjection_O]; exact (orthogonalProjection (facePlane t) (O t)).property
  have := Submodule.inner_right_of_mem_orthogonal hdir hmem
  rw [show O' t - O t = -(O t - O' t) by abel, inner_neg_right, this, neg_zero]

/-! ## 以 O 为原点的向量 -/

/-- v₀ = V₀ − O。 -/
abbrev v₀ : E3 := V₀ t - O t
/-- g = G − O。 -/
abbrev g : E3 := G t - O t
/-- p = O′ − O。 -/
abbrev p : E3 := O' t - O t

/-- 对面三个顶点的和：Σⱼ (V_{j+1} − O) = 4g − v₀。 -/
theorem sum_face : ∑ j : Fin 3, (t.points j.succ - O t) = (4 : ℝ) • g t - v₀ t := by
  rw [g, G_sub_O, smul_smul, Fin.sum_univ_succ (f := fun i => t.points i - O t)]
  norm_num [v₀, V₀]

/-- 论文 (2.1) 式：⟪4g − v₀, p⟫ = 3‖p‖²。 -/
theorem inner_s_p : ⟪(4 : ℝ) • g t - v₀ t, p t⟫ = 3 * ⟪p t, p t⟫ := by
  rw [← sum_face, sum_inner]
  have : ∀ j : Fin 3, ⟪t.points j.succ - O t, p t⟫ = ⟪p t, p t⟫ := by
    intro j
    have h := inner_face t j
    rw [show t.points j.succ - O t = (t.points j.succ - O' t) + p t by simp [p], inner_add_left,
      h, zero_add]
  simp [this]

/-! ## 七个点的向量公式 -/

theorem pointD_sub : pointD t - O t = (4 : ℝ) • g t := by
  simp [pointD, AffineMap.homothety_apply, g]

theorem pointF_sub : pointF t - O t = (4 : ℝ) • p t := by
  simp [pointF, AffineMap.homothety_apply, p]

theorem pointC_sub : pointC t - O t = (4 : ℝ) • g t - (3 : ℝ) • v₀ t := by
  simp only [pointC, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, g, v₀]
  module

theorem pointE_sub : pointE t - O t = (R t ^ 2 / ⟪g t, g t⟫) • g t := by
  rw [pointE, inversion, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right, dist_eq_norm,
    div_pow, ← real_inner_self_eq_norm_sq]

theorem pointB_sub : pointB t - O t = (R t ^ 2 / ⟪p t, p t⟫) • p t := by
  rw [pointB, Sphere.pole, t.circumsphere_center, t.circumsphere_radius,
    show t.circumcenter = O t from rfl, show t.circumradius = R t from rfl, orthogonalProjection_O,
    inversion, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right, dist_eq_norm, div_pow,
    ← real_inner_self_eq_norm_sq]

theorem pointA_sub : pointA t - O t =
    (-2 * ⟪g t - v₀ t, v₀ t⟫ / ⟪g t - v₀ t, g t - v₀ t⟫) • (g t - v₀ t) + v₀ t := by
  have h1 : G t -ᵥ V₀ t = g t - v₀ t := by simp [g, v₀]
  rw [pointA, Sphere.secondInter, t.circumsphere_center, h1, vadd_eq_add, vsub_eq_sub]
  simp only [v₀, O]
  abel

theorem pointH'_sub : pointH' t - O t = (4 : ℝ) • g t - v₀ t - (2 : ℝ) • p t := by
  rw [pointH', Affine.Triangle.orthocenter_eq_mongePoint,
    Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter, vadd_eq_add, vsub_eq_sub]
  have hc := centroid_sub (face t).points (O t)
  have hsum : ∑ j, ((face t).points j - O t) = (4 : ℝ) • g t - v₀ t := by
    simp only [face_points]; exact sum_face t
  rw [hsum] at hc
  have hO' : (face t).circumcenter = O' t := rfl
  rw [hO', show Finset.univ.centroid ℝ (face t).points - O' t
      = (Finset.univ.centroid ℝ (face t).points - O t) - p t by simp [p], hc]
  simp only [p]
  norm_num
  module

/-! ## O、G、O′、V₀ 张成的向量空间 -/

/-- O、G、O′、V₀ 张成的向量子空间。 -/
abbrev vspan : Submodule ℝ E3 := vectorSpan ℝ (Set.range ![O t, G t, O' t, V₀ t])

/-- 与 g、p、v₀ 都垂直的向量，与整个 vspan 垂直。 -/
theorem vspan_le_orth {c : E3} (h1 : ⟪c, g t⟫ = 0) (h2 : ⟪c, p t⟫ = 0) (h3 : ⟪c, v₀ t⟫ = 0) :
    vspan t ≤ (ℝ ∙ c)ᗮ := by
  rw [vspan, vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self (0 : Fin 4)),
    Submodule.span_le]
  rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
  fin_cases i
  · simp
  · simpa [vsub_eq_sub] using h1
  · simpa [vsub_eq_sub] using h2
  · simpa [vsub_eq_sub] using h3

theorem g_mem_vspan : g t ∈ vspan t :=
  vsub_mem_vectorSpan ℝ ⟨1, rfl⟩ ⟨0, rfl⟩

theorem p_mem_vspan : p t ∈ vspan t :=
  vsub_mem_vectorSpan ℝ ⟨2, rfl⟩ ⟨0, rfl⟩

theorem v₀_mem_vspan : v₀ t ∈ vspan t :=
  vsub_mem_vectorSpan ℝ ⟨3, rfl⟩ ⟨0, rfl⟩

/-- 不共面时，与 g、p、v₀ 都垂直的向量只有 0。 -/
theorem eq_zero_of_inner (hind : AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) {c : E3}
    (h1 : ⟪c, g t⟫ = 0) (h2 : ⟪c, p t⟫ = 0) (h3 : ⟪c, v₀ t⟫ = 0) : c = 0 := by
  have hrank : Module.finrank ℝ (vspan t) = 3 :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (n := 3) (by simp)).mp hind
  have htop : vspan t = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hrank, finrank_euclideanSpace_fin])
  have hc : c ∈ (ℝ ∙ c)ᗮ := vspan_le_orth t h1 h2 h3 (htop ▸ Submodule.mem_top)
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hc
  simpa using hc

/-- 共面时，存在与 g、p、v₀ 都垂直的非零向量。 -/
theorem exists_orth (hnot : ¬ AffineIndependent ℝ ![O t, G t, O' t, V₀ t]) :
    ∃ c : E3, c ≠ 0 ∧ ⟪c, g t⟫ = 0 ∧ ⟪c, p t⟫ = 0 ∧ ⟪c, v₀ t⟫ = 0 := by
  have hne : vspan t ≠ ⊤ := by
    intro htop
    apply hnot
    rw [affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (n := 3) (by simp)]
    change Module.finrank ℝ (vspan t) = 3
    rw [htop, finrank_top, finrank_euclideanSpace_fin]
  have hbot : (vspan t)ᗮ ≠ ⊥ := by
    rwa [Ne, Submodule.orthogonal_eq_bot_iff]
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hbot
  refine ⟨c, hc0, ?_, ?_, ?_⟩
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal (g_mem_vspan t) hc
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal (p_mem_vspan t) hc
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal (v₀_mem_vspan t) hc

/-! ## 直线 V₀G 不与外接球相切 -/

/-- ⟪G − V₀, V₀ − O⟫ < 0：G 在外接球内部，直线 V₀G 与外接球确有第二个交点。 -/
theorem inner_g_sub_v₀_neg : ⟪g t - v₀ t, v₀ t⟫ < 0 := by
  have hgv : g t - v₀ t = (1 / 4 : ℝ) • ∑ i, (t.points i - V₀ t) := by
    rw [g, G_sub_O]
    simp only [v₀, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    module
  have hterm : ∀ i, ⟪t.points i - V₀ t, v₀ t⟫ = -(1 / 2) * ‖t.points i - V₀ t‖ ^ 2 := by
    intro i
    have hi := norm_point_sub_O t i
    have h0 := norm_point_sub_O t 0
    rw [show t.points i - V₀ t = (t.points i - O t) - v₀ t by simp [v₀]]
    have hv0 : ‖v₀ t‖ = R t := h0
    rw [@norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq, hi, hv0]
    ring
  rw [hgv, real_inner_smul_left, sum_inner]
  simp only [hterm]
  have hpos : 0 < ∑ i, ‖t.points i - V₀ t‖ ^ 2 := by
    apply Finset.sum_pos' (fun i _ => by positivity)
    refine ⟨1, Finset.mem_univ _, ?_⟩
    have hne : t.points 1 ≠ t.points 0 := fun h => by
      have := t.independent.injective h; exact absurd this (by decide)
    have : t.points 1 - V₀ t ≠ 0 := sub_ne_zero.mpr hne
    positivity
  rw [← Finset.mul_sum]
  nlinarith

end GeometryResearch.SevenPoint
