module

public import GeometryResearch.Orthocentric.Defs
public import GeometryResearch.Orthocentric.Model

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
  rw [Affine.Simplex.altitude_def, AffineSubspace.mem_inf_iff]
  refine ⟨?_, t.mongePoint_mem_affineSpan⟩
  rw [AffineSubspace.mem_mk', direction_affineSpan, Submodule.mem_orthogonal]
  intro x hx
  have := orth_face t ho i hx
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
  rw [vsub_eq_sub, show H t - t.points i = -(t.points i - H t) by abel, inner_neg_right,
    real_inner_comm, this, neg_zero]

/-- 论文第 2 节：⟪Vᵢ − H, Vⱼ − H⟫（i ≠ j）都等于同一个数 p。 -/
theorem inner_eq_p (ho : IsOrthocentric t) {i j : Fin 4} (hij : i ≠ j) :
    ⟪t.points i - H t, t.points j - H t⟫ = p t :=
  inner_pt_H t ho hij

/-- 论文 (2.1) 式：aᵢ = |HVᵢ|² − p。 -/
theorem a_eq (ho : IsOrthocentric t) (i : Fin 4) :
    a t i = ‖t.points i - H t‖ ^ 2 - p t := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hf : Hfoot t i ∈ affineSpan ℝ (t.points '' {i}ᶜ) :=
    t.altitudeFoot_mem_affineSpan_image_compl i
  have h0 := inner_face t ho i hj hf
  have h1 := inner_pt_H t ho (Ne.symm hj)
  rw [a, show H t - t.points i = -(t.points i - H t) by abel,
    show Hfoot t i - t.points i = (Hfoot t i - t.points j) + (t.points j - H t)
      - (t.points i - H t) by abel,
    inner_neg_left, inner_sub_right, inner_add_right, h0, h1, real_inner_self_eq_norm_sq]
  ring

/-- 论文第 2 节：极反演 ψ 把顶点 Vᵢ 映到高的垂足 Hᵢ。 -/
theorem ψ_point (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) (i : Fin 4) :
    ψ t (t.points i) = Hfoot t i := by
  set v := t.points i - H t with hvdef
  have hv0 : v ≠ 0 := sub_ne_zero.mpr (hH i).symm
  have hvv : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  set S := affineSpan ℝ (Set.range (t.faceOpposite i).points) with hS
  have hrange : Set.range (t.faceOpposite i).points = t.points '' {i}ᶜ :=
    t.range_faceOpposite_points i
  -- 面所在平面的方向恰好是 v 的正交补（三维空间里两个 2 维子空间，一个包含另一个）
  have hdir : S.direction = (ℝ ∙ v)ᗮ := by
    rw [direction_affineSpan]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hrange]; exact orth_face t ho i
    · have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
      rw [Submodule.finrank_orthogonal_span_singleton (n := 2) hv0,
        (t.faceOpposite i).independent.finrank_vectorSpan (n := 2) (by simp)]
  obtain ⟨j, hj⟩ := exists_ne i
  have hVj : t.points j ∈ S := by
    rw [hS, hrange]; exact mem_affineSpan ℝ ⟨j, hj, rfl⟩
  have hpj : ⟪v, t.points j - H t⟫ = p t := inner_pt_H t ho (Ne.symm hj)
  symm
  change (orthogonalProjection S (t.points i) : E3) = ψ t (t.points i)
  rw [coe_orthogonalProjection_eq_iff_mem]
  constructor
  · -- ψ(Vᵢ) 在面所在平面上：ψ(Vᵢ) − Vⱼ 与 v 垂直
    rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hVj, hdir,
      Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub, ψ, ← hvdef,
      show H t + (p t / ‖v‖ ^ 2) • v - t.points j = (p t / ‖v‖ ^ 2) • v - (t.points j - H t)
        by abel,
      inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hpj]
    field_simp
    ring
  · -- Vᵢ − ψ(Vᵢ) 是 v 的倍数，与平面垂直
    rw [hdir, Submodule.orthogonal_orthogonal, vsub_eq_sub, ψ, ← hvdef,
      show t.points i - (H t + (p t / ‖v‖ ^ 2) • v) = (1 - p t / ‖v‖ ^ 2) • v by
        rw [hvdef]; module]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

/-- `ofWeights` 给出的点，重心坐标与权重成比例：这保证 `isogonal`、`isotomic`
确实是「重心坐标为 (S₀²/x₀ : …)、(1/x₀ : …) 的点」。 -/
theorem bary_ofWeights (w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0) (i : Fin 4) :
    bary t (ofWeights t w) i = w i / ∑ j, w j := by
  have hsum : ∑ j, w j / ∑ j, w j = 1 := by rw [← Finset.sum_div, div_self hw]
  have hb : (⇑(basis t) : Fin 4 → E3) = t.points := rfl
  simp only [bary, ofWeights, AffineBasis.coords_apply]
  rw [← hb]
  exact (basis t).coord_apply_combination_of_mem (Finset.mem_univ i) hsum

/-- Fermat 点存在（所以定理 5 不是空的）。 -/
theorem exists_fermatPoint : ∃ F, IsFermatPoint t F := by
  have hc : Continuous (fun Y : E3 => ∑ i, dist Y (t.points i)) := by fun_prop
  have hlim : Filter.Tendsto (fun Y : E3 => ∑ i, dist Y (t.points i))
      (Filter.cocompact E3) Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun Y => Finset.single_le_sum (f := fun i => dist Y (t.points i))
        (fun i _ => dist_nonneg) (Finset.mem_univ 0))
      (tendsto_dist_right_cocompact_atTop (t.points 0))
  obtain ⟨F, hF⟩ := hc.exists_forall_le hlim
  exact ⟨F, hF⟩

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
  set S := facePlane t i with hS
  set N := (t.faceOpposite i).ninePointCircle.center
  set r9 := (t.faceOpposite i).ninePointCircle.radius
  have hN : N ∈ S := (t.faceOpposite i).ninePointCircle_center_mem_affineSpan
  -- n = Vᵢ − Hᵢ：Vᵢ 到面所在平面的垂线方向
  set n : E3 := t.points i - (orthogonalProjection S (t.points i) : E3) with hn
  have hnperp : n ∈ S.directionᗮ := by
    rw [hn, ← vsub_eq_sub]; exact vsub_orthogonalProjection_mem_direction_orthogonal S _
  have hn0 : n ≠ 0 := by
    intro h0
    have heq : t.points i = (orthogonalProjection S (t.points i) : E3) := sub_eq_zero.mp h0
    have hmem : t.points i ∈ S := heq ▸ (orthogonalProjection S (t.points i)).property
    exact t.points_notMem_affineSpan_faceOpposite i hmem
  have hnn : ‖n‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hn0)
  -- 平面上的点 X 满足 ⟪X − N, n⟫ = 0
  have hperp : ∀ X ∈ S, ⟪X - N, n⟫ = 0 := by
    intro X hX
    have hd : X -ᵥ N ∈ S.direction := AffineSubspace.vsub_mem_direction hX hN
    rw [← vsub_eq_sub]; exact Submodule.inner_right_of_mem_orthogonal hd hnperp
  have hVn : ⟪t.points i - N, n⟫ = ‖n‖ ^ 2 := by
    have hP : (orthogonalProjection S (t.points i) : E3) ∈ S :=
      (orthogonalProjection S (t.points i)).property
    rw [show t.points i - N = n + ((orthogonalProjection S (t.points i) : E3) - N) by
      rw [hn]; abel, inner_add_left, hperp _ hP, real_inner_self_eq_norm_sq, add_zero]
  set τ := (‖t.points i - N‖ ^ 2 - r9 ^ 2) / (2 * ‖n‖ ^ 2)
  set c : E3 := N + τ • n
  -- 球心 c 到点 X 的距离平方
  have hdist : ∀ X : E3, ‖X - c‖ ^ 2 = ‖X - N‖ ^ 2 - 2 * τ * ⟪X - N, n⟫ + τ ^ 2 * ‖n‖ ^ 2 := by
    intro X
    rw [show X - c = (X - N) - τ • n by simp [c]; abel, @norm_sub_sq_real, norm_smul,
      inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  refine ⟨⟨c, dist (t.points i) c⟩, rfl, fun X hX hX9 => ?_⟩
  rw [EuclideanGeometry.mem_sphere] at hX9 ⊢
  rw [dist_eq_norm, dist_eq_norm]
  have h1 := hdist X
  have h2 := hdist (t.points i)
  rw [hperp X hX] at h1
  rw [hVn] at h2
  rw [dist_eq_norm] at hX9
  change ‖X - N‖ = r9 at hX9
  have hτ : 2 * τ * ‖n‖ ^ 2 = ‖t.points i - N‖ ^ 2 - r9 ^ 2 := by
    simp only [τ]; field_simp
  have hsq : ‖X - c‖ ^ 2 = ‖t.points i - c‖ ^ 2 := by
    rw [h1, h2, hX9]; linarith
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

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
