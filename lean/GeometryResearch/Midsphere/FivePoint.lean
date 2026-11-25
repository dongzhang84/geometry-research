module

public import GeometryResearch.Midsphere.Concyclic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# 定理 5（五点球）的证明

T₁₂ 与两个 Feuerbach 点都在棱切球 μ 上。设 Π 为过这三点的平面，ℓ 为它的仿射方程（由重心坐标值给出）。
所求的球取 μ 与 Π 生成的球束中的 pow_μ + λℓ = 0。弦中点 N 对 μ 的幂为 −(半弦长)²，
所以条件化为 |T₀₂T₁₃|²(ℓ(T₀₁) + ℓ(T₂₃)) = |T₀₁T₂₃|²(ℓ(T₀₂) + ℓ(T₁₃))。
r₁ = r₂ 时三点重合为 T₁₂，五点只剩三个，自然共面。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary basis)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 仿射函数可以写成 ⟪c, X − V⟫ + κ。 -/
theorem affine_repr (f : E3 →ᵃ[ℝ] ℝ) (V : E3) :
    ∃ c : E3, ∃ κ : ℝ, ∀ X, f X = ⟪c, X - V⟫ + κ := by
  refine ⟨(InnerProductSpace.toDual ℝ E3).symm (LinearMap.toContinuousLinearMap f.linear), f V,
    fun X => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap', ← vsub_eq_sub,
    AffineMap.linear_apply_vsub, vsub_eq_sub]
  ring

/-- 若点集满足 |XV|² + ⟪c, X − W⟫ + κ = 0，则共球。 -/
theorem cosph_of {S : Set E3} (V W c : E3) (κ : ℝ)
    (h : ∀ X ∈ S, dist X V ^ 2 + (⟪c, X - W⟫ + κ) = 0) : Cospherical S := by
  refine ⟨V - (1 / 2 : ℝ) • c, √(‖c‖ ^ 2 / 4 - (⟪c, V - W⟫ + κ)), fun X hX => ?_⟩
  have hX' := h X hX
  rw [dist_eq_norm, show X - W = (X - V) + (V - W) by abel, inner_add_right] at hX'
  have e : dist X (V - (1 / 2 : ℝ) • c) ^ 2 = ‖c‖ ^ 2 / 4 - (⟪c, V - W⟫ + κ) := by
    rw [dist_eq_norm, show X - (V - (1 / 2 : ℝ) • c) = (X - V) + (1 / 2 : ℝ) • c by abel,
      norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    norm_num
    linarith
  rw [← e, Real.sqrt_sq dist_nonneg]

/-- 若点集落在平面 ⟪c, X − V⟫ + κ = 0 上（c ≠ 0），则共面。 -/
theorem coplanar_of_inner {S : Set E3} (c V : E3) (κ : ℝ) (hc : c ≠ 0)
    (h : ∀ X ∈ S, ⟪c, X - V⟫ + κ = 0) : Coplanar ℝ S := by
  rw [coplanar_iff_finrank_le_two]
  have hle : vectorSpan ℝ S ≤ (ℝ ∙ c)ᗮ := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro x ⟨X, hX, Y, hY, rfl⟩
    change X -ᵥ Y ∈ (ℝ ∙ c)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub,
      show X - Y = (X - V) - (Y - V) by abel, inner_sub_right]
    linarith [h X hX, h Y hY]
  have : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  calc Module.finrank ℝ (vectorSpan ℝ S) ≤ Module.finrank ℝ (ℝ ∙ c)ᗮ := Submodule.finrank_mono hle
    _ = 2 := Submodule.finrank_orthogonal_span_singleton hc

variable (t) in
/-- 由顶点上的值 Lᵢ 给出的仿射函数 X ↦ Σ Lᵢ·xᵢ（x 为 X 的重心坐标）。 -/
def ellV (Lv : Fin 4 → ℝ) (X : E3) : ℝ := ∑ i, Lv i * (basis t).coord i X

theorem ellV_repr (Lv : Fin 4 → ℝ) (V : E3) :
    ∃ c : E3, ∃ κ : ℝ, ∀ X, ellV t Lv X = ⟪c, X - V⟫ + κ := by
  choose c κ hc using fun i => affine_repr ((basis t).coord i) V
  refine ⟨∑ i, Lv i • c i, ∑ i, Lv i * κ i, fun X => ?_⟩
  simp only [ellV, hc, sum_inner, real_inner_smul_left, mul_add, Finset.sum_add_distrib]

theorem ellV_ofW (Lv w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0) :
    ellV t Lv (ofWeights t w) = ∑ i, Lv i * (w i / ∑ j, w j) := by
  simp only [ellV]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← GeometryResearch.Orthocentric.bary_ofWeights' t w hw i]
  rfl

theorem ellV_vertex (Lv : Fin 4 → ℝ) (j : Fin 4) : ellV t Lv (t.points j) = Lv j := by
  have hb : (⇑(basis t) : Fin 4 → E3) = t.points := rfl
  simp only [ellV, ← hb]
  rw [Finset.sum_eq_single j (fun i _ hij => by rw [AffineBasis.coord_apply_ne _ hij, mul_zero])
    (by simp), AffineBasis.coord_apply_eq, mul_one]

theorem ellV_mid (Lv : Fin 4 → ℝ) (A B : E3) :
    ellV t Lv (midpoint ℝ A B) = (ellV t Lv A + ellV t Lv B) / 2 := by
  obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) Lv A
  rw [hc, hc, hc, midpoint_eq_smul_add, show (⅟2 : ℝ) • (A + B) - A = (1 / 2 : ℝ) • (B - A) by
    rw [invOf_eq_inv]; module, real_inner_smul_right, sub_self, inner_zero_right]
  ring

/-- 两点都在球上，则中点的幂为 −(半弦长)²。 -/
theorem mid_power {A B C : E3} {ρs : ℝ} (hA : dist A C = ρs) (hB : dist B C = ρs) :
    dist (midpoint ℝ A B) C ^ 2 = ρs ^ 2 - dist A B ^ 2 / 4 := by
  have hB' : ‖B - C‖ ^ 2 = ‖A - C‖ ^ 2 := by rw [← dist_eq_norm, ← dist_eq_norm, hA, hB]
  have hA' : ‖A - C‖ ^ 2 = ρs ^ 2 := by rw [← dist_eq_norm, hA]
  rw [dist_eq_norm, dist_eq_norm, midpoint_eq_smul_add, invOf_eq_inv,
    show (2⁻¹ : ℝ) • (A + B) - C = (1 / 2 : ℝ) • ((A - C) + (B - C)) by module,
    show A - B = (A - C) - (B - C) by abel]
  generalize A - C = u at hA' hB' ⊢
  generalize B - C = v at hA' hB' ⊢
  rw [norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real, hB', hA', Real.norm_eq_abs, sq_abs]
  ring

/-- 面 012 的 Feuerbach 点的论文权重 (r₀(r₁ − r₂)² : r₁(r₀ − r₂)² : r₂(r₀ − r₁)² : 0)。 -/
def aW (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![r 0 * (r 1 - r 2) ^ 2, r 1 * (r 0 - r 2) ^ 2, r 2 * (r 0 - r 1) ^ 2, 0]

/-- 面 123 的 Feuerbach 点的论文权重。 -/
def bW (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![0, r 1 * (r 2 - r 3) ^ 2, r 2 * (r 1 - r 3) ^ 2, r 3 * (r 1 - r 2) ^ 2]

theorem X11_3 (hfb : IsFourBall t r) : X11 t r 3 = ofWeights t (aW r) := by
  have h3 := (hfb.1 3).ne'
  simp only [X11]; congr 1; funext i
  fin_cases i <;> simp [aW, Fin.sum_univ_four, Fin.prod_univ_four] <;> field_simp <;> ring

theorem X11_0 (hfb : IsFourBall t r) : X11 t r 0 = ofWeights t (bW r) := by
  have h0 := (hfb.1 0).ne'
  simp only [X11]; congr 1; funext i
  fin_cases i <;> simp [bW, Fin.sum_univ_four, Fin.prod_univ_four] <;> field_simp <;> ring

theorem tri_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : ¬ (x = y ∧ y = z)) :
    0 < x * (y - z) ^ 2 + y * (x - z) ^ 2 + z * (x - y) ^ 2 := by
  have t1 := mul_nonneg hx.le (sq_nonneg (y - z))
  have t2 := mul_nonneg hy.le (sq_nonneg (x - z))
  have t3 := mul_nonneg hz.le (sq_nonneg (x - y))
  by_contra hc
  have e1 : x * (y - z) ^ 2 = 0 := by linarith
  have e3 : z * (x - y) ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp e1 with h1 | h1; · linarith
  rcases mul_eq_zero.mp e3 with h3 | h3; · linarith
  exact h ⟨by nlinarith [sq_nonneg (x - y)], by nlinarith [sq_nonneg (y - z)]⟩

theorem aW_sum (hfb : IsFourBall t r) (h : ¬ (r 0 = r 1 ∧ r 1 = r 2)) : 0 < ∑ j, aW r j := by
  have hr := hfb.1
  have := tri_pos (hr 0) (hr 1) (hr 2) h
  simp only [aW, Fin.sum_univ_four]; simp; linarith

theorem bW_sum (hfb : IsFourBall t r) (h : ¬ (r 1 = r 2 ∧ r 2 = r 3)) : 0 < ∑ j, bW r j := by
  have hr := hfb.1
  have := tri_pos (hr 1) (hr 2) (hr 3) h
  simp only [bW, Fin.sum_univ_four]; simp; linarith

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem aW_on (hfb : IsFourBall t r) (h : ¬ (r 0 = r 1 ∧ r 1 = r 2)) :
    dist (ofWeights t (aW r)) (M t r) ^ 2 = ρ t r ^ 2 := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hs := (aW_sum hfb h).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [dρ hfb, M_comb, dist_ofW' hfb hs (by rw [hsumM]; positivity), hsumM]
  generalize hS : ∑ j, aW r j = S at hs ⊢
  have hS' : S = r 0 * (r 1 - r 2) ^ 2 + r 1 * (r 0 - r 2) ^ 2 + r 2 * (r 0 - r 1) ^ 2 := by
    rw [← hS]; simp [aW, Fin.sum_univ_four]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, aW, e, sInv]
  simp
  field_simp
  rw [← hDv, hS']
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem bW_on (hfb : IsFourBall t r) (h : ¬ (r 1 = r 2 ∧ r 2 = r 3)) :
    dist (ofWeights t (bW r)) (M t r) ^ 2 = ρ t r ^ 2 := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hs := (bW_sum hfb h).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [dρ hfb, M_comb, dist_ofW' hfb hs (by rw [hsumM]; positivity), hsumM]
  generalize hS : ∑ j, bW r j = S at hs ⊢
  have hS' : S = r 1 * (r 2 - r 3) ^ 2 + r 2 * (r 1 - r 3) ^ 2 + r 3 * (r 1 - r 2) ^ 2 := by
    rw [← hS]; simp [bW, Fin.sum_univ_four]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, bW, e, sInv]
  simp
  field_simp
  rw [← hDv, hS']
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es4]
  field_simp
  ring

/-- 平面 Π（过 T₁₂ 与两个 Feuerbach 点）在顶点上的值。 -/
def Lv (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![bW r 3 * (aW r 2 * r 2 - aW r 1 * r 1), aW r 0 * bW r 3 * r 1, -(aW r 0 * bW r 3 * r 2),
    aW r 0 * (bW r 2 * r 2 - bW r 1 * r 1)]

theorem ellV_T (hfb : IsFourBall t r) (Lw : Fin 4 → ℝ) {a b : Fin 4} (hab : a ≠ b) :
    ellV t Lw (T t r a b) = (Lw a * r b + Lw b * r a) / (r a + r b) := by
  have hr := hfb.1
  have hab' : r a + r b ≠ 0 := (add_pos (hr a) (hr b)).ne'
  rw [T, lineMap_eq_ofW hab, ellV_ofW _ _ (by rw [tw_sum hab]; exact one_ne_zero), tw_sum hab]
  simp only [tw, div_one, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp; ring

theorem ell_T12 (hfb : IsFourBall t r) : ellV t (Lv r) (T t r 1 2) = 0 := by
  rw [ellV_T hfb _ (by decide), div_eq_zero_iff]; left; simp [Lv]; ring

theorem ell_a (hfb : IsFourBall t r) (h : ¬ (r 0 = r 1 ∧ r 1 = r 2)) :
    ellV t (Lv r) (ofWeights t (aW r)) = 0 := by
  rw [ellV_ofW _ _ (aW_sum hfb h).ne']
  have : aW r 3 = 0 := rfl
  simp only [Fin.sum_univ_four, Lv, this]; simp; ring

theorem ell_b (hfb : IsFourBall t r) (h : ¬ (r 1 = r 2 ∧ r 2 = r 3)) :
    ellV t (Lv r) (ofWeights t (bW r)) = 0 := by
  rw [ellV_ofW _ _ (bW_sum hfb h).ne']
  have : bW r 0 = 0 := rfl
  simp only [Fin.sum_univ_four, Lv, this]; simp; ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
/-- 定理 5 的代数核心：|T₀₂T₁₃|²(ℓ(T₀₁) + ℓ(T₂₃)) = |T₀₁T₂₃|²(ℓ(T₀₂) + ℓ(T₁₃))。 -/
theorem key5 (hfb : IsFourBall t r) :
    dist (T t r 0 2) (T t r 1 3) ^ 2 * (ellV t (Lv r) (T t r 0 1) + ellV t (Lv r) (T t r 2 3)) =
      dist (T t r 0 1) (T t r 2 3) ^ 2 *
        (ellV t (Lv r) (T t r 0 2) + ellV t (Lv r) (T t r 1 3)) := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have p0 := hr 0; have p1 := hr 1; have p2 := hr 2; have p3 := hr 3
  rw [ellV_T hfb _ (by decide), ellV_T hfb _ (by decide), ellV_T hfb _ (by decide),
    ellV_T hfb _ (by decide)]
  simp only [T]
  rw [lineMap_eq_ofW (by decide), lineMap_eq_ofW (by decide), lineMap_eq_ofW (by decide),
    lineMap_eq_ofW (by decide), dist_ofW hfb (tw_sum (by decide) _) (tw_sum (by decide) _),
    dist_ofW hfb (tw_sum (by decide) _) (tw_sum (by decide) _)]
  simp only [Fin.sum_univ_four, tw, e, Lv, aW, bW]
  simp
  field_simp
  ring

theorem T_on (hfb : IsFourBall t r) {a b : Fin 4} (hab : a ≠ b) :
    dist (T t r a b) (M t r) = ρ t r :=
  (M_tangent' hfb hab).1

theorem ofW_on {x : Fin 4 → ℝ} (h : dist (ofWeights t x) (M t r) ^ 2 = ρ t r ^ 2) :
    dist (ofWeights t x) (M t r) = ρ t r :=
  (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp h

/-- r₁ = r₂ 时 Feuerbach 点与 T₁₂ 重合。 -/
theorem ofW_eq_T12 (hfb : IsFourBall t r) {x : Fin 4 → ℝ} (k : ℝ) (hk : k ≠ 0)
    (hx : x = fun i => k * tw 1 2 (1 / 2) i) (h12 : r 1 = r 2) : ofWeights t x = T t r 1 2 := by
  have h1 := (hfb.1 1).ne'
  rw [hx, ofW_smul t k hk, T, lineMap_eq_ofW (by decide), ← h12,
    show r 1 / (r 1 + r 1) = 1 / 2 by field_simp; ring]

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in -- 组装
/-- 定理 5 的证明。 -/
theorem five_main (hfb : IsFourBall t r) (h012 : ¬ (r 0 = r 1 ∧ r 1 = r 2))
    (h123 : ¬ (r 1 = r 2 ∧ r 2 = r 3)) :
    MCospherical ({T t r 1 2, N t r 0 1 2 3, N t r 0 2 1 3, X11 t r 3, X11 t r 0} : Set E3) := by
  have hr := hfb.1
  rw [X11_3 hfb, X11_0 hfb]
  by_cases h12 : r 1 = r 2
  · right
    have h01 : r 0 ≠ r 1 := fun h => h012 ⟨h, h12⟩
    have h13 : r 1 ≠ r 3 := fun h => h123 ⟨h12, h12 ▸ h⟩
    have ea : ofWeights t (aW r) = T t r 1 2 :=
      ofW_eq_T12 hfb (2 * r 1 * (r 0 - r 1) ^ 2)
        (mul_ne_zero (mul_ne_zero two_ne_zero (hr 1).ne') (pow_ne_zero 2 (sub_ne_zero.mpr h01)))
        (by funext i; fin_cases i <;> simp [aW, tw, ← h12] <;> ring) h12
    have eb : ofWeights t (bW r) = T t r 1 2 :=
      ofW_eq_T12 hfb (2 * r 1 * (r 1 - r 3) ^ 2)
        (mul_ne_zero (mul_ne_zero two_ne_zero (hr 1).ne') (pow_ne_zero 2 (sub_ne_zero.mpr h13)))
        (by funext i; fin_cases i <;> simp [bW, tw, ← h12] <;> ring) h12
    rw [ea, eb]
    refine (coplanar_triple ℝ (T t r 1 2) (N t r 0 1 2 3) (N t r 0 2 1 3)).subset ?_
    intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto
  -- 一般情形
  have ha0 : aW r 0 ≠ 0 := by
    simp only [aW]; simp
    exact ⟨(hr 0).ne', sub_ne_zero.mpr h12⟩
  have hb3 : bW r 3 ≠ 0 := by
    simp only [bW]; simp
    exact ⟨(hr 3).ne', sub_ne_zero.mpr h12⟩
  obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) (Lv r) (M t r)
  have hc0 : c ≠ 0 := by
    rintro rfl
    have e1 := hc (t.points 1); have e2 := hc (t.points 2)
    rw [ellV_vertex, inner_zero_left] at e1 e2
    have : Lv r 1 - Lv r 2 = aW r 0 * bW r 3 * (r 1 + r 2) := by simp [Lv]; ring
    rw [e1, e2, sub_self] at this
    exact mul_ne_zero (mul_ne_zero ha0 hb3) (add_pos (hr 1) (hr 2)).ne' this.symm
  have hA := ofW_on (aW_on hfb h012)
  have hB := ofW_on (bW_on hfb h123)
  have hT12 := T_on hfb (show (1 : Fin 4) ≠ 2 by decide)
  have pN1 := mid_power (T_on hfb (show (0 : Fin 4) ≠ 1 by decide))
    (T_on hfb (show (2 : Fin 4) ≠ 3 by decide))
  have pN2 := mid_power (T_on hfb (show (0 : Fin 4) ≠ 2 by decide))
    (T_on hfb (show (1 : Fin 4) ≠ 3 by decide))
  have lN1 := ellV_mid (t := t) (Lv r) (T t r 0 1) (T t r 2 3)
  have lN2 := ellV_mid (t := t) (Lv r) (T t r 0 2) (T t r 1 3)
  have hkey := key5 hfb
  have lT12 := ell_T12 hfb
  have lA := ell_a hfb h012
  have lB := ell_b hfb h123
  -- |T₀₁T₂₃| ≠ 0
  have hd1 : dist (T t r 0 1) (T t r 2 3) ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 (dist_ne_zero.mpr fun h => ?_)
    have e1 := ellV_T (t := t) hfb ![1, 0, 0, 0] (show (0 : Fin 4) ≠ 1 by decide)
    have e2 := ellV_T (t := t) hfb ![1, 0, 0, 0] (show (2 : Fin 4) ≠ 3 by decide)
    rw [h, e2] at e1
    simp at e1
    have := div_pos (hr 1) (add_pos (hr 0) (hr 1))
    linarith
  simp only [N] at *
  set N1 := midpoint ℝ (T t r 0 1) (T t r 2 3)
  set N2 := midpoint ℝ (T t r 0 2) (T t r 1 3)
  set d1 := dist (T t r 0 1) (T t r 2 3) ^ 2
  set d2 := dist (T t r 0 2) (T t r 1 3) ^ 2
  by_cases hm : ellV t (Lv r) N1 = 0
  · right
    have hm2 : ellV t (Lv r) N2 = 0 := by
      have : d1 * ellV t (Lv r) N2 = 0 := by rw [lN2]; rw [lN1] at hm; nlinarith
      exact (mul_eq_zero.mp this).resolve_left hd1
    refine coplanar_of_inner c (M t r) κ hc0 (fun X hX => ?_)
    rw [← hc]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    exacts [lT12, hm, hm2, lA, lB]
  · left
    refine cosph_of (M t r) (M t r) ((d1 / (4 * ellV t (Lv r) N1)) • c)
      ((d1 / (4 * ellV t (Lv r) N1)) * κ - ρ t r ^ 2) (fun X hX => ?_)
    have hX' : dist X (M t r) ^ 2 + (⟪(d1 / (4 * ellV t (Lv r) N1)) • c, X - M t r⟫ +
        ((d1 / (4 * ellV t (Lv r) N1)) * κ - ρ t r ^ 2)) =
        dist X (M t r) ^ 2 - ρ t r ^ 2 + (d1 / (4 * ellV t (Lv r) N1)) * ellV t (Lv r) X := by
      rw [hc X, real_inner_smul_left]; ring
    rw [hX']
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [hT12, lT12]; ring
    · rw [pN1]; field_simp; ring
    · rw [pN2, lN2]; rw [lN1] at hm ⊢
      have hm' : ellV t (Lv r) (T t r 0 1) + ellV t (Lv r) (T t r 2 3) ≠ 0 := by
        intro h; apply hm; rw [h, zero_div]
      field_simp
      linear_combination (-1 : ℝ) * hkey
    · rw [hA, lA]; ring
    · rw [hB, lB]; ring

end GeometryResearch.Midsphere
