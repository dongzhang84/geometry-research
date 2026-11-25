module

public import GeometryResearch.Midsphere.Orth

/-!
# 定理 8（位似引理）的证明

* 共面（综合论证）：由 Menelaus，E 在直线 TᵢₖTᵢₗ 上；Z 在弦 TᵢₖTⱼₗ 上，N₁ 是它的中点，
  Z ≠ N₁（三点不共线），所以 Tᵢₖ 在直线 ZN₁ 上；同理 Tᵢₗ 在直线 ZN₂ 上。
* 幂：平面内一点 P = Σλₐ Aₐ（Σλ = 1）对三角形外接圆的幂为 −Σ_{a<b} λₐλ_b |AₐA_b|²；
  距离由重心坐标公式 |XY|² = −½ ΣΣ uₐu_b e_ab 给出，化为切长的有理恒等式。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 平面内一点对三角形外接圆的幂（重心坐标形式）。 -/
theorem power_triangle (Δ : Affine.Triangle ℝ E3) (a b : ℝ) :
    Δ.circumsphere.power (Δ.points 0 + a • (Δ.points 1 - Δ.points 0) +
        b • (Δ.points 2 - Δ.points 0)) =
      -((1 - a - b) * a * dist (Δ.points 0) (Δ.points 1) ^ 2 +
        (1 - a - b) * b * dist (Δ.points 0) (Δ.points 2) ^ 2 +
        a * b * dist (Δ.points 1) (Δ.points 2) ^ 2) := by
  set C := Δ.circumcenter
  set R := Δ.circumradius
  have hR : ∀ m, ‖Δ.points m - C‖ = R := fun m => by
    rw [← dist_eq_norm]; exact Δ.dist_circumcenter_eq_circumradius m
  have hd : ∀ m m', dist (Δ.points m) (Δ.points m') ^ 2 =
      2 * R ^ 2 - 2 * ⟪Δ.points m - C, Δ.points m' - C⟫ := by
    intro m m'
    rw [dist_eq_norm, show Δ.points m - Δ.points m' = (Δ.points m - C) - (Δ.points m' - C) by
      abel, @norm_sub_sq_real, hR, hR]
    ring
  rw [Sphere.power, Affine.Simplex.circumsphere_center, Affine.Simplex.circumsphere_radius,
    hd, hd, hd, dist_eq_norm,
    show Δ.points 0 + a • (Δ.points 1 - Δ.points 0) + b • (Δ.points 2 - Δ.points 0) - C =
      (1 - a - b) • (Δ.points 0 - C) + a • (Δ.points 1 - C) + b • (Δ.points 2 - C) by module]
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (Δ.points 0 - C) (Δ.points 1 - C),
    real_inner_comm (Δ.points 0 - C) (Δ.points 2 - C),
    real_inner_comm (Δ.points 1 - C) (Δ.points 2 - C)]
  simp only [real_inner_self_eq_norm_sq, hR]
  ring

/-- 两点权重函数 (1 − c 在 a，c 在 b)。 -/
def tw (a b : Fin 4) (c : ℝ) : Fin 4 → ℝ :=
  fun m => (if m = a then 1 - c else 0) + (if m = b then c else 0)

theorem tw_sum {a b : Fin 4} (_hab : a ≠ b) (c : ℝ) : ∑ m, tw a b c m = 1 := by
  simp only [tw, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]; ring

theorem L_tw {a b : Fin 4} (c : ℝ) :
    L t (tw a b c) = (1 - c) • w t a + c • w t b := by
  simp only [L, tw, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem lineMap_eq_ofW {a b : Fin 4} (hab : a ≠ b) (c : ℝ) :
    AffineMap.lineMap (t.points a) (t.points b) c = ofWeights t (tw a b c) := by
  have h := ofW_sub_V0 t (tw a b c) (by rw [tw_sum hab]; exact one_ne_zero)
  rw [tw_sum hab, div_one, one_smul, L_tw] at h
  rw [← sub_left_inj (a := t.points 0), h, AffineMap.lineMap_apply_module]
  simp only [w]; module

theorem mid_ofW {x y : Fin 4 → ℝ} (hx : ∑ m, x m = 1) (hy : ∑ m, y m = 1) :
    midpoint ℝ (ofWeights t x) (ofWeights t y) = ofWeights t (fun m => (x m + y m) / 2) := by
  have hs : ∑ m, (x m + y m) / 2 = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hx, hy]; norm_num
  have ex := ofW_sub_V0 t x (by rw [hx]; exact one_ne_zero)
  have ey := ofW_sub_V0 t y (by rw [hy]; exact one_ne_zero)
  have exy := ofW_sub_V0 t _ (by rw [hs]; exact one_ne_zero)
  rw [hx, div_one, one_smul] at ex; rw [hy, div_one, one_smul] at ey
  rw [hs, div_one, one_smul] at exy
  rw [← sub_left_inj (a := t.points 0), exy, midpoint_eq_smul_add, invOf_eq_inv,
    show (2⁻¹ : ℝ) • (ofWeights t x + ofWeights t y) - t.points 0 =
      (2⁻¹ : ℝ) • ((ofWeights t x - t.points 0) + (ofWeights t y - t.points 0)) by module, ex, ey]
  simp only [L_four]; module

set_option linter.flexible false in
/-- 重心坐标的距离公式 |XY|² = −½ ΣΣ uₐu_b e_ab（u = x − y，Σx = Σy = 1）。 -/
theorem dist_ofW (hfb : IsFourBall t r) {x y : Fin 4 → ℝ} (hx : ∑ m, x m = 1)
    (hy : ∑ m, y m = 1) :
    dist (ofWeights t x) (ofWeights t y) ^ 2 =
      -(1 / 2) * ∑ a, ∑ b, (x a - y a) * (x b - y b) * e r a b := by
  have ex := ofW_sub_V0 t x (by rw [hx]; exact one_ne_zero)
  have ey := ofW_sub_V0 t y (by rw [hy]; exact one_ne_zero)
  rw [hx, div_one, one_smul] at ex; rw [hy, div_one, one_smul] at ey
  rw [dist_eq_norm, show ofWeights t x - ofWeights t y =
    (ofWeights t x - t.points 0) - (ofWeights t y - t.points 0) by abel, ex, ey,
    ← real_inner_self_eq_norm_sq]
  rw [Fin.sum_univ_four] at hx hy
  have hx0 : x 0 = 1 - x 1 - x 2 - x 3 := by linarith
  have hy0 : y 0 = 1 - y 1 - y 2 - y 3 := by linarith
  rw [show L t x - L t y = L t (fun m => x m - y m) by rw [L_four, L_four, L_four]; module,
    inner_L hfb]
  simp only [Fin.sum_univ_three, Fin.sum_univ_four, g, e]
  simp
  rw [hx0, hy0]
  ring

theorem lineMap_half (a b : E3) : AffineMap.lineMap a b (1 / 2 : ℝ) = midpoint ℝ a b := by
  rw [AffineMap.lineMap_apply_module, midpoint_eq_smul_add, invOf_eq_inv]; module

/-- 弦上一点 Z = T + λ(T′ − T)，N 为中点且 Z ≠ N，则 T = Z + (−λ/(1/2 − λ))(N − Z)。 -/
theorem T_on_ZN {T₁ T₂ Zp : E3} {lam : ℝ} (hZ : AffineMap.lineMap T₁ T₂ lam = Zp)
    (hne : Zp ≠ midpoint ℝ T₁ T₂) :
    T₁ = Zp + (-lam / (1 / 2 - lam)) • (midpoint ℝ T₁ T₂ - Zp) := by
  have hl : 1 / 2 - lam ≠ 0 := by
    intro h; apply hne; rw [← hZ, show lam = 1 / 2 by linarith, lineMap_half]
  rw [← hZ, AffineMap.lineMap_apply_module, midpoint_eq_smul_add, invOf_eq_inv]
  have : (-lam / (1 / 2 - lam)) * (1 / 2 - lam) = -lam := div_mul_cancel₀ _ hl
  rw [show (1 - lam) • T₁ + lam • T₂ + (-lam / (1 / 2 - lam)) • ((2⁻¹ : ℝ) • (T₁ + T₂) -
      ((1 - lam) • T₁ + lam • T₂)) = (1 - lam) • T₁ + lam • T₂ +
      ((-lam / (1 / 2 - lam)) * (1 / 2 - lam)) • (T₂ - T₁) by module, this]
  module

set_option maxHeartbeats 4000000 in -- 最后一步对很大的有理式做 field_simp
/-- 定理 8 的证明。 -/
theorem homothety_main (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hrkl : r k ≠ r l)
    (hΓ : AffineIndependent ℝ ![Z t r, N t r i k j l, N t r i l j k]) :
    Eext t r k l ∈ affineSpan ℝ {Z t r, N t r i k j l, N t r i l j k} ∧
      (⟨_, hΓ⟩ : Affine.Triangle ℝ E3).circumsphere.power (Eext t r k l) =
        r l / r k * (ball t r k).power (Eext t r k l) := by
  have hr := hfb.1
  have hZ1 := Z_lineMap hfb hik hij hil (Ne.symm hjk) hkl hjl
  have hZ2 := Z_lineMap hfb hil hij hik (Ne.symm hjl) (Ne.symm hkl) hjk
  have hZN1 : Z t r ≠ N t r i k j l := fun h => by
    have := hΓ.injective.ne (show (0 : Fin 3) ≠ 1 by decide); exact this (by simpa using h)
  have hZN2 : Z t r ≠ N t r i l j k := fun h => by
    have := hΓ.injective.ne (show (0 : Fin 3) ≠ 2 by decide); exact this (by simpa using h)
  set lm1 := (1 / r j + 1 / r l) / sInv r
  set lm2 := (1 / r j + 1 / r k) / sInv r
  have eT1 := T_on_ZN hZ1 hZN1
  have eT2 := T_on_ZN hZ2 hZN2
  set N1 := N t r i k j l
  set N2 := N t r i l j k
  -- Menelaus：E = (1 − ν)Tᵢₖ + ν Tᵢₗ
  set c := -(r k) / (r l - r k)
  set cik := r i / (r i + r k)
  set cil := r i / (r i + r l)
  set ν := c / cil
  have pi := hr i; have pk := hr k; have pl := hr l
  have hkl' : r l - r k ≠ 0 := sub_ne_zero.mpr (Ne.symm hrkl)
  have hMen : Eext t r k l = (1 - ν) • T t r i k + ν • T t r i l := by
    have f1 : (1 - ν) * cik = 1 - c := by
      simp only [ν, c, cil, cik]; field_simp; ring
    have f2 : ν * cil = c := div_mul_cancel₀ c (by simp only [cil]; positivity)
    rw [Eext, T, T, AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module,
      AffineMap.lineMap_apply_module]
    rw [show (1 - ν) • ((1 - r i / (r i + r k)) • t.points i + (r i / (r i + r k)) • t.points k) +
        ν • ((1 - r i / (r i + r l)) • t.points i + (r i / (r i + r l)) • t.points l) =
        (1 - (1 - ν) * cik - ν * cil) • t.points i + ((1 - ν) * cik) • t.points k +
          (ν * cil) • t.points l by simp only [cik, cil]; module, f1, f2]
    simp only [c]; module
  set a := (1 - ν) * (-lm1 / (1 / 2 - lm1))
  set b := ν * (-lm2 / (1 / 2 - lm2))
  have hE : Eext t r k l = Z t r + a • (N1 - Z t r) + b • (N2 - Z t r) := by
    rw [hMen, eT1, eT2]
    simp only [a, b, N1, N2, N]
    module
  refine ⟨?_, ?_⟩
  · rw [hE]
    have hmem : ∀ X ∈ ({Z t r, N1, N2} : Set E3), X ∈ affineSpan ℝ {Z t r, N1, N2} :=
      fun X hX => mem_affineSpan ℝ hX
    have hZm := hmem (Z t r) (by simp)
    have hv : a • (N1 - Z t r) + b • (N2 - Z t r) ∈ (affineSpan ℝ {Z t r, N1, N2}).direction := by
      rw [direction_affineSpan]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ (by simp) (by simp)))
        (Submodule.smul_mem _ _ (vsub_mem_vectorSpan ℝ (by simp) (by simp)))
    have := AffineSubspace.vadd_mem_of_mem_direction hv hZm
    rw [vadd_eq_add] at this
    rw [show Z t r + a • (N1 - Z t r) + b • (N2 - Z t r) =
      a • (N1 - Z t r) + b • (N2 - Z t r) + Z t r by abel]
    exact this
  · -- 幂：三角形外接圆的重心坐标公式 + 重心坐标距离公式
    have hRHS : (ball t r k).power (Eext t r k l) = c ^ 2 * (r k + r l) ^ 2 - r k ^ 2 := by
      rw [Sphere.power, ball, Eext, dist_lineMap_left, hfb.2 k l hkl, Real.norm_eq_abs, mul_pow,
        sq_abs]
    rw [hRHS]
    set Δ : Affine.Triangle ℝ E3 := ⟨_, hΓ⟩
    have h0 : Δ.points 0 = Z t r := rfl
    have h1 : Δ.points 1 = N1 := rfl
    have h2 : Δ.points 2 = N2 := rfl
    rw [hE, ← h0, ← h1, ← h2, power_triangle, h0, h1, h2]
    -- 各点的重心坐标
    have hs := (sInv_pos hfb).ne'
    have hzs : ∑ m, (1 / sInv r) * (1 / r m) = 1 := by
      rw [← Finset.mul_sum]; exact one_div_mul_cancel hs
    have hZw : Z t r = ofWeights t (fun m => (1 / sInv r) * (1 / r m)) :=
      (ofW_smul t _ (one_div_ne_zero hs) _).symm
    have hTw : ∀ {a b : Fin 4}, a ≠ b → T t r a b = ofWeights t (tw a b (r a / (r a + r b))) :=
      fun hab => lineMap_eq_ofW hab _
    have hN1 : N1 = ofWeights t (fun m => (tw i k (r i / (r i + r k)) m +
        tw j l (r j / (r j + r l)) m) / 2) := by
      simp only [N1, N, hTw hik, hTw hjl]; exact mid_ofW (tw_sum hik _) (tw_sum hjl _)
    have hN2 : N2 = ofWeights t (fun m => (tw i l (r i / (r i + r l)) m +
        tw j k (r j / (r j + r k)) m) / 2) := by
      simp only [N2, N, hTw hil, hTw hjk]; exact mid_ofW (tw_sum hil _) (tw_sum hjk _)
    have hn1s : ∑ m, (tw i k (r i / (r i + r k)) m + tw j l (r j / (r j + r l)) m) / 2 = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, tw_sum hik, tw_sum hjl]; norm_num
    have hn2s : ∑ m, (tw i l (r i / (r i + r l)) m + tw j k (r j / (r j + r k)) m) / 2 = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, tw_sum hil, tw_sum hjk]; norm_num
    rw [hZw, hN1, hN2, dist_ofW hfb hzs hn1s, dist_ofW hfb hzs hn2s, dist_ofW hfb hn1s hn2s]
    have hl1 : (1 : ℝ) / 2 - lm1 ≠ 0 := by
      intro h; apply hZN1; rw [← hZ1, show lm1 = 1 / 2 by linarith, lineMap_half]; rfl
    have hl2 : (1 : ℝ) / 2 - lm2 ≠ 0 := by
      intro h; apply hZN2; rw [← hZ2, show lm2 = 1 / 2 by linarith, lineMap_half]; rfl
    have hsum4 : ∀ f : Fin 4 → ℝ, ∑ m, f m = f i + f j + f k + f l := fun f => by
      rw [Fin.sum_univ_four]
      exact (GeometryResearch.Orthocentric.sum_perm f hij hik hil hjk hjl hkl).symm
    have hsI : sInv r = 1 / r i + 1 / r j + 1 / r k + 1 / r l := by rw [sInv, hsum4]
    simp only [a, b, ν, c, cil]
    generalize hQ1 : (1 : ℝ) / 2 - lm1 = Q1 at hl1 ⊢
    generalize hQ2 : (1 : ℝ) / 2 - lm2 = Q2 at hl2 ⊢
    simp only [hsum4]
    simp only [tw, e, ite_true, hij, hik, hil, hjk, hjl, hkl, hij.symm, hik.symm, hil.symm,
      hjk.symm, hjl.symm, hkl.symm, ite_false]
    have pj := hr j
    have hi := pi.ne'; have hj := pj.ne'; have hk := pk.ne'; have hl := pl.ne'
    have hsI' : 1 / r i + 1 / r j + 1 / r k + 1 / r l ≠ 0 := by rw [← hsI]; exact hs
    rw [hsI]
    field_simp
    rw [← hQ1, ← hQ2]
    simp only [lm1, lm2, hsI]
    field_simp
    ring

end GeometryResearch.Midsphere
