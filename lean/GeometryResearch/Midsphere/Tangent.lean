module

public import GeometryResearch.Midsphere.Central

/-!
# 棱切球与 Zeeman 点的忠实性

* `M_power`：|MVᵢ|² − rᵢ² 与 i 无关（M 对四个球 Σᵢ 的幂相等）。
* 由此 MTᵢⱼ ⊥ VᵢVⱼ，且 |MTᵢⱼ|² = |MVᵢ|² − rᵢ²，所以棱切球过六个切点并与棱相切。
* Z 的权重 (xᵢ) 是 Tᵢⱼ 的权重 (xᵢ, xⱼ) 与 Tₖₗ 的权重 (xₖ, xₗ) 之和，所以 Z 在 TᵢⱼTₖₗ 上。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- M 对四个球的幂相等：|MVᵢ|² − rᵢ² = |MV₀|² − r₀²。 -/
theorem M_power (hfb : IsFourBall t r) (i : Fin 4) :
    dist (M t r) (t.points i) ^ 2 - r i ^ 2 = dist (M t r) (t.points 0) ^ 2 - r 0 ^ 2 := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  by_cases hi : i = 0
  · subst hi; rfl
  have hsum : ∑ j, (0 * 1 + (sInv r / 2) * (1 / r j) + (-1) * (1 / r j ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have hσ : 6 * Ddisc r ≠ 0 := mul_ne_zero (by norm_num) hD
  have eM := ofW_sub_V0 t _ (by rw [hsum]; exact hσ)
  rw [hsum, ← M_comb] at eM
  have hw : ‖w t i‖ ^ 2 = g r i i := by rw [← real_inner_self_eq_norm_sq, inner_w hfb]
  have key : ⟪M t r - t.points 0, w t i⟫ = (g r i i - r i ^ 2 + r 0 ^ 2) / 2 := by
    rw [eM, real_inner_smul_left, inner_Lw hfb, one_div_mul_eq_div, div_eq_iff hσ]
    have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'
    have h3 := (hr 3).ne'
    fin_cases i
    · exact absurd rfl hi
    all_goals
      simp only [Ddisc, sInv, qInv, g, e, Fin.sum_univ_four]
      simp
      field_simp
      ring
  rw [dist_eq_norm, dist_eq_norm, show M t r - t.points i = (M t r - t.points 0) - w t i by
    simp only [w]; abel, @norm_sub_sq_real, hw, key]
  ring

/-- 棱切球：μ 经过 Tᵢⱼ，并在那里与棱相切。 -/
theorem M_tangent' (hfb : IsFourBall t r) {i j : Fin 4} (hij : i ≠ j) :
    T t r i j ∈ midsphere t r ∧ ⟪T t r i j - M t r, t.points j - t.points i⟫ = 0 := by
  have hr := hfb.1
  -- 一般的两点论证：Tᵢⱼ = Vᵢ + rᵢ·u，Vⱼ = Vᵢ + (rᵢ + rⱼ)·u，|u| = 1
  have tang : ∀ {a b : Fin 4}, a ≠ b →
      ⟪T t r a b - M t r, t.points b - t.points a⟫ = 0 ∧
        dist (M t r) (T t r a b) ^ 2 = dist (M t r) (t.points a) ^ 2 - r a ^ 2 := by
    intro a b hab
    have ha := hr a; have hb := hr b
    have hs : r a + r b ≠ 0 := by linarith
    have hd := hfb.2 a b hab
    set d := t.points b - t.points a
    have hdn : ‖d‖ ^ 2 = (r a + r b) ^ 2 := by
      rw [show d = t.points b - t.points a from rfl, ← dist_eq_norm, dist_comm, hd]
    have hT : T t r a b - t.points a = (r a / (r a + r b)) • d := by
      rw [T, AffineMap.lineMap_apply_module']; simp [d]
    have hpa := M_power hfb a; have hpb := M_power hfb b
    set m := M t r - t.points a
    have eMb : M t r - t.points b = m - d := by simp only [m, d]; abel
    have hma : dist (M t r) (t.points a) ^ 2 = ‖m‖ ^ 2 := by rw [dist_eq_norm]
    have hmb : dist (M t r) (t.points b) ^ 2 = ‖m - d‖ ^ 2 := by rw [dist_eq_norm, eMb]
    have hmd : ⟪m, d⟫ = r a * (r a + r b) := by
      have := hpa.trans hpb.symm
      have e2 := norm_sub_sq_real m d
      rw [hma, hmb, e2, hdn] at this
      nlinarith
    have eTM : T t r a b - M t r = (r a / (r a + r b)) • d - m := by
      rw [← hT]; simp only [m]; abel
    refine ⟨?_, ?_⟩
    · rw [eTM, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hdn, hmd]
      field_simp; ring
    · rw [dist_comm, dist_eq_norm, eTM, hma, norm_sub_sq_real ((r a / (r a + r b)) • d) m,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hdn, real_inner_smul_left,
        real_inner_comm m d, hmd]
      field_simp; ring
  obtain ⟨h1, h2⟩ := tang hij
  obtain ⟨-, h01⟩ := tang (show (0 : Fin 4) ≠ 1 by decide)
  refine ⟨?_, h1⟩
  rw [EuclideanGeometry.mem_sphere, midsphere, ρ, dist_comm, ← sq_eq_sq₀ dist_nonneg dist_nonneg,
    h2, h01, M_power hfb i, M_power hfb 0]

theorem T_sub_V0 (a b : Fin 4) :
    T t r a b - t.points 0 = (1 - r a / (r a + r b)) • w t a + (r a / (r a + r b)) • w t b := by
  rw [T, AffineMap.lineMap_apply_module]; simp only [w]; module

/-- Zeeman 点在三条连线 TᵢⱼTₖₗ 上。 -/
theorem Z_mem_chord' (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    Z t r ∈ line[ℝ, T t r i j, T t r k l] := by
  have hr := hfb.1
  have hs := (sInv_pos hfb).ne'
  have ps := GeometryResearch.Orthocentric.sum_perm (fun m => 1 / r m) hij hik hil hjk hjl hkl
  have pv := GeometryResearch.Orthocentric.sum_perm (fun m => (1 / r m) • w t m) hij hik hil hjk
    hjl hkl
  have hS : sInv r = 1 / r i + 1 / r j + 1 / r k + 1 / r l := by
    rw [sInv, Fin.sum_univ_four, ← ps]
  set lam := (1 / r k + 1 / r l) / sInv r
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  refine ⟨lam, ?_⟩
  rw [← sub_left_inj (a := t.points 0), AffineMap.lineMap_apply_module,
    show (1 - lam) • T t r i j + lam • T t r k l - t.points 0 =
      (1 - lam) • (T t r i j - t.points 0) + lam • (T t r k l - t.points 0) by module,
    T_sub_V0, T_sub_V0, show Z t r = ofWeights t (fun m => 1 / r m) from rfl,
    ofW_sub_V0 t _ hs, L, Fin.sum_univ_four (f := fun k => (1 / r k) • w t k), ← pv]
  have hi := (hr i).ne'; have hj := (hr j).ne'; have hk := (hr k).ne'; have hl := (hr l).ne'
  have pi := hr i; have pj := hr j; have pk := hr k; have pl := hr l
  have he3 : r l * r k * r i + r l * r k * r j + r l * r i * r j + r k * r i * r j ≠ 0 := by
    positivity
  have hij' : r i + r j ≠ 0 := by have := hr i; have := hr j; linarith
  have hkl' : r k + r l ≠ 0 := by have := hr k; have := hr l; linarith
  have f1 : (1 - lam) * (1 - r i / (r i + r j)) = 1 / sInv r * (1 / r i) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f2 : (1 - lam) * (r i / (r i + r j)) = 1 / sInv r * (1 / r j) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f3 : lam * (1 - r k / (r k + r l)) = 1 / sInv r * (1 / r k) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f4 : lam * (r k / (r k + r l)) = 1 / sInv r * (1 / r l) := by
    simp only [lam]; rw [hS]; field_simp; ring
  rw [show (1 - lam) • ((1 - r i / (r i + r j)) • w t i + (r i / (r i + r j)) • w t j) +
      lam • ((1 - r k / (r k + r l)) • w t k + (r k / (r k + r l)) • w t l) =
      ((1 - lam) * (1 - r i / (r i + r j))) • w t i + ((1 - lam) * (r i / (r i + r j))) • w t j +
      (lam * (1 - r k / (r k + r l))) • w t k + (lam * (r k / (r k + r l))) • w t l by module,
    f1, f2, f3, f4, show sInv r = ∑ j, 1 / r j from rfl]
  module

/-- Z 在弦 TᵢⱼTₖₗ 上的位置：Z = Tᵢⱼ + λ(Tₖₗ − Tᵢⱼ)，λ = (1/rₖ + 1/rₗ)/s。 -/
theorem Z_lineMap (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    AffineMap.lineMap (T t r i j) (T t r k l) ((1 / r k + 1 / r l) / sInv r) = Z t r := by
  have hr := hfb.1
  have hs := (sInv_pos hfb).ne'
  have ps := GeometryResearch.Orthocentric.sum_perm (fun m => 1 / r m) hij hik hil hjk hjl hkl
  have pv := GeometryResearch.Orthocentric.sum_perm (fun m => (1 / r m) • w t m) hij hik hil hjk
    hjl hkl
  have hS : sInv r = 1 / r i + 1 / r j + 1 / r k + 1 / r l := by
    rw [sInv, Fin.sum_univ_four, ← ps]
  set lam := (1 / r k + 1 / r l) / sInv r
  rw [← sub_left_inj (a := t.points 0), AffineMap.lineMap_apply_module,
    show (1 - lam) • T t r i j + lam • T t r k l - t.points 0 =
      (1 - lam) • (T t r i j - t.points 0) + lam • (T t r k l - t.points 0) by module,
    T_sub_V0, T_sub_V0, show Z t r = ofWeights t (fun m => 1 / r m) from rfl,
    ofW_sub_V0 t _ hs, L, Fin.sum_univ_four (f := fun k => (1 / r k) • w t k), ← pv]
  have hi := (hr i).ne'; have hj := (hr j).ne'; have hk := (hr k).ne'; have hl := (hr l).ne'
  have pi := hr i; have pj := hr j; have pk := hr k; have pl := hr l
  have he3 : r l * r k * r i + r l * r k * r j + r l * r i * r j + r k * r i * r j ≠ 0 := by
    positivity
  have hij' : r i + r j ≠ 0 := by have := hr i; have := hr j; linarith
  have hkl' : r k + r l ≠ 0 := by have := hr k; have := hr l; linarith
  have f1 : (1 - lam) * (1 - r i / (r i + r j)) = 1 / sInv r * (1 / r i) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f2 : (1 - lam) * (r i / (r i + r j)) = 1 / sInv r * (1 / r j) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f3 : lam * (1 - r k / (r k + r l)) = 1 / sInv r * (1 / r k) := by
    simp only [lam]; rw [hS]; field_simp; ring
  have f4 : lam * (r k / (r k + r l)) = 1 / sInv r * (1 / r l) := by
    simp only [lam]; rw [hS]; field_simp; ring
  rw [show (1 - lam) • ((1 - r i / (r i + r j)) • w t i + (r i / (r i + r j)) • w t j) +
      lam • ((1 - r k / (r k + r l)) • w t k + (r k / (r k + r l)) • w t l) =
      ((1 - lam) * (1 - r i / (r i + r j))) • w t i + ((1 - lam) * (r i / (r i + r j))) • w t j +
      (lam * (1 - r k / (r k + r l))) • w t k + (lam * (r k / (r k + r l))) • w t l by module,
    f1, f2, f3, f4, show sInv r = ∑ j, 1 / r j from rfl]
  module

end GeometryResearch.Midsphere
