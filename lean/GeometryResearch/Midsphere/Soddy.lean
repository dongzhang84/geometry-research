module

public import GeometryResearch.Midsphere.GMPlane

/-!
# Soddy 球：曲率刻画与存在性

P(ρ) 为权重 −(s − ρq)·xᵢ + (2 − ρs)·xᵢ² 的点（权重和 −12D）。它对任意 ρ 满足
⟪P(ρ) − V₀, wᵢ⟫ = ((ρ + r₀)² + gᵢᵢ − (ρ + rᵢ)²)/2，并且
|P(ρ) − V₀|² − (ρ + r₀)² = (1 − sρ + (s²/4 − 9D)ρ²)/(3D)。
所以 (P(ρ), ρ) 是 Soddy 球当且仅当 1/ρ = s/2 ± 3√D。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- Soddy 球心的候选点 P(ρ)。 -/
def Pρ (t : Affine.Simplex ℝ E3 3) (r : Fin 4 → ℝ) (ρs : ℝ) : E3 :=
  ofWeights t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r i) +
    (2 - ρs * sInv r) * (1 / r i ^ 2))

theorem Pρ_sub (hfb : IsFourBall t r) (ρs : ℝ) :
    Pρ t r ρs - t.points 0 = (1 / (-12 * Ddisc r)) • L t (fun i => 0 * 1 +
      (-(sInv r - ρs * qInv r)) * (1 / r i) + (2 - ρs * sInv r) * (1 / r i ^ 2)) := by
  have hD := (D_pos hfb).ne'
  have hsum : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have := ofW_sub_V0 t _ (by rw [hsum]; exact mul_ne_zero (by norm_num) hD)
  rw [hsum] at this; exact this

theorem Pρ_inner (hfb : IsFourBall t r) (ρs : ℝ) {k : Fin 4} (hk : k ≠ 0) :
    ⟪Pρ t r ρs - t.points 0, w t k⟫ = ((ρs + r 0) ^ 2 + g r k k - (ρs + r k) ^ 2) / 2 := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hσ : -12 * Ddisc r ≠ 0 := mul_ne_zero (by norm_num) hD
  rw [Pρ_sub hfb, real_inner_smul_left, inner_Lw hfb, one_div_mul_eq_div, div_eq_iff hσ]
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  fin_cases k
  · exact absurd rfl hk
  all_goals
    simp only [Ddisc, sInv, qInv, g, e, Fin.sum_univ_four]
    simp
    field_simp
    ring

theorem Pρ_norm (hfb : IsFourBall t r) (ρs : ℝ) :
    ‖Pρ t r ρs - t.points 0‖ ^ 2 - (ρs + r 0) ^ 2 =
      (1 - sInv r * ρs + (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2) / (3 * Ddisc r) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hN : ⟪L t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r i) +
      (2 - ρs * sInv r) * (1 / r i ^ 2)), L t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) *
      (1 / r i) + (2 - ρs * sInv r) * (1 / r i ^ 2))⟫ =
      144 * Ddisc r ^ 2 * (ρs + r 0) ^ 2 +
        48 * Ddisc r * (1 - sInv r * ρs + (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2) := by
    rw [inner_L hfb]
    simp only [Fin.sum_univ_three, Ddisc, sInv, qInv, g, e, Fin.sum_univ_four]
    simp
    field_simp
    ring
  rw [Pρ_sub hfb, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← real_inner_self_eq_norm_sq, hN]
  field_simp
  ring

/-- (P(ρ), ρ) 满足全部四个相切条件，只要 i = 0 的那个成立。 -/
theorem Pρ_dist (hfb : IsFourBall t r) (ρs : ℝ)
    (h0 : ‖Pρ t r ρs - t.points 0‖ ^ 2 = (ρs + r 0) ^ 2) (i : Fin 4) :
    dist (Pρ t r ρs) (t.points i) ^ 2 = (ρs + r i) ^ 2 := by
  by_cases hi : i = 0
  · subst hi; rw [dist_eq_norm, h0]
  have hw : ‖w t i‖ ^ 2 = g r i i := by rw [← real_inner_self_eq_norm_sq, inner_w hfb]
  rw [dist_eq_norm, show Pρ t r ρs - t.points i = (Pρ t r ρs - t.points 0) - w t i by
    simp only [w]; abel, @norm_sub_sq_real, h0, hw, Pρ_inner hfb ρs hi]
  ring

theorem soddy_curvature' (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    1 / ρs = sInv r / 2 + 3 * √(Ddisc r) ∨ 1 / ρs = sInv r / 2 - 3 * √(Ddisc r) := by
  have hD := D_pos hfb
  have hSP : S = Pρ t r ρs := S_eq hfb hS
  have h0 := hS.2 0
  rw [hSP, dist_eq_norm] at h0
  have hq := Pρ_norm hfb ρs
  rw [h0, sub_self] at hq
  have hQ : 1 - sInv r * ρs + (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2 = 0 := by
    have := hq.symm
    rwa [div_eq_zero_iff, or_iff_left (by positivity)] at this
  have hρ := hS.1
  have hk : (1 / ρs - sInv r / 2) ^ 2 = (3 * √(Ddisc r)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD.le]
    field_simp
    linear_combination 4 * hQ
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk with h | h
  · left; linarith
  · right; linarith

/-- 曲率 κ = s/2 ± 3√D 给出 Soddy 球（κ ≠ 0）。 -/
theorem soddy_of_curv (hfb : IsFourBall t r) {κ : ℝ} (hκ : κ ≠ 0)
    (hk : (κ - sInv r / 2) ^ 2 = 9 * Ddisc r) : IsSoddy t r (Pρ t r (1 / κ)) (1 / κ) := by
  have hD := D_pos hfb
  refine ⟨one_div_ne_zero hκ, Pρ_dist hfb _ ?_⟩
  have hq := Pρ_norm hfb (1 / κ)
  have hQ : 1 - sInv r * (1 / κ) + (sInv r ^ 2 / 4 - 9 * Ddisc r) * (1 / κ) ^ 2 = 0 := by
    field_simp
    linear_combination 4 * hk
  rw [hQ, zero_div] at hq
  linarith

theorem exists_soddy' (hfb : IsFourBall t r) (hplane : sInv r ^ 2 ≠ 3 * qInv r) :
    ∃ S₁ ρ₁ S₂ ρ₂, IsSoddy t r S₁ ρ₁ ∧ IsSoddy t r S₂ ρ₂ ∧ (S₁, ρ₁) ≠ (S₂, ρ₂) := by
  have hD := D_pos hfb
  have hsq := Real.sq_sqrt hD.le
  have hsp := Real.sqrt_pos.mpr hD
  set κ₁ := sInv r / 2 + 3 * √(Ddisc r)
  set κ₂ := sInv r / 2 - 3 * √(Ddisc r)
  have hprod : κ₁ * κ₂ = (3 * qInv r - sInv r ^ 2) / 2 := by
    simp only [κ₁, κ₂]; ring_nf; rw [hsq]; simp only [Ddisc]; ring
  have hne : κ₁ * κ₂ ≠ 0 := by
    rw [hprod]; intro h; apply hplane; linarith
  have h1 : κ₁ ≠ 0 := left_ne_zero_of_mul hne
  have h2 : κ₂ ≠ 0 := right_ne_zero_of_mul hne
  refine ⟨_, _, _, _, soddy_of_curv hfb h1 (by simp only [κ₁]; ring_nf; rw [hsq]),
    soddy_of_curv hfb h2 (by simp only [κ₂]; ring_nf; rw [hsq]), ?_⟩
  intro h
  have := congrArg Prod.snd h
  simp only at this
  have h12 : κ₁ = κ₂ := by
    have := congrArg (fun x => 1 / x) this; simpa using this
  simp only [κ₁, κ₂] at h12
  linarith

end GeometryResearch.Midsphere
