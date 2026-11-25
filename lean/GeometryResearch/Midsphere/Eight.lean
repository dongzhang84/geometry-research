module

public import GeometryResearch.Midsphere.FivePoint
public import GeometryResearch.Midsphere.Soddy

/-!
# 定理 3（八点球）的证明

T₀₁、T₀₂、T₁₃、T₂₃ 都在棱切球 μ 上，也都在平面 ℓ = r₀x₀ − r₁x₁ − r₂x₂ + r₃x₃ = 0 上，
所求的球取 μ 与这个平面生成的球束中的 pow_μ + λℓ = 0。

Soddy 球 (Sₖ, ρₖ) 与 Σᵢ 的切点 s 满足 pow_μ(s) = rᵢ(Pₖ − ρₖ²)/(rᵢ + ρₖ)，其中 Pₖ = pow_μ(Sₖ)；
又 ℓ(s) = rᵢ(ℓ(Sₖ) ∓ ρₖ)/(rᵢ + ρₖ)（i = 1, 2 取 −，i = 0, 3 取 +）。
于是条件化为 (P₁ − ρ₁²)(ℓ(S₂) + ρ₂) = (P₂ − ρ₂²)(ℓ(S₁) − ρ₁)。
用 P(ρ) = (4 + (s² − 4q)ρ²)/(2q − s²)、ℓ(P(ρ)) = σ(2 − sρ)/(2q − s²) 和 Soddy 方程，
它化为 1/ρ₁ + 1/ρ₂ = s，即两个 Soddy 曲率之和。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 平面 T₀₁T₀₂T₁₃T₂₃ 在顶点上的值。 -/
def L3 (r : Fin 4 → ℝ) : Fin 4 → ℝ := ![r 0, -r 1, -r 2, r 3]

theorem ellV_line (Lw : Fin 4 → ℝ) (A B : E3) (c : ℝ) :
    ellV t Lw (AffineMap.lineMap A B c) = (1 - c) * ellV t Lw A + c * ellV t Lw B := by
  obtain ⟨u, κ, hu⟩ := ellV_repr (t := t) Lw A
  rw [hu, hu, hu, AffineMap.lineMap_apply_module, show (1 - c) • A + c • B - A = c • (B - A) by
    module, real_inner_smul_right, sub_self, inner_zero_right]
  ring

/-- 顶点对 μ 的幂为 rᵢ²。 -/
theorem vert_pow (hfb : IsFourBall t r) (i : Fin 4) :
    dist (t.points i) (M t r) ^ 2 = ρ t r ^ 2 + r i ^ 2 := by
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := ⟨i + 1, by simp⟩
  have hr := hfb.1
  have hT := T_on hfb hij
  have ho := (M_tangent' hfb hij).2
  have hd := hfb.2 i j hij
  have hs : r i + r j ≠ 0 := (add_pos (hr i) (hr j)).ne'
  have e1 : T t r i j - t.points i = (r i / (r i + r j)) • (t.points j - t.points i) := by
    rw [T, AffineMap.lineMap_apply_module]; module
  have hn : ‖t.points j - t.points i‖ = r i + r j := by rw [← dist_eq_norm, dist_comm, hd]
  rw [dist_eq_norm, show t.points i - M t r = (T t r i j - M t r) - (T t r i j - t.points i) by
    abel, norm_sub_sq_real, e1, inner_smul_right, ho, norm_smul, ← dist_eq_norm, hT,
    Real.norm_eq_abs, mul_pow, sq_abs, hn]
  field_simp
  ring

/-- Soddy 球与 Σᵢ 的切点对 μ 的幂。 -/
theorem spt_pow (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (i : Fin 4)
    (hS : dist S (t.points i) ^ 2 = (ρs + r i) ^ 2) (hne : r i + ρs ≠ 0) :
    dist (soddyPt t r S ρs i) (M t r) ^ 2 - ρ t r ^ 2 =
      r i * (dist S (M t r) ^ 2 - ρ t r ^ 2 - ρs ^ 2) / (r i + ρs) := by
  have hv := vert_pow hfb i
  have hSV : ‖S - t.points i‖ ^ 2 = (ρs + r i) ^ 2 := by rw [← dist_eq_norm, hS]
  have hpol : ⟪t.points i - M t r, S - t.points i⟫ =
      (dist S (M t r) ^ 2 - dist (t.points i) (M t r) ^ 2 - ‖S - t.points i‖ ^ 2) / 2 := by
    rw [dist_eq_norm, dist_eq_norm, show S - M t r = (t.points i - M t r) + (S - t.points i) by
      abel, norm_add_sq_real]
    ring
  rw [dist_eq_norm, soddyPt, AffineMap.lineMap_apply_module,
    show (1 - r i / (r i + ρs)) • t.points i + (r i / (r i + ρs)) • S - M t r =
      (t.points i - M t r) + (r i / (r i + ρs)) • (S - t.points i) by module,
    norm_add_sq_real, inner_smul_right, hpol, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hSV,
    ← dist_eq_norm, hv]
  field_simp
  ring

/-- Soddy 球的 ρₛ ≠ −rᵢ。 -/
theorem soddy_ne (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) (i : Fin 4) :
    r i + ρs ≠ 0 := by
  intro h
  have hr := hfb.1
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := ⟨i + 1, by simp⟩
  have h1 := hS.2 i
  rw [show ρs + r i = 0 by linarith, zero_pow two_ne_zero, sq_eq_zero_iff, dist_eq_zero] at h1
  have h2 := hS.2 j
  rw [h1, hfb.2 i j hij, show ρs = -r i by linarith] at h2
  have : (r i + r j) ^ 2 - (-r i + r j) ^ 2 = 4 * r i * r j := by ring
  have := mul_pos (hr i) (hr j)
  nlinarith

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem Pρ_pow (hfb : IsFourBall t r) (ρs : ℝ) :
    dist (Pρ t r ρs) (M t r) ^ 2 - ρ t r ^ 2 =
      -(4 + (sInv r ^ 2 - 4 * qInv r) * ρs ^ 2) / (12 * Ddisc r) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have hsumP : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [dρ hfb, M_comb, Pρ, dist_ofW' hfb (by rw [hsumP]; exact mul_ne_zero (by norm_num) hD)
    (by rw [hsumM]; positivity), hsumM, hsumP]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, e, sInv, qInv]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es4]
  field_simp
  ring

theorem ell_Pρ (hfb : IsFourBall t r) (ρs : ℝ) :
    ellV t (L3 r) (Pρ t r ρs) = -((1 / r 0 - 1 / r 1 - 1 / r 2 + 1 / r 3) *
      (2 - sInv r * ρs)) / (12 * Ddisc r) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsumP : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [Pρ, ellV_ofW _ _ (by rw [hsumP]; exact mul_ne_zero (by norm_num) hD), hsumP]
  simp only [Fin.sum_univ_four, L3]
  simp
  field_simp
  ring

/-- Soddy 球满足 Q(ρ) = 0。 -/
theorem soddy_Q (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    1 - sInv r * ρs + (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2 = 0 := by
  have hD := D_pos hfb
  have h0 := hS.2 0
  rw [S_eq hfb hS, dist_eq_norm] at h0
  have hq := Pρ_norm hfb ρs
  rw [show Pρ t r ρs = ofWeights t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r i) +
    (2 - ρs * sInv r) * (1 / r i ^ 2)) from rfl, h0, sub_self] at hq
  have := hq.symm
  rwa [div_eq_zero_iff, or_iff_left (by positivity)] at this

/-- 两个不同 Soddy 球的曲率之和为 s。 -/
theorem soddy_sum (hfb : IsFourBall t r) {S₁ S₂ : E3} {ρ₁ ρ₂ : ℝ}
    (h₁ : IsSoddy t r S₁ ρ₁) (h₂ : IsSoddy t r S₂ ρ₂) (hne : (S₁, ρ₁) ≠ (S₂, ρ₂)) :
    1 / ρ₁ + 1 / ρ₂ = sInv r := by
  have hρ : ρ₁ ≠ ρ₂ := by
    intro h; apply hne; rw [S_eq hfb h₁, S_eq hfb h₂, h]
  have hD := D_pos hfb
  have hsp := Real.sqrt_pos.mpr hD
  have hk : 1 / ρ₁ ≠ 1 / ρ₂ := fun h => hρ (by simpa using h)
  rcases soddy_curvature' hfb h₁ with a | a <;> rcases soddy_curvature' hfb h₂ with b | b
  · exact absurd (a.trans b.symm) hk
  · rw [a, b]; ring
  · rw [a, b]; ring
  · exact absurd (a.trans b.symm) hk

/-- 定理 3 的代数核心。 -/
theorem alg3 {s σ X ρ₁ ρ₂ : ℝ} (hX : X ≠ 0) (h : ρ₁ + ρ₂ = s * ρ₁ * ρ₂) :
    (8 - 4 * s * ρ₁) / X * (σ * (2 - s * ρ₂) / X + ρ₂) =
      (8 - 4 * s * ρ₂) / X * (σ * (2 - s * ρ₁) / X - ρ₁) := by
  field_simp
  linear_combination 8 * X * h

theorem A_eq (hfb : IsFourBall t r) {ρs : ℝ}
    (hQ : 1 - sInv r * ρs + (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2 = 0) :
    dist (Pρ t r ρs) (M t r) ^ 2 - ρ t r ^ 2 - ρs ^ 2 =
      (8 - 4 * sInv r * ρs) / (-12 * Ddisc r) := by
  have hD := (D_pos hfb).ne'
  rw [Pρ_pow hfb]
  field_simp
  simp only [Ddisc] at hQ ⊢
  linear_combination (4 : ℝ) * hQ

/-- 球束判据：pow_μ + λℓ 在 S 上为零，则 S 共球。 -/
theorem cosph_pencil {S : Set E3} (Lw : Fin 4 → ℝ) (lam : ℝ)
    (h : ∀ X ∈ S, dist X (M t r) ^ 2 - ρ t r ^ 2 + lam * ellV t Lw X = 0) : Cospherical S := by
  obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) Lw (M t r)
  refine cosph_of (M t r) (M t r) (lam • c) (lam * κ - ρ t r ^ 2) (fun X hX => ?_)
  rw [real_inner_smul_left, ← h X hX, hc X]; ring

/-- 平面判据：ℓ 在 S 上为零且 ℓ 在两个顶点上取值不同，则 S 共面。 -/
theorem coplanar_ell {S : Set E3} (Lw : Fin 4 → ℝ) {a b : Fin 4} (hab : Lw a ≠ Lw b)
    (h : ∀ X ∈ S, ellV t Lw X = 0) : Coplanar ℝ S := by
  obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) Lw (t.points 0)
  refine coplanar_of_inner c (t.points 0) κ ?_ (fun X hX => by rw [← hc]; exact h X hX)
  rintro rfl
  have e1 := hc (t.points a); have e2 := hc (t.points b)
  rw [ellV_vertex, inner_zero_left] at e1 e2
  exact hab (e1.trans e2.symm)

/-- 切点处 pow_μ + λℓ 的值。 -/
theorem spt_comb (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) (i : Fin 4)
    (Lw : Fin 4 → ℝ) (lam : ℝ) :
    dist (soddyPt t r S ρs i) (M t r) ^ 2 - ρ t r ^ 2 + lam * ellV t Lw (soddyPt t r S ρs i) =
      (r i * (dist S (M t r) ^ 2 - ρ t r ^ 2 - ρs ^ 2) +
        lam * (ρs * Lw i + r i * ellV t Lw S)) / (r i + ρs) := by
  have hne := soddy_ne hfb hS i
  rw [spt_pow hfb i (hS.2 i) hne, soddyPt, ellV_line, ellV_vertex]
  field_simp
  ring

set_option maxHeartbeats 1000000 in -- 组装
/-- 定理 3 的证明。 -/
theorem eight_main (hfb : IsFourBall t r) {S₁ S₂ : E3} {ρ₁ ρ₂ : ℝ}
    (h₁ : IsSoddy t r S₁ ρ₁) (h₂ : IsSoddy t r S₂ ρ₂) (hne : (S₁, ρ₁) ≠ (S₂, ρ₂)) :
    MCospherical ({T t r 0 1, T t r 0 2, T t r 1 3, T t r 2 3,
      soddyPt t r S₁ ρ₁ 1, soddyPt t r S₁ ρ₁ 2, soddyPt t r S₂ ρ₂ 0, soddyPt t r S₂ ρ₂ 3} :
        Set E3) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hX : -12 * Ddisc r ≠ 0 := mul_ne_zero (by norm_num) hD
  have hsum := soddy_sum hfb h₁ h₂ hne
  have hρ1 := h₁.1; have hρ2 := h₂.1
  have hsum' : ρ₁ + ρ₂ = sInv r * ρ₁ * ρ₂ := by
    rw [← hsum]; field_simp; ring
  set A₁ := dist S₁ (M t r) ^ 2 - ρ t r ^ 2 - ρ₁ ^ 2
  set A₂ := dist S₂ (M t r) ^ 2 - ρ t r ^ 2 - ρ₂ ^ 2
  set B₁ := ellV t (L3 r) S₁ - ρ₁
  set B₂ := ellV t (L3 r) S₂ + ρ₂
  have hkey : A₁ * B₂ = A₂ * B₁ := by
    have e1 : A₁ = (8 - 4 * sInv r * ρ₁) / (-12 * Ddisc r) := by
      simp only [A₁]; rw [S_eq hfb h₁]; exact A_eq hfb (soddy_Q hfb h₁)
    have e2 : A₂ = (8 - 4 * sInv r * ρ₂) / (-12 * Ddisc r) := by
      simp only [A₂]; rw [S_eq hfb h₂]; exact A_eq hfb (soddy_Q hfb h₂)
    have f1 : ellV t (L3 r) S₁ = (1 / r 0 - 1 / r 1 - 1 / r 2 + 1 / r 3) * (2 - sInv r * ρ₁) /
        (-12 * Ddisc r) := by
      rw [S_eq hfb h₁]
      exact (ell_Pρ hfb ρ₁).trans (by rw [neg_div, ← div_neg]; ring_nf)
    have f2 : ellV t (L3 r) S₂ = (1 / r 0 - 1 / r 1 - 1 / r 2 + 1 / r 3) * (2 - sInv r * ρ₂) /
        (-12 * Ddisc r) := by
      rw [S_eq hfb h₂]
      exact (ell_Pρ hfb ρ₂).trans (by rw [neg_div, ← div_neg]; ring_nf)
    simp only [B₁, B₂]
    rw [e1, e2, f1, f2]
    exact alg3 hX hsum'
  have hT : ∀ {a b : Fin 4}, a ≠ b → L3 r a * r b + L3 r b * r a = 0 →
      ∀ lam : ℝ,
        dist (T t r a b) (M t r) ^ 2 - ρ t r ^ 2 + lam * ellV t (L3 r) (T t r a b) = 0 := by
    intro a b hab h0 lam
    rw [T_on hfb hab, ellV_T hfb _ hab, h0, zero_div]; ring
  have t01 := hT (show (0 : Fin 4) ≠ 1 by decide) (by simp [L3]; ring)
  have t02 := hT (show (0 : Fin 4) ≠ 2 by decide) (by simp [L3]; ring)
  have t13 := hT (show (1 : Fin 4) ≠ 3 by decide) (by simp [L3]; ring)
  have t23 := hT (show (2 : Fin 4) ≠ 3 by decide) (by simp [L3]; ring)
  have s11 : ∀ lam, _ = _ := spt_comb hfb h₁ 1 (L3 r)
  have s12 : ∀ lam, _ = _ := spt_comb hfb h₁ 2 (L3 r)
  have s20 : ∀ lam, _ = _ := spt_comb hfb h₂ 0 (L3 r)
  have s23 : ∀ lam, _ = _ := spt_comb hfb h₂ 3 (L3 r)
  -- 在 pow + λℓ 下，各切点的值是 rᵢ(Aₖ + λBₖ)/(rᵢ + ρₖ)
  have c1 : ∀ lam, ∀ i : Fin 4, (i = 1 ∨ i = 2) →
      (r i * A₁ + lam * (ρ₁ * -r i + r i * ellV t (L3 r) S₁)) / (r i + ρ₁) =
        r i * (A₁ + lam * B₁) / (r i + ρ₁) := by
    intro lam i _; simp only [B₁]; ring
  have c2 : ∀ lam, ∀ i : Fin 4,
      (r i * A₂ + lam * (ρ₂ * r i + r i * ellV t (L3 r) S₂)) / (r i + ρ₂) =
        r i * (A₂ + lam * B₂) / (r i + ρ₂) := by
    intro lam i; simp only [B₂]; ring
  by_cases hB : B₁ = 0 ∧ B₂ = 0
  · right
    refine coplanar_ell (t := t) (L3 r) (a := 0) (b := 1)
      (by simp [L3]; linarith [hr 0, hr 1]) (fun X hX => ?_)
    have z : ∀ {a b : Fin 4}, a ≠ b → L3 r a * r b + L3 r b * r a = 0 →
        ellV t (L3 r) (T t r a b) = 0 := by
      intro a b hab h0; rw [ellV_T hfb _ hab, h0, zero_div]
    have zs : ∀ {S : E3} {ρs : ℝ}, IsSoddy t r S ρs → ∀ i,
        (ρs * L3 r i + r i * ellV t (L3 r) S) = 0 →
        ellV t (L3 r) (soddyPt t r S ρs i) = 0 := by
      intro S ρs hS i h0
      rw [soddyPt, ellV_line, ellV_vertex]
      have hne := soddy_ne hfb hS i
      field_simp
      linear_combination h0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact z (by decide) (by simp [L3]; ring)
    · exact z (by decide) (by simp [L3]; ring)
    · exact z (by decide) (by simp [L3]; ring)
    · exact z (by decide) (by simp [L3]; ring)
    · exact zs h₁ 1 (by rw [show L3 r 1 = -r 1 from rfl]; linear_combination (r 1) * hB.1)
    · exact zs h₁ 2 (by rw [show L3 r 2 = -r 2 from rfl]; linear_combination (r 2) * hB.1)
    · exact zs h₂ 0 (by rw [show L3 r 0 = r 0 from rfl]; linear_combination (r 0) * hB.2)
    · exact zs h₂ 3 (by rw [show L3 r 3 = r 3 from rfl]; linear_combination (r 3) * hB.2)
  · left
    have hl : ∃ lam : ℝ, A₁ + lam * B₁ = 0 ∧ A₂ + lam * B₂ = 0 := by
      by_cases h1 : B₁ = 0
      · have h2 : B₂ ≠ 0 := fun h2 => hB ⟨h1, h2⟩
        refine ⟨-A₂ / B₂, ?_, by field_simp; ring⟩
        rw [h1, mul_zero, add_zero]
        rw [h1, mul_zero] at hkey
        exact (mul_eq_zero.mp hkey).resolve_right h2
      · refine ⟨-A₁ / B₁, by field_simp; ring, ?_⟩
        field_simp
        linear_combination (-1 : ℝ) * hkey
    obtain ⟨lam, l1, l2⟩ := hl
    refine cosph_pencil (t := t) (r := r) (L3 r) lam (fun X hX => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t01 lam
    · exact t02 lam
    · exact t13 lam
    · exact t23 lam
    · rw [s11, show L3 r 1 = -r 1 from rfl, c1 lam 1 (by simp), l1, mul_zero, zero_div]
    · rw [s12, show L3 r 2 = -r 2 from rfl, c1 lam 2 (by simp), l1, mul_zero, zero_div]
    · rw [s20, show L3 r 0 = r 0 from rfl, c2 lam 0, l2, mul_zero, zero_div]
    · rw [s23, show L3 r 3 = r 3 from rfl, c2 lam 3, l2, mul_zero, zero_div]

end GeometryResearch.Midsphere
