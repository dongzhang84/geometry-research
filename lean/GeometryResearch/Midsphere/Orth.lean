module

public import GeometryResearch.Midsphere.Soddy

/-!
# 定理 9（正交球引理）的证明

Soddy 球心 S = P(ρ) 对 ρ 是仿射的：P(ρ) = P(0) + ρ·A，A = P(1) − P(0)。以 Vᵢ 为基点，
u = c − Vᵢ（c 为球 s 的球心）。由 |S − Vᵢ|² = (ρ + rᵢ)²，「s 过 Tᵢⱼ 且与 Soddy 球正交」化为
ρ 的一次式 2⟪u, Tᵢⱼ − P(0)⟫ + ρ(2rᵢ − 2⟪u, A⟫) = 0；两个 Soddy 球的 ρ 不同，所以
⟪u, Tᵢⱼ − P(0)⟫ = 0，⟪u, A⟫ = rᵢ。再由向量恒等式 Tᵢⱼ − Tₖₗ = a(Tᵢⱼ − P(0)) + b·A
（b = −2rₖrₗ/(rₖ + rₗ)）和 Stewart 定理 |VᵢTₖₗ|² = rᵢ² + 4rᵢrₖrₗ/(rₖ + rₗ)，得 |c − Tₖₗ| = |c − Tᵢⱼ|。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- P(ρ) 对 ρ 仿射。 -/
theorem Pρ_affine (hfb : IsFourBall t r) (ρs : ℝ) :
    Pρ t r ρs = Pρ t r 0 + ρs • (Pρ t r 1 - Pρ t r 0) := by
  have e := Pρ_sub hfb ρs; have e0 := Pρ_sub hfb 0; have e1 := Pρ_sub hfb 1
  rw [← sub_eq_zero, show Pρ t r ρs - (Pρ t r 0 + ρs • (Pρ t r 1 - Pρ t r 0)) =
    (Pρ t r ρs - t.points 0) - (Pρ t r 0 - t.points 0) -
      ρs • ((Pρ t r 1 - t.points 0) - (Pρ t r 0 - t.points 0)) by module, e, e0, e1]
  simp only [L_four]
  module

/-- Stewart 定理：|VᵢTₖₗ|² = rᵢ² + 4rᵢrₖrₗ/(rₖ + rₗ)。 -/
theorem stewart (hfb : IsFourBall t r) {i k l : Fin 4} (hik : i ≠ k) (hil : i ≠ l)
    (hkl : k ≠ l) :
    dist (t.points i) (T t r k l) ^ 2 = r i ^ 2 + 4 * r i * r k * r l / (r k + r l) := by
  have hr := hfb.1
  have hs : r k + r l ≠ 0 := by have := hr k; have := hr l; linarith
  set c := r k / (r k + r l)
  have hT : T t r k l - t.points i =
      (1 - c) • (t.points k - t.points i) + c • (t.points l - t.points i) := by
    rw [T, AffineMap.lineMap_apply_module]; module
  have ek : ‖t.points k - t.points i‖ ^ 2 = (r i + r k) ^ 2 := by
    rw [← dist_eq_norm, hfb.2 k i (Ne.symm hik), add_comm]
  have el : ‖t.points l - t.points i‖ ^ 2 = (r i + r l) ^ 2 := by
    rw [← dist_eq_norm, hfb.2 l i (Ne.symm hil), add_comm]
  have ekl : ⟪t.points k - t.points i, t.points l - t.points i⟫ =
      ((r i + r k) ^ 2 + (r i + r l) ^ 2 - (r k + r l) ^ 2) / 2 := by
    rw [← ek, ← el, ← hfb.2 k l hkl, dist_eq_norm,
      show t.points k - t.points l = (t.points k - t.points i) - (t.points l - t.points i) by abel]
    generalize t.points k - t.points i = a; generalize t.points l - t.points i = b
    rw [@norm_sub_sq_real]; ring
  rw [dist_comm, dist_eq_norm, hT, @norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, ek, el, real_inner_smul_left,
    real_inner_smul_right, ekl]
  simp only [c]
  field_simp
  ring

/-- 向量恒等式 Tᵢⱼ − Tₖₗ = a(Tᵢⱼ − P(0)) + b(P(1) − P(0))。 -/
theorem orth_vec (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    T t r i j - T t r k l =
      ((r i * r j * r k + r i * r j * r l + r i * r k * r l + r j * r k * r l) /
        (r i * r j * (r k + r l))) • (T t r i j - Pρ t r 0) +
      (-2 * r k * r l / (r k + r l)) • (Pρ t r 1 - Pρ t r 0) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have ps := GeometryResearch.Orthocentric.sum_perm (fun m => 1 / r m) hij hik hil hjk hjl hkl
  have pq := GeometryResearch.Orthocentric.sum_perm (fun m => 1 / r m ^ 2) hij hik hil hjk hjl hkl
  have hs : sInv r = 1 / r i + 1 / r j + 1 / r k + 1 / r l := by rw [sInv, Fin.sum_univ_four, ← ps]
  have hq : qInv r = 1 / r i ^ 2 + 1 / r j ^ 2 + 1 / r k ^ 2 + 1 / r l ^ 2 := by
    rw [qInv, Fin.sum_univ_four, ← pq]
  have hσ : -12 * Ddisc r = 2 * qInv r - sInv r ^ 2 := by simp only [Ddisc]; ring
  -- 各点相对 V₀ 的表示
  have eL : ∀ f : Fin 4 → ℝ, L t f = f i • w t i + f j • w t j + f k • w t k + f l • w t l := by
    intro f
    rw [L, Fin.sum_univ_four]
    exact (GeometryResearch.Orthocentric.sum_perm (fun m => f m • w t m) hij hik hil hjk hjl
      hkl).symm
  have e0 := Pρ_sub hfb 0; have e1 := Pρ_sub hfb 1
  rw [eL] at e0 e1
  rw [show T t r i j - T t r k l = (T t r i j - t.points 0) - (T t r k l - t.points 0) by abel,
    show T t r i j - Pρ t r 0 = (T t r i j - t.points 0) - (Pρ t r 0 - t.points 0) by abel,
    show Pρ t r 1 - Pρ t r 0 = (Pρ t r 1 - t.points 0) - (Pρ t r 0 - t.points 0) by abel,
    T_sub_V0, T_sub_V0, e0, e1, hσ, hs, hq]
  have pi := hr i; have pj := hr j; have pk := hr k; have pl := hr l
  have hi := pi.ne'; have hj := pj.ne'; have hk := pk.ne'; have hl := pl.ne'
  set X := 2 * (1 / r i ^ 2 + 1 / r j ^ 2 + 1 / r k ^ 2 + 1 / r l ^ 2) -
    (1 / r i + 1 / r j + 1 / r k + 1 / r l) ^ 2 with hX
  have hX0 : X ≠ 0 := by rw [hX, ← hq, ← hs, ← hσ]; exact mul_ne_zero (by norm_num) hD
  have hij' : r i + r j ≠ 0 := by linarith
  have hkl' : r k + r l ≠ 0 := by linarith
  match_scalars <;> field_simp <;> simp only [hX] <;> field_simp <;> ring

/-- 定理 9 的证明。 -/
theorem orth_main (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {S₁ S₂ : E3} {ρ₁ ρ₂ : ℝ}
    (h₁ : IsSoddy t r S₁ ρ₁) (h₂ : IsSoddy t r S₂ ρ₂) (hne : (S₁, ρ₁) ≠ (S₂, ρ₂))
    (s : Sphere E3) (hT : T t r i j ∈ s)
    (ho₁ : dist s.center S₁ ^ 2 = s.radius ^ 2 + ρ₁ ^ 2)
    (ho₂ : dist s.center S₂ ^ 2 = s.radius ^ 2 + ρ₂ ^ 2) :
    T t r k l ∈ s := by
  have hr := hfb.1
  have e₁ : S₁ = Pρ t r ρ₁ := S_eq hfb h₁
  have e₂ : S₂ = Pρ t r ρ₂ := S_eq hfb h₂
  have hρ : ρ₁ ≠ ρ₂ := by
    intro h; apply hne; rw [e₁, e₂, h]
  set A := Pρ t r 1 - Pρ t r 0
  set u := s.center - t.points i
  set τ := T t r i j - t.points i
  set p0 := Pρ t r 0 - t.points i
  have hτ : ‖τ‖ ^ 2 = r i ^ 2 := by
    rw [show τ = T t r i j - t.points i from rfl, ← dist_eq_norm, dist_comm,
      (T_spec' hfb hij).2.1]
  have hR : ‖u - τ‖ ^ 2 = s.radius ^ 2 := by
    rw [show u - τ = s.center - T t r i j by simp only [u, τ]; abel, ← dist_eq_norm, dist_comm,
      EuclideanGeometry.mem_sphere.mp hT]
  -- 对每个 Soddy 球得到一个 ρ 的一次式
  have lin : ∀ {S : E3} {ρs : ℝ}, IsSoddy t r S ρs → S = Pρ t r ρs →
      dist s.center S ^ 2 = s.radius ^ 2 + ρs ^ 2 →
      2 * ⟪u, τ - p0⟫ + ρs * (2 * r i - 2 * ⟪u, A⟫) = 0 := by
    intro S ρs hS hSP ho
    have hSi := hS.2 i
    have eS : S - t.points i = p0 + ρs • A := by
      rw [hSP, Pρ_affine hfb ρs]; simp only [p0, A]; abel
    rw [dist_eq_norm, eS] at hSi
    rw [dist_eq_norm, show s.center - S = u - (S - t.points i) by simp only [u]; abel, eS,
      ← hR] at ho
    have i1 : ⟪u, p0 + ρs • A⟫ = ⟪u, p0⟫ + ρs * ⟪u, A⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    rw [norm_sub_sq_real u (p0 + ρs • A), norm_sub_sq_real u τ, hSi, hτ, i1] at ho
    rw [inner_sub_right]
    linarith
  have l₁ := lin h₁ e₁ ho₁
  have l₂ := lin h₂ e₂ ho₂
  have hY : ⟪u, A⟫ = r i := by
    have : (ρ₁ - ρ₂) * (2 * r i - 2 * ⟪u, A⟫) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hρ)
    linarith
  have hX : ⟪u, τ - p0⟫ = 0 := by rw [hY] at l₁; linarith
  -- 结论
  have hv := orth_vec hfb hij hik hil hjk hjl hkl
  have hst := stewart hfb hik hil hkl
  have hrad : 0 ≤ s.radius := (EuclideanGeometry.mem_sphere.mp hT) ▸ dist_nonneg
  set τ' := T t r k l - t.points i
  have hτ' : ‖τ'‖ ^ 2 = r i ^ 2 + 4 * r i * r k * r l / (r k + r l) := by
    rw [show τ' = T t r k l - t.points i from rfl, ← dist_eq_norm, dist_comm, hst]
  have hd : τ - τ' = ((r i * r j * r k + r i * r j * r l + r i * r k * r l + r j * r k * r l) /
      (r i * r j * (r k + r l))) • (τ - p0) + (-2 * r k * r l / (r k + r l)) • A := by
    rw [show τ - τ' = T t r i j - T t r k l by simp only [τ, τ']; abel,
      show τ - p0 = T t r i j - Pρ t r 0 by simp only [τ, p0]; abel, hv]
  have hin : ⟪u, τ - τ'⟫ = (-2 * r k * r l / (r k + r l)) * r i := by
    rw [hd, inner_add_right, real_inner_smul_right, real_inner_smul_right, hX, hY]; ring
  have hkl' : r k + r l ≠ 0 := by have := hr k; have := hr l; linarith
  rw [EuclideanGeometry.mem_sphere, dist_comm, ← sq_eq_sq₀ dist_nonneg hrad, ← hR, dist_eq_norm,
    show s.center - T t r k l = u - τ' by simp only [u, τ']; abel, norm_sub_sq_real u τ',
    norm_sub_sq_real u τ, hτ', hτ]
  rw [inner_sub_right] at hin
  field_simp
  field_simp at hin
  linarith

end GeometryResearch.Midsphere
