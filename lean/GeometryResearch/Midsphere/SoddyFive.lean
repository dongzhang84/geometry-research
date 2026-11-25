module

public import GeometryResearch.Midsphere.Eight

/-!
# 定理 10（Soddy 五点球）的证明

论文用以 T_kl 为中心的反演。这里改用代数方法，先证 (i j | k l) = (0 1 | 2 3) 的情形，
再对单形重新编号得到一般情形。

所求的球写成 pow_σ(X) + ℓ(X) = 0，σ 为 Soddy 球，ℓ 为仿射函数（重心坐标下的值 `L10`）。
- 两个切点在 σ 上，只需 ℓ 在它们上为零；
- Z、N 的条件是 rᵢ、ρ 的有理恒等式；
- 对 M′ = ι_σ(M)，pow_σ(M′) + ℓ(M′) = (pow_σ(M)(ℓ(S) − ρ²) + ρ²ℓ(M))/|MS|²，
  其分子是 Soddy 方程 Q(ρ) 的倍数。
ℓ 的表达式里有 1/(r₀ − r₁)。r₀ = r₁ 时，交换 V₀、V₁ 的反射保持五个点不动，五点都在平面
x₀ = x₁ 上。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- Lagrange 公式：|XY|² = Σ xₐ|VₐY|² − ½ΣΣ xₐx_b e_ab（x 归一化）。 -/
theorem dist_ofW_pt (hfb : IsFourBall t r) {x : Fin 4 → ℝ} (hx : ∑ m, x m ≠ 0) (Y : E3) :
    dist (ofWeights t x) Y ^ 2 =
      ∑ a, (x a / ∑ m, x m) * dist (t.points a) Y ^ 2 -
        (1 / 2) * ∑ a, ∑ b, (x a / ∑ m, x m) * (x b / ∑ m, x m) * e r a b := by
  set y : Fin 4 → ℝ := fun m => x m / ∑ m, x m with hy_def
  have hy : ∑ m, y m = 1 := by simp only [y]; rw [← Finset.sum_div, div_self hx]
  have nx : ofWeights t x = ofWeights t y := by
    rw [show y = fun m => (1 / ∑ m, x m) * x m by funext m; simp only [y]; ring]
    exact (ofW_smul t _ (one_div_ne_zero hx) x).symm
  change dist (ofWeights t x) Y ^ 2 = ∑ a, y a * dist (t.points a) Y ^ 2 -
    (1 / 2) * ∑ a, ∑ b, y a * y b * e r a b
  rw [nx]
  clear_value y
  have ex := ofW_sub_V0 t y (by rw [hy]; exact one_ne_zero)
  rw [hy, div_one, one_smul] at ex
  have hv : ∀ a, dist (t.points a) Y ^ 2 = ‖w t a‖ ^ 2 - 2 * ⟪w t a, Y - t.points 0⟫ +
      ‖Y - t.points 0‖ ^ 2 := by
    intro a
    rw [dist_eq_norm, show t.points a - Y = w t a - (Y - t.points 0) by simp only [w]; abel,
      norm_sub_sq_real]
  have hw : ∀ a, ‖w t a‖ ^ 2 = g r a a := fun a => by
    rw [← real_inner_self_eq_norm_sq, inner_w hfb]
  rw [dist_eq_norm, show ofWeights t y - Y = L t y - (Y - t.points 0) by rw [← ex]; abel,
    norm_sub_sq_real, ← real_inner_self_eq_norm_sq, inner_L hfb]
  simp only [hv, hw, L, sum_inner, real_inner_smul_left]
  generalize Y - t.points 0 = u
  simp only [Fin.sum_univ_four, Fin.sum_univ_three, g, e] at hy ⊢
  simp
  linear_combination (y 1 * (r 0 + r 1) ^ 2 + y 2 * (r 0 + r 2) ^ 2 + y 3 * (r 0 + r 3) ^ 2 -
    ‖u‖ ^ 2) * hy

/-- Soddy 球的幂：pow_σ(X) = Σ xₐ(rₐ² + 2ρrₐ) − ½ΣΣ xₐx_b e_ab。 -/
theorem powσ (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) {x : Fin 4 → ℝ}
    (hx : ∑ m, x m ≠ 0) :
    dist (ofWeights t x) S ^ 2 - ρs ^ 2 =
      ∑ a, (x a / ∑ m, x m) * (r a ^ 2 + 2 * ρs * r a) -
        (1 / 2) * ∑ a, ∑ b, (x a / ∑ m, x m) * (x b / ∑ m, x m) * e r a b := by
  have hs : ∑ a, x a / ∑ m, x m = 1 := by rw [← Finset.sum_div, div_self hx]
  rw [dist_ofW_pt hfb hx]
  simp only [dist_comm (t.points _) S, hS.2]
  have : ∑ a, (x a / ∑ m, x m) * (ρs + r a) ^ 2 =
      ∑ a, (x a / ∑ m, x m) * (r a ^ 2 + 2 * ρs * r a) + ρs ^ 2 * ∑ a, x a / ∑ m, x m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [this, hs]; ring

/-- 反演点处 pow_σ + ℓ 的值。 -/
theorem inv_comb (Lw : Fin 4 → ℝ) {S X : E3} {ρs : ℝ} (hX : X ≠ S) :
    dist (inversion S |ρs| X) S ^ 2 - ρs ^ 2 + ellV t Lw (inversion S |ρs| X) =
      ((dist X S ^ 2 - ρs ^ 2) * (ellV t Lw S - ρs ^ 2) + ρs ^ 2 * ellV t Lw X) /
        dist X S ^ 2 := by
  have hd : dist X S ≠ 0 := dist_ne_zero.mpr hX
  rw [dist_inversion_center, inversion_eq_lineMap, ellV_line, div_pow, sq_abs]
  field_simp
  rw [sq_abs]
  ring

/-- 切点在 Soddy 球上。 -/
theorem spt_onσ (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) (i : Fin 4) :
    dist (soddyPt t r S ρs i) S ^ 2 = ρs ^ 2 := by
  have hne := soddy_ne hfb hS i
  have h := hS.2 i
  rw [dist_comm] at h
  rw [soddyPt, dist_eq_norm, AffineMap.lineMap_apply_module,
    show (1 - r i / (r i + ρs)) • t.points i + (r i / (r i + ρs)) • S - S =
      (ρs / (r i + ρs)) • (t.points i - S) by
      rw [show ρs / (r i + ρs) = 1 - r i / (r i + ρs) by field_simp; ring]; module,
    norm_smul, mul_pow, ← dist_eq_norm, h, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- e₃(r)。 -/
def e3r (r : Fin 4 → ℝ) : ℝ := r 0 * r 1 * r 2 + r 0 * r 1 * r 3 + r 0 * r 2 * r 3 + r 1 * r 2 * r 3

/-- Π − ρe₃。 -/
def Wq (r : Fin 4 → ℝ) (ρs : ℝ) : ℝ := r 0 * r 1 * r 2 * r 3 - ρs * e3r r

/-- ℓ 的系数中出现的多项式。 -/
def Aq (a b c d ρs : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 * c ^ 2 * d - 4 * a ^ 2 * b ^ 2 * c ^ 2 * ρs + 2 * a ^ 2 * b ^ 2 * c * d ^ 2 +
    4 * a ^ 2 * b ^ 2 * c * d * ρs - 4 * a ^ 2 * b ^ 2 * d ^ 2 * ρs +
    5 * a ^ 2 * b * c ^ 2 * d * ρs + 5 * a ^ 2 * b * c * d ^ 2 * ρs -
    3 * a ^ 2 * c ^ 2 * d ^ 2 * ρs + 4 * a * b ^ 2 * c ^ 2 * d ^ 2 +
    3 * a * b ^ 2 * c ^ 2 * d * ρs + 3 * a * b ^ 2 * c * d ^ 2 * ρs +
    4 * a * b * c ^ 2 * d ^ 2 * ρs - 5 * b ^ 2 * c ^ 2 * d ^ 2 * ρs

/-- 公分母 r₂r₃(r₀ − r₁)e₃(2Π − ρe₃)。 -/
def Dq (r : Fin 4 → ℝ) (ρs : ℝ) : ℝ :=
  r 2 * r 3 * (r 0 - r 1) * e3r r * (2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r)

/-- 定理 10 的仿射函数 ℓ 在四个顶点上的值。 -/
def L10 (r : Fin 4 → ℝ) (ρs : ℝ) : Fin 4 → ℝ :=
  ![-2 * r 0 * Wq r ρs * Aq (r 0) (r 1) (r 2) (r 3) ρs / Dq r ρs,
    2 * r 1 * Wq r ρs * Aq (r 1) (r 0) (r 2) (r 3) ρs / Dq r ρs,
    2 * r 2 * Wq r ρs / e3r r, 2 * r 3 * Wq r ρs / e3r r]

theorem e3r_pos (hfb : IsFourBall t r) : 0 < e3r r := by
  have hr := hfb.1
  have := hr 0; have := hr 1; have := hr 2; have := hr 3
  simp only [e3r]; positivity

/-- 2Π − ρe₃ ≠ 0（否则 ρ = 2/s，与 Soddy 方程矛盾）。 -/
theorem two_ne (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r ≠ 0 := by
  intro h
  have hr := hfb.1
  have hD := D_pos hfb
  have hQ := soddy_Q hfb hS
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hs : ρs * sInv r = 2 := by
    simp only [sInv, Fin.sum_univ_four]
    field_simp
    simp only [e3r] at h
    linear_combination -h
  have : Ddisc r * ρs ^ 2 = 0 := by
    have e : (sInv r ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2 =
        (ρs * sInv r) ^ 2 / 4 - 9 * (Ddisc r * ρs ^ 2) := by ring
    rw [e, hs] at hQ
    linarith
  rcases mul_eq_zero.mp this with h' | h'
  · linarith
  · exact hS.1 (pow_eq_zero_iff two_ne_zero |>.mp h')

theorem Dq_ne (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) : Dq r ρs ≠ 0 := by
  have hr := hfb.1
  simp only [Dq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hr 2).ne' (hr 3).ne')
    (sub_ne_zero.mpr h01)) (e3r_pos hfb).ne') (two_ne hfb hS)

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem condZ (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) :
    dist (Z t r) S ^ 2 - ρs ^ 2 + ellV t (L10 r ρs) (Z t r) = 0 := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hs : ∑ m, 1 / r m ≠ 0 := (sInv_pos hfb).ne'
  have hDq := Dq_ne hfb hS h01
  have hE := (e3r_pos hfb).ne'
  rw [Z, powσ hfb hS hs, ellV_ofW _ _ hs]
  simp only [L10]
  generalize hDv : Dq r ρs = Dv at hDq ⊢
  generalize hEv : e3r r = Ev at hE ⊢
  simp only [Fin.sum_univ_four, e]
  simp
  field_simp
  rw [← hDv, ← hEv]
  simp only [Dq, Wq, Aq, e3r]
  ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem condN (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) :
    dist (N t r 0 1 2 3) S ^ 2 - ρs ^ 2 + ellV t (L10 r ρs) (N t r 0 1 2 3) = 0 := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have h01' := (add_pos (hr 0) (hr 1)).ne'; have h23' := (add_pos (hr 2) (hr 3)).ne'
  have hDq := Dq_ne hfb hS h01
  have hE := (e3r_pos hfb).ne'
  have hsum : ∑ m, (tw 0 1 (r 0 / (r 0 + r 1)) m + tw 2 3 (r 2 / (r 2 + r 3)) m) / 2 = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, tw_sum (by decide), tw_sum (by decide)]; norm_num
  rw [N, T, T, lineMap_eq_ofW (by decide), lineMap_eq_ofW (by decide),
    mid_ofW (tw_sum (by decide) _) (tw_sum (by decide) _),
    powσ hfb hS (by rw [hsum]; exact one_ne_zero), ellV_ofW _ _ (by rw [hsum]; exact one_ne_zero),
    hsum]
  simp only [L10]
  generalize hDv : Dq r ρs = Dv at hDq ⊢
  generalize hEv : e3r r = Ev at hE ⊢
  simp only [Fin.sum_univ_four, e, tw]
  simp
  field_simp
  rw [← hDv, ← hEv]
  simp only [Dq, Wq, Aq, e3r]
  ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem ellS10 (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) :
    ellV t (L10 r ρs) S = -2 * ρs * Wq r ρs / e3r r := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hDq := Dq_ne hfb hS h01
  have hE := (e3r_pos hfb).ne'
  have hsumP : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [S_eq hfb hS, ellV_ofW _ _ (by rw [hsumP]; exact mul_ne_zero (by norm_num) hD), hsumP]
  simp only [L10]
  generalize hDv : Dq r ρs = Dv at hDq ⊢
  generalize hEv : e3r r = Ev at hE ⊢
  generalize hDd : Ddisc r = Dd at hD ⊢
  simp only [Fin.sum_univ_four]
  simp
  field_simp
  rw [← hDv, ← hEv, ← hDd]
  simp only [Dq, Wq, Aq, e3r, Ddisc, sInv, qInv, Fin.sum_univ_four]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem powM10 (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    dist (M t r) S ^ 2 - ρs ^ 2 = -Wq r ρs / (3 * Ddisc r * (r 0 * r 1 * r 2 * r 3)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [M_comb, powσ hfb hS (by rw [hsumM]; positivity), hsumM]
  generalize hDd : Ddisc r = Dd at hD ⊢
  simp only [Fin.sum_univ_four, e, sInv]
  simp
  field_simp
  rw [← hDd]
  simp only [Wq, e3r, Ddisc, sInv, qInv, Fin.sum_univ_four]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 有理恒等式
theorem ellM10 (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) :
    ellV t (L10 r ρs) (M t r) = -12 * (r 0 * r 1 * r 2 * r 3) * ρs * Wq r ρs /
      (e3r r * (2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hDq := Dq_ne hfb hS h01
  have hE := (e3r_pos hfb).ne'
  have h2n := two_ne hfb hS
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [M_comb, ellV_ofW _ _ (by rw [hsumM]; positivity), hsumM]
  simp only [L10]
  generalize hDv : Dq r ρs = Dv at hDq ⊢
  generalize hFv : 2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r = Fv at h2n ⊢
  generalize hEv : e3r r = Ev at hE ⊢
  generalize hDd : Ddisc r = Dd at hD ⊢
  simp only [Fin.sum_univ_four]
  simp
  field_simp
  rw [← hDv, ← hFv, ← hEv, ← hDd]
  have hsub : r 0 - r 1 ≠ 0 := sub_ne_zero.mpr h01
  have h2e := two_ne hfb hS
  have hEe := (e3r_pos hfb).ne'
  simp only [e3r] at h2e hEe
  simp only [Dq, Wq, Aq, e3r, Ddisc, sInv, qInv, Fin.sum_univ_four]
  field_simp
  ring

/-- M′ 的条件：pow_σ(M)(ℓ(S) − ρ²) + ρ²ℓ(M) = 0（分子是 Soddy 方程的倍数）。 -/
theorem condM (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) :
    (dist (M t r) S ^ 2 - ρs ^ 2) * (ellV t (L10 r ρs) S - ρs ^ 2) +
      ρs ^ 2 * ellV t (L10 r ρs) (M t r) = 0 := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hE := (e3r_pos hfb).ne'
  have h2n := two_ne hfb hS
  have hQ := soddy_Q hfb hS
  have hP : r 0 * r 1 * r 2 * r 3 ≠ 0 := by positivity
  rw [powM10 hfb hS, ellS10 hfb hS h01, ellM10 hfb hS h01]
  have hse : sInv r = e3r r / (r 0 * r 1 * r 2 * r 3) := by
    simp only [sInv, e3r, Fin.sum_univ_four]; field_simp; ring
  rw [hse] at hQ
  rw [show (0 : ℝ) = 4 * ρs * (r 0 * r 1 * r 2 * r 3) * Wq r ρs /
      (3 * Ddisc r * e3r r * (2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r)) *
      (1 - e3r r / (r 0 * r 1 * r 2 * r 3) * ρs +
        ((e3r r / (r 0 * r 1 * r 2 * r 3)) ^ 2 / 4 - 9 * Ddisc r) * ρs ^ 2) by
      rw [hQ, mul_zero]]
  simp only [Wq]
  generalize hFv : 2 * (r 0 * r 1 * r 2 * r 3) - ρs * e3r r = Fv at h2n ⊢
  generalize hEv : e3r r = Ev at hE hFv ⊢
  generalize hDd : Ddisc r = Dd at hD ⊢
  generalize hPv : r 0 * r 1 * r 2 * r 3 = Pv at hP hFv ⊢
  field_simp
  subst hFv
  ring

/-- r₀ ≠ r₁ 时 M 不是 Soddy 球心。 -/
theorem M_ne_S (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs)
    (h01 : r 0 ≠ r 1) : M t r ≠ S := by
  intro h
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hq := qInv_pos hfb
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have hsumP : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [M_comb, S_eq hfb hS] at h
  have hs1 : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) ≠ 0 := by
    rw [hsumM]; positivity
  have hs2 : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) ≠ 0 := by
    rw [hsumP]; exact mul_ne_zero (by norm_num) hD
  have key : ∀ m, ρs * (qInv r * r m - sInv r) = 0 := by
    intro m
    have := congrArg (fun X => GeometryResearch.Orthocentric.bary t X m) h
    rw [GeometryResearch.Orthocentric.bary_ofWeights' t _ hs1,
      GeometryResearch.Orthocentric.bary_ofWeights' t _ hs2, hsumM, hsumP] at this
    have hm := (hr m).ne'
    rw [div_eq_div_iff (by positivity) (mul_ne_zero (by norm_num) hD)] at this
    have k2 : ρs * (qInv r * r m - sInv r) * (6 * Ddisc r) =
        -(r m ^ 2) * ((0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) * (-12 * Ddisc r) -
          (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r m) + (2 - ρs * sInv r) * (1 / r m ^ 2)) *
            (6 * Ddisc r)) := by
      field_simp; ring
    rw [this, sub_self, mul_zero] at k2
    exact (mul_eq_zero.mp k2).resolve_right (mul_ne_zero (by norm_num) hD)
  have k0 := (mul_eq_zero.mp (key 0)).resolve_left hS.1
  have k1 := (mul_eq_zero.mp (key 1)).resolve_left hS.1
  exact h01 (mul_left_cancel₀ hq.ne' (by linarith))

theorem ellSym_ofW (Lw : Fin 4 → ℝ) (w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0)
    (h : Lw 0 * w 0 + Lw 1 * w 1 + Lw 2 * w 2 + Lw 3 * w 3 = 0) :
    ellV t Lw (ofWeights t w) = 0 := by
  rw [ellV_ofW _ _ hw, Fin.sum_univ_four]
  rw [show Lw 0 * (w 0 / ∑ j, w j) + Lw 1 * (w 1 / ∑ j, w j) + Lw 2 * (w 2 / ∑ j, w j) +
    Lw 3 * (w 3 / ∑ j, w j) = (Lw 0 * w 0 + Lw 1 * w 1 + Lw 2 * w 2 + Lw 3 * w 3) / ∑ j, w j by
    ring, h, zero_div]

set_option maxHeartbeats 1000000 in -- 组装
/-- 定理 10 在 (0 1 | 2 3) 情形的证明。 -/
theorem sf_main (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    MCospherical ({Z t r, N t r 0 1 2 3, soddyPt t r S ρs 2, soddyPt t r S ρs 3,
      inversion S |ρs| (M t r)} : Set E3) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have hsumP : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  by_cases h01 : r 0 = r 1
  · right
    set Ls : Fin 4 → ℝ := ![1, -1, 0, 0]
    have lS : ellV t Ls S = 0 := by
      rw [S_eq hfb hS]
      exact ellSym_ofW _ _ (by rw [hsumP]; exact mul_ne_zero (by norm_num) hD)
        (by simp [Ls, h01])
    have lM : ellV t Ls (M t r) = 0 := by
      rw [M_comb]
      exact ellSym_ofW _ _ (by rw [hsumM]; positivity) (by simp [Ls, h01])
    have lsp : ∀ k : Fin 4, Ls k = 0 → ellV t Ls (soddyPt t r S ρs k) = 0 := by
      intro k hk
      rw [soddyPt, ellV_line, ellV_vertex, hk, lS]; ring
    refine coplanar_ell (t := t) Ls (a := 0) (b := 1) (by simp [Ls]; norm_num) (fun X hX => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [Z]; exact ellSym_ofW _ _ (sInv_pos hfb).ne' (by simp [Ls, h01])
    · have hsum : ∑ m, (tw 0 1 (r 0 / (r 0 + r 1)) m + tw 2 3 (r 2 / (r 2 + r 3)) m) / 2 = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, tw_sum (by decide), tw_sum (by decide)]
        norm_num
      rw [N, T, T, lineMap_eq_ofW (by decide), lineMap_eq_ofW (by decide),
        mid_ofW (tw_sum (by decide) _) (tw_sum (by decide) _)]
      exact ellSym_ofW _ _ (by rw [hsum]; exact one_ne_zero) (by
        have := (hr 1).ne'; simp [Ls, tw, h01]; field_simp; ring)
    · exact lsp 2 rfl
    · exact lsp 3 rfl
    · rw [inversion_eq_lineMap, ellV_line, lS, lM]; ring
  · left
    obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) (L10 r ρs) S
    refine cosph_of S S c (κ - ρs ^ 2) (fun X hX => ?_)
    suffices h : dist X S ^ 2 - ρs ^ 2 + ellV t (L10 r ρs) X = 0 by rw [hc] at h; linarith
    have hsk : ∀ k : Fin 4, k = 2 ∨ k = 3 →
        dist (soddyPt t r S ρs k) S ^ 2 - ρs ^ 2 + ellV t (L10 r ρs) (soddyPt t r S ρs k) = 0 := by
      intro k hk
      have hne := soddy_ne hfb hS k
      have hE := (e3r_pos hfb).ne'
      rw [spt_onσ hfb hS, soddyPt, ellV_line, ellV_vertex, ellS10 hfb hS h01]
      have hL : L10 r ρs k = 2 * r k * Wq r ρs / e3r r := by
        rcases hk with rfl | rfl <;> rfl
      rw [hL]
      field_simp
      ring
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · exact condZ hfb hS h01
    · exact condN hfb hS h01
    · exact hsk 2 (by simp)
    · exact hsk 3 (by simp)
    · rw [inv_comb _ (M_ne_S hfb hS h01), condM hfb hS h01, zero_div]

/-! ## 重新编号 -/

theorem ofW_reindex (σ : Fin 4 ≃ Fin 4) (w : Fin 4 → ℝ) :
    ofWeights (t.reindex σ.symm) w = ofWeights t (fun m => w (σ.symm m)) := by
  simp only [GeometryResearch.Orthocentric.ofWeights]
  have hs : ∑ j, w (σ.symm j) = ∑ j, w j := Equiv.sum_comp σ.symm w
  rw [hs]
  have := Finset.univ.affineCombination_map (k := ℝ) σ.toEmbedding
    (fun m => w (σ.symm m) / ∑ j, w j) t.points
  rw [Finset.map_univ_equiv] at this
  rw [this]
  congr 1
  funext m
  simp

theorem fourBall_reindex (hfb : IsFourBall t r) (σ : Fin 4 ≃ Fin 4) :
    IsFourBall (t.reindex σ.symm) (fun m => r (σ m)) := by
  refine ⟨fun m => hfb.1 _, fun a b hab => ?_⟩
  simp only [Affine.Simplex.reindex, Function.comp, Equiv.symm_symm]
  exact hfb.2 _ _ (σ.injective.ne hab)

theorem soddy_reindex {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) (σ : Fin 4 ≃ Fin 4) :
    IsSoddy (t.reindex σ.symm) (fun m => r (σ m)) S ρs := by
  refine ⟨hS.1, fun m => ?_⟩
  simp only [Affine.Simplex.reindex, Function.comp, Equiv.symm_symm]
  exact hS.2 _

theorem sInv_reindex (σ : Fin 4 ≃ Fin 4) : sInv (fun m => r (σ m)) = sInv r :=
  Equiv.sum_comp σ (fun m => 1 / r m)

theorem Z_reindex (σ : Fin 4 ≃ Fin 4) : Z (t.reindex σ.symm) (fun m => r (σ m)) = Z t r := by
  rw [Z, ofW_reindex, Z]; simp

theorem M_reindex (σ : Fin 4 ≃ Fin 4) : M (t.reindex σ.symm) (fun m => r (σ m)) = M t r := by
  rw [M, ofW_reindex, M, sInv_reindex]; simp

/-- 由两两不同的 i, j, k, l 构造的置换。 -/
def perm4 {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) : Fin 4 ≃ Fin 4 :=
  Equiv.ofBijective ![i, j, k, l] (Finite.injective_iff_bijective.mp (by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]))

/-- 定理 10 的证明。 -/
theorem soddy_five_main (hfb : IsFourBall t r) {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {S : E3} {ρs : ℝ}
    (hS : IsSoddy t r S ρs) :
    MCospherical ({Z t r, N t r i j k l, soddyPt t r S ρs k, soddyPt t r S ρs l,
      inversion S |ρs| (M t r)} : Set E3) := by
  set σ := perm4 hij hik hil hjk hjl hkl
  have h := sf_main (fourBall_reindex hfb σ) (soddy_reindex hS σ)
  rw [Z_reindex, M_reindex] at h
  have e0 : σ 0 = i := rfl
  have e1 : σ 1 = j := rfl
  have e2 : σ 2 = k := rfl
  have e3 : σ 3 = l := rfl
  have hN : N (t.reindex σ.symm) (fun m => r (σ m)) 0 1 2 3 = N t r i j k l := by
    simp only [N, T, Affine.Simplex.reindex, Function.comp, Equiv.symm_symm, e0, e1, e2, e3]
  have hs2 : soddyPt (t.reindex σ.symm) (fun m => r (σ m)) S ρs 2 = soddyPt t r S ρs k := by
    simp only [soddyPt, Affine.Simplex.reindex, Function.comp, Equiv.symm_symm, e2]
  have hs3 : soddyPt (t.reindex σ.symm) (fun m => r (σ m)) S ρs 3 = soddyPt t r S ρs l := by
    simp only [soddyPt, Affine.Simplex.reindex, Function.comp, Equiv.symm_symm, e3]
  rwa [hN, hs2, hs3] at h

end GeometryResearch.Midsphere
