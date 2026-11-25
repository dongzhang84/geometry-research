module

public import GeometryResearch.Midsphere.Homothety

/-!
# 定理 4（中心平面上的四点共圆）的证明

记 Eₖ 为切长的初等对称多项式。O、M、G、K 两两的距离平方、R²、ρ² 都是 E₁, …, E₄ 与 D 的简单
有理式（`dOG` 等）。所有点都在平面 OMG 上；取 v 为 OG 垂直于 OM 的分量，
n = λv，λ = (R² − |OG|²)/(2|v|²)，则球心 O + n、半径² = R² + |n|² 的球经过 A、B、2O − G、G′，
经过 K′ 等价于论文 (eq:four)，它是 E₁, …, E₄ 的有理恒等式。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights G O R)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 非归一化权重的距离公式。 -/
theorem dist_ofW' (hfb : IsFourBall t r) {x y : Fin 4 → ℝ} (hx : ∑ m, x m ≠ 0)
    (hy : ∑ m, y m ≠ 0) :
    dist (ofWeights t x) (ofWeights t y) ^ 2 =
      -(1 / 2) * ∑ a, ∑ b, (x a / ∑ m, x m - y a / ∑ m, y m) *
        (x b / ∑ m, x m - y b / ∑ m, y m) * e r a b := by
  have nx : ofWeights t x = ofWeights t (fun m => (1 / ∑ m, x m) * x m) :=
    (ofW_smul t _ (one_div_ne_zero hx) x).symm
  have ny : ofWeights t y = ofWeights t (fun m => (1 / ∑ m, y m) * y m) :=
    (ofW_smul t _ (one_div_ne_zero hy) y).symm
  rw [nx, ny, dist_ofW hfb (by rw [← Finset.mul_sum]; exact one_div_mul_cancel hx)
    (by rw [← Finset.mul_sum]; exact one_div_mul_cancel hy)]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

/-- 切长的初等对称多项式。 -/
def es1 (r : Fin 4 → ℝ) : ℝ := r 0 + r 1 + r 2 + r 3
def es2 (r : Fin 4 → ℝ) : ℝ :=
  r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 1 * r 2 + r 1 * r 3 + r 2 * r 3
def es3 (r : Fin 4 → ℝ) : ℝ :=
  r 0 * r 1 * r 2 + r 0 * r 1 * r 3 + r 0 * r 2 * r 3 + r 1 * r 2 * r 3
def es4 (r : Fin 4 → ℝ) : ℝ := r 0 * r 1 * r 2 * r 3

theorem D_E (hfb : IsFourBall t r) : 12 * Ddisc r * es4 r ^ 2 = 4 * es2 r * es4 r - es3 r ^ 2 := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es2, es3, es4]
  field_simp
  ring

/-- |OG|²。 -/
theorem dOG (hfb : IsFourBall t r) :
    dist (O t) (G t) ^ 2 = -(es1 r ^ 2 * (8 * es2 r * es4 r - 3 * es3 r ^ 2)) /
      (16 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumO : ∑ m, ((-12 * Ddisc r / ∑ j, r j) * 1 + (-qInv r) * (1 / r m) +
      sInv r * (1 / r m ^ 2)) = -48 * Ddisc r / es1 r := by
    simp only [Fin.sum_univ_four, sInv, qInv, hsr]; ring
  have hsumG : ∑ m : Fin 4, (1 : ℝ) = 4 := by simp
  rw [O_eq hfb, G_eq, dist_ofW' hfb (by rw [hsumO]; exact div_ne_zero (by positivity) hE1.ne')
    (by rw [hsumG]; norm_num), hsumO, hsumG]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dOM (hfb : IsFourBall t r) :
    dist (O t) (M t r) ^ 2 = (es1 r ^ 2 * es2 r * es4 r - 4 * es1 r * es3 r * es4 r - 4 * es2 r ^ 2 * es4 r + es2 r * es3 r ^ 2 + 16 * es4 r ^ 2) / (4 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumO : ∑ m, ((-12 * Ddisc r / ∑ j, r j) * 1 + (-qInv r) * (1 / r m) +
      sInv r * (1 / r m ^ 2)) = -48 * Ddisc r / es1 r := by
    simp only [Fin.sum_univ_four, sInv, qInv, hsr]; ring
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [O_eq hfb, M_comb, dist_ofW' hfb (by rw [hsumO]; exact div_ne_zero (by positivity) hE1.ne') (by rw [hsumM]; positivity), hsumO, hsumM]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dGM (hfb : IsFourBall t r) :
    dist (G t) (M t r) ^ 2 = (4 * es1 r ^ 2 * es2 r * es4 r - es1 r ^ 2 * es3 r ^ 2 - 16 * es2 r ^ 2 * es4 r + 4 * es2 r * es3 r ^ 2 + 64 * es4 r ^ 2) / (16 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumG : ∑ m : Fin 4, (1 : ℝ) = 4 := by simp
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [G_eq, M_comb, dist_ofW' hfb (by rw [hsumG]; norm_num) (by rw [hsumM]; positivity), hsumG, hsumM]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dOK (hfb : IsFourBall t r) :
    dist (O t) (K t) ^ 2 = es1 r ^ 2 * (es1 r ^ 2 * es2 r * es3 r ^ 2 * es4 r - 8 * es1 r * es2 r * es3 r * es4 r ^ 2 - 4 * es2 r ^ 2 * es3 r ^ 2 * es4 r + es2 r * es3 r ^ 4 - 32 * es2 r * es4 r ^ 3 + 12 * es3 r ^ 2 * es4 r ^ 2) / (4 * (es1 r * es3 r - 4 * es4 r) ^ 2 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumO : ∑ m, ((-12 * Ddisc r / ∑ j, r j) * 1 + (-qInv r) * (1 / r m) +
      sInv r * (1 / r m ^ 2)) = -48 * Ddisc r / es1 r := by
    simp only [Fin.sum_univ_four, sInv, qInv, hsr]; ring
  have hsumK : ∑ m, ((-(∏ j, r j)) * 1 + ((∏ j, r j) * ∑ j, r j) * (1 / r m) +
      0 * (1 / r m ^ 2)) = es1 r * es3 r - 4 * es4 r := by
    simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4]; field_simp; ring
  have hK0 : es1 r * es3 r - 4 * es4 r ≠ 0 := by
    have := sr_s_gt hfb
    have hP : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
    have e : es1 r * es3 r - 4 * es4 r = (∏ j, r j) * ((∑ j, r j) * sInv r - 4) := by
      simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4, sInv]; field_simp; ring
    rw [e]; exact mul_ne_zero hP.ne' (by linarith)
  rw [O_eq hfb, K_comb hfb, dist_ofW' hfb (by rw [hsumO]; exact div_ne_zero (by positivity) hE1.ne') (by rw [hsumK]; exact hK0), hsumO, hsumK]
  generalize hDv : Ddisc r = Dv at hD ⊢
  generalize hKv : es1 r * es3 r - 4 * es4 r = Kv at hK0 ⊢
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv, ← hKv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dKM (hfb : IsFourBall t r) :
    dist (K t) (M t r) ^ 2 = -(es4 r ^ 2 * (12 * es1 r ^ 2 * es2 r * es4 r - 7 * es1 r ^ 2 * es3 r ^ 2 + 32 * es1 r * es3 r * es4 r + 16 * es2 r ^ 2 * es4 r - 4 * es2 r * es3 r ^ 2 - 64 * es4 r ^ 2)) / ((es1 r * es3 r - 4 * es4 r) ^ 2 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumK : ∑ m, ((-(∏ j, r j)) * 1 + ((∏ j, r j) * ∑ j, r j) * (1 / r m) +
      0 * (1 / r m ^ 2)) = es1 r * es3 r - 4 * es4 r := by
    simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4]; field_simp; ring
  have hK0 : es1 r * es3 r - 4 * es4 r ≠ 0 := by
    have := sr_s_gt hfb
    have hP : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
    have e : es1 r * es3 r - 4 * es4 r = (∏ j, r j) * ((∑ j, r j) * sInv r - 4) := by
      simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4, sInv]; field_simp; ring
    rw [e]; exact mul_ne_zero hP.ne' (by linarith)
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [K_comb hfb, M_comb, dist_ofW' hfb (by rw [hsumK]; exact hK0) (by rw [hsumM]; positivity), hsumK, hsumM]
  generalize hDv : Ddisc r = Dv at hD ⊢
  generalize hKv : es1 r * es3 r - 4 * es4 r = Kv at hK0 ⊢
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv, ← hKv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dGK (hfb : IsFourBall t r) :
    dist (G t) (K t) ^ 2 = es1 r ^ 2 * (es1 r ^ 2 * es3 r ^ 2 + 16 * es1 r * es3 r * es4 r - 4 * es2 r * es3 r ^ 2 - 128 * es4 r ^ 2) / (16 * (es1 r * es3 r - 4 * es4 r) ^ 2) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumG : ∑ m : Fin 4, (1 : ℝ) = 4 := by simp
  have hsumK : ∑ m, ((-(∏ j, r j)) * 1 + ((∏ j, r j) * ∑ j, r j) * (1 / r m) +
      0 * (1 / r m ^ 2)) = es1 r * es3 r - 4 * es4 r := by
    simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4]; field_simp; ring
  have hK0 : es1 r * es3 r - 4 * es4 r ≠ 0 := by
    have := sr_s_gt hfb
    have hP : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
    have e : es1 r * es3 r - 4 * es4 r = (∏ j, r j) * ((∑ j, r j) * sInv r - 4) := by
      simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4, sInv]; field_simp; ring
    rw [e]; exact mul_ne_zero hP.ne' (by linarith)
  rw [G_eq, K_comb hfb, dist_ofW' hfb (by rw [hsumG]; norm_num) (by rw [hsumK]; exact hK0), hsumG, hsumK]
  generalize hKv : es1 r * es3 r - 4 * es4 r = Kv at hK0 ⊢
  simp only [Fin.sum_univ_four, Fin.prod_univ_four, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hKv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

theorem V0_ofW : t.points 0 = ofWeights t (tw 0 1 0) := by
  rw [← lineMap_eq_ofW (show (0 : Fin 4) ≠ 1 by decide), AffineMap.lineMap_apply_zero]

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dR (hfb : IsFourBall t r) :
    R t ^ 2 = es2 r * (es1 r ^ 2 * es4 r - 4 * es2 r * es4 r + es3 r ^ 2) /
      (4 * (12 * Ddisc r * es4 r ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hE1 : 0 < es1 r := by
    simp only [es1]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hsr : ∑ j, r j = es1 r := by simp only [es1, Fin.sum_univ_four]
  have hsumO : ∑ m, ((-12 * Ddisc r / ∑ j, r j) * 1 + (-qInv r) * (1 / r m) +
      sInv r * (1 / r m ^ 2)) = -48 * Ddisc r / es1 r := by
    simp only [Fin.sum_univ_four, sInv, qInv, hsr]; ring
  have hR : R t = dist (t.points 0) (O t) := (t.dist_circumcenter_eq_circumradius 0).symm
  rw [hR, V0_ofW, O_eq hfb, dist_ofW' hfb (by rw [tw_sum (by decide)]; exact one_ne_zero)
    (by rw [hsumO]; exact div_ne_zero (by positivity) hE1.ne'), tw_sum (by decide), hsumO]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, tw, e, sInv, qInv, hsr]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
theorem dρ (hfb : IsFourBall t r) :
    ρ t r ^ 2 = 4 * es4 r ^ 2 / (12 * Ddisc r * es4 r ^ 2) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have p0 := hr 0; have p1 := hr 1
  have hsumM : ∑ m, (0 * 1 + (sInv r / 2) * (1 / r m) + (-1) * (1 / r m ^ 2)) = 6 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  rw [ρ, T, lineMap_eq_ofW (show (0 : Fin 4) ≠ 1 by decide), M_comb,
    dist_ofW' hfb (by rw [hsumM]; positivity) (by rw [tw_sum (by decide)]; exact one_ne_zero),
    hsumM, tw_sum (by decide)]
  generalize hDv : Ddisc r = Dv at hD ⊢
  simp only [Fin.sum_univ_four, tw, e, sInv, qInv]
  simp
  field_simp
  rw [← hDv]
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four, es1, es2, es3, es4]
  field_simp
  ring

set_option maxHeartbeats 4000000 in -- 大的有理恒等式
/-- 定理 4 的代数核心（论文 (eq:four)），只涉及初等对称多项式。 -/
theorem alg4 {e1 e2 e3 e4 OG OM GM OK KM GK R2 ρ2 : ℝ}
    (hd : 4 * e2 * e4 - e3 ^ 2 ≠ 0) (hk : e1 * e3 - 4 * e4 ≠ 0) (hOM0 : OM ≠ 0) (hKM0 : KM ≠ 0)
    (hOG : OG = -(e1 ^ 2 * (8 * e2 * e4 - 3 * e3 ^ 2)) / (16 * (4 * e2 * e4 - e3 ^ 2)))
    (hOM : OM = (e1 ^ 2 * e2 * e4 - 4 * e1 * e3 * e4 - 4 * e2 ^ 2 * e4 + e2 * e3 ^ 2 +
      16 * e4 ^ 2) / (4 * (4 * e2 * e4 - e3 ^ 2)))
    (hGM : GM = (4 * e1 ^ 2 * e2 * e4 - e1 ^ 2 * e3 ^ 2 - 16 * e2 ^ 2 * e4 + 4 * e2 * e3 ^ 2 +
      64 * e4 ^ 2) / (16 * (4 * e2 * e4 - e3 ^ 2)))
    (hOK : OK = e1 ^ 2 * (e1 ^ 2 * e2 * e3 ^ 2 * e4 - 8 * e1 * e2 * e3 * e4 ^ 2 -
      4 * e2 ^ 2 * e3 ^ 2 * e4 + e2 * e3 ^ 4 - 32 * e2 * e4 ^ 3 + 12 * e3 ^ 2 * e4 ^ 2) /
      (4 * (e1 * e3 - 4 * e4) ^ 2 * (4 * e2 * e4 - e3 ^ 2)))
    (hKM : KM = -(e4 ^ 2 * (12 * e1 ^ 2 * e2 * e4 - 7 * e1 ^ 2 * e3 ^ 2 + 32 * e1 * e3 * e4 +
      16 * e2 ^ 2 * e4 - 4 * e2 * e3 ^ 2 - 64 * e4 ^ 2)) /
      ((e1 * e3 - 4 * e4) ^ 2 * (4 * e2 * e4 - e3 ^ 2)))
    (hGK : GK = e1 ^ 2 * (e1 ^ 2 * e3 ^ 2 + 16 * e1 * e3 * e4 - 4 * e2 * e3 ^ 2 -
      128 * e4 ^ 2) / (16 * (e1 * e3 - 4 * e4) ^ 2))
    (hR2 : R2 = e2 * (e1 ^ 2 * e4 - 4 * e2 * e4 + e3 ^ 2) / (4 * (4 * e2 * e4 - e3 ^ 2)))
    (hρ2 : ρ2 = 4 * e4 ^ 2 / (4 * e2 * e4 - e3 ^ 2)) :
    let mg := (OM + OG - GM) / 2
    let aM := (OK - OM - KM) / 2
    let aG := (OK + OG - GK) / 2 - mg
    let kap := ρ2 / KM
    (OM + 2 * kap * aM + kap ^ 2 * KM - R2) * (OG - mg ^ 2 / OM) =
      (R2 - OG) * (mg + kap * aG - mg / OM * (OM + kap * aM)) := by
  intro mg aM aG kap
  simp only [mg, aM, aG, kap]
  rw [hOG, hGM, hOK, hGK, hR2, hρ2]
  generalize hDd : 4 * e2 * e4 - e3 ^ 2 = Dd at hd hOM hKM ⊢
  generalize hKk : e1 * e3 - 4 * e4 = Kk at hk hOM hKM ⊢
  field_simp
  rw [hOM, hKM]
  field_simp
  rw [← hDd, ← hKk]
  ring

/-- 共面点集里，若 O、M、G 张成平面，则每个点减 O 都在 span{M − O, G − O} 中。 -/
theorem plane_span {S : Set E3} {Op Mp Gp X : E3} (hcop : Coplanar ℝ S) (hO : Op ∈ S)
    (hM : Mp ∈ S) (hG : Gp ∈ S) (hli : LinearIndependent ℝ ![Mp - Op, Gp - Op]) (hX : X ∈ S) :
    X - Op ∈ Submodule.span ℝ (Set.range ![Mp - Op, Gp - Op]) := by
  haveI := hcop.finiteDimensional_vectorSpan
  have hle : Submodule.span ℝ (Set.range ![Mp - Op, Gp - Op]) ≤ vectorSpan ℝ S := by
    rw [Submodule.span_le]
    rintro z ⟨m, rfl⟩
    fin_cases m
    · exact vsub_mem_vectorSpan ℝ hM hO
    · exact vsub_mem_vectorSpan ℝ hG hO
  have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range ![Mp - Op, Gp - Op])) = 2 := by
    rw [finrank_span_eq_card hli]; simp
  have hfS : Module.finrank ℝ (vectorSpan ℝ S) ≤ 2 := coplanar_iff_finrank_le_two.mp hcop
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [hfr]; exact hfS)
  rw [heq]
  exact vsub_mem_vectorSpan ℝ hX hO

/-- O、M、G 不共线，则 M − O、G − O 线性无关。 -/
theorem linIndep_of_not_collinear {Op Mp Gp : E3}
    (hcol : ¬ Collinear ℝ ({Op, Mp, Gp} : Set E3)) :
    LinearIndependent ℝ ![Mp - Op, Gp - Op] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_contra hne
  apply hcol
  rw [collinear_iff_of_mem (Set.mem_insert Op _)]
  by_cases hb : b = 0
  · have ha : a ≠ 0 := by intro h; exact hne ⟨h, hb⟩
    rw [hb, zero_smul, add_zero, smul_eq_zero] at hab
    have hMO : Mp = Op := sub_eq_zero.mp (hab.resolve_left ha)
    refine ⟨Gp - Op, fun X hX => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hMO]⟩
    · exact ⟨1, by simp⟩
  · refine ⟨Mp - Op, fun X hX => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨-a / b, ?_⟩
      have h2 : X - Op = (-a / b) • (Mp - Op) := by
        have : b • (X - Op) = -(a • (Mp - Op)) := eq_neg_of_add_eq_zero_right hab
        calc X - Op = b⁻¹ • (b • (X - Op)) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
          _ = (-a / b) • (Mp - Op) := by rw [this]; module
      rw [vadd_eq_add, ← h2]; abel

set_option maxHeartbeats 4000000 in -- 证明较长
/-- 定理 4 的证明。 -/
theorem concyclic_main (hfb : IsFourBall t r)
    (hcol : ¬ Collinear ℝ ({O t, M t r, G t} : Set E3)) (hKM : K t ≠ M t r) :
    let A := O t + (R t / ‖M t r - O t‖) • (M t r - O t)
    let B := O t - (R t / ‖M t r - O t‖) • (M t r - O t)
    let K' := inversion (M t r) (ρ t r) (K t)
    let G' := inversion (O t) (R t) (G t)
    let G2 := AffineMap.homothety (O t) (-1 : ℝ) (G t)
    Concyclic ({K', G', A, B, G2} : Set E3) ∧
      Coplanar ℝ ({G t, O t, K t, M t r, Z t r, K', G', A, B, G2} : Set E3) := by
  intro A B K' G' G2
  have hr := hfb.1
  set u := M t r - O t with hu_def
  set g := G t - O t with hg_def
  set a := K t - M t r with ha_def
  have hli : LinearIndependent ℝ ![u, g] := linIndep_of_not_collinear hcol
  have hcop := (central_main hfb).1
  have hKs : K t - O t ∈ Submodule.span ℝ (Set.range ![u, g]) :=
    plane_span hcop (by simp) (by simp) (by simp) hli (by simp)
  have hZs : Z t r - O t ∈ Submodule.span ℝ (Set.range ![u, g]) :=
    plane_span hcop (by simp) (by simp) (by simp) hli (by simp)
  have su : u ∈ Submodule.span ℝ (Set.range ![u, g]) := Submodule.subset_span ⟨0, rfl⟩
  have sg : g ∈ Submodule.span ℝ (Set.range ![u, g]) := Submodule.subset_span ⟨1, rfl⟩
  -- 各点相对 O 的向量
  have eK' : K' - O t = u + (ρ t r ^ 2 / dist (K t) (M t r) ^ 2) • a := by
    simp only [K', inversion, vsub_eq_sub, vadd_eq_add, div_pow]; simp only [u, a]; abel
  have eG' : G' - O t = (R t ^ 2 / dist (O t) (G t) ^ 2) • g := by
    simp only [G', inversion, vsub_eq_sub, vadd_eq_add, div_pow, dist_comm (G t)]
    simp only [g]; abel
  have eG2 : G2 - O t = -g := by
    simp only [G2, AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, g]; module
  have eA : A - O t = (R t / ‖u‖) • u := by simp only [A]; abel
  have eB : B - O t = -((R t / ‖u‖) • u) := by simp only [B]; abel
  -- 内积用距离表示
  have nu : ‖u‖ ^ 2 = dist (O t) (M t r) ^ 2 := by rw [dist_comm, dist_eq_norm]
  have ng : ‖g‖ ^ 2 = dist (O t) (G t) ^ 2 := by rw [dist_comm, dist_eq_norm]
  have na : ‖a‖ ^ 2 = dist (K t) (M t r) ^ 2 := by rw [dist_eq_norm]
  have iug : ⟪u, g⟫ = (dist (O t) (M t r) ^ 2 + dist (O t) (G t) ^ 2 -
      dist (G t) (M t r) ^ 2) / 2 := by
    have : ‖u - g‖ ^ 2 = dist (G t) (M t r) ^ 2 := by
      rw [dist_comm, dist_eq_norm, show u - g = M t r - G t by simp only [u, g]; abel]
    rw [← nu, ← ng, ← this, norm_sub_sq_real u g]; ring
  have iau : ⟪a, u⟫ = (dist (O t) (K t) ^ 2 - dist (O t) (M t r) ^ 2 -
      dist (K t) (M t r) ^ 2) / 2 := by
    have : ‖a + u‖ ^ 2 = dist (O t) (K t) ^ 2 := by
      rw [dist_comm, dist_eq_norm, show a + u = K t - O t by simp only [a, u]; abel]
    rw [← nu, ← na, ← this, norm_add_sq_real a u]; ring
  have iag : ⟪a, g⟫ = (dist (O t) (K t) ^ 2 + dist (O t) (G t) ^ 2 -
      dist (G t) (K t) ^ 2) / 2 - ⟪u, g⟫ := by
    have h1 : ‖a + u‖ ^ 2 = dist (O t) (K t) ^ 2 := by
      rw [dist_comm, dist_eq_norm, show a + u = K t - O t by simp only [a, u]; abel]
    have h2 : ‖a + u - g‖ ^ 2 = dist (G t) (K t) ^ 2 := by
      rw [dist_comm, dist_eq_norm, show a + u - g = K t - G t by simp only [a, u, g]; abel]
    rw [← h1, ← ng, ← h2, norm_sub_sq_real (a + u) g, inner_add_left]; ring
  -- u, g 不共线
  have hu0 : u ≠ 0 := hli.ne_zero 0
  have hnu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have huu : ⟪u, u⟫ ≠ 0 := by rw [real_inner_self_eq_norm_sq]; positivity
  set c := ⟪u, g⟫ / ⟪u, u⟫ with hc
  set v := g - c • u with hv
  have huv : ⟪u, v⟫ = 0 := by
    rw [hv, inner_sub_right, real_inner_smul_right, hc]; field_simp; ring
  have hgv : ⟪g, v⟫ = ⟪v, v⟫ := by
    rw [show g = v + c • u by rw [hv]; abel, inner_add_left, real_inner_smul_left]
    rw [huv]; ring
  have hv0 : ⟪v, v⟫ ≠ 0 := by
    intro h
    have hv' : v = 0 := inner_self_eq_zero.mp h
    have hg' : g = c • u := by rw [hv] at hv'; exact sub_eq_zero.mp hv'
    have := (LinearIndependent.pair_iff.mp hli) (-c) 1 (by rw [hg']; module)
    exact one_ne_zero this.2
  set lam := (R t ^ 2 - dist (O t) (G t) ^ 2) / (2 * ⟪v, v⟫)
  set n := lam • v
  set C := O t + n
  have onS : ∀ P : E3, ‖P - O t‖ ^ 2 - 2 * ⟪P - O t, n⟫ = R t ^ 2 →
      dist P C = √(R t ^ 2 + ‖n‖ ^ 2) := by
    intro P hP
    rw [← Real.sqrt_sq dist_nonneg, dist_eq_norm, show P - C = (P - O t) - n by simp only [C]; abel,
      norm_sub_sq_real, ← hP]
  have hRu : (R t / ‖u‖) ^ 2 * ‖u‖ ^ 2 = R t ^ 2 := by field_simp
  have hdOG : dist (O t) (G t) ≠ 0 := by
    rw [dist_comm, dist_eq_norm]; exact norm_ne_zero_iff.mpr (hli.ne_zero 1)
  have hng : dist (O t) (G t) ^ 2 ≠ 0 := pow_ne_zero 2 hdOG
  have mA : dist A C = √(R t ^ 2 + ‖n‖ ^ 2) := onS A (by
    rw [eA, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hRu, real_inner_smul_left,
      real_inner_smul_right, huv]; ring)
  have mB : dist B C = √(R t ^ 2 + ‖n‖ ^ 2) := onS B (by
    rw [eB, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hRu, inner_neg_left,
      real_inner_smul_left, real_inner_smul_right, huv]; ring)
  have mG2 : dist G2 C = √(R t ^ 2 + ‖n‖ ^ 2) := onS G2 (by
    rw [eG2, norm_neg, ng, inner_neg_left, real_inner_smul_right, hgv]
    simp only [lam]; field_simp; ring)
  have mG' : dist G' C = √(R t ^ 2 + ‖n‖ ^ 2) := onS G' (by
    rw [eG', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ng, real_inner_smul_left,
      real_inner_smul_right, hgv]
    simp only [lam]; field_simp; ring)
  -- K′：代数核心
  have hD := D_pos hfb
  have h4 : 0 < es4 r := by
    simp only [es4]; have := hr 0; have := hr 1; have := hr 2; have := hr 3; positivity
  have hd : 4 * es2 r * es4 r - es3 r ^ 2 ≠ 0 := by rw [← D_E hfb]; positivity
  have hk : es1 r * es3 r - 4 * es4 r ≠ 0 := by
    have := sr_s_gt hfb
    have hP : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
    have e : es1 r * es3 r - 4 * es4 r = (∏ j, r j) * ((∑ j, r j) * sInv r - 4) := by
      have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
      simp only [Fin.sum_univ_four, Fin.prod_univ_four, es1, es3, es4, sInv]; field_simp; ring
    rw [e]; exact mul_ne_zero hP.ne' (by linarith)
  have hOM0 : dist (O t) (M t r) ^ 2 ≠ 0 := by rw [← nu]; positivity
  have hKM0 : dist (K t) (M t r) ^ 2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hKM)
  have halg := alg4 (e1 := es1 r) (e2 := es2 r) (e3 := es3 r) (e4 := es4 r)
    (OG := dist (O t) (G t) ^ 2) (OM := dist (O t) (M t r) ^ 2) (GM := dist (G t) (M t r) ^ 2)
    (OK := dist (O t) (K t) ^ 2) (KM := dist (K t) (M t r) ^ 2) (GK := dist (G t) (K t) ^ 2)
    (R2 := R t ^ 2) (ρ2 := ρ t r ^ 2) hd hk hOM0 hKM0
    (by rw [dOG hfb, D_E hfb]) (by rw [dOM hfb, D_E hfb]) (by rw [dGM hfb, D_E hfb])
    (by rw [dOK hfb, D_E hfb]) (by rw [dKM hfb, D_E hfb]) (dGK hfb) (by rw [dR hfb, D_E hfb])
    (by rw [dρ hfb, D_E hfb])
  simp only at halg
  set OMv := dist (O t) (M t r) ^ 2
  set OGv := dist (O t) (G t) ^ 2
  set KMv := dist (K t) (M t r) ^ 2
  set mg := ⟪u, g⟫
  set κ := ρ t r ^ 2 / KMv
  have huu' : ⟪u, u⟫ = OMv := by rw [real_inner_self_eq_norm_sq, nu]
  have hvv : ⟪v, v⟫ = OGv - mg ^ 2 / OMv := by
    rw [← hgv, hv, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ng, hc,
      huu', real_inner_comm u g]; ring
  have hav : ⟪a, v⟫ = ⟪a, g⟫ - mg / OMv * ⟪a, u⟫ := by
    rw [hv, inner_sub_right, real_inner_smul_right, hc, huu']
  have mK' : dist K' C = √(R t ^ 2 + ‖n‖ ^ 2) := onS K' (by
    rw [eK', norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, nu, na,
      real_inner_smul_right, real_inner_comm a u, iau, inner_add_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, huv, hav, iag]
    rw [iau]
    simp only [lam, hvv]
    rw [hvv] at hv0
    rw [iug] at hv0 ⊢
    have hOM' : OMv ≠ 0 := hOM0
    set mgd := (OMv + OGv - dist (G t) (M t r) ^ 2) / 2
    set aMd := (dist (O t) (K t) ^ 2 - OMv - KMv) / 2
    set aGd := (dist (O t) (K t) ^ 2 + OGv - dist (G t) (K t) ^ 2) / 2 - mgd
    have hY : mgd + κ * aGd - mgd / OMv * (OMv + κ * aMd) = κ * (aGd - mgd / OMv * aMd) := by
      field_simp; ring
    rw [hY] at halg
    generalize hW : OGv - mgd ^ 2 / OMv = W at hv0 halg ⊢
    have hdOM : dist (O t) (M t r) ≠ 0 := by intro h; apply hOM'; simp only [OMv, h]; ring
    have hdKM : dist (K t) (M t r) ≠ 0 := dist_ne_zero.mpr hKM
    field_simp
    field_simp at halg
    linear_combination halg)
  -- 共面：所有点减 O 都在 span{u, g} 中
  have hcop2 : Coplanar ℝ ({G t, O t, K t, M t r, Z t r, K', G', A, B, G2} : Set E3) := by
    refine GeometryResearch.Orthocentric.coplanar_of_span (Q := O t) (by simp) u g
      (fun X hX => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sg
    · rw [sub_self]; exact Submodule.zero_mem _
    · exact hKs
    · exact su
    · exact hZs
    · rw [eK']
      exact Submodule.add_mem _ su (Submodule.smul_mem _ _
        (by rw [show a = (K t - O t) - u by simp only [a, u]; abel]; exact Submodule.sub_mem _ hKs su))
    · rw [eG']; exact Submodule.smul_mem _ _ sg
    · rw [eA]; exact Submodule.smul_mem _ _ su
    · rw [eB]; exact Submodule.neg_mem _ (Submodule.smul_mem _ _ su)
    · rw [eG2]; exact Submodule.neg_mem _ sg
  refine ⟨⟨⟨C, √(R t ^ 2 + ‖n‖ ^ 2), fun p hp => ?_⟩, hcop2.subset (by
    intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)⟩, hcop2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  exacts [mK', mG', mA, mB, mG2]

end GeometryResearch.Midsphere
