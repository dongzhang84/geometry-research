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

end GeometryResearch.Midsphere
