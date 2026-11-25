module

public import GeometryResearch.Midsphere.Faith
public import GeometryResearch.Orthocentric.Conj

/-!
# 定理 1（中心平面）的证明

记 xᵢ = 1/rᵢ，s = Σxᵢ，q = Σxᵢ²，Y 为权重 (xᵢ²) 的点。权重为 a + b·xᵢ + c·xᵢ² 的点 P 满足
P − G = (bs/σ)(Z − G) + (cq/σ)(Y − G)，σ = 4a + bs + cq 为权重和。G、Z、M、K、O 与 Soddy 球心
的权重都是这种形式（论文 Lemma 2.1 与定理 1 的证明），所以都落在平面 GZY 上。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary S2 isogonal G O)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- q = Σ 1/rᵢ²。 -/
def qInv (r : Fin 4 → ℝ) : ℝ := ∑ i, 1 / r i ^ 2

/-- Descartes 判别式 D = (s² − 2q)/12。 -/
def Ddisc (r : Fin 4 → ℝ) : ℝ := (sInv r ^ 2 - 2 * qInv r) / 12

/-- Y：权重 (1/rᵢ²) 的点。 -/
def Y (t : Affine.Simplex ℝ E3 3) (r : Fin 4 → ℝ) : E3 := ofWeights t (fun i => 1 / r i ^ 2)

/-! ## D > 0 -/

theorem linIndep_w : LinearIndependent ℝ (fun k : Fin 3 => w t k.succ) := by
  have h := (affineIndependent_iff_linearIndependent_vsub ℝ t.points 0).mp t.independent
  have hinj : Function.Injective (fun k : Fin 3 => (⟨k.succ, Fin.succ_ne_zero k⟩ :
      {x : Fin 4 // x ≠ 0})) := by
    intro a b hab; simpa using hab
  have := h.comp _ hinj
  simpa [w, Function.comp_def] using this

set_option linter.flexible false in
/-- Gram 行列式 = 48·D·Π rᵢ²，而 Gram 矩阵正定，所以 D > 0。 -/
theorem D_pos (hfb : IsFourBall t r) : 0 < Ddisc r := by
  have hr := hfb.1
  have hpd := Matrix.posDef_gram_of_linearIndependent (linIndep_w (t := t))
  have hdet := hpd.det_pos
  rw [Matrix.det_fin_three] at hdet
  simp only [Matrix.gram, inner_w hfb] at hdet
  simp only [g, e] at hdet
  simp at hdet
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
  have hP : 0 < (r 0 * r 1 * r 2 * r 3) ^ 2 := by positivity
  by_contra hneg
  push Not at hneg
  have hD : Ddisc r * (r 0 * r 1 * r 2 * r 3) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hP.le
  simp only [Ddisc, sInv, qInv, Fin.sum_univ_four] at hD
  field_simp at hD
  nlinarith [hdet, hD]

/-! ## 组合引理 -/

theorem L_lin (a b c : ℝ) (f g h : Fin 4 → ℝ) :
    L t (fun i => a * f i + b * g i + c * h i) = a • L t f + b • L t g + c • L t h := by
  rw [L_four, L_four, L_four, L_four]; module

theorem sInv_pos (hfb : IsFourBall t r) : 0 < sInv r := by
  have hr := hfb.1
  simp only [sInv, Fin.sum_univ_four]
  have := hr 0; have := hr 1; have := hr 2; have := hr 3
  positivity

theorem qInv_pos (hfb : IsFourBall t r) : 0 < qInv r := by
  have hr := hfb.1
  simp only [qInv, Fin.sum_univ_four]
  have := hr 0; have := hr 1; have := hr 2; have := hr 3
  positivity

/-- 权重 a + b·xᵢ + c·xᵢ² 的点 P：P − G = (bs/σ)(Z − G) + (cq/σ)(Y − G)。 -/
theorem comb (hfb : IsFourBall t r) (a b c : ℝ)
    (hσ : 4 * a + b * sInv r + c * qInv r ≠ 0) :
    ofWeights t (fun i => a * 1 + b * (1 / r i) + c * (1 / r i ^ 2)) - G t =
      (b * sInv r / (4 * a + b * sInv r + c * qInv r)) • (Z t r - G t) +
      (c * qInv r / (4 * a + b * sInv r + c * qInv r)) • (Y t r - G t) := by
  have hs := (sInv_pos hfb).ne'
  have hq := (qInv_pos hfb).ne'
  set σ := 4 * a + b * sInv r + c * qInv r with hσdef
  have hsum : ∑ i, (a * 1 + b * (1 / r i) + c * (1 / r i ^ 2)) = σ := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    rw [hσdef, sInv, qInv]; simp; ring
  have h1 : ∑ i : Fin 4, (1 : ℝ) = 4 := by simp
  have eP := ofW_sub_V0 t _ (by rw [hsum]; exact hσ)
  have eG := ofW_sub_V0 t (fun _ => (1 : ℝ)) (by rw [h1]; norm_num)
  have eZ := ofW_sub_V0 t (fun i => 1 / r i) hs
  have eY := ofW_sub_V0 t (fun i => 1 / r i ^ 2) hq
  rw [hsum, L_lin] at eP
  rw [h1] at eG
  rw [show ofWeights t (fun i => 1 / r i) = Z t r from rfl] at eZ
  rw [show ofWeights t (fun i => 1 / r i ^ 2) = Y t r from rfl] at eY
  rw [← G_eq] at eG
  rw [show ofWeights t (fun i => a * 1 + b * (1 / r i) + c * (1 / r i ^ 2)) - G t =
      (ofWeights t (fun i => a * 1 + b * (1 / r i) + c * (1 / r i ^ 2)) - t.points 0) -
        (G t - t.points 0) by abel,
    show Z t r - G t = (Z t r - t.points 0) - (G t - t.points 0) by abel,
    show Y t r - G t = (Y t r - t.points 0) - (G t - t.points 0) by abel, eP, eG, eZ, eY]
  simp only [show (∑ j, 1 / r j) = sInv r from rfl, show (∑ j, 1 / r j ^ 2) = qInv r from rfl]
  set L1 := L t (fun _ => (1 : ℝ)); set Lx := L t (fun i => 1 / r i)
  set Lq := L t (fun i => 1 / r i ^ 2)
  set S1 := sInv r; set S2' := qInv r
  have c1 : (1 / σ) * a - 1 / 4 = -((b * S1 / σ + c * S2' / σ) * (1 / 4)) := by
    field_simp; rw [hσdef]; ring
  have c2 : (1 / σ) * b = b * S1 / σ * (1 / S1) := by field_simp
  have c3 : (1 / σ) * c = c * S2' / σ * (1 / S2') := by field_simp
  have lhs : (1 / σ) • (a • L1 + b • Lx + c • Lq) - (1 / 4 : ℝ) • L1 =
      ((1 / σ) * a - 1 / 4) • L1 + ((1 / σ) * b) • Lx + ((1 / σ) * c) • Lq := by module
  have rhs : (b * S1 / σ) • ((1 / S1) • Lx - (1 / 4 : ℝ) • L1) +
      (c * S2' / σ) • ((1 / S2') • Lq - (1 / 4 : ℝ) • L1) =
      (-((b * S1 / σ + c * S2' / σ) * (1 / 4))) • L1 + (b * S1 / σ * (1 / S1)) • Lx +
        (c * S2' / σ * (1 / S2')) • Lq := by module
  rw [lhs, rhs, c1, c2, c3]

/-! ## 各点的权重 -/

theorem inner_Lw (hfb : IsFourBall t r) (x : Fin 4 → ℝ) (i : Fin 4) :
    ⟪L t x, w t i⟫ = x 1 * g r 1 i + x 2 * g r 2 i + x 3 * g r 3 i := by
  rw [L_four]; simp only [inner_add_left, real_inner_smul_left, inner_w hfb]

/-- 若 ⟪P − V₀, wᵢ⟫ = gᵢᵢ/2 对 i = 1, 2, 3 成立，则 P 到四个顶点等距，P 就是外心。 -/
theorem eq_O_of_inner (hfb : IsFourBall t r) {P : E3}
    (h : ∀ i : Fin 4, i ≠ 0 → ⟪P - t.points 0, w t i⟫ = g r i i / 2) : P = O t := by
  have hmem : P ∈ affineSpan ℝ (Set.range t.points) := by
    rw [show Set.range t.points = Set.range (GeometryResearch.Orthocentric.basis t) from rfl,
      (GeometryResearch.Orthocentric.basis t).tot]; exact AffineSubspace.mem_top _ _ _
  refine t.eq_circumcenter_of_dist_eq hmem (r := dist (t.points 0) P) (fun i => ?_)
  by_cases hi : i = 0
  · subst hi; rfl
  · have hw : ‖w t i‖ ^ 2 = g r i i := by rw [← real_inner_self_eq_norm_sq, inner_w hfb]
    rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, dist_eq_norm, dist_eq_norm,
      show t.points i - P = w t i - (P - t.points 0) by simp only [w]; abel,
      show t.points 0 - P = -(P - t.points 0) by abel, norm_neg, @norm_sub_sq_real, hw,
      real_inner_comm, h i hi]
    ring

/-- 外心的权重（论文定理 1 的证明）：oᵢ = −12D/Σr + (−q)·xᵢ + s·xᵢ²。 -/
theorem O_eq (hfb : IsFourBall t r) :
    O t = ofWeights t (fun i => (-12 * Ddisc r / ∑ j, r j) * 1 + (-qInv r) * (1 / r i) +
      sInv r * (1 / r i ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  have hsr : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  set a := -12 * Ddisc r / ∑ j, r j
  have ha : a ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hD) hsr.ne'
  have hσ : 4 * a + (-qInv r) * sInv r + sInv r * qInv r ≠ 0 := by
    rw [show 4 * a + (-qInv r) * sInv r + sInv r * qInv r = 4 * a by ring]
    exact mul_ne_zero four_ne_zero ha
  symm; apply eq_O_of_inner hfb
  intro i hi
  have hsum : ∑ j, (a * 1 + (-qInv r) * (1 / r j) + sInv r * (1 / r j ^ 2)) =
      4 * a + (-qInv r) * sInv r + sInv r * qInv r := by
    simp only [Fin.sum_univ_four, sInv, qInv]; ring
  rw [ofW_sub_V0 t _ (by rw [hsum]; exact hσ), real_inner_smul_left, inner_Lw hfb, hsum,
    show 4 * a + (-qInv r) * sInv r + sInv r * qInv r = 4 * a by ring,
    one_div_mul_eq_div, div_eq_iff (mul_ne_zero four_ne_zero ha)]
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have hs' := hsr.ne'
  fin_cases i
  · exact absurd rfl hi
  all_goals
    simp only [a, Ddisc, sInv, qInv, g, e, Fin.sum_univ_four] at hs' ⊢
    simp
    field_simp
    ring

/-- Soddy 球心的权重：σᵢ = −(s − ρq)·xᵢ + (2 − ρs)·xᵢ²（权重和 = −12D）。 -/
theorem S_eq (hfb : IsFourBall t r) {S : E3} {ρs : ℝ} (hS : IsSoddy t r S ρs) :
    S = ofWeights t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r i) +
      (2 - ρs * sInv r) * (1 / r i ^ 2)) := by
  have hr := hfb.1
  have hD := (D_pos hfb).ne'
  set P := ofWeights t (fun i => 0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r i) +
      (2 - ρs * sInv r) * (1 / r i ^ 2))
  have hsum : ∑ j, (0 * 1 + (-(sInv r - ρs * qInv r)) * (1 / r j) +
      (2 - ρs * sInv r) * (1 / r j ^ 2)) = -12 * Ddisc r := by
    simp only [Fin.sum_univ_four, sInv, qInv, Ddisc]; ring
  have hσ : -12 * Ddisc r ≠ 0 := mul_ne_zero (by norm_num) hD
  have eP := ofW_sub_V0 t _ (by rw [hsum]; exact hσ)
  rw [hsum] at eP
  rw [← sub_eq_zero]
  apply GeometryResearch.Orthocentric.eq_zero_of_inner_edges t 0
  intro k
  by_cases hk : k = 0
  · subst hk; simp
  have hS0 := hS.2 0; have hSk := hS.2 k
  have hw : ‖w t k‖ ^ 2 = g r k k := by rw [← real_inner_self_eq_norm_sq, inner_w hfb]
  have eS : ⟪S - t.points 0, w t k⟫ = ((ρs + r 0) ^ 2 + g r k k - (ρs + r k) ^ 2) / 2 := by
    rw [dist_eq_norm] at hS0 hSk
    rw [show S - t.points k = (S - t.points 0) - w t k by simp only [w]; abel,
      @norm_sub_sq_real, hw] at hSk
    linarith
  rw [show S - P = (S - t.points 0) - (P - t.points 0) by abel, inner_sub_left, eS, eP,
    real_inner_smul_left, inner_Lw hfb]
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  rw [sub_eq_zero, one_div_mul_eq_div, eq_div_iff hσ]
  fin_cases k
  · exact absurd rfl hk
  all_goals
    simp only [Ddisc, sInv, qInv, g, e, Fin.sum_univ_four]
    simp
    field_simp
    ring

theorem M_comb :
    M t r = ofWeights t (fun i => 0 * 1 + (sInv r / 2) * (1 / r i) + (-1) * (1 / r i ^ 2)) := by
  simp only [M]; congr 1; funext i; ring

theorem K_comb (hfb : IsFourBall t r) :
    GeometryResearch.Midsphere.K t = ofWeights t (fun i => (-(∏ j, r j)) * 1 +
      ((∏ j, r j) * ∑ j, r j) * (1 / r i) + 0 * (1 / r i ^ 2)) := by
  simp only [K]; congr 1; funext i
  rw [heron hfb]; field_simp [(hfb.1 i).ne']; ring

theorem sr_s_gt (hfb : IsFourBall t r) : 4 < (∑ j, r j) * sInv r := by
  have hr := hfb.1
  have h0 := hr 0; have h1 := hr 1; have h2 := hr 2; have h3 := hr 3
  simp only [sInv, Fin.sum_univ_four]
  have : (r 0 + r 1 + r 2 + r 3) * (1 / r 0 + 1 / r 1 + 1 / r 2 + 1 / r 3) - 4 =
      r 0 / r 1 + r 0 / r 2 + r 0 / r 3 + r 1 / r 0 + r 1 / r 2 + r 1 / r 3 +
      r 2 / r 0 + r 2 / r 1 + r 2 / r 3 + r 3 / r 0 + r 3 / r 1 + r 3 / r 2 := by
    field_simp; ring
  have : 0 < r 0 / r 1 + r 0 / r 2 + r 0 / r 3 + r 1 / r 0 + r 1 / r 2 + r 1 / r 3 +
      r 2 / r 0 + r 2 / r 1 + r 2 / r 3 + r 3 / r 0 + r 3 / r 1 + r 3 / r 2 := by positivity
  linarith

/-- 点 X 的权重形如 a + b·xᵢ + c·xᵢ²（权重和非零），则 X − G ∈ span{Z − G, Y − G}。 -/
theorem mem_plane (hfb : IsFourBall t r) {X : E3} (a b c : ℝ)
    (hσ : 4 * a + b * sInv r + c * qInv r ≠ 0)
    (hX : X = ofWeights t (fun i => a * 1 + b * (1 / r i) + c * (1 / r i ^ 2))) :
    X - G t ∈ Submodule.span ℝ (Set.range ![Z t r - G t, Y t r - G t]) := by
  rw [hX, comb hfb a b c hσ]
  exact GeometryResearch.Orthocentric.mem_span2 _ _ _ _

theorem Z_comb : Z t r = ofWeights t (fun i => 0 * 1 + 1 * (1 / r i) + 0 * (1 / r i ^ 2)) := by
  simp only [Z]; congr 1; funext i; ring

theorem G_comb : G t = ofWeights t (fun i => 1 * 1 + 0 * (1 / r i) + 0 * (1 / r i ^ 2)) := by
  rw [G_eq]; congr 1; funext i; ring

/-- 定理 1 的证明。 -/
theorem central_main (hfb : IsFourBall t r) :
    Coplanar ℝ ({G t, O t, K t, M t r, Z t r} : Set E3) ∧
      ∀ S ρs, IsSoddy t r S ρs → Coplanar ℝ ({G t, O t, K t, M t r, Z t r, S} : Set E3) := by
  have hr := hfb.1
  have hD := D_pos hfb
  have hs := sInv_pos hfb
  have hsr : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have hP : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
  have hgt := sr_s_gt hfb
  have mG := mem_plane hfb (X := G t) 1 0 0 (by simp) G_comb
  have mZ := mem_plane hfb (X := Z t r) 0 1 0 (by simpa using hs.ne') Z_comb
  have mM := mem_plane hfb (X := M t r) 0 (sInv r / 2) (-1)
    (by
      have : 4 * 0 + sInv r / 2 * sInv r + -1 * qInv r = 6 * Ddisc r := by
        simp only [Ddisc]; ring
      rw [this]; positivity) M_comb
  have mK := mem_plane hfb (X := K t) (-(∏ j, r j)) ((∏ j, r j) * ∑ j, r j) 0
    (by
      have : 4 * -(∏ j, r j) + (∏ j, r j) * (∑ j, r j) * sInv r + 0 * qInv r =
          (∏ j, r j) * ((∑ j, r j) * sInv r - 4) := by ring
      rw [this]; exact mul_ne_zero hP.ne' (by linarith)) (K_comb hfb)
  have mO := mem_plane hfb (X := O t) (-12 * Ddisc r / ∑ j, r j) (-qInv r) (sInv r)
    (by
      rw [show 4 * (-12 * Ddisc r / ∑ j, r j) + -qInv r * sInv r + sInv r * qInv r =
        4 * (-12 * Ddisc r / ∑ j, r j) by ring]
      exact mul_ne_zero four_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) hD.ne') hsr.ne'))
    (O_eq hfb)
  have hG : G t ∈ ({G t, O t, K t, M t r, Z t r} : Set E3) := Set.mem_insert _ _
  refine ⟨GeometryResearch.Orthocentric.coplanar_of_span hG (Z t r - G t) (Y t r - G t)
    (fun X hX => ?_),
    fun S ρs hS => ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    exacts [mG, mO, mK, mM, mZ]
  · have mS := mem_plane hfb (X := S) 0 (-(sInv r - ρs * qInv r)) (2 - ρs * sInv r)
      (by
        rw [show 4 * 0 + -(sInv r - ρs * qInv r) * sInv r + (2 - ρs * sInv r) * qInv r =
          -12 * Ddisc r by simp only [Ddisc]; ring]
        exact mul_ne_zero (by norm_num) hD.ne') (S_eq hfb hS)
    have hG' : G t ∈ ({G t, O t, K t, M t r, Z t r, S} : Set E3) := Set.mem_insert _ _
    refine GeometryResearch.Orthocentric.coplanar_of_span hG' (Z t r - G t) (Y t r - G t)
      (fun X hX => ?_)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [mG, mO, mK, mM, mZ, mS]

/-- 类似重心是 G 的等角共轭。 -/
theorem K_isog : GeometryResearch.Midsphere.K t = isogonal t (G t) := by
  have hb : ∀ i, bary t (G t) i = 1 / 4 := by
    intro i
    rw [G_eq, GeometryResearch.Orthocentric.bary_ofWeights' t _ (by simp)]
    simp
  simp only [K, isogonal, hb]
  rw [show (fun i => S2 t i / (1 / 4)) = (fun i => 4 * S2 t i) by funext i; ring,
    ofW_smul t 4 (by norm_num)]

end GeometryResearch.Midsphere
