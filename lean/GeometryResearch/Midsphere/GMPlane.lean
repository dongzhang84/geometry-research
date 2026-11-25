module

public import GeometryResearch.Midsphere.Tangent

/-!
# 定理 2（GM 共轭平面）的证明

P = (1 − u)G + uM 的重心坐标 pᵢ = α + β mᵢ，mᵢ = s xᵢ/2 − xᵢ²（xᵢ = 1/rᵢ）。论文的证明说明
多项式 c₁p(x) + m(x)p(x) + c₃x + c₄ 等于 β∏(x − xⱼ)，于是对每个 i，
c₁ + mᵢ + c₃ xᵢ/pᵢ + c₄/pᵢ = 0。由 Heron 公式 Sᵢ² = Πr·(T xᵢ − 1)，这是 G、M、P*、Pᵗ 的权重之间的
一个线性关系，M 的系数为 1，所以 M − G ∈ span{P* − G, Pᵗ − G}。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary S2 isogonal isotomic ConjDefined G)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

theorem bary_of_V0 {X : E3} (x : Fin 4 → ℝ) (h1 : ∑ j, x j = 1)
    (hX : X - t.points 0 = L t x) : bary t X = x := by
  have hX' : X = ofWeights t x := by
    have := ofW_sub_V0 t x (by rw [h1]; exact one_ne_zero)
    rw [h1, div_one, one_smul, ← hX] at this
    exact (sub_left_inj.mp this).symm
  funext i
  rw [hX', GeometryResearch.Orthocentric.bary_ofWeights' t x (by rw [h1]; exact one_ne_zero), h1,
    div_one]

theorem L_lin4 (a b c d : ℝ) (f g h k : Fin 4 → ℝ) :
    L t (fun i => a * f i + b * g i + c * h i + d * k i) =
      a • L t f + b • L t g + c • L t h + d • L t k := by
  rw [L_four, L_four, L_four, L_four, L_four]; module

/-- 定理 2 的证明。 -/
theorem gm_main (hfb : IsFourBall t r) {P : E3} (hP : P ∈ line[ℝ, G t, M t r])
    (hd : ConjDefined t P) :
    Coplanar ℝ ({G t, M t r, isogonal t P, isotomic t P} : Set E3) := by
  have hr := hfb.1
  have hD := D_pos hfb
  obtain ⟨u, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP
  set σM := 6 * Ddisc r with hσMdef
  have hσM : σM ≠ 0 := by positivity
  set m : Fin 4 → ℝ := fun i => sInv r / (2 * r i) - 1 / r i ^ 2 with hm
  have hmsum : ∑ j, m j = σM := by simp only [m, Fin.sum_univ_four, sInv, qInv, σM, Ddisc]; ring
  have eM : M t r - t.points 0 = (1 / σM) • L t m := by
    rw [← hmsum]; exact ofW_sub_V0 t m (by rw [hmsum]; exact hσM)
  have e1 : ∑ j : Fin 4, (1 : ℝ) = 4 := by simp
  have eG : G t - t.points 0 = (1 / 4 : ℝ) • L t (fun _ => 1) := by
    rw [G_eq, ← e1]; exact ofW_sub_V0 t _ (by rw [e1]; norm_num)
  set p : Fin 4 → ℝ := fun i => (1 - u) / 4 * 1 + u / σM * m i + 0 * 0 + 0 * 0 with hp
  have hbP : bary t (AffineMap.lineMap (G t) (M t r) u) = p := by
    apply bary_of_V0
    · simp only [p, Fin.sum_univ_four]
      rw [show (1 - u) / 4 * 1 + u / σM * m 0 + 0 * 0 + 0 * 0 + ((1 - u) / 4 * 1 + u / σM * m 1 +
          0 * 0 + 0 * 0) + ((1 - u) / 4 * 1 + u / σM * m 2 + 0 * 0 + 0 * 0) +
          ((1 - u) / 4 * 1 + u / σM * m 3 + 0 * 0 + 0 * 0) = (1 - u) +
          u / σM * (m 0 + m 1 + m 2 + m 3) by ring, ← Fin.sum_univ_four, hmsum]
      field_simp; ring
    · rw [AffineMap.lineMap_apply_module, show (1 - u) • G t + u • M t r - t.points 0 =
          (1 - u) • (G t - t.points 0) + u • (M t r - t.points 0) by module, eG, eM,
        L_lin4]
      rw [show (fun _ : Fin 4 => (0 : ℝ)) = fun _ => 0 from rfl]
      simp only [L_four]
      module
  obtain ⟨hp0, hσs, hσt⟩ := hd
  rw [hbP] at hp0 hσs hσt
  rw [isogonal, isotomic, hbP]
  set α := (1 - u) / 4
  set β := u / σM
  by_cases hu : u = 0
  · -- P = G：Pᵗ = G
    have hpG : ofWeights t (fun i => 1 / p i) = G t := by
      rw [G_eq, show (fun i => 1 / p i) = (fun _ => 4 * 1) by
        funext i; simp [p, hu], ofW_smul t 4 (by norm_num) (fun _ => 1)]
    rw [hpG]
    exact (coplanar_triple (k := ℝ) (G t) (M t r) (ofWeights t (fun i => S2 t i / p i))).subset
      (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
  have hβ : β ≠ 0 := div_ne_zero hu hσM
  -- 记号
  set x : Fin 4 → ℝ := fun i => 1 / r i with hx
  set e2 := x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3
  set e3 := x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3
  set e4 := x 0 * x 1 * x 2 * x 3
  set k1 := -α + β * (sInv r ^ 2 / 4 - e2)
  set k3 := β * (-β * e3 - sInv r * (k1 + α) / 2)
  set k4 := β ^ 2 * e4 - k1 * α
  have hsx : sInv r = x 0 + x 1 + x 2 + x 3 := by simp only [sInv, Fin.sum_univ_four, x]
  -- 关键恒等式：p(k₁ + β m) + k₃ x + k₄ = β²∏(x − xⱼ) = 0
  have key : ∀ i, p i * (k1 + β * m i) + k3 * x i + k4 = 0 := by
    have hm' : ∀ i, m i = sInv r * x i / 2 - x i ^ 2 := by
      intro i; simp only [m, x]; ring
    intro i
    simp only [p, hm', k3, k4, k1, e2, e3, e4]
    rw [hsx]
    fin_cases i <;> simp <;> ring
  have hT : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have hPi : 0 < ∏ j, r j := Finset.prod_pos (fun j _ => hr j)
  set l3 := k3 / ((∑ j, r j) * ∏ j, r j)
  set l4 := k3 / (∑ j, r j) + k4
  have comp : ∀ i, k1 * 1 + β * m i + l3 * (S2 t i / p i) + l4 * (1 / p i) = 0 := by
    intro i
    have hpi := hp0 i
    have hri := (hr i).ne'
    have h1 : l3 * (S2 t i / p i) + l4 * (1 / p i) = k3 * (x i / p i) + k4 * (1 / p i) := by
      rw [heron hfb]; simp only [l3, l4, x]; field_simp; ring
    have h2 : k1 + β * m i + k3 * (x i / p i) + k4 * (1 / p i) =
        (p i * (k1 + β * m i) + k3 * x i + k4) / p i := by field_simp
    rw [show k1 * 1 + β * m i + l3 * (S2 t i / p i) + l4 * (1 / p i) =
      k1 + β * m i + (l3 * (S2 t i / p i) + l4 * (1 / p i)) by ring, h1, ← add_assoc, h2,
      key i, zero_div]
  -- 求和与 L
  set σs := ∑ i, S2 t i / p i
  set σt := ∑ i, 1 / p i
  have hsum : k1 * 4 + β * σM + l3 * σs + l4 * σt = 0 := by
    have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => comp i)
    rw [Finset.sum_const_zero] at this
    rw [← this, ← hmsum]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, σs, σt]
    simp
  have hL : k1 • L t (fun _ => 1) + β • L t m + l3 • L t (fun i => S2 t i / p i) +
      l4 • L t (fun i => 1 / p i) = 0 := by
    rw [← L_lin4]
    rw [show (fun i => k1 * 1 + β * m i + l3 * (S2 t i / p i) + l4 * (1 / p i)) = fun _ => 0 by
      funext i; exact comp i]
    simp [L]
  have eS := ofW_sub_V0 t (fun i => S2 t i / p i) hσs
  have eT := ofW_sub_V0 t (fun i => 1 / p i) hσt
  set Ps := ofWeights t (fun i => S2 t i / p i)
  set Pt := ofWeights t (fun i => 1 / p i)
  have hvec : (β * σM) • (M t r - G t) + (l3 * σs) • (Ps - G t) + (l4 * σt) • (Pt - G t) = 0 := by
    rw [show M t r - G t = (M t r - t.points 0) - (G t - t.points 0) by abel,
      show Ps - G t = (Ps - t.points 0) - (G t - t.points 0) by abel,
      show Pt - G t = (Pt - t.points 0) - (G t - t.points 0) by abel, eM, eG, eS, eT]
    have c1 : (β * σM) * (1 / σM) = β := by field_simp
    have c2 : (l3 * σs) * (1 / σs) = l3 := by field_simp
    have c3 : (l4 * σt) * (1 / σt) = l4 := by field_simp
    have c4 : -((β * σM + l3 * σs + l4 * σt) * (1 / 4)) = k1 := by linarith
    rw [show (β * σM) • ((1 / σM) • L t m - (1 / 4 : ℝ) • L t (fun _ => 1)) +
        (l3 * σs) • ((1 / σs) • L t (fun i => S2 t i / p i) - (1 / 4 : ℝ) • L t (fun _ => 1)) +
        (l4 * σt) • ((1 / σt) • L t (fun i => 1 / p i) - (1 / 4 : ℝ) • L t (fun _ => 1)) =
        (-((β * σM + l3 * σs + l4 * σt) * (1 / 4))) • L t (fun _ => 1) +
        ((β * σM) * (1 / σM)) • L t m + ((l3 * σs) * (1 / σs)) • L t (fun i => S2 t i / p i) +
        ((l4 * σt) * (1 / σt)) • L t (fun i => 1 / p i) by module, c1, c2, c3, c4]
    exact hL
  have hc : β * σM ≠ 0 := mul_ne_zero hβ hσM
  have hMG : M t r - G t = (-(l3 * σs) / (β * σM)) • (Ps - G t) +
      (-(l4 * σt) / (β * σM)) • (Pt - G t) := by
    have h := hvec
    rw [add_assoc, add_eq_zero_iff_eq_neg] at h
    rw [show (-(l3 * σs) / (β * σM)) • (Ps - G t) + (-(l4 * σt) / (β * σM)) • (Pt - G t) =
      (1 / (β * σM)) • -((l3 * σs) • (Ps - G t) + (l4 * σt) • (Pt - G t)) by module, ← h,
      smul_smul, one_div_mul_cancel hc, one_smul]
  have hG : G t ∈ ({G t, M t r, Ps, Pt} : Set E3) := Set.mem_insert _ _
  refine GeometryResearch.Orthocentric.coplanar_of_span hG (Ps - G t) (Pt - G t)
    (fun X hX => ?_)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · convert GeometryResearch.Orthocentric.mem_span2 (Ps - G t) (Pt - G t) 0 0 using 1; simp
  · rw [hMG]; exact GeometryResearch.Orthocentric.mem_span2 _ _ _ _
  · convert GeometryResearch.Orthocentric.mem_span2 (Ps - G t) (Pt - G t) 1 0 using 1; simp
  · convert GeometryResearch.Orthocentric.mem_span2 (Ps - G t) (Pt - G t) 0 1 using 1; simp

end GeometryResearch.Midsphere
