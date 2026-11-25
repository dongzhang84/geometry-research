module

public import GeometryResearch.Midsphere.SixSeven

/-!
# Feuerbach 点的忠实性（`X11_faithful`）

- 九点圆：它过面的三条边的中点（Mathlib 的 `faceOppositeCentroid_mem_ninePointCircle`）。设 qₘ = |VₘN|²，
  三个中点在圆上给出 q_b + q_c = 2R² + e_bc/2 等三条关系；由 Lagrange 公式，面上点 X 在圆上当且仅当
  x_a x_b e_ab + x_a x_c e_ac + x_b x_c e_bc = Σ (x_a + x_b − x_c) e_ab/4。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights mid sum_perm)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

theorem e_symm (m n : Fin 4) : e r m n = e r n m := by simp only [e, eq_comm, add_comm]

theorem tw_mul_sum {i j : Fin 4} (c : ℝ) (f : Fin 4 → ℝ) :
    ∑ m, tw i j c m * f m = (1 - c) * f i + c * f j := by
  simp only [tw, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem tw_sum2 {i j : Fin 4} (hij : i ≠ j) (c : ℝ) :
    ∑ m, ∑ n, tw i j c m * tw i j c n * e r m n = 2 * (1 - c) * c * e r i j := by
  simp only [mul_assoc, ← Finset.mul_sum, tw_mul_sum]
  simp only [e, ite_true, hij, hij.symm, ite_false]
  ring

/-- 三角形与对顶点相对的边的中点。 -/
theorem foc_eq (Δ : Affine.Triangle ℝ E3) {i j k : Fin 3} (hj : i.succAbove 0 = j)
    (hk : i.succAbove 1 = k) : Δ.faceOppositeCentroid i = midpoint ℝ (Δ.points j) (Δ.points k) := by
  rw [Affine.Simplex.faceOppositeCentroid, Affine.Simplex.centroid, Finset.centroid_pair_fin,
    Affine.Simplex.faceOpposite_point_eq_point_succAbove,
    Affine.Simplex.faceOpposite_point_eq_point_succAbove]
  erw [hj, hk]
  rw [midpoint_eq_smul_add]
  simp only [vsub_eq_sub, vadd_eq_add, invOf_eq_inv]
  module

/-- 中点在球 (N, R) 上给出 (|VᵢN|² + |VⱼN|²)/2 − eᵢⱼ/4 = R²。 -/
theorem mid_rel (hfb : IsFourBall t r) {i j : Fin 4} (hij : i ≠ j) {Nc : E3} {R : ℝ}
    (h : dist (midpoint ℝ (t.points i) (t.points j)) Nc = R) :
    (dist (t.points i) Nc ^ 2 + dist (t.points j) Nc ^ 2) / 2 - e r i j / 4 = R ^ 2 := by
  rw [← lineMap_half, lineMap_eq_ofW hij] at h
  have h2 := dist_ofW_pt hfb (x := tw i j (1 / 2)) (by rw [tw_sum hij]; exact one_ne_zero) Nc
  simp only [tw_sum hij, div_one] at h2
  rw [h, tw_mul_sum, tw_sum2 hij] at h2
  rw [h2]; ring

set_option maxHeartbeats 1000000 in -- 展开求和
/-- 面上的点在九点圆上的判据。 -/
theorem nine_face (hfb : IsFourBall t r) {l a b c : Fin 4} (ha : l.succAbove 0 = a)
    (hb : l.succAbove 1 = b) (hc : l.succAbove 2 = c) (x : Fin 4 → ℝ)
    (hs : x a + x b + x c = 1) (hxl : x l = 0)
    (hN : x a * x b * e r a b + x a * x c * e r a c + x b * x c * e r b c =
      ((x a + x b - x c) * e r a b + (x a + x c - x b) * e r a c +
        (x b + x c - x a) * e r b c) / 4) :
    ofWeights t x ∈ (t.faceOpposite l).ninePointCircle := by
  have inj := Fin.succAbove_right_injective (p := l)
  have hab : a ≠ b := by rw [← ha, ← hb]; exact inj.ne (by decide)
  have hac : a ≠ c := by rw [← ha, ← hc]; exact inj.ne (by decide)
  have hbc : b ≠ c := by rw [← hb, ← hc]; exact inj.ne (by decide)
  have hal : a ≠ l := by rw [← ha]; exact Fin.succAbove_ne l 0
  have hbl : b ≠ l := by rw [← hb]; exact Fin.succAbove_ne l 1
  have hcl : c ≠ l := by rw [← hc]; exact Fin.succAbove_ne l 2
  have S : ∀ f : Fin 4 → ℝ, ∑ m, f m = f a + f b + f c + f l := fun f => by
    rw [Fin.sum_univ_four]; exact (sum_perm f hab hac hal hbc hbl hcl).symm
  set Δ := t.faceOpposite l
  set Nc := Δ.ninePointCircle.center
  set R := Δ.ninePointCircle.radius
  have pa : Δ.points 0 = t.points a := fp l 0 a ha
  have pb : Δ.points 1 = t.points b := fp l 1 b hb
  have pc : Δ.points 2 = t.points c := fp l 2 c hc
  have m0 := Δ.faceOppositeCentroid_mem_ninePointCircle 0
  have m1 := Δ.faceOppositeCentroid_mem_ninePointCircle 1
  have m2 := Δ.faceOppositeCentroid_mem_ninePointCircle 2
  rw [foc_eq Δ (j := 1) (k := 2) (by decide) (by decide), pb, pc, mem_sphere] at m0
  rw [foc_eq Δ (j := 0) (k := 2) (by decide) (by decide), pa, pc, mem_sphere] at m1
  rw [foc_eq Δ (j := 0) (k := 1) (by decide) (by decide), pa, pb, mem_sphere] at m2
  have r0 := mid_rel hfb hbc m0
  have r1 := mid_rel hfb hac m1
  have r2 := mid_rel hfb hab m2
  have hsum : ∑ m, x m = 1 := by rw [S, hxl, add_zero, hs]
  have hR : 0 ≤ R := by
    simp only [R, Affine.Simplex.ninePointCircle_radius]
    exact div_nonneg Δ.circumradius_nonneg (by norm_num)
  rw [mem_sphere, ← pow_left_inj₀ dist_nonneg hR two_ne_zero,
    dist_ofW_pt hfb (by rw [hsum]; exact one_ne_zero), hsum]
  simp only [div_one, S, hxl, zero_mul, mul_zero, add_zero, e_symm l, e_symm (r := r) b a,
    e_symm (r := r) c a, e_symm (r := r) c b]
  simp only [e, ite_true]
  simp only [e] at hN r0 r1 r2
  simp only [hab, hac, hbc, ite_false] at hN r0 r1 r2 ⊢
  linear_combination (x b + x c - x a) * r0 + (x a + x c - x b) * r1 + (x a + x b - x c) * r2 -
    hN + R ^ 2 * hs

/-- 三角形内切圆半径的平方（Heron 形式）。 -/
theorem inradius_sq (Δ : Affine.Triangle ℝ E3) :
    Δ.inradius ^ 2 = (dist (Δ.points 0) (Δ.points 2) ^ 2 * dist (Δ.points 0) (Δ.points 1) ^ 2 -
      ((dist (Δ.points 0) (Δ.points 2) ^ 2 + dist (Δ.points 0) (Δ.points 1) ^ 2 -
        dist (Δ.points 1) (Δ.points 2) ^ 2) / 2) ^ 2) /
      (dist (Δ.points 1) (Δ.points 2) + dist (Δ.points 0) (Δ.points 2) +
        dist (Δ.points 0) (Δ.points 1)) ^ 2 := by
  have hp : ∀ i, 0 < Δ.height i := fun i => Δ.height_pos i
  have hd : ∀ i j, i ≠ j → 0 < dist (Δ.points i) (Δ.points j) := fun i j h =>
    dist_pos.mpr (Δ.independent.injective.ne h)
  have d12 := hd 1 2 (by decide); have d02 := hd 0 2 (by decide); have d01 := hd 0 1 (by decide)
  obtain ⟨k0, k1⟩ := height_mul_side Δ
  have h0 := (hp 0).ne'; have h1 := (hp 1).ne'; have h2 := (hp 2).ne'
  have hK : Δ.height 2 * dist (Δ.points 0) (Δ.points 1) ≠ 0 := by positivity
  have e0 : (Δ.height 0)⁻¹ = dist (Δ.points 1) (Δ.points 2) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by rw [← k0]; field_simp
  have e1 : (Δ.height 1)⁻¹ = dist (Δ.points 0) (Δ.points 2) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by rw [← k1]; field_simp
  have e2 : (Δ.height 2)⁻¹ = dist (Δ.points 0) (Δ.points 1) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by field_simp
  rw [Affine.Simplex.inradius_eq_abs_inv_sum, sq_abs]
  simp only [Affine.Simplex.excenterWeightsUnnorm, Finset.notMem_empty, ite_false, one_mul]
  rw [Fin.sum_univ_three, e0, e1, e2]
  -- h₂ = sin θ · |P₀P₂|，cos θ 由余弦定理给出
  have hs := Δ.height_eq_sin_mul_dist (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide)
    (by decide)
  have hc := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
    (Δ.points 2) (Δ.points 0) (Δ.points 1)
  have hsc := Real.sin_sq_add_cos_sq (∠ (Δ.points 2) (Δ.points 0) (Δ.points 1))
  rw [dist_comm (Δ.points 2) (Δ.points 0)] at hs hc
  rw [dist_comm (Δ.points 2) (Δ.points 1), dist_comm (Δ.points 1) (Δ.points 0)] at hc
  have hK2 : (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) ^ 2 =
      dist (Δ.points 0) (Δ.points 2) ^ 2 * dist (Δ.points 0) (Δ.points 1) ^ 2 -
      ((dist (Δ.points 0) (Δ.points 2) ^ 2 + dist (Δ.points 0) (Δ.points 1) ^ 2 -
        dist (Δ.points 1) (Δ.points 2) ^ 2) / 2) ^ 2 := by
    rw [hs]
    have : (dist (Δ.points 0) (Δ.points 2) ^ 2 + dist (Δ.points 0) (Δ.points 1) ^ 2 -
        dist (Δ.points 1) (Δ.points 2) ^ 2) / 2 = dist (Δ.points 0) (Δ.points 2) *
        dist (Δ.points 0) (Δ.points 1) * Real.cos (∠ (Δ.points 2) (Δ.points 0) (Δ.points 1)) := by
      linarith
    rw [this]
    linear_combination (dist (Δ.points 0) (Δ.points 2) ^ 2 * dist (Δ.points 0) (Δ.points 1) ^ 2) *
      hsc
  rw [← hK2]
  field_simp

/-- 面 l 的内切圆半径的平方为 r_a r_b r_c/(r_a + r_b + r_c)。 -/
theorem inr_face (hfb : IsFourBall t r) {l a b c : Fin 4} (ha : l.succAbove 0 = a)
    (hb : l.succAbove 1 = b) (hc : l.succAbove 2 = c) :
    (t.faceOpposite l).inradius ^ 2 = r a * r b * r c / (r a + r b + r c) := by
  have inj := Fin.succAbove_right_injective (p := l)
  have hab : a ≠ b := by rw [← ha, ← hb]; exact inj.ne (by decide)
  have hac : a ≠ c := by rw [← ha, ← hc]; exact inj.ne (by decide)
  have hbc : b ≠ c := by rw [← hb, ← hc]; exact inj.ne (by decide)
  have hr := hfb.1
  have := hr a; have := hr b; have := hr c
  rw [inradius_sq, fp l 0 a ha, fp l 1 b hb, fp l 2 c hc, hfb.2 a b hab, hfb.2 a c hac,
    hfb.2 b c hbc]
  field_simp
  ring

theorem Ipt0_eq (hfb : IsFourBall t r) :
    Ipt t 0 = ofWeights t ![0, r 2 + r 3, r 1 + r 3, r 1 + r 2] := by
  have hr := hfb.1
  have hs : r 2 + r 3 + (r 1 + r 3) + (r 1 + r 2) ≠ 0 := by
    have := hr 1; have := hr 2; have := hr 3; positivity
  rw [Ipt, incenter_eq, fp 0 0 1 (by decide), fp 0 1 2 (by decide), fp 0 2 3 (by decide),
    hfb.2 2 3 (by decide), hfb.2 1 3 (by decide), hfb.2 1 2 (by decide),
    ← ofW_smul t (1 / (r 2 + r 3 + (r 1 + r 3) + (r 1 + r 2))) (one_div_ne_zero hs)]
  refine face_comb (a := 1) (b := 2) (c := 3) (by decide) (by decide) (by decide) _ ?_ _ ?_ ?_
  · simp only [Fin.sum_univ_three]; simp; field_simp
  · simp only [Fin.sum_univ_four]; simp; field_simp
  · simp only [L, Fin.sum_univ_four, w]; simp; module

theorem Ipt2_eq (hfb : IsFourBall t r) :
    Ipt t 2 = ofWeights t ![r 1 + r 3, r 0 + r 3, 0, r 0 + r 1] := by
  have hr := hfb.1
  have hs : r 1 + r 3 + (r 0 + r 3) + (r 0 + r 1) ≠ 0 := by
    have := hr 0; have := hr 1; have := hr 3; positivity
  rw [Ipt, incenter_eq, fp 2 0 0 (by decide), fp 2 1 1 (by decide), fp 2 2 3 (by decide),
    hfb.2 1 3 (by decide), hfb.2 0 3 (by decide), hfb.2 0 1 (by decide),
    ← ofW_smul t (1 / (r 1 + r 3 + (r 0 + r 3) + (r 0 + r 1))) (one_div_ne_zero hs)]
  refine face_comb (a := 0) (b := 1) (c := 3) (by decide) (by decide) (by decide) _ ?_ _ ?_ ?_
  · simp only [Fin.sum_univ_three]; simp; field_simp
  · simp only [Fin.sum_univ_four]; simp; field_simp
  · simp only [L, Fin.sum_univ_four, w]; simp; module

theorem X11_1 (hfb : IsFourBall t r) :
    X11 t r 1 = ofWeights t ![r 0 * (r 2 - r 3) ^ 2, 0, r 2 * (r 0 - r 3) ^ 2,
      r 3 * (r 0 - r 2) ^ 2] := by
  have h1 := (hfb.1 1).ne'
  simp only [X11]; congr 1; funext i
  fin_cases i <;> simp [Fin.sum_univ_four, Fin.prod_univ_four] <;> field_simp <;> ring

/-- 一个面上的忠实性：由两条有理恒等式得到。 -/
theorem faith_case (hfb : IsFourBall t r) {l a b c : Fin 4} (ha : l.succAbove 0 = a)
    (hb : l.succAbove 1 = b) (hc : l.succAbove 2 = c) (wx wi : Fin 4 → ℝ)
    (hX : X11 t r l = ofWeights t wx) (hI : Ipt t l = ofWeights t wi)
    (hxl : wx l = 0) (hs : wx a + wx b + wx c ≠ 0)
    (hN : let x := fun m => wx m / (wx a + wx b + wx c)
      x a * x b * e r a b + x a * x c * e r a c + x b * x c * e r b c =
        ((x a + x b - x c) * e r a b + (x a + x c - x b) * e r a c +
          (x b + x c - x a) * e r b c) / 4)
    (hD : dist (ofWeights t wx) (ofWeights t wi) ^ 2 = r a * r b * r c / (r a + r b + r c)) :
    X11 t r l ∈ (t.faceOpposite l).ninePointCircle ∧
      dist (X11 t r l) (Ipt t l) = (t.faceOpposite l).inradius := by
  refine ⟨?_, ?_⟩
  · rw [hX, ← ofW_smul t (1 / (wx a + wx b + wx c)) (one_div_ne_zero hs)]
    refine nine_face hfb ha hb hc _ (by field_simp) (by rw [hxl, mul_zero]) ?_
    simp only at hN
    convert hN using 2 <;> simp only [one_div_mul_eq_div]
  · rw [hX, hI, ← pow_left_inj₀ dist_nonneg (t.faceOpposite l).inradius_pos.le two_ne_zero, hD,
      inr_face hfb ha hb hc]

set_option maxHeartbeats 4000000 in -- 有理恒等式
set_option linter.flexible false in
/-- `X11_faithful` 的证明。 -/
theorem X11_main (hfb : IsFourBall t r) (l : Fin 4)
    (hne : ∃ i j, i ≠ l ∧ j ≠ l ∧ r i ≠ r j) :
    X11 t r l ∈ (t.faceOpposite l).ninePointCircle ∧
      dist (X11 t r l) (Ipt t l) = (t.faceOpposite l).inradius := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have p0 := hr 0; have p1 := hr 1; have p2 := hr 2; have p3 := hr 3
  obtain ⟨i, j, hi, hj, hij⟩ := hne
  fin_cases l
  · -- 面 123
    have hq : ¬ (r 1 = r 2 ∧ r 2 = r 3) := by
      rintro ⟨e1, e2⟩; fin_cases i <;> fin_cases j <;> simp_all
    have hs := (tri_pos (hr 1) (hr 2) (hr 3) hq).ne'
    have sI : r 2 + r 3 + (r 1 + r 3) + (r 1 + r 2) ≠ 0 := by positivity
    refine faith_case hfb (a := 1) (b := 2) (c := 3) (by decide) (by decide) (by decide) _ _
      (X11_0 hfb) (Ipt0_eq hfb) rfl (by simpa [bW] using hs) ?_ ?_
    · simp only [bW, e]; simp; field_simp; ring
    · rw [dist_ofW' hfb (by simpa [bW, Fin.sum_univ_four] using hs)
        (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, bW, e]; field_simp; ring
  · -- 面 023
    have hq : ¬ (r 0 = r 2 ∧ r 2 = r 3) := by
      rintro ⟨e1, e2⟩; fin_cases i <;> fin_cases j <;> simp_all
    have hs := (tri_pos (hr 0) (hr 2) (hr 3) hq).ne'
    have sI : r 2 + r 3 + (r 0 + r 3) + (r 0 + r 2) ≠ 0 := by positivity
    refine faith_case hfb (a := 0) (b := 2) (c := 3) (by decide) (by decide) (by decide) _ _
      (X11_1 hfb) (Ipt1_eq hfb) rfl (by simpa using hs) ?_ ?_
    · simp only [e]; simp; field_simp; ring
    · rw [dist_ofW' hfb (by simpa [Fin.sum_univ_four] using hs)
        (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, e]; field_simp; ring
  · -- 面 013
    have hq : ¬ (r 0 = r 1 ∧ r 1 = r 3) := by
      rintro ⟨e1, e2⟩; fin_cases i <;> fin_cases j <;> simp_all
    have hs := (tri_pos (hr 0) (hr 1) (hr 3) hq).ne'
    have sI : r 1 + r 3 + (r 0 + r 3) + (r 0 + r 1) ≠ 0 := by positivity
    refine faith_case hfb (a := 0) (b := 1) (c := 3) (by decide) (by decide) (by decide) _ _
      (X11_2 hfb) (Ipt2_eq hfb) rfl (by simpa using hs) ?_ ?_
    · simp only [e]; simp; field_simp; ring
    · rw [dist_ofW' hfb (by simpa [Fin.sum_univ_four] using hs)
        (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, e]; field_simp; ring
  · -- 面 012
    have hq : ¬ (r 0 = r 1 ∧ r 1 = r 2) := by
      rintro ⟨e1, e2⟩; fin_cases i <;> fin_cases j <;> simp_all
    have hs := (tri_pos (hr 0) (hr 1) (hr 2) hq).ne'
    have sI : r 1 + r 2 + (r 0 + r 2) + (r 0 + r 1) ≠ 0 := by positivity
    refine faith_case hfb (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) _ _
      (X11_3 hfb) (Ipt3_eq hfb) rfl (by simpa [aW] using hs) ?_ ?_
    · simp only [aW, e]; simp; field_simp; ring
    · rw [dist_ofW' hfb (by simpa [aW, Fin.sum_univ_four] using hs)
        (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, aW, e]; field_simp; ring

end GeometryResearch.Midsphere
