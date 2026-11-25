module

public import GeometryResearch.Midsphere.SoddyFive
public import Mathlib.Geometry.Euclidean.Incenter.Basic
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# 面的内心与到直线的垂足

- 三角形的内心：Mathlib 的权重是 1/hᵢ（hᵢ 为高）。由 hᵢ = sin(角)·边 得 hᵢ·aᵢ 都等于两倍面积，
  所以权重与对边长成正比。对切长为 r 的面，内心的重心坐标为 (r_b + r_c : r_a + r_c : r_a + r_b)。
- 点到直线 BC 的垂足为 B + (⟪P − B, C − B⟫/|BC|²)(C − B)。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights basis mid)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 点到直线的垂足。 -/
theorem proj_line {B C P : E3} (h : B ≠ C) :
    (orthogonalProjection line[ℝ, B, C] P : E3) =
      AffineMap.lineMap B C (⟪P - B, C - B⟫ / ‖C - B‖ ^ 2) := by
  have hn : ‖C - B‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h.symm)
  rw [coe_orthogonalProjection_eq_iff_mem]
  refine ⟨AffineMap.lineMap_mem_affineSpan_pair _ _ _, ?_⟩
  rw [direction_affineSpan, vectorSpan_pair_rev, Submodule.mem_orthogonal_singleton_iff_inner_right,
    AffineMap.lineMap_apply_module, vsub_eq_sub, vsub_eq_sub,
    show P - ((1 - ⟪P - B, C - B⟫ / ‖C - B‖ ^ 2) • B + (⟪P - B, C - B⟫ / ‖C - B‖ ^ 2) • C) =
      (P - B) - (⟪P - B, C - B⟫ / ‖C - B‖ ^ 2) • (C - B) by module,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
  field_simp
  ring

/-- 三角形的 hᵢ·aᵢ 与 i 无关（都等于两倍面积）。 -/
theorem height_mul_side (Δ : Affine.Triangle ℝ E3) :
    Δ.height 0 * dist (Δ.points 1) (Δ.points 2) = Δ.height 2 * dist (Δ.points 0) (Δ.points 1) ∧
    Δ.height 1 * dist (Δ.points 0) (Δ.points 2) = Δ.height 2 * dist (Δ.points 0) (Δ.points 1) := by
  have h0 := Δ.height_eq_sin_mul_dist (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have h2 := Δ.height_eq_sin_mul_dist (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide)
    (by decide)
  have h1 := Δ.height_eq_sin_mul_dist (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide)
    (by decide)
  have h2' := Δ.height_eq_sin_mul_dist (i₁ := 2) (i₂ := 0) (i₃ := 1) (by decide) (by decide)
    (by decide)
  rw [angle_comm] at h2 h2'
  constructor
  · rw [h0, h2, dist_comm (Δ.points 2) (Δ.points 1)]; ring
  · rw [h1, h2', dist_comm (Δ.points 1) (Δ.points 0), dist_comm (Δ.points 2) (Δ.points 0)]; ring

/-- 三角形内心的权重与对边长成正比。 -/
theorem incenter_eq (Δ : Affine.Triangle ℝ E3) :
    Δ.incenter = Finset.univ.affineCombination ℝ Δ.points
      (fun i => ![dist (Δ.points 1) (Δ.points 2), dist (Δ.points 0) (Δ.points 2),
        dist (Δ.points 0) (Δ.points 1)] i /
        (dist (Δ.points 1) (Δ.points 2) + dist (Δ.points 0) (Δ.points 2) +
          dist (Δ.points 0) (Δ.points 1))) := by
  have hp : ∀ i, 0 < Δ.height i := fun i => Δ.height_pos i
  have hd : ∀ i j, i ≠ j → 0 < dist (Δ.points i) (Δ.points j) := fun i j h =>
    dist_pos.mpr (Δ.independent.injective.ne h)
  have d12 := hd 1 2 (by decide); have d02 := hd 0 2 (by decide); have d01 := hd 0 1 (by decide)
  obtain ⟨k0, k1⟩ := height_mul_side Δ
  have hsum : ∑ i, ![dist (Δ.points 1) (Δ.points 2), dist (Δ.points 0) (Δ.points 2),
        dist (Δ.points 0) (Δ.points 1)] i /
        (dist (Δ.points 1) (Δ.points 2) + dist (Δ.points 0) (Δ.points 2) +
          dist (Δ.points 0) (Δ.points 1)) = 1 := by
    simp only [Fin.sum_univ_three]; simp; field_simp
  symm
  rw [show Δ.incenter = Δ.excenter ∅ from rfl,
    Δ.excenterExists_empty.affineCombination_eq_excenter_iff hsum]
  funext i
  simp only [Affine.Simplex.excenterWeights, Affine.Simplex.excenterWeightsUnnorm,
    Finset.notMem_empty, ite_false, one_mul, Pi.smul_apply, smul_eq_mul]
  have h0 := (hp 0).ne'; have h1 := (hp 1).ne'; have h2 := (hp 2).ne'
  have hK : Δ.height 2 * dist (Δ.points 0) (Δ.points 1) ≠ 0 := by positivity
  have e0 : (Δ.height 0)⁻¹ = dist (Δ.points 1) (Δ.points 2) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by
    rw [← k0]; field_simp
  have e1 : (Δ.height 1)⁻¹ = dist (Δ.points 0) (Δ.points 2) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by
    rw [← k1]; field_simp
  have e2 : (Δ.height 2)⁻¹ = dist (Δ.points 0) (Δ.points 1) /
      (Δ.height 2 * dist (Δ.points 0) (Δ.points 1)) := by
    field_simp
  rw [Fin.sum_univ_three, e0, e1, e2]
  fin_cases i <;> simp [e0, e1, e2] <;> field_simp

/-! ## 重心坐标下的广义球 α(−½xᵀEx) + Σpₐxₐ = 0 -/

variable (t) in
/-- 广义球的方程 α(|XV₀|² − Σxₐe₀ₐ) + Σpₐxₐ，即 α(−½xᵀEx) + Σpₐxₐ。 -/
def Gq (α : ℝ) (p : Fin 4 → ℝ) (X : E3) : ℝ :=
  α * (dist X (t.points 0) ^ 2 - ellV t (fun a => e r 0 a) X) + ellV t p X

theorem Gq_ofW (hfb : IsFourBall t r) (α : ℝ) (p x : Fin 4 → ℝ) (hx : ∑ m, x m ≠ 0) :
    Gq t (r := r) α p (ofWeights t x) =
      α * (-(1 / 2) * ∑ a, ∑ b, (x a / ∑ m, x m) * (x b / ∑ m, x m) * e r a b) +
        ∑ a, p a * (x a / ∑ m, x m) := by
  rw [Gq, dist_ofW_pt hfb hx, ellV_ofW _ _ hx, ellV_ofW _ _ hx]
  simp only [dist_sq_e hfb, e]
  have : ∀ a : Fin 4, (if a = 0 then 0 else (r a + r 0) ^ 2) =
      (if (0 : Fin 4) = a then 0 else (r 0 + r a) ^ 2) := by
    intro a; by_cases h : a = 0 <;> simp [h, eq_comm, add_comm]
  simp only [this]
  have hc : ∑ a, (x a / ∑ m, x m) * (if (0 : Fin 4) = a then 0 else (r 0 + r a) ^ 2) =
      ∑ a, (if (0 : Fin 4) = a then 0 else (r 0 + r a) ^ 2) * (x a / ∑ m, x m) :=
    Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  rw [hc]
  ring

theorem Gq_vertex (hfb : IsFourBall t r) (α : ℝ) (p : Fin 4 → ℝ) (j : Fin 4) :
    Gq t (r := r) α p (t.points j) = p j := by
  have : e r j 0 = e r 0 j := by simp only [e, eq_comm, add_comm]
  rw [Gq, ellV_vertex, ellV_vertex, dist_sq_e hfb, this, sub_self, mul_zero, zero_add]

/-- 广义球判据：α ≠ 0 时是球，α = 0 且 p 不是常数时是平面。 -/
theorem mcosph_of_Gq {S : Set E3} (α : ℝ) (p : Fin 4 → ℝ)
    (h : ∀ X ∈ S, Gq t (r := r) α p X = 0) (hne : α ≠ 0 ∨ ∃ a b, p a ≠ p b) :
    MCospherical S := by
  by_cases hα : α = 0
  · right
    obtain ⟨a, b, hab⟩ := hne.resolve_left (not_not.mpr hα)
    refine coplanar_ell (t := t) p hab (fun X hX => ?_)
    have := h X hX
    rwa [Gq, hα, zero_mul, zero_add] at this
  · left
    obtain ⟨c, κ, hc⟩ := ellV_repr (t := t) (fun a => p a / α - e r 0 a) (t.points 0)
    refine cosph_of (t.points 0) (t.points 0) c κ (fun X hX => ?_)
    have h1 := h X hX
    have h2 := hc X
    simp only [ellV] at h1 h2
    rw [← h2]
    simp only [Gq, ellV] at h1
    have : ∑ i, (p i / α - e r 0 i) * (basis t).coord i X =
        (∑ i, p i * (basis t).coord i X) / α - ∑ i, e r 0 i * (basis t).coord i X := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by field_simp)
    rw [this]
    field_simp
    linear_combination h1

/-! ## 各点的重心坐标 -/

/-- 面上的仿射组合写成四面体的 ofWeights。 -/
theorem face_comb {l : Fin 4} {a b c : Fin 4} (ha : l.succAbove 0 = a) (hb : l.succAbove 1 = b)
    (hc : l.succAbove 2 = c) (w : Fin 3 → ℝ) (hw : ∑ m, w m = 1) (W : Fin 4 → ℝ)
    (hW : ∑ m, W m = 1)
    (hv : (1 : ℝ) • L t W = w 0 • (t.points a - t.points 0) + w 1 • (t.points b - t.points 0) +
      w 2 • (t.points c - t.points 0)) :
    Finset.univ.affineCombination ℝ (t.faceOpposite l).points w = ofWeights t W := by
  have e := ofW_sub_V0 t W (by rw [hW]; exact one_ne_zero)
  rw [hW, div_one] at e
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hw (t.points 0),
    Finset.weightedVSubOfPoint_apply, Fin.sum_univ_three, fp l 0 a ha, fp l 1 b hb,
    fp l 2 c hc, ← sub_eq_zero, vadd_eq_add, show ∀ X : E3, X + t.points 0 - ofWeights t W =
      X - (ofWeights t W - t.points 0) from fun X => by abel, e, hv]
  simp only [vsub_eq_sub]
  abel

theorem Ipt3_eq (hfb : IsFourBall t r) :
    Ipt t 3 = ofWeights t ![r 1 + r 2, r 0 + r 2, r 0 + r 1, 0] := by
  have hr := hfb.1
  have hs : r 1 + r 2 + (r 0 + r 2) + (r 0 + r 1) ≠ 0 := by
    have := hr 0; have := hr 1; have := hr 2; positivity
  rw [Ipt, incenter_eq, fp 3 0 0 (by decide), fp 3 1 1 (by decide), fp 3 2 2 (by decide),
    hfb.2 1 2 (by decide), hfb.2 0 2 (by decide), hfb.2 0 1 (by decide),
    ← ofW_smul t (1 / (r 1 + r 2 + (r 0 + r 2) + (r 0 + r 1))) (one_div_ne_zero hs)]
  refine face_comb (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) _ ?_ _ ?_ ?_
  · simp only [Fin.sum_univ_three]; simp; field_simp
  · simp only [Fin.sum_univ_four]; simp; field_simp
  · simp only [L, Fin.sum_univ_four, w]; simp; module

theorem Ipt1_eq (hfb : IsFourBall t r) :
    Ipt t 1 = ofWeights t ![r 2 + r 3, 0, r 0 + r 3, r 0 + r 2] := by
  have hr := hfb.1
  have hs : r 2 + r 3 + (r 0 + r 3) + (r 0 + r 2) ≠ 0 := by
    have := hr 0; have := hr 2; have := hr 3; positivity
  rw [Ipt, incenter_eq, fp 1 0 0 (by decide), fp 1 1 2 (by decide), fp 1 2 3 (by decide),
    hfb.2 2 3 (by decide), hfb.2 0 3 (by decide), hfb.2 0 2 (by decide),
    ← ofW_smul t (1 / (r 2 + r 3 + (r 0 + r 3) + (r 0 + r 2))) (one_div_ne_zero hs)]
  refine face_comb (a := 0) (b := 2) (c := 3) (by decide) (by decide) (by decide) _ ?_ _ ?_ ?_
  · simp only [Fin.sum_univ_three]; simp; field_simp
  · simp only [Fin.sum_univ_four]; simp; field_simp
  · simp only [L, Fin.sum_univ_four, w]; simp; module

/-- m₀₂ 到直线 V₁V₃ 的垂足。 -/
theorem foot02_eq (hfb : IsFourBall t r) :
    foot02 t = ofWeights t (tw 1 3 ((r 0 * r 1 - r 0 * r 3 + 2 * r 1 ^ 2 + r 1 * r 2 +
      2 * r 1 * r 3 - r 2 * r 3) / (2 * (r 1 + r 3) ^ 2))) := by
  have hr := hfb.1
  have h13 : t.points 1 ≠ t.points 3 := t.independent.injective.ne (by decide)
  have hs := (add_pos (hr 1) (hr 3)).ne'
  rw [foot02, proj_line h13, lineMap_eq_ofW (by decide)]
  congr 2
  have hm : mid t 0 2 = ofWeights t (tw 0 2 (1 / 2)) := by
    rw [mid, ← lineMap_half, lineMap_eq_ofW (by decide)]
  have d1 := dist_ofW hfb (tw_sum (show (0 : Fin 4) ≠ 2 by decide) (1 / 2))
    (tw_sum (show (1 : Fin 4) ≠ 3 by decide) 0)
  have d3 := dist_ofW hfb (tw_sum (show (0 : Fin 4) ≠ 2 by decide) (1 / 2))
    (tw_sum (show (3 : Fin 4) ≠ 1 by decide) 0)
  have hv1 : t.points 1 = ofWeights t (tw 1 3 0) := by
    rw [← lineMap_eq_ofW (by decide), AffineMap.lineMap_apply_zero]
  have hv3 : t.points 3 = ofWeights t (tw 3 1 0) := by
    rw [← lineMap_eq_ofW (by decide), AffineMap.lineMap_apply_zero]
  rw [← hm, ← hv1] at d1
  rw [← hm, ← hv3] at d3
  have hn : ‖t.points 3 - t.points 1‖ = r 1 + r 3 := by
    rw [← dist_eq_norm, dist_comm, hfb.2 1 3 (by decide)]
  have hi : ⟪mid t 0 2 - t.points 1, t.points 3 - t.points 1⟫ =
      (dist (mid t 0 2) (t.points 1) ^ 2 + ‖t.points 3 - t.points 1‖ ^ 2 -
        dist (mid t 0 2) (t.points 3) ^ 2) / 2 := by
    rw [dist_eq_norm, dist_eq_norm, show mid t 0 2 - t.points 3 =
      (mid t 0 2 - t.points 1) - (t.points 3 - t.points 1) by abel]
    generalize mid t 0 2 - t.points 1 = u
    generalize t.points 3 - t.points 1 = v
    rw [norm_sub_sq_real]
    ring
  rw [hi, hn, d1, d3]
  simp only [Fin.sum_univ_four, tw, e]
  simp
  field_simp
  ring

theorem X11_2 (hfb : IsFourBall t r) :
    X11 t r 2 = ofWeights t ![r 0 * (r 1 - r 3) ^ 2, r 1 * (r 0 - r 3) ^ 2, 0,
      r 3 * (r 0 - r 1) ^ 2] := by
  have h2 := (hfb.1 2).ne'
  simp only [X11]; congr 1; funext i
  fin_cases i <;> simp [Fin.sum_univ_four, Fin.prod_univ_four] <;> field_simp <;> ring

end GeometryResearch.Midsphere
