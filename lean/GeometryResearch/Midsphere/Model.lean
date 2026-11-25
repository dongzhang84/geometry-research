module

public import GeometryResearch.Midsphere.Defs

/-!
# 棱切球四面体：以 V₀ 为原点的 Gram 计算

wₖ = Vₖ − V₀，|VᵢVⱼ|² = eᵢⱼ = (rᵢ + rⱼ)²（i ≠ j），于是
⟪wᵢ, wⱼ⟫ = gᵢⱼ = (e₀ᵢ + e₀ⱼ − eᵢⱼ)/2 是切长的多项式。权重为 x 的点满足
σ(x)·(X − V₀) = Σ xₖwₖ，所以一切内积、距离都化为切长的有理式。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights)

variable (t : Affine.Simplex ℝ E3 3) (r : Fin 4 → ℝ)

/-- wₖ = Vₖ − V₀。 -/
abbrev w (k : Fin 4) : E3 := t.points k - t.points 0

/-- eᵢⱼ = |VᵢVⱼ|²。 -/
def e (i j : Fin 4) : ℝ := if i = j then 0 else (r i + r j) ^ 2

/-- gᵢⱼ = ⟪wᵢ, wⱼ⟫。 -/
def g (i j : Fin 4) : ℝ := (e r 0 i + e r 0 j - e r i j) / 2

variable {t r}

theorem dist_sq_e (hfb : IsFourBall t r) (i j : Fin 4) :
    dist (t.points i) (t.points j) ^ 2 = e r i j := by
  by_cases h : i = j
  · subst h; simp [e]
  · rw [hfb.2 i j h, e, ite_eq_right_iff.mpr (fun h' => absurd h' h)]

theorem inner_w (hfb : IsFourBall t r) (i j : Fin 4) : ⟪w t i, w t j⟫ = g r i j := by
  have h1 : ‖w t i‖ ^ 2 = e r 0 i := by rw [← dist_eq_norm, dist_comm, dist_sq_e hfb]
  have h2 : ‖w t j‖ ^ 2 = e r 0 j := by rw [← dist_eq_norm, dist_comm, dist_sq_e hfb]
  have h3 : ‖w t i - w t j‖ ^ 2 = e r i j := by
    rw [show w t i - w t j = t.points i - t.points j by simp only [w]; abel, ← dist_eq_norm,
      dist_sq_e hfb]
  rw [g, ← h1, ← h2, ← h3]
  generalize w t i = a at *
  generalize w t j = b at *
  rw [@norm_sub_sq_real]
  ring

variable (t)

/-- L(x) = Σ xₖ wₖ。 -/
def L (x : Fin 4 → ℝ) : E3 := ∑ k, x k • w t k

theorem L_four (x : Fin 4 → ℝ) : L t x = x 1 • w t 1 + x 2 • w t 2 + x 3 • w t 3 := by
  rw [L, Fin.sum_univ_four]; simp [w]

/-- 权重为 x 的点：X − V₀ = L(x)/σ(x)。 -/
theorem ofW_sub_V0 (x : Fin 4 → ℝ) (hx : ∑ j, x j ≠ 0) :
    ofWeights t x - t.points 0 = (1 / ∑ j, x j) • L t x := by
  have hsum : ∑ j, x j / ∑ j, x j = 1 := by rw [← Finset.sum_div, div_self hx]
  rw [GeometryResearch.Orthocentric.ofWeights,
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum (t.points 0),
    Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_sub_cancel_right, L, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, vsub_eq_sub]
  congr 1
  ring

variable {t}

/-- Gram 展开：⟪L(x), L(y)⟫ = Σ xₖyₗ gₖₗ（k, l = 1, 2, 3）。 -/
theorem inner_L (hfb : IsFourBall t r) (x y : Fin 4 → ℝ) :
    ⟪L t x, L t y⟫ = ∑ k : Fin 3, ∑ l : Fin 3, x k.succ * y l.succ * g r k.succ l.succ := by
  rw [L_four, L_four]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_w hfb, Fin.sum_univ_three]
  simp
  ring

end GeometryResearch.Midsphere
