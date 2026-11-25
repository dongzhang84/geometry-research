module

public import GeometryResearch.Midsphere.Incenter

/-!
# 定理 6、7（两个五点球）的证明

五个点都写成重心坐标，所求的球写成 −½xᵀEx + Σpₐxₐ = 0（`Gq`），p 由四个点解出（`p6`、`p7`），
第五个点的条件是 rᵢ 的有理恒等式。
- 定理 6：p 的表达式有 1/(r₁ − r₃)。r₁ = r₃ 时五点在平面 (r₀ + r₁)x₀ − (r₁ + r₂)x₂ = 0 上。
- 定理 7：p 的表达式有 1/(r₀ − r₂)。r₀ = r₂ 时交换 V₀、V₂ 的反射保持五点不动，五点在平面
  x₀ = x₂ 上。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights mid)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

/-- 定理 6 的球的系数。 -/
def p6 (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(r 0 ^ 2 * r 1 - r 0 ^ 2 * r 3 + r 0 * r 1 ^ 2 + r 0 * r 1 * r 3 - 2 * r 1 ^ 2 * r 3) /
      (r 1 - r 3), 0,
    (r 1 + r 2) * (r 0 * r 1 * r 2 - 2 * r 0 * r 1 * r 3 - r 0 * r 2 * r 3 + r 1 ^ 2 * r 2 +
      2 * r 1 ^ 2 * r 3 - r 1 * r 2 * r 3) / ((r 0 + r 1) * (r 1 - r 3)),
    r 3 * (r 1 + r 3)]

/-- 定理 7 的球的系数。 -/
def p7 (r : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(r 0 + r 2) * (r 0 ^ 2 * r 1 + r 0 ^ 2 * r 3 - r 0 * r 1 * r 2 - 2 * r 0 * r 1 * r 3 -
      r 0 * r 2 * r 3 - 2 * r 1 * r 2 * r 3) / (2 * (r 0 - r 2) * (r 1 + r 3)),
    r 1 * (r 0 * r 1 - r 0 * r 3 + 2 * r 1 ^ 2 + r 1 * r 2 + 2 * r 1 * r 3 - r 2 * r 3) /
      (2 * (r 1 + r 3)),
    (r 0 + r 2) * (r 0 * r 1 * r 2 + 2 * r 0 * r 1 * r 3 + r 0 * r 2 * r 3 - r 1 * r 2 ^ 2 +
      2 * r 1 * r 2 * r 3 - r 2 ^ 2 * r 3) / (2 * (r 0 - r 2) * (r 1 + r 3)),
    -(r 3 * (r 0 * r 1 - r 0 * r 3 + r 1 * r 2 - 2 * r 1 * r 3 - r 2 * r 3 - 2 * r 3 ^ 2)) /
      (2 * (r 1 + r 3))]

theorem T_ofW {a b : Fin 4} (hab : a ≠ b) :
    T t r a b = ofWeights t (tw a b (r a / (r a + r b))) := by
  rw [T, lineMap_eq_ofW hab]

theorem N0123_ofW :
    N t r 0 1 2 3 = ofWeights t (fun m => (tw 0 1 (r 0 / (r 0 + r 1)) m +
      tw 2 3 (r 2 / (r 2 + r 3)) m) / 2) := by
  rw [N, T_ofW (by decide), T_ofW (by decide),
    mid_ofW (tw_sum (by decide) _) (tw_sum (by decide) _)]

theorem mid02_ofW : mid t 0 2 = ofWeights t (tw 0 2 (1 / 2)) := by
  rw [mid, ← lineMap_half, lineMap_eq_ofW (by decide)]

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in -- 有理恒等式
/-- 定理 6 的证明。 -/
theorem five6_main (hfb : IsFourBall t r) (h013 : ¬ (r 0 = r 1 ∧ r 1 = r 3)) :
    MCospherical ({t.points 1, Ipt t 3, T t r 1 3, N t r 0 1 2 3, X11 t r 2} : Set E3) := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have p0 := hr 0; have p1 := hr 1; have p2 := hr 2; have p3 := hr 3
  have s01 := (add_pos (hr 0) (hr 1)).ne'; have s13 := (add_pos (hr 1) (hr 3)).ne'
  have s23 := (add_pos (hr 2) (hr 3)).ne'
  have sI : r 1 + r 2 + (r 0 + r 2) + (r 0 + r 1) ≠ 0 := by positivity
  have sX := (tri_pos (hr 0) (hr 1) (hr 3) h013).ne'
  have hN1 : ∑ m, (tw 0 1 (r 0 / (r 0 + r 1)) m + tw 2 3 (r 2 / (r 2 + r 3)) m) / 2 = 1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, tw_sum (by decide), tw_sum (by decide)]
    norm_num
  rw [Ipt3_eq hfb, X11_2 hfb, T_ofW (by decide), N0123_ofW]
  by_cases h13 : r 1 = r 3
  · refine mcosph_of_Gq (t := t) (r := r) 0 ![r 0 + r 1, 0, -(r 1 + r 2), 0] (fun X hX => ?_)
      (Or.inr ⟨0, 1, by simp; linarith⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [Gq_vertex hfb]; rfl
    · rw [Gq_ofW hfb _ _ _ (by simp [Fin.sum_univ_four]; exact sI)]
      simp [Fin.sum_univ_four]; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw]
    · rw [Gq_ofW hfb _ _ _ (by rw [hN1]; exact one_ne_zero), hN1]
      simp [Fin.sum_univ_four, tw]
      field_simp; rw [h13]; ring
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sX)]
      simp [Fin.sum_univ_four, h13]
  · have h13' := sub_ne_zero.mpr h13
    refine mcosph_of_Gq (t := t) (r := r) 1 (p6 r) (fun X hX => ?_) (Or.inl one_ne_zero)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [Gq_vertex hfb]; rfl
    · rw [Gq_ofW hfb _ _ _ (by simp [Fin.sum_univ_four]; exact sI)]
      simp [Fin.sum_univ_four, p6, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw, p6, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [hN1]; exact one_ne_zero), hN1]
      simp [Fin.sum_univ_four, tw, p6, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sX)]
      have sX' : r 0 * (r 1 - r 3) ^ 2 + r 1 * (r 0 - r 3) ^ 2 + r 3 * (r 0 - r 1) ^ 2 ≠ 0 := sX
      simp [Fin.sum_univ_four, p6, e]
      field_simp; ring

set_option linter.flexible false in
set_option maxHeartbeats 1000000 in -- 有理恒等式
/-- 定理 7 的证明。 -/
theorem five7_main (hfb : IsFourBall t r) :
    MCospherical ({Ipt t 3, Ipt t 1, mid t 0 2, foot02 t, T t r 1 3} : Set E3) := by
  have hr := hfb.1
  have h0 := (hr 0).ne'; have h1 := (hr 1).ne'; have h2 := (hr 2).ne'; have h3 := (hr 3).ne'
  have p0 := hr 0; have p1 := hr 1; have p2 := hr 2; have p3 := hr 3
  have s13 := (add_pos (hr 1) (hr 3)).ne'
  have sI : r 1 + r 2 + (r 0 + r 2) + (r 0 + r 1) ≠ 0 := by positivity
  have sJ : r 2 + r 3 + (r 0 + r 3) + (r 0 + r 2) ≠ 0 := by positivity
  rw [Ipt3_eq hfb, Ipt1_eq hfb, mid02_ofW, foot02_eq hfb, T_ofW (by decide)]
  by_cases h02 : r 0 = r 2
  · refine mcosph_of_Gq (t := t) (r := r) 0 ![1, 0, -1, 0] (fun X hX => ?_) (Or.inr ⟨0, 1, by simp⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, h02]; ring
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sJ)]
      simp [Fin.sum_univ_four, h02]
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw]; norm_num
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw]
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw]
  · have h02' := sub_ne_zero.mpr h02
    refine mcosph_of_Gq (t := t) (r := r) 1 (p7 r) (fun X hX => ?_) (Or.inl one_ne_zero)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl | rfl | rfl
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sI)]
      simp [Fin.sum_univ_four, p7, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by simpa [Fin.sum_univ_four] using sJ)]
      simp [Fin.sum_univ_four, p7, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw, p7, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw, p7, e]
      field_simp; ring
    · rw [Gq_ofW hfb _ _ _ (by rw [tw_sum (by decide)]; exact one_ne_zero), tw_sum (by decide)]
      simp [Fin.sum_univ_four, tw, p7, e]
      field_simp; ring

end GeometryResearch.Midsphere
