module

public import GeometryResearch.Midsphere.Model
public import GeometryResearch.Orthocentric.Model

/-!
# 棱切球四面体：忠实性引理与基本公式
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Midsphere

open GeometryResearch.Orthocentric (E3 ofWeights bary S2 isogonal IsFermatPoint G basis)

variable {t : Affine.Simplex ℝ E3 3} {r : Fin 4 → ℝ}

theorem T_spec' (hfb : IsFourBall t r) {i j : Fin 4} (hij : i ≠ j) :
    T t r i j ∈ segment ℝ (t.points i) (t.points j) ∧
      dist (t.points i) (T t r i j) = r i ∧ dist (T t r i j) (t.points j) = r j := by
  have hi := hfb.1 i; have hj := hfb.1 j
  have hd := hfb.2 i j hij
  have hs : 0 < r i + r j := by linarith
  have h01 : r i / (r i + r j) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hs]; linarith⟩
  refine ⟨by rw [T, segment_eq_image_lineMap]; exact ⟨_, h01, rfl⟩, ?_, ?_⟩
  · rw [T, dist_comm, dist_lineMap_left, hd, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  · rw [T, dist_lineMap_right, hd, Real.norm_eq_abs,
      abs_of_pos (by rw [sub_pos, div_lt_one hs]; linarith)]
    field_simp
    ring

theorem exists_fermat' : ∃ F, IsFermatPoint t F := by
  have hc : Continuous (fun Y : E3 => ∑ i, dist Y (t.points i)) := by fun_prop
  have hlim : Filter.Tendsto (fun Y : E3 => ∑ i, dist Y (t.points i))
      (Filter.cocompact E3) Filter.atTop :=
    Filter.tendsto_atTop_mono
      (fun Y => Finset.single_le_sum (f := fun i => dist Y (t.points i))
        (fun i _ => dist_nonneg) (Finset.mem_univ 0))
      (tendsto_dist_right_cocompact_atTop (t.points 0))
  obtain ⟨F, hF⟩ := hc.exists_forall_le hlim
  exact ⟨F, hF⟩

/-- 面积平方用三条边长表示（Heron 的 Gram 形式）。 -/
theorem S2_dists (i : Fin 4) :
    let P := (t.faceOpposite i).points
    S2 t i = (dist (P 0) (P 1) ^ 2 * dist (P 0) (P 2) ^ 2 -
      ((dist (P 0) (P 1) ^ 2 + dist (P 0) (P 2) ^ 2 - dist (P 1) (P 2) ^ 2) / 2) ^ 2) / 4 := by
  intro P
  have e1 : ‖P 1 - P 0‖ ^ 2 = dist (P 0) (P 1) ^ 2 := by rw [dist_comm, dist_eq_norm]
  have e2 : ‖P 2 - P 0‖ ^ 2 = dist (P 0) (P 2) ^ 2 := by rw [dist_comm, dist_eq_norm]
  have e3 : ⟪P 1 - P 0, P 2 - P 0⟫ =
      (dist (P 0) (P 1) ^ 2 + dist (P 0) (P 2) ^ 2 - dist (P 1) (P 2) ^ 2) / 2 := by
    rw [← e1, ← e2, dist_eq_norm, show P 1 - P 2 = (P 1 - P 0) - (P 2 - P 0) by abel]
    generalize P 1 - P 0 = a; generalize P 2 - P 0 = b
    rw [@norm_sub_sq_real]; ring
  simp only [S2]
  rw [e1, e2, e3]

theorem fp (i : Fin 4) (m : Fin 3) (k : Fin 4) (h : i.succAbove m = k) :
    (t.faceOpposite i).points m = t.points k := by
  rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove, ← h]; rfl

/-- Heron：Sᵢ² = (Σr − rᵢ)·Πr/rᵢ。 -/
theorem heron (hfb : IsFourBall t r) (i : Fin 4) :
    S2 t i = (∑ j, r j - r i) * (∏ j, r j) / r i := by
  have hr := hfb.1
  have key : ∀ {i a b c : Fin 4}, a ≠ b → a ≠ c → b ≠ c →
      (t.faceOpposite i).points 0 = t.points a → (t.faceOpposite i).points 1 = t.points b →
      (t.faceOpposite i).points 2 = t.points c →
      S2 t i = (r a + r b + r c) * r a * r b * r c := by
    intro i a b c hab hac hbc ha hb hc
    rw [S2_dists]
    simp only [ha, hb, hc, hfb.2 a b hab, hfb.2 a c hac, hfb.2 b c hbc]
    ring
  rw [Fin.sum_univ_four, Fin.prod_univ_four]
  have k0 : S2 t 0 = (r 0 + r 1 + r 2 + r 3 - r 0) * (r 0 * r 1 * r 2 * r 3) / r 0 := by
    rw [key (i := 0) (a := 1) (b := 2) (c := 3) (by decide) (by decide) (by decide) (fp 0 0 1 rfl)
      (fp 0 1 2 rfl) (fp 0 2 3 rfl)]
    field_simp [(hr 0).ne']; ring
  have k1 : S2 t 1 = (r 0 + r 1 + r 2 + r 3 - r 1) * (r 0 * r 1 * r 2 * r 3) / r 1 := by
    rw [key (i := 1) (a := 0) (b := 2) (c := 3) (by decide) (by decide) (by decide) (fp 1 0 0 rfl)
      (fp 1 1 2 rfl) (fp 1 2 3 rfl)]
    field_simp [(hr 1).ne']; ring
  have k2 : S2 t 2 = (r 0 + r 1 + r 2 + r 3 - r 2) * (r 0 * r 1 * r 2 * r 3) / r 2 := by
    rw [key (i := 2) (a := 0) (b := 1) (c := 3) (by decide) (by decide) (by decide) (fp 2 0 0 rfl)
      (fp 2 1 1 rfl) (fp 2 2 3 rfl)]
    field_simp [(hr 2).ne']; ring
  have k3 : S2 t 3 = (r 0 + r 1 + r 2 + r 3 - r 3) * (r 0 * r 1 * r 2 * r 3) / r 3 := by
    rw [key (i := 3) (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) (fp 3 0 0 rfl)
      (fp 3 1 1 rfl) (fp 3 2 2 rfl)]
    field_simp [(hr 3).ne']; ring
  fin_cases i
  exacts [k0, k1, k2, k3]

variable (t)

/-- 权重整体乘一个非零数，点不变。 -/
theorem ofW_smul (c : ℝ) (hc : c ≠ 0) (x : Fin 4 → ℝ) :
    ofWeights t (fun i => c * x i) = ofWeights t x := by
  simp only [GeometryResearch.Orthocentric.ofWeights]
  congr 1; funext i
  rw [← Finset.mul_sum]
  by_cases hx : ∑ j, x j = 0
  · simp [hx]
  · field_simp

/-- 重心 G 是权重全为 1 的点。 -/
theorem G_eq : G t = ofWeights t (fun _ => 1) := by
  simp only [GeometryResearch.Orthocentric.G, GeometryResearch.Orthocentric.ofWeights,
    Finset.centroid_def, Finset.centroidWeights]
  congr 1; funext i
  simp

end GeometryResearch.Midsphere
