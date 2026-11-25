module

public import GeometryResearch.Orthocentric.Seven

/-!
# 定理 2、3（两条欧拉线上的共轭）的证明

以 H 为原点，权重为 w 的点满足 σ(w)·(X − H) = L(w)，其中 σ(w) = Σwⱼ，L(w) = Σ wⱼvⱼ。
核心关系 Σ vⱼ/aⱼ = 0 说明：权重 (c₁ + c₂/aⱼ + c₃gⱼ) 的 L 等于 c₁·s + c₃·L(g)。

* 定理 2：O、H、P*、Pᵗ 减去 H 都落在 span{s, z} 里，所以四点共面。
* 定理 3：O 的权重是 Pᵗ 与 P* 的权重的线性组合，所以三点共线。

面积的平方 Sⱼ² 由 4Sⱼ² = 对面三个 a 的两两乘积之和（论文 Lemma 2.1(b)）和
Vieta 关系化为 4Sⱼ²aⱼ² = e₃(aⱼ + p)。H 是顶点（三直角四面体）的情形单独处理。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

variable (t : Affine.Simplex ℝ E3 3)

/-- L(f) = Σⱼ fⱼ vⱼ。 -/
def Lv (f : Fin 4 → ℝ) : E3 := ∑ j, f j • v t j

theorem Lv_four (f : Fin 4 → ℝ) :
    Lv t f = f 0 • v t 0 + f 1 • v t 1 + f 2 • v t 2 + f 3 • v t 3 := by
  rw [Lv, Fin.sum_univ_four]

/-- σ(w)·(X − H) = L(w)：权重为 w 的点减 H。 -/
theorem ofW_sub_H (w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0) :
    ofWeights t w - H t = (1 / ∑ j, w j) • Lv t w := by
  have hsum : ∑ j, w j / ∑ j, w j = 1 := by rw [← Finset.sum_div, div_self hw]
  rw [ofWeights, Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ hsum
    (H t), Finset.weightedVSubOfPoint_apply, vadd_eq_add, add_sub_cancel_right, Lv,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, vsub_eq_sub]
  congr 1
  ring

theorem bary_ofWeights' (w : Fin 4 → ℝ) (hw : ∑ j, w j ≠ 0) (i : Fin 4) :
    bary t (ofWeights t w) i = w i / ∑ j, w j := by
  have hsum : ∑ j, w j / ∑ j, w j = 1 := by rw [← Finset.sum_div, div_self hw]
  have hb : (⇑(basis t) : Fin 4 → E3) = t.points := rfl
  simp only [bary, ofWeights, AffineBasis.coords_apply]
  rw [← hb]
  exact (basis t).coord_apply_combination_of_mem (Finset.mem_univ i) hsum

/-- 若 Σw = 1 且 X − H = L(w)，则 X 的重心坐标就是 w。 -/
theorem bary_of_Lv {X : E3} (w : Fin 4 → ℝ) (h1 : ∑ j, w j = 1) (hX : X - H t = Lv t w) :
    bary t X = w := by
  have hX' : X = ofWeights t w := by
    have := ofW_sub_H t w (by rw [h1]; exact one_ne_zero)
    rw [h1, div_one, one_smul, ← hX] at this
    exact (sub_left_inj.mp this).symm
  funext i
  rw [hX', bary_ofWeights' t w (by rw [h1]; exact one_ne_zero), h1, div_one]

/-- 核心关系的用法：权重 c₁ + c₂/Aⱼ + c₃gⱼ 的 L 等于 c₁·s + c₃·L(g)。 -/
theorem Lv_comb (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) {w g : Fin 4 → ℝ}
    (c₁ c₂ c₃ : ℝ) (hw : ∀ j, w j = c₁ + c₂ / A t j + c₃ * g j) :
    Lv t w = c₁ • sv t + c₃ • Lv t g := by
  obtain ⟨-, -, hrel⟩ := rel t ho hH
  have key : Lv t w = c₁ • sv t +
      c₂ • ((1 / A t 0) • v t 0 + (1 / A t 1) • v t 1 + (1 / A t 2) • v t 2 +
        (1 / A t 3) • v t 3) + c₃ • Lv t g := by
    rw [Lv_four, Lv_four, hw, hw, hw, hw, sv]
    module
  rw [key, hrel, smul_zero, add_zero]

/-- e₃ = 三个 A 的乘积之和，Π = 四个 A 的乘积。 -/
def e3 : ℝ := A t 0 * A t 1 * A t 2 + A t 0 * A t 1 * A t 3 + A t 0 * A t 2 * A t 3 +
  A t 1 * A t 2 * A t 3

theorem p_e3 (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) :
    p t * e3 t = -(A t 0 * A t 1 * A t 2 * A t 3) := by
  obtain ⟨-, hsum, -⟩ := rel t ho hH
  have hA := A_ne t ho hH
  have h0 := hA 0; have h1 := hA 1; have h2 := hA 2; have h3 := hA 3
  field_simp at hsum
  rw [e3]
  linear_combination hsum

/-- 论文 Lemma 2.1(c)：O 的重心坐标 oⱼ = 1/2 + p/Aⱼ。 -/
theorem bary_O (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) :
    bary t (O t) = fun j => 1 / 2 + p t / A t j := by
  obtain ⟨-, hsum, -⟩ := rel t ho hH
  apply bary_of_Lv
  · rw [Fin.sum_univ_four]
    linear_combination hsum
  · rw [O_sub_H, Lv_comb t ho hH (g := fun _ => 0) (1 / 2) (p t) 0 (fun j => by ring),
      zero_smul, add_zero]

/-! ## 面积的平方 -/

/-- 面 i 的三个顶点为 Vₐ、V_b、V_c 时，4Sᵢ² = AₐA_b + AₐA_c + A_bA_c（论文 Lemma 2.1(b)）。 -/
theorem S2_abc (ho : IsOrthocentric t) {i a b c : Fin 4}
    (ha : (t.faceOpposite i).points 0 = t.points a) (hb : (t.faceOpposite i).points 1 = t.points b)
    (hc : (t.faceOpposite i).points 2 = t.points c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    4 * S2 t i = A t a * A t b + A t a * A t c + A t b * A t c := by
  have e1 : t.points b - t.points a = v t b - v t a := by simp only [v, sub_sub_sub_cancel_right]
  have e2 : t.points c - t.points a = v t c - v t a := by simp only [v, sub_sub_sub_cancel_right]
  have hba : b ≠ a := hab.symm
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := hbc.symm
  have faa := inner_v_self t a; have fbb := inner_v_self t b; have fcc := inner_v_self t c
  have fab : ⟪v t a, v t b⟫ = p t := inner_pt_H t ho hab
  have fac : ⟪v t a, v t c⟫ = p t := inner_pt_H t ho hac
  have fbc : ⟪v t b, v t c⟫ = p t := inner_pt_H t ho hbc
  have fba : ⟪v t b, v t a⟫ = p t := inner_pt_H t ho hba
  have fca : ⟪v t c, v t a⟫ = p t := inner_pt_H t ho hca
  have fcb : ⟪v t c, v t b⟫ = p t := inner_pt_H t ho hcb
  simp only [S2, ha, hb, hc, e1, e2]
  generalize v t a = x at *
  generalize v t b = y at *
  generalize v t c = z at *
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, faa, fbb, fcc, fab,
    fac, fbc, fba, fca]
  ring

theorem fp (i : Fin 4) (m : Fin 3) (k : Fin 4) (h : i.succAbove m = k) :
    (t.faceOpposite i).points m = t.points k := by
  rw [face_point, h]

/-- 四个面的 4Sᵢ²。 -/
theorem S2_all (ho : IsOrthocentric t) :
    4 * S2 t 0 = A t 1 * A t 2 + A t 1 * A t 3 + A t 2 * A t 3 ∧
    4 * S2 t 1 = A t 0 * A t 2 + A t 0 * A t 3 + A t 2 * A t 3 ∧
    4 * S2 t 2 = A t 0 * A t 1 + A t 0 * A t 3 + A t 1 * A t 3 ∧
    4 * S2 t 3 = A t 0 * A t 1 + A t 0 * A t 2 + A t 1 * A t 2 :=
  ⟨S2_abc t ho (fp t 0 0 1 rfl) (fp t 0 1 2 rfl) (fp t 0 2 3 rfl) (by decide) (by decide)
      (by decide),
    S2_abc t ho (fp t 1 0 0 rfl) (fp t 1 1 2 rfl) (fp t 1 2 3 rfl) (by decide) (by decide)
      (by decide),
    S2_abc t ho (fp t 2 0 0 rfl) (fp t 2 1 1 rfl) (fp t 2 2 3 rfl) (by decide) (by decide)
      (by decide),
    S2_abc t ho (fp t 3 0 0 rfl) (fp t 3 1 1 rfl) (fp t 3 2 2 rfl) (by decide) (by decide)
      (by decide)⟩

/-- Vieta 关系化简后：4Sⱼ²·Aⱼ² = e₃·(Aⱼ + p)。 -/
theorem S2_mul (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) (j : Fin 4) :
    4 * S2 t j * A t j ^ 2 = e3 t * (A t j + p t) := by
  obtain ⟨h0, h1, h2, h3⟩ := S2_all t ho
  have hpe := p_e3 t ho hH
  rw [e3] at hpe
  have k0 : 4 * S2 t 0 * A t 0 ^ 2 = e3 t * (A t 0 + p t) := by
    rw [h0, e3]; linear_combination (-1 : ℝ) * hpe
  have k1 : 4 * S2 t 1 * A t 1 ^ 2 = e3 t * (A t 1 + p t) := by
    rw [h1, e3]; linear_combination (-1 : ℝ) * hpe
  have k2 : 4 * S2 t 2 * A t 2 ^ 2 = e3 t * (A t 2 + p t) := by
    rw [h2, e3]; linear_combination (-1 : ℝ) * hpe
  have k3 : 4 * S2 t 3 * A t 3 ^ 2 = e3 t * (A t 3 + p t) := by
    rw [h3, e3]; linear_combination (-1 : ℝ) * hpe
  fin_cases j
  exacts [k0, k1, k2, k3]

/-! ## 共面与共线的判别 -/

theorem mem_span2 (z₁ z₂ : E3) (a b : ℝ) :
    a • z₁ + b • z₂ ∈ Submodule.span ℝ (Set.range ![z₁, z₂]) :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))

/-- 集合中每点减去 Q 都落在 span{z₁, z₂} 中，则共面。 -/
theorem coplanar_of_span {S : Set E3} {Q : E3} (hQ : Q ∈ S) (z₁ z₂ : E3)
    (h : ∀ X ∈ S, X - Q ∈ Submodule.span ℝ (Set.range ![z₁, z₂])) : Coplanar ℝ S := by
  rw [coplanar_iff_finrank_le_two]
  have hle : vectorSpan ℝ S ≤ Submodule.span ℝ (Set.range ![z₁, z₂]) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ hQ, Submodule.span_le]
    rintro x ⟨y, hy, rfl⟩
    exact h y hy
  calc Module.finrank ℝ (vectorSpan ℝ S)
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range ![z₁, z₂])) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin 2) := finrank_range_le_card _
    _ = 2 := Fintype.card_fin 2

/-- (c₁ + c₂)(X₀ − Q) = c₁(X₁ − Q) + c₂(X₂ − Q) 且 c₁ + c₂ ≠ 0，则 X₀、X₁、X₂ 共线。 -/
theorem collinear_of_comb {X₀ X₁ X₂ Q : E3} {c₁ c₂ : ℝ} (h0 : c₁ + c₂ ≠ 0)
    (h : (c₁ + c₂) • (X₀ - Q) = c₁ • (X₁ - Q) + c₂ • (X₂ - Q)) :
    Collinear ℝ ({X₀, X₁, X₂} : Set E3) := by
  have key : c₁ • (X₁ - X₀) + c₂ • (X₂ - X₀) = 0 := by
    rw [show c₁ • (X₁ - X₀) + c₂ • (X₂ - X₀) =
      c₁ • (X₁ - Q) + c₂ • (X₂ - Q) - (c₁ + c₂) • (X₀ - Q) by module, h, sub_self]
  rw [collinear_iff_of_mem (Set.mem_insert X₀ _)]
  by_cases hc2 : c₂ = 0
  · have hc1 : c₁ ≠ 0 := by rwa [hc2, add_zero] at h0
    rw [hc2, zero_smul, add_zero, smul_eq_zero] at key
    have h10 : X₁ = X₀ := sub_eq_zero.mp (key.resolve_left hc1)
    refine ⟨X₂ - X₀, fun X hX => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [h10]⟩
    · exact ⟨1, by simp⟩
  · refine ⟨X₁ - X₀, fun X hX => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · refine ⟨-c₁ / c₂, ?_⟩
      rw [vadd_eq_add]
      have : c₂ • (X - X₀) = -c₁ • (X₁ - X₀) := by
        rw [neg_smul]; exact eq_neg_of_add_eq_zero_right key
      have h2 : X - X₀ = (-c₁ / c₂) • (X₁ - X₀) := by
        rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hc2, one_smul]
      rw [← h2]; abel

/-! ## H 是顶点（三直角四面体）的情形 -/

theorem Lv_add (α β : ℝ) (f g : Fin 4 → ℝ) :
    Lv t (fun j => α * f j + β * g j) = α • Lv t f + β • Lv t g := by
  rw [Lv_four, Lv_four, Lv_four]; module

theorem sum_add (α β : ℝ) (f g : Fin 4 → ℝ) :
    ∑ j, (α * f j + β * g j) = α * ∑ j, f j + β * ∑ j, g j := by
  simp only [Fin.sum_univ_four]; ring

/-- vₖ = 0 时，除第 k 个以外权重都等于 c 的 L 等于 c·s。 -/
theorem Lv_vertex {k : Fin 4} (hvk : v t k = 0) (f : Fin 4 → ℝ) (c : ℝ)
    (hf : ∀ j, j ≠ k → f j = c) : Lv t f = c • sv t := by
  have h : ∀ j, f j • v t j = c • v t j := by
    intro j
    by_cases hj : j = k
    · subst hj; rw [hvk, smul_zero, smul_zero]
    · rw [hf j hj]
  rw [Lv_four, h, h, h, h, sv]
  module

/-- H = Vₖ 时：vₖ = 0，p = 0，Aₖ = 0，O 的重心坐标为 (1/2, …, −1/2, …, 1/2)。 -/
theorem vertex_facts (ho : IsOrthocentric t) {k : Fin 4} (hk : H t = t.points k) :
    v t k = 0 ∧ p t = 0 ∧ A t k = 0 ∧
      bary t (O t) = fun j => if j = k then -1 / 2 else 1 / 2 := by
  have hvk : v t k = 0 := by simp [v, hk]
  obtain ⟨j, hj⟩ := exists_ne k
  have hp : p t = 0 := by
    have := inner_pt_H t ho (Ne.symm hj)
    rw [show t.points k - H t = v t k from rfl, hvk, inner_zero_left] at this
    exact this.symm
  refine ⟨hvk, hp, by simp [A, hvk, hp], ?_⟩
  apply bary_of_Lv
  · fin_cases k <;> simp [Fin.sum_univ_four] <;> norm_num
  · rw [O_sub_H, Lv_vertex t hvk _ (1 / 2) (fun j hj => by simp [hj])]

/-- 定理 3 的假设（O 的两种共轭有定义）排除了 H 是顶点：否则由德古阿定理 Σ Sⱼ²/oⱼ = 0。 -/
theorem H_ne_vertex_of_O (ho : IsOrthocentric t) (hO : ConjDefined t (O t)) :
    ∀ j, H t ≠ t.points j := by
  intro k hk
  obtain ⟨-, hp, hAk, hbO⟩ := vertex_facts t ho hk
  obtain ⟨h0, h1, h2, h3⟩ := S2_all t ho
  apply hO.2.1
  rw [hbO, Fin.sum_univ_four]
  fin_cases k <;> simp at hAk ⊢ <;>
    simp only [hAk, zero_mul, mul_zero, zero_add, add_zero] at h0 h1 h2 h3 <;> linarith

/-! ## 定理 3 -/

theorem oostar_main (ho : IsOrthocentric t) (hO : ConjDefined t (O t)) {P : E3}
    (hP : P ∈ line[ℝ, O t, isogonal t (O t)]) (hd : ConjDefined t P) :
    Collinear ℝ ({O t, isogonal t P, isotomic t P} : Set E3) := by
  have hH := H_ne_vertex_of_O t ho hO
  obtain ⟨hp0, hsum, -⟩ := rel t ho hH
  have hA := A_ne t ho hH
  have hbO := bary_O t ho hH
  have hpe := p_e3 t ho hH
  have he3 : e3 t ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hpe
    have := mul_ne_zero (mul_ne_zero (mul_ne_zero (hA 0) (hA 1)) (hA 2)) (hA 3)
    exact this (by linarith)
  set o : Fin 4 → ℝ := fun j => 1 / 2 + p t / A t j with hodef
  set W : Fin 4 → ℝ := fun j => S2 t j / o j with hW
  have hσW : ∑ j, W j ≠ 0 := by have := hO.2.1; rwa [hbO] at this
  have ho1 : ∑ j, o j = 1 := by
    simp only [o, Fin.sum_univ_four]; linear_combination hsum
  -- P = (1 − r)O + rO*，重心坐标 x = (1 − r)o + (r/σ*)W
  obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP
  have hOs : isogonal t (O t) - H t = (1 / ∑ j, W j) • Lv t W := by
    rw [isogonal, hbO]; exact ofW_sub_H t W hσW
  have hOH : O t - H t = Lv t o := by
    rw [O_sub_H, Lv_comb t ho hH (g := fun _ => 0) (1 / 2) (p t) 0 (fun j => by simp [o]),
      zero_smul, add_zero]
  set x : Fin 4 → ℝ := fun j => (1 - r) * o j + (r / ∑ i, W i) * W j with hx
  have hbP : bary t (AffineMap.lineMap (O t) (isogonal t (O t)) r) = x := by
    apply bary_of_Lv
    · rw [sum_add, ho1, div_mul_cancel₀ _ hσW]; ring
    · rw [Lv_add, AffineMap.lineMap_apply_module,
        show (1 - r) • O t + r • isogonal t (O t) - H t =
          (1 - r) • (O t - H t) + r • (isogonal t (O t) - H t) by module, hOH, hOs]
      module
  obtain ⟨hx0, hσs, hσt⟩ := hd
  rw [hbP] at hx0 hσs hσt
  rw [isogonal, isotomic, hbP]
  set w₁ : Fin 4 → ℝ := fun j => 1 / x j with hw₁
  set w₂ : Fin 4 → ℝ := fun j => S2 t j / x j with hw₂
  set α : ℝ := (1 - r) / 4
  set β : ℝ := 4 * (1 - r) * p t / e3 t + r / ∑ i, W i
  -- 关键恒等式：oⱼ = α/xⱼ + β·Sⱼ²/xⱼ
  have hcomb : ∀ j, o j = α * w₁ j + β * w₂ j := by
    intro j
    have hoj : o j ≠ 0 := by have := hO.1 j; rwa [hbO] at this
    have hS : S2 t j = e3 t * (A t j + p t) / (4 * A t j ^ 2) := by
      have := S2_mul t ho hH j
      field_simp [hA j]
      linarith
    have e1 : o j * x j = (1 - r) * o j ^ 2 + (r / ∑ i, W i) * S2 t j := by
      simp only [x, W]; field_simp
    simp only [w₁, w₂]
    rw [show α * (1 / x j) + β * (S2 t j / x j) = (α + β * S2 t j) / x j by ring,
      eq_div_iff (hx0 j), e1]
    simp only [α, β, hS, o]
    field_simp [hA j]
    ring
  have hLv : Lv t o = α • Lv t w₁ + β • Lv t w₂ := by
    rw [← Lv_add]; congr 1; funext j; exact hcomb j
  have hσ : ∑ j, o j = α * ∑ j, w₁ j + β * ∑ j, w₂ j := by
    rw [← sum_add]; exact Finset.sum_congr rfl (fun j _ => hcomb j)
  have hPt := ofW_sub_H t w₁ hσt
  have hPs := ofW_sub_H t w₂ hσs
  rw [Set.pair_comm (ofWeights t w₂)]
  refine collinear_of_comb (Q := H t) (c₁ := α * ∑ j, w₁ j) (c₂ := β * ∑ j, w₂ j)
    (by rw [← hσ, ho1]; exact one_ne_zero) ?_
  rw [← hσ, ho1, one_smul, hOH, hPt, hPs, smul_smul, smul_smul, mul_assoc, mul_assoc,
    mul_one_div_cancel hσt, mul_one_div_cancel hσs, mul_one, mul_one, hLv]

/-! ## 定理 2 -/

/-- 四个点 O、H、X、Y：O − H ∈ span{s}，X − H、Y − H ∈ span{s, z}，则共面。 -/
theorem coplanar_OH (z X Y : E3) (hX : X - H t ∈ Submodule.span ℝ (Set.range ![sv t, z]))
    (hY : Y - H t ∈ Submodule.span ℝ (Set.range ![sv t, z])) :
    Coplanar ℝ ({O t, H t, X, Y} : Set E3) := by
  apply coplanar_of_span (Q := H t) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (sv t) z
  intro W hW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hW
  rcases hW with rfl | rfl | rfl | rfl
  · rw [O_sub_H]; convert mem_span2 (sv t) z (1 / 2) 0 using 1; simp [sv]
  · convert mem_span2 (sv t) z 0 0 using 1; simp
  · exact hX
  · exact hY

theorem mem_span_of {X : E3} (σ c₁ c₃ : ℝ) (z : E3) (h : X - H t = (1 / σ) • (c₁ • sv t + c₃ • z)) :
    X - H t ∈ Submodule.span ℝ (Set.range ![sv t, z]) := by
  rw [h]; convert mem_span2 (sv t) z (c₁ / σ) (c₃ / σ) using 1; module

theorem euler_main (ho : IsOrthocentric t) {P : E3} (hP : P ∈ line[ℝ, O t, H t])
    (hd : ConjDefined t P) :
    Coplanar ℝ ({O t, H t, isogonal t P, isotomic t P} : Set E3) := by
  obtain ⟨r, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP
  have hPH : AffineMap.lineMap (O t) (H t) r - H t = ((1 - r) / 2) • sv t := by
    rw [AffineMap.lineMap_apply_module,
      show (1 - r) • O t + r • H t - H t = (1 - r) • (O t - H t) by module, O_sub_H]
    module
  obtain ⟨hx0, hσs, hσt⟩ := hd
  by_cases hv : ∃ k, H t = t.points k
  · -- H 是顶点 Vₖ：Pᵗ 在欧拉线上
    obtain ⟨k, hk⟩ := hv
    obtain ⟨hvk, -, -, -⟩ := vertex_facts t ho hk
    set x : Fin 4 → ℝ := fun j => if j = k then (3 * r - 1) / 2 else (1 - r) / 2
    have hbP : bary t (AffineMap.lineMap (O t) (H t) r) = x := by
      apply bary_of_Lv
      · fin_cases k <;> simp [x, Fin.sum_univ_four] <;> ring
      · rw [hPH, Lv_vertex t hvk x ((1 - r) / 2) (fun j hj => by simp [x, hj])]
    rw [hbP] at hx0 hσs hσt
    rw [isogonal, isotomic, hbP]
    apply coplanar_OH t (ofWeights t (fun i => S2 t i / x i) - H t)
    · convert mem_span2 (sv t) (ofWeights t (fun i => S2 t i / x i) - H t) 0 1 using 1; simp
    · apply mem_span_of t (∑ j, 1 / x j) (1 / ((1 - r) / 2)) 0
      rw [ofW_sub_H t _ hσt, Lv_vertex t hvk _ (1 / ((1 - r) / 2)) (fun j hj => by simp [x, hj]),
        zero_smul, add_zero]
  · have hH : ∀ j, H t ≠ t.points j := fun j h => hv ⟨j, h⟩
    obtain ⟨hp0, hsum, -⟩ := rel t ho hH
    have hA := A_ne t ho hH
    set l : ℝ := (1 - r) / 2 with hl
    set μ : ℝ := -(1 - 2 * r) * p t with hμ
    set x : Fin 4 → ℝ := fun j => l - μ / A t j with hx
    have hbP : bary t (AffineMap.lineMap (O t) (H t) r) = x := by
      apply bary_of_Lv
      · simp only [x, l, μ, Fin.sum_univ_four]; linear_combination (1 - 2 * r) * hsum
      · rw [hPH, Lv_comb t ho hH (g := fun _ => 0) l (-μ) 0 (fun j => by simp [x]; ring),
          zero_smul, add_zero]
    rw [hbP] at hx0 hσs hσt
    rw [isogonal, isotomic, hbP]
    have hS : ∀ j, S2 t j = e3 t * (A t j + p t) / (4 * A t j ^ 2) := by
      intro j
      have := S2_mul t ho hH j
      field_simp [hA j]
      linarith
    have hlin : ∀ j, l * A t j - μ ≠ 0 := by
      intro j h0; apply hx0 j; simp only [x]; field_simp [hA j]; linarith
    by_cases hl0 : l = 0
    · -- P = H：P* 在欧拉线上
      have hμ0 : μ ≠ 0 := by
        intro h0; apply hlin 0; rw [hl0, h0]; ring
      apply coplanar_OH t (ofWeights t (fun i => 1 / x i) - H t)
      · apply mem_span_of t (∑ j, S2 t j / x j) (-e3 t / (4 * μ)) 0
        rw [ofW_sub_H t _ hσs, Lv_comb t ho hH (g := fun _ => 0) (-e3 t / (4 * μ))
          (-e3 t * p t / (4 * μ)) 0 (fun j => by
            simp only [x, hS j, hl0]; field_simp [hA j, hμ0]; ring), zero_smul, zero_smul]
      · convert mem_span2 (sv t) (ofWeights t (fun i => 1 / x i) - H t) 0 1 using 1; simp
    by_cases hμ0 : μ = 0
    · -- P = G：Pᵗ = G 在欧拉线上
      apply coplanar_OH t (ofWeights t (fun i => S2 t i / x i) - H t)
      · convert mem_span2 (sv t) (ofWeights t (fun i => S2 t i / x i) - H t) 0 1 using 1; simp
      · apply mem_span_of t (∑ j, 1 / x j) (1 / l) 0
        rw [ofW_sub_H t _ hσt, Lv_comb t ho hH (g := fun _ => 0) (1 / l) 0 0 (fun j => by
          simp only [x, hμ0, zero_div, sub_zero]; field_simp; ring), zero_smul, zero_smul]
    · -- 一般情形：z = Σ vⱼ/(λAⱼ − μ)
      set g : Fin 4 → ℝ := fun j => 1 / (l * A t j - μ) with hg
      have hlin' : ∀ j, A t j * l - μ ≠ 0 := fun j h0 => hlin j (by linarith)
      apply coplanar_OH t (Lv t g)
      · apply mem_span_of t (∑ j, S2 t j / x j) 0 (e3 t / 4 * (1 + p t * l / μ))
        rw [ofW_sub_H t _ hσs, Lv_comb t ho hH (g := g) 0 (e3 t / 4 * (-p t / μ))
          (e3 t / 4 * (1 + p t * l / μ)) (fun j => by
            simp only [x, g, hS j]; field_simp [hA j, hlin j, hlin' j, hμ0]; ring)]
      · apply mem_span_of t (∑ j, 1 / x j) (1 / l) (μ / l)
        rw [ofW_sub_H t _ hσt, Lv_comb t ho hH (g := g) (1 / l) 0 (μ / l) (fun j => by
            simp only [x, g]; field_simp [hA j, hlin j, hlin' j, hl0]; ring)]

end GeometryResearch.Orthocentric
