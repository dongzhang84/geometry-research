module

public import GeometryResearch.Orthocentric.Conj

/-!
# 定理 5（Fermat 点的共线）的证明

第一步（分析）：F 使 Σ|FVⱼ| 最小且不是顶点，则 Σ (Vⱼ − F)/dⱼ = 0。
沿方向 g = Σ (F − Vⱼ)/dⱼ 的一元函数在 0 处取极小，导数 ⟪g, g⟫ = 0。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

variable (t : Affine.Simplex ℝ E3 3)

/-- ‖F + s•g − V‖ 在 s = 0 处的导数是 ⟪F − V, g⟫/‖F − V‖（F ≠ V）。 -/
theorem hasDerivAt_dist_line {F V g : E3} (h : F ≠ V) :
    HasDerivAt (fun s : ℝ => ‖F + s • g - V‖) (⟪F - V, g⟫ / ‖F - V‖) 0 := by
  have hf : HasDerivAt (fun s : ℝ => F + s • g - V) g 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const g).const_add F |>.sub_const V
    simpa using this
  have hsq := hf.norm_sq
  have hne : ‖F + (0 : ℝ) • g - V‖ ^ 2 ≠ 0 := by
    simpa [sub_eq_zero] using h
  have hs := hsq.sqrt hne
  have hfun : (fun s : ℝ => √(‖F + s • g - V‖ ^ 2)) = fun s : ℝ => ‖F + s • g - V‖ := by
    funext s; exact Real.sqrt_sq (norm_nonneg _)
  rw [hfun] at hs
  convert hs using 1
  simp only [zero_smul, add_zero]
  rw [Real.sqrt_sq (norm_nonneg _)]
  have : ‖F - V‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  field_simp

/-- Fermat 点的一阶条件：Σ (Vⱼ − F)/dⱼ = 0。 -/
theorem fermat_grad {F : E3} (hF : IsFermatPoint t F) (hFv : ∀ j, F ≠ t.points j) :
    ∑ j, (1 / dist F (t.points j)) • (t.points j - F) = 0 := by
  set g : E3 := ∑ j, (1 / dist F (t.points j)) • (F - t.points j) with hg
  have hmin : IsLocalMin (fun s : ℝ => ∑ j, ‖F + s • g - t.points j‖) 0 := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    have := hF (F + s • g)
    simp only [dist_eq_norm] at this
    simpa using this
  have hder : HasDerivAt (fun s : ℝ => ∑ j, ‖F + s • g - t.points j‖)
      (∑ j, ⟪F - t.points j, g⟫ / ‖F - t.points j‖) 0 :=
    HasDerivAt.fun_sum (fun j _ => hasDerivAt_dist_line (g := g) (hFv j))
  have h0 := hmin.hasDerivAt_eq_zero hder
  have hgg : ⟪g, g⟫ = 0 := by
    rw [← h0]
    conv_lhs => rw [hg]
    rw [sum_inner]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [real_inner_smul_left, dist_eq_norm]
    ring
  have hg0 : g = 0 := inner_self_eq_zero.mp hgg
  rw [show (∑ j, (1 / dist F (t.points j)) • (t.points j - F)) = -g by
    rw [hg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← smul_neg, neg_sub], hg0, neg_zero]

/-! ## 第二步：几何化归为标量命题 -/

/-- Gram 公式：⟪L(α), L(β)⟫ = p·(Σα)(Σβ) + Σ Aⱼαⱼβⱼ。 -/
theorem gram (ho : IsOrthocentric t) (α β : Fin 4 → ℝ) :
    ⟪Lv t α, Lv t β⟫ = p t * (∑ j, α j) * (∑ j, β j) + ∑ j, A t j * α j * β j := by
  have hp : ∀ {j k : Fin 4}, j ≠ k → ⟪v t j, v t k⟫ = p t := fun h => inner_pt_H t ho h
  rw [Lv_four, Lv_four]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_v_self, hp (show (0 : Fin 4) ≠ 1 by decide), hp (show (0 : Fin 4) ≠ 2 by decide),
    hp (show (0 : Fin 4) ≠ 3 by decide), hp (show (1 : Fin 4) ≠ 0 by decide),
    hp (show (1 : Fin 4) ≠ 2 by decide), hp (show (1 : Fin 4) ≠ 3 by decide),
    hp (show (2 : Fin 4) ≠ 0 by decide), hp (show (2 : Fin 4) ≠ 1 by decide),
    hp (show (2 : Fin 4) ≠ 3 by decide), hp (show (3 : Fin 4) ≠ 0 by decide),
    hp (show (3 : Fin 4) ≠ 1 by decide), hp (show (3 : Fin 4) ≠ 2 by decide),
    Fin.sum_univ_four]
  ring

theorem Lv_sub (α β : Fin 4 → ℝ) : Lv t (fun j => α j - β j) = Lv t α - Lv t β := by
  rw [Lv_four, Lv_four, Lv_four]; module

/-- 分量成比例：∀ i j, αᵢβⱼ = αⱼβᵢ，且 L(β) ≠ 0，则 L(α) = κ·L(β)。 -/
theorem Lv_prop {α β : Fin 4 → ℝ} (h : ∀ i j, α i * β j = α j * β i) (hβ : Lv t β ≠ 0) :
    ∃ κ : ℝ, Lv t α = κ • Lv t β := by
  have : ∃ k, β k ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hβ
    rw [Lv_four, hc 0, hc 1, hc 2, hc 3]; simp
  obtain ⟨k, hk⟩ := this
  refine ⟨α k / β k, ?_⟩
  have e : ∀ j, α j = α k / β k * β j := by
    intro j; field_simp; linarith [h j k]
  rw [Lv_four, Lv_four, e 0, e 1, e 2, e 3]
  module

/-- 标量核心（待证）：在 Fermat 点的关系下，αᵢβⱼ = αⱼβᵢ。 -/
theorem fermat_scalar (a d : Fin 4 → ℝ) (p c C : ℝ) (hd : ∀ j, 0 < d j) (ha : ∀ j, a j ≠ 0)
    (hp : p ≠ 0) (hR : ∀ j, d j ^ 2 = a j * (1 - 2 * (c / d j)) + C)
    (hc : c * ∑ j, 1 / d j = 1) (hC : C = ∑ j, a j * (c / d j) ^ 2)
    (hpr : p * ∑ j, 1 / a j = -1) (hω : ∑ j, a j / d j ^ 2 ≠ 0) (i j : Fin 4) :
    ((a i / d i ^ 2) / (∑ k, a k / d k ^ 2) - c / d i) * (1 / 2 + p / a j - c / d j) =
      ((a j / d j ^ 2) / (∑ k, a k / d k ^ 2) - c / d j) * (1 / 2 + p / a i - c / d i) := by
  sorry

/-- 论文 (2.1)：aᵢ = Aᵢ = ‖Vᵢ − H‖² − p（与 `Statement.lean` 的 `a_eq` 相同）。 -/
theorem a_eq_A (ho : IsOrthocentric t) (i : Fin 4) : a t i = A t i := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hf : Hfoot t i ∈ affineSpan ℝ (t.points '' {i}ᶜ) :=
    t.altitudeFoot_mem_affineSpan_image_compl i
  have h0 := inner_face t ho i hj hf
  have h1 := inner_pt_H t ho (Ne.symm hj)
  rw [a, A, show H t - t.points i = -(t.points i - H t) by abel,
    show Hfoot t i - t.points i = (Hfoot t i - t.points j) + (t.points j - H t)
      - (t.points i - H t) by abel,
    inner_neg_left, inner_sub_right, inner_add_right, h0, h1, real_inner_self_eq_norm_sq]
  ring

theorem Lv_single (j : Fin 4) : Lv t (fun k => if k = j then 1 else 0) = v t j := by
  rw [Lv_four]; fin_cases j <;> simp

theorem Lv_smul (c : ℝ) (g : Fin 4 → ℝ) : Lv t (fun j => c * g j) = c • Lv t g := by
  rw [Lv_four, Lv_four]; module

/-- 定理 5 的证明（标量核心见 `fermat_scalar`）。 -/
theorem fermat_main (ho : IsOrthocentric t) {F : E3} (hF : IsFermatPoint t F)
    (hFv : ∀ j, F ≠ t.points j) (hH : ∀ j, H t ≠ t.points j) (hFO : F ≠ O t)
    (hW : ∑ j, a t j / dist F (t.points j) ^ 2 ≠ 0) :
    Collinear ℝ ({F, O t, ofWeights t (fun j => a t j / dist F (t.points j) ^ 2)} : Set E3) := by
  obtain ⟨hp0, hsum, -⟩ := rel t ho hH
  have hA := A_ne t ho hH
  have haA : ∀ j, a t j = A t j := a_eq_A t ho
  simp only [haA] at hW ⊢
  set d : Fin 4 → ℝ := fun j => dist F (t.points j) with hd
  have hd0 : ∀ j, 0 < d j := fun j => dist_pos.mpr (hFv j)
  have hσd : 0 < ∑ j, 1 / d j :=
    Finset.sum_pos (fun j _ => one_div_pos.mpr (hd0 j)) Finset.univ_nonempty
  set c : ℝ := 1 / ∑ j, 1 / d j with hcdef
  have hc : c * ∑ j, 1 / d j = 1 := by rw [hcdef]; field_simp
  set f : Fin 4 → ℝ := fun j => c / d j with hf
  have hf1 : ∑ j, f j = 1 := by
    rw [← hc, Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by simp [f]; ring)
  -- F − H = L(f)
  have hFH : F - H t = Lv t f := by
    have hg := fermat_grad t hF hFv
    have e : ∑ j, (1 / dist F (t.points j)) • (t.points j - F) =
        Lv t (fun j => 1 / d j) - (∑ j, 1 / d j) • (F - H t) := by
      rw [Lv_four, Fin.sum_univ_four, Fin.sum_univ_four]; simp only [d, v]; module
    rw [e, sub_eq_zero] at hg
    rw [show f = fun j => c * (1 / d j) by funext j; simp [f]; ring, Lv_smul, hg, smul_smul,
      hcdef, one_div_mul_cancel hσd.ne', one_smul]
  set C : ℝ := ∑ j, A t j * f j ^ 2 with hCdef
  -- dⱼ² = Aⱼ(1 − 2fⱼ) + C
  have hR : ∀ j, d j ^ 2 = A t j * (1 - 2 * f j) + C := by
    intro j
    have e : t.points j - F = Lv t (fun k => (if k = j then 1 else 0) - f k) := by
      rw [Lv_sub, Lv_single, ← hFH]; simp only [v]; abel
    change dist F (t.points j) ^ 2 = _
    rw [dist_comm, dist_eq_norm, e, ← real_inner_self_eq_norm_sq, gram t ho,
      Finset.sum_sub_distrib, hf1]
    simp only [Fin.sum_univ_four, hCdef]
    fin_cases j <;> simp <;> ring
  -- O − F 与 W − F 的权重
  set o : Fin 4 → ℝ := fun j => 1 / 2 + p t / A t j with ho_def
  have hOH : O t - H t = Lv t o := by
    rw [O_sub_H, Lv_comb t ho hH (g := fun _ => 0) (1 / 2) (p t) 0 (fun j => by simp [o]),
      zero_smul, add_zero]
  set ω : Fin 4 → ℝ := fun j => A t j / d j ^ 2 with hω
  have hWH := ofW_sub_H t ω hW
  set α : Fin 4 → ℝ := fun j => ω j / (∑ k, ω k) - f j
  set β : Fin 4 → ℝ := fun j => o j - f j
  have hWF : ofWeights t ω - F = Lv t α := by
    rw [show ofWeights t ω - F = (ofWeights t ω - H t) - (F - H t) by abel, hWH, hFH,
      show α = fun j => (fun k => (1 / ∑ k, ω k) * ω k) j - f j by funext j; simp [α]; ring,
      Lv_sub, Lv_smul]
  have hOF : O t - F = Lv t β := by
    rw [show O t - F = (O t - H t) - (F - H t) by abel, hOH, hFH, Lv_sub]
  have hβ : Lv t β ≠ 0 := by rw [← hOF]; exact sub_ne_zero.mpr hFO.symm
  have hcore : ∀ i j, α i * β j = α j * β i := by
    intro i j
    have := fermat_scalar (fun j => A t j) d (p t) c C hd0 hA hp0
      (fun j => by rw [hR j]) hc (by simp [hCdef, f]) (by
        have := hsum; simp only [Fin.sum_univ_four]; linear_combination this) hW i j
    simpa [α, β, o, ω, f] using this
  obtain ⟨κ, hκ⟩ := Lv_prop t hcore hβ
  rw [collinear_iff_of_mem (Set.mem_insert F _)]
  refine ⟨O t - F, fun X hX => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · refine ⟨κ, ?_⟩
    rw [vadd_eq_add, hOF, ← hκ, ← hWF]; abel

end GeometryResearch.Orthocentric
