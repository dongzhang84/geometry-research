module

public import GeometryResearch.Orthocentric.Defs

/-!
# 垂心四面体：代数模型（论文第 2 节）

以外心 O 为原点，记 `uᵢ = Vᵢ − O`。用到的事实只有：

* `‖uᵢ‖² = R²`；
* 垂心条件：`⟪u₀ − u₁, u₂ − u₃⟫ = ⟪u₀ − u₂, u₁ − u₃⟫ = ⟪u₀ − u₃, u₁ − u₂⟫ = 0`；
* `H − O = ½(u₀ + u₁ + u₂ + u₃)`（Mathlib 的 Monge 点公式）。

由此推出 `⟪Vᵢ − H, Vⱼ − H⟫`（i ≠ j）都相等，即论文的 p。
-/

@[expose] public noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

/-! ## 纯向量部分 -/

namespace Alg

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- 四个向量的「垂心模型」假设：长度相等，三对对棱垂直。 -/
structure Hyp (u₀ u₁ u₂ u₃ : V) (R : ℝ) : Prop where
  n0 : ⟪u₀, u₀⟫ = R ^ 2
  n1 : ⟪u₁, u₁⟫ = R ^ 2
  n2 : ⟪u₂, u₂⟫ = R ^ 2
  n3 : ⟪u₃, u₃⟫ = R ^ 2
  o1 : ⟪u₀ - u₁, u₂ - u₃⟫ = 0
  o2 : ⟪u₀ - u₂, u₁ - u₃⟫ = 0
  o3 : ⟪u₀ - u₃, u₁ - u₂⟫ = 0

variable {u₀ u₁ u₂ u₃ : V} {R : ℝ}

/-- 内积展开后的标准形：把 ⟪uⱼ, uᵢ⟫（j > i）都写成 ⟪uᵢ, uⱼ⟫。 -/
theorem Hyp.expand (h : Hyp u₀ u₁ u₂ u₃ R) :
    ⟪u₀, u₂⟫ - ⟪u₀, u₃⟫ - ⟪u₁, u₂⟫ + ⟪u₁, u₃⟫ = 0 ∧
    ⟪u₀, u₁⟫ - ⟪u₀, u₃⟫ - ⟪u₁, u₂⟫ + ⟪u₂, u₃⟫ = 0 ∧
    ⟪u₀, u₁⟫ - ⟪u₀, u₂⟫ - ⟪u₁, u₃⟫ + ⟪u₂, u₃⟫ = 0 := by
  obtain ⟨-, -, -, -, o1, o2, o3⟩ := h
  simp only [inner_sub_left, inner_sub_right, real_inner_comm u₀ u₁, real_inner_comm u₀ u₂,
    real_inner_comm u₀ u₃, real_inner_comm u₁ u₂, real_inner_comm u₁ u₃, real_inner_comm u₂ u₃]
    at o1 o2 o3
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `w = ½(u₀ + u₁ + u₂ + u₃)`，即 H − O。 -/
def w (u₀ u₁ u₂ u₃ : V) : V := (1 / 2 : ℝ) • (u₀ + u₁ + u₂ + u₃)

/-- `mg a b = ½(a + b) − ¼(u₀ + u₁ + u₂ + u₃)`：棱中点减重心（以 O 为原点）。 -/
def mg (u₀ u₁ u₂ u₃ a b : V) : V := (1 / 2 : ℝ) • (a + b) - (1 / 4 : ℝ) • (u₀ + u₁ + u₂ + u₃)

/-- 展开内积、统一下标顺序、代入长度，再用三个垂心条件做线性组合。 -/
macro "ortho_alg" h:ident : tactic => `(tactic| (
  obtain ⟨e1, e2, e3⟩ := ($h).expand
  have n0 := ($h).n0; have n1 := ($h).n1; have n2 := ($h).n2; have n3 := ($h).n3
  simp only [w, mg, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm u₀ u₁, real_inner_comm u₀ u₂,
    real_inner_comm u₀ u₃, real_inner_comm u₁ u₂, real_inner_comm u₁ u₃, real_inner_comm u₂ u₃]
  linarith))

/-- 论文第 2 节：六个内积 ⟪uᵢ − w, uⱼ − w⟫（i ≠ j）都相等。 -/
theorem pair_eq (h : Hyp u₀ u₁ u₂ u₃ R) :
    ⟪u₀ - w u₀ u₁ u₂ u₃, u₂ - w u₀ u₁ u₂ u₃⟫ = ⟪u₀ - w u₀ u₁ u₂ u₃, u₁ - w u₀ u₁ u₂ u₃⟫ ∧
    ⟪u₀ - w u₀ u₁ u₂ u₃, u₃ - w u₀ u₁ u₂ u₃⟫ = ⟪u₀ - w u₀ u₁ u₂ u₃, u₁ - w u₀ u₁ u₂ u₃⟫ ∧
    ⟪u₁ - w u₀ u₁ u₂ u₃, u₂ - w u₀ u₁ u₂ u₃⟫ = ⟪u₀ - w u₀ u₁ u₂ u₃, u₁ - w u₀ u₁ u₂ u₃⟫ ∧
    ⟪u₁ - w u₀ u₁ u₂ u₃, u₃ - w u₀ u₁ u₂ u₃⟫ = ⟪u₀ - w u₀ u₁ u₂ u₃, u₁ - w u₀ u₁ u₂ u₃⟫ ∧
    ⟪u₂ - w u₀ u₁ u₂ u₃, u₃ - w u₀ u₁ u₂ u₃⟫ = ⟪u₀ - w u₀ u₁ u₂ u₃, u₁ - w u₀ u₁ u₂ u₃⟫ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ortho_alg h

/-- 论文 Lemma 2.1(d)：六个棱中点到重心的距离平方都相等。 -/
theorem mid_eq (h : Hyp u₀ u₁ u₂ u₃ R) :
    ⟪mg u₀ u₁ u₂ u₃ u₀ u₂, mg u₀ u₁ u₂ u₃ u₀ u₂⟫ = ⟪mg u₀ u₁ u₂ u₃ u₀ u₁, mg u₀ u₁ u₂ u₃ u₀ u₁⟫ ∧
    ⟪mg u₀ u₁ u₂ u₃ u₀ u₃, mg u₀ u₁ u₂ u₃ u₀ u₃⟫ = ⟪mg u₀ u₁ u₂ u₃ u₀ u₁, mg u₀ u₁ u₂ u₃ u₀ u₁⟫ ∧
    ⟪mg u₀ u₁ u₂ u₃ u₁ u₂, mg u₀ u₁ u₂ u₃ u₁ u₂⟫ = ⟪mg u₀ u₁ u₂ u₃ u₀ u₁, mg u₀ u₁ u₂ u₃ u₀ u₁⟫ ∧
    ⟪mg u₀ u₁ u₂ u₃ u₁ u₃, mg u₀ u₁ u₂ u₃ u₁ u₃⟫ = ⟪mg u₀ u₁ u₂ u₃ u₀ u₁, mg u₀ u₁ u₂ u₃ u₀ u₁⟫ ∧
    ⟪mg u₀ u₁ u₂ u₃ u₂ u₃, mg u₀ u₁ u₂ u₃ u₂ u₃⟫ =
      ⟪mg u₀ u₁ u₂ u₃ u₀ u₁, mg u₀ u₁ u₂ u₃ u₀ u₁⟫ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ortho_alg h

end Alg

/-! ## 接到四面体上 -/

variable (t : Affine.Simplex ℝ E3 3)

/-- uᵢ = Vᵢ − O。 -/
abbrev u (i : Fin 4) : E3 := t.points i - O t

/-- 重心公式：n + 1 个点的重心减去 q，等于各点减 q 的平均。 -/
theorem centroid_sub {n : ℕ} (pts : Fin (n + 1) → E3) (q : E3) :
    Finset.univ.centroid ℝ pts - q = (1 / (n + 1 : ℝ)) • ∑ i, (pts i - q) := by
  have h := Finset.univ.centroid_vsub_const (k := ℝ) (p := pts) (p₀ := q) Finset.univ_nonempty
  simp only [vsub_eq_sub] at h
  rw [h, Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (Finset.univ.sum_centroidWeights_eq_one_of_card_ne_zero ℝ (by simp))]
  simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum]
  norm_num

/-- 垂心四面体满足代数模型的假设。 -/
theorem hyp (ho : IsOrthocentric t) : Alg.Hyp (u t 0) (u t 1) (u t 2) (u t 3) (R t) := by
  have hn : ∀ i, ⟪u t i, u t i⟫ = R t ^ 2 := by
    intro i
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm]
    exact congrArg (· ^ 2) (t.dist_circumcenter_eq_circumradius i)
  obtain ⟨o1, o2, o3⟩ := ho
  refine ⟨hn 0, hn 1, hn 2, hn 3, ?_, ?_, ?_⟩ <;> simp only [u, sub_sub_sub_cancel_right] <;>
    assumption

/-- H − O = ½(u₀ + u₁ + u₂ + u₃)（Mathlib 的 Monge 点公式，n = 3）。 -/
theorem H_sub_O : H t - O t = Alg.w (u t 0) (u t 1) (u t 2) (u t 3) := by
  simp only [H, u, O, Alg.w]
  rw [Affine.Simplex.mongePoint_eq_smul_vsub_vadd_circumcenter, vadd_eq_add, vsub_eq_sub,
    add_sub_cancel_right, centroid_sub t.points t.circumcenter, Fin.sum_univ_four, smul_smul]
  norm_num

/-- G − O = ¼(u₀ + u₁ + u₂ + u₃)。 -/
theorem G_sub_O : G t - O t = (1 / 4 : ℝ) • (u t 0 + u t 1 + u t 2 + u t 3) := by
  simp only [G, u]
  rw [centroid_sub t.points (O t), Fin.sum_univ_four]
  norm_num

/-- 棱中点减重心：mᵢⱼ − G = mg(uᵢ, uⱼ)。 -/
theorem mid_sub_G (i j : Fin 4) :
    mid t i j - G t = Alg.mg (u t 0) (u t 1) (u t 2) (u t 3) (u t i) (u t j) := by
  rw [show mid t i j - G t = (mid t i j - O t) - (G t - O t) by abel, G_sub_O]
  simp only [mid, Alg.mg, midpoint_eq_smul_add, u, invOf_eq_inv]
  module

/-- Vᵢ − H = uᵢ − w。 -/
theorem pt_sub_H (i : Fin 4) :
    t.points i - H t = u t i - Alg.w (u t 0) (u t 1) (u t 2) (u t 3) := by
  rw [← H_sub_O]; simp [u]

set_option linter.flexible false in
/-- 论文第 2 节：⟪Vᵢ − H, Vⱼ − H⟫（i ≠ j）都等于 p。 -/
theorem inner_pt_H (ho : IsOrthocentric t) {i j : Fin 4} (hij : i ≠ j) :
    ⟪t.points i - H t, t.points j - H t⟫ = p t := by
  obtain ⟨h02, h03, h12, h13, h23⟩ := Alg.pair_eq (hyp t ho)
  simp only [p, pt_sub_H]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
    first
    | rfl
    | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
    | (rw [real_inner_comm] <;>
        first | rfl | exact h02 | exact h03 | exact h12 | exact h13 | exact h23)

/-- 每个下标都有另一个不同的下标。 -/
theorem exists_ne (i : Fin 4) : ∃ j, j ≠ i := ⟨i + 1, by fin_cases i <;> decide⟩

/-- Vᵢ − H 与面 i（Vᵢ 的对面）的方向垂直。 -/
theorem orth_face (ho : IsOrthocentric t) (i : Fin 4) :
    vectorSpan ℝ (t.points '' {i}ᶜ) ≤ (ℝ ∙ (t.points i - H t))ᗮ := by
  obtain ⟨j, hj⟩ := exists_ne i
  rw [vectorSpan_eq_span_vsub_set_right ℝ (⟨j, hj, rfl⟩ : t.points j ∈ t.points '' {i}ᶜ),
    Submodule.span_le]
  rintro x ⟨y, ⟨k, hk, rfl⟩, rfl⟩
  rw [Set.mem_compl_singleton_iff] at hk
  rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp only [vsub_eq_sub]
  rw [show t.points k - t.points j = (t.points k - H t) - (t.points j - H t) by abel,
    inner_sub_right, inner_pt_H t ho (Ne.symm hk), inner_pt_H t ho (Ne.symm hj), sub_self]

/-- 面 i 所在平面上的点 X 满足 ⟪Vᵢ − H, X − Vⱼ⟫ = 0（j ≠ i）。 -/
theorem inner_face (ho : IsOrthocentric t) (i : Fin 4) {j : Fin 4} (hj : j ≠ i) {X : E3}
    (hX : X ∈ affineSpan ℝ (t.points '' {i}ᶜ)) : ⟪t.points i - H t, X - t.points j⟫ = 0 := by
  have hmem : X -ᵥ t.points j ∈ vectorSpan ℝ (t.points '' {i}ᶜ) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hX (mem_affineSpan ℝ ⟨j, hj, rfl⟩)
  have := orth_face t ho i hmem
  rwa [Submodule.mem_orthogonal_singleton_iff_inner_right, vsub_eq_sub] at this

/-! ## 核心关系（论文第 2 节）：Σ vᵢ/aᵢ = 0，p·Σ 1/aᵢ = −1 -/

/-- vᵢ = Vᵢ − H（以 H 为原点）。 -/
abbrev v (i : Fin 4) : E3 := t.points i - H t

/-- Aᵢ = ‖vᵢ‖² − p（就是论文的 aᵢ，见 `a_eq`）。 -/
def A (i : Fin 4) : ℝ := ‖v t i‖ ^ 2 - p t

/-- 与从 Vⱼ 出发的三条棱都垂直的向量是零向量。 -/
theorem eq_zero_of_inner_edges (j : Fin 4) {z : E3}
    (h : ∀ k, ⟪z, t.points k - t.points j⟫ = 0) : z = 0 := by
  have htop : vectorSpan ℝ (Set.range t.points) = ⊤ := by
    rw [← direction_affineSpan, show Set.range t.points = Set.range (basis t) from rfl,
      (basis t).tot]
    exact AffineSubspace.direction_top ℝ E3 E3
  have hle : vectorSpan ℝ (Set.range t.points) ≤ (ℝ ∙ z)ᗮ := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (Set.mem_range_self j), Submodule.span_le]
    rintro x ⟨y, ⟨k, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa only [vsub_eq_sub] using h k
  rw [htop] at hle
  have hz := hle (Submodule.mem_top (x := z))
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hz
  exact inner_self_eq_zero.mp hz

theorem inner_v_self (i : Fin 4) : ⟪v t i, v t i⟫ = p t + A t i := by
  rw [real_inner_self_eq_norm_sq, A]; ring

/-- H 不是顶点时 Aᵢ ≠ 0。 -/
theorem A_ne (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) (j : Fin 4) : A t j ≠ 0 := by
  intro h0
  apply hH j
  have hz : v t j = 0 := by
    apply eq_zero_of_inner_edges t j
    intro k
    by_cases hk : k = j
    · subst hk; simp
    · rw [show t.points k - t.points j = v t k - v t j by simp only [v, sub_sub_sub_cancel_right],
        inner_sub_right, inner_pt_H t ho (Ne.symm hk), real_inner_self_eq_norm_sq]
      simp only [A] at h0; linarith
  exact (sub_eq_zero.mp hz).symm

/-- 论文第 2 节的核心关系：H 不是顶点时 p ≠ 0，p·Σ 1/Aᵢ = −1，Σ vᵢ/Aᵢ = 0。
证明：三维空间里四个向量 vᵢ 线性相关，Σ gᵢvᵢ = 0；与 vₖ 做内积得 p·Σgᵢ + Aₖgₖ = 0。 -/
theorem rel (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) :
    p t ≠ 0 ∧ p t * (1 / A t 0 + 1 / A t 1 + 1 / A t 2 + 1 / A t 3) = -1 ∧
    (1 / A t 0) • v t 0 + (1 / A t 1) • v t 1 + (1 / A t 2) • v t 2 + (1 / A t 3) • v t 3 = 0 := by
  have hA := A_ne t ho hH
  have hnot : ¬ LinearIndependent ℝ (v t) := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp [finrank_euclideanSpace] at this
  obtain ⟨g, hg, k0, hk0⟩ := Fintype.not_linearIndependent_iff.mp hnot
  rw [Fin.sum_univ_four] at hg
  have hvv := inner_v_self t
  have hp : ∀ {j k : Fin 4}, j ≠ k → ⟪v t j, v t k⟫ = p t := fun h => inner_pt_H t ho h
  have d0 : ⟪v t 0, v t 0⟫ = p t + A t 0 := hvv 0
  have h01 : ⟪v t 0, v t 1⟫ = p t := hp (by decide)
  have h02 : ⟪v t 0, v t 2⟫ = p t := hp (by decide)
  have h03 : ⟪v t 0, v t 3⟫ = p t := hp (by decide)
  have h10 : ⟪v t 1, v t 0⟫ = p t := hp (by decide)
  have d1 : ⟪v t 1, v t 1⟫ = p t + A t 1 := hvv 1
  have h12 : ⟪v t 1, v t 2⟫ = p t := hp (by decide)
  have h13 : ⟪v t 1, v t 3⟫ = p t := hp (by decide)
  have h20 : ⟪v t 2, v t 0⟫ = p t := hp (by decide)
  have h21 : ⟪v t 2, v t 1⟫ = p t := hp (by decide)
  have d2 : ⟪v t 2, v t 2⟫ = p t + A t 2 := hvv 2
  have h23 : ⟪v t 2, v t 3⟫ = p t := hp (by decide)
  have h30 : ⟪v t 3, v t 0⟫ = p t := hp (by decide)
  have h31 : ⟪v t 3, v t 1⟫ = p t := hp (by decide)
  have h32 : ⟪v t 3, v t 2⟫ = p t := hp (by decide)
  have d3 : ⟪v t 3, v t 3⟫ = p t + A t 3 := hvv 3
  have e0 : p t * (g 0 + g 1 + g 2 + g 3) + A t 0 * g 0 = 0 := by
    have := congrArg (fun z => ⟪z, v t 0⟫) hg
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, d0, h01, h02, h03, h10, d1,
        h12, h13, h20, h21, d2, h23, h30, h31, h32, d3] at this
    linarith
  have e1 : p t * (g 0 + g 1 + g 2 + g 3) + A t 1 * g 1 = 0 := by
    have := congrArg (fun z => ⟪z, v t 1⟫) hg
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, d0, h01, h02, h03, h10, d1,
        h12, h13, h20, h21, d2, h23, h30, h31, h32, d3] at this
    linarith
  have e2 : p t * (g 0 + g 1 + g 2 + g 3) + A t 2 * g 2 = 0 := by
    have := congrArg (fun z => ⟪z, v t 2⟫) hg
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, d0, h01, h02, h03, h10, d1,
        h12, h13, h20, h21, d2, h23, h30, h31, h32, d3] at this
    linarith
  have e3 : p t * (g 0 + g 1 + g 2 + g 3) + A t 3 * g 3 = 0 := by
    have := congrArg (fun z => ⟪z, v t 3⟫) hg
    simp only [inner_add_left, real_inner_smul_left, inner_zero_left, d0, h01, h02, h03, h10, d1,
        h12, h13, h20, h21, d2, h23, h30, h31, h32, d3] at this
    linarith
  have e : ∀ k, p t * (g 0 + g 1 + g 2 + g 3) + A t k * g k = 0 := by
    intro k; fin_cases k
    exacts [e0, e1, e2, e3]
  set Λ := g 0 + g 1 + g 2 + g 3 with hΛdef
  have hgk : ∀ k, p t * Λ = 0 → g k = 0 := by
    intro k h
    have := e k
    rw [h, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_left (hA k)
  have hpΛ : p t * Λ ≠ 0 := fun h => hk0 (hgk k0 h)
  have hp0 : p t ≠ 0 := left_ne_zero_of_mul hpΛ
  have hΛ : Λ ≠ 0 := right_ne_zero_of_mul hpΛ
  have hg' : ∀ k, 1 / A t k = (-1 / (p t * Λ)) * g k := by
    intro k
    have := e k
    field_simp [hA k]
    linarith
  refine ⟨hp0, ?_, ?_⟩
  · rw [hg', hg', hg', hg']
    field_simp
    simp only [hΛdef]; ring
  · rw [hg', hg', hg', hg']
    simp only [← smul_smul, ← smul_add, hg, smul_zero]

end GeometryResearch.Orthocentric
