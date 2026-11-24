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
set_option linter.flexible false

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

/-- 展开内积、统一下标顺序、代入长度，再用三个垂心条件做线性组合。 -/
macro "ortho_alg" h:ident : tactic => `(tactic| (
  obtain ⟨e1, e2, e3⟩ := ($h).expand
  have n0 := ($h).n0; have n1 := ($h).n1; have n2 := ($h).n2; have n3 := ($h).n3
  simp only [w, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
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

/-- Vᵢ − H = uᵢ − w。 -/
theorem pt_sub_H (i : Fin 4) :
    t.points i - H t = u t i - Alg.w (u t 0) (u t 1) (u t 2) (u t 3) := by
  rw [← H_sub_O]; simp [u]

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

end GeometryResearch.Orthocentric
