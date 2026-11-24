module

public import Mathlib

/-!
# 七点球定理：代数核心

以外心 O 为原点。记 `v₀ = V₀ − O`、`g = G − O`、`p = O′ − O`，外接球半径 `R`。
所用的几何事实只有两条：

* `‖v₀‖² = R²`（V₀ 在外接球上）；
* `⟪4g − v₀, p⟫ = 3‖p‖²`。这里 `4g − v₀ = v₁ + v₂ + v₃`，等式即论文 (2.1) 式 `s · O′ = 3|O′|²`。

点 X（相对 O 的向量）在 Möbius 球 Σ(α, c) 上，指
`α‖X‖² − 2⟪c, X⟫ + 4αR² = 0`。论文的三个线性方程（R = 1 时即论文 (G)、(O′)、(V₀) 三式）：

* `eqG`：`2⟪c, g⟫ = α(4‖g‖² + R²)`；
* `eqP`：`2⟪c, p⟫ = α(4‖p‖² + R²)`；
* `eqV`：`2⟪c, v₀⟫ = α(8⟪g, v₀⟫ − 3R²)`。

本文件证明：三个方程成立时，七个点都在 Σ(α, c) 上；并且三个方程总有不全为零的解。
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

namespace GeometryResearch.SevenPoint.Algebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- 点 X（相对 O 的向量）在 Möbius 球 Σ(α, c) 上。 -/
def OnSphere (R α : ℝ) (c X : V) : Prop :=
  α * ⟪X, X⟫ - 2 * ⟪c, X⟫ + 4 * α * R ^ 2 = 0

variable (R α : ℝ) (v₀ g p c : V)

/-- 论文的三个线性方程。 -/
structure Eqs : Prop where
  eqG : 2 * ⟪c, g⟫ = α * (4 * ⟪g, g⟫ + R ^ 2)
  eqP : 2 * ⟪c, p⟫ = α * (4 * ⟪p, p⟫ + R ^ 2)
  eqV : 2 * ⟪c, v₀⟫ = α * (8 * ⟪g, v₀⟫ - 3 * R ^ 2)

variable {R α v₀ g p c}

/-- 点 D = 4G − 3O，即向量 4g。 -/
theorem onSphere_D (h : Eqs R α v₀ g p c) : OnSphere R α c ((4 : ℝ) • g) := by
  unfold OnSphere
  simp only [real_inner_smul_left, real_inner_smul_right]
  linear_combination (-4 : ℝ) * h.eqG

/-- 点 F = 4O′ − 3O，即向量 4p。 -/
theorem onSphere_F (h : Eqs R α v₀ g p c) : OnSphere R α c ((4 : ℝ) • p) := by
  unfold OnSphere
  simp only [real_inner_smul_left, real_inner_smul_right]
  linear_combination (-4 : ℝ) * h.eqP

/-- 点 E = inv(G)，即向量 (R²/‖g‖²) g。 -/
theorem onSphere_E (h : Eqs R α v₀ g p c) (hg : g ≠ 0) :
    OnSphere R α c ((R ^ 2 / ⟪g, g⟫) • g) := by
  unfold OnSphere
  have hgg : ⟪g, g⟫ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  simp only [real_inner_smul_left, real_inner_smul_right]
  field_simp
  linear_combination (-R ^ 2) * h.eqG

/-- 点 B = inv(O′)，即向量 (R²/‖p‖²) p。 -/
theorem onSphere_B (h : Eqs R α v₀ g p c) (hp : p ≠ 0) :
    OnSphere R α c ((R ^ 2 / ⟪p, p⟫) • p) := by
  unfold OnSphere
  have hpp : ⟪p, p⟫ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  simp only [real_inner_smul_left, real_inner_smul_right]
  field_simp
  linear_combination (-R ^ 2) * h.eqP

/-- 点 C = 4G − 3V₀，即向量 4g − 3v₀。 -/
theorem onSphere_C (h : Eqs R α v₀ g p c) (hv : ⟪v₀, v₀⟫ = R ^ 2) :
    OnSphere R α c ((4 : ℝ) • g - (3 : ℝ) • v₀) := by
  unfold OnSphere
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm v₀ g]
  linear_combination (-4 : ℝ) * h.eqG + 3 * h.eqV + 9 * α * hv
    + 24 * α * real_inner_comm v₀ g

/-- 点 H′ = 面 V₁V₂V₃ 的垂心，即向量 (v₁ + v₂ + v₃) − 2p = 4g − v₀ − 2p。 -/
theorem onSphere_H (h : Eqs R α v₀ g p c) (hv : ⟪v₀, v₀⟫ = R ^ 2)
    (hs : ⟪(4 : ℝ) • g - v₀, p⟫ = 3 * ⟪p, p⟫) :
    OnSphere R α c ((4 : ℝ) • g - v₀ - (2 : ℝ) • p) := by
  unfold OnSphere
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    at hs ⊢
  rw [real_inner_comm v₀ g, real_inner_comm p g, real_inner_comm p v₀]
  linear_combination (-4 : ℝ) * h.eqG + h.eqV + 2 * h.eqP + α * hv - 4 * α * hs
    + 8 * α * real_inner_comm v₀ g + 16 * α * real_inner_comm p g - 4 * α * real_inner_comm p v₀

/-- 点 A = 直线 V₀G 与外接球的第二个交点，即向量 v₀ + t(g − v₀)，
`t = −2⟪g − v₀, v₀⟫ / ‖g − v₀‖²`（Mathlib `Sphere.secondInter` 的展开）。 -/
theorem onSphere_A (h : Eqs R α v₀ g p c) (hv : ⟪v₀, v₀⟫ = R ^ 2) :
    OnSphere R α c
      ((-2 * ⟪g - v₀, v₀⟫ / ⟪g - v₀, g - v₀⟫) • (g - v₀) + v₀) := by
  unfold OnSphere
  by_cases hw : g - v₀ = 0
  · -- g = v₀：A = V₀ 本身
    have hgv : g = v₀ := sub_eq_zero.mp hw
    subst hgv
    simp
    linear_combination -h.eqV - 7 * α * hv - α * real_inner_self_eq_norm_sq g
  · have hww : ⟪g - v₀, g - v₀⟫ ≠ 0 := by
      rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
    obtain ⟨eG, eP, eV⟩ := h
    set w := g - v₀ with hwdef
    have hgw : g = w + v₀ := by rw [hwdef]; abel
    -- ⟪g, v₀⟫ = ⟪w, v₀⟫ + ⟪v₀, v₀⟫
    have hgv : ⟪g, v₀⟫ = ⟪w, v₀⟫ + ⟪v₀, v₀⟫ := by rw [hgw, inner_add_left]
    -- 2⟪c, w⟫ = 4α‖w‖²
    have hcw : 2 * ⟪c, w⟫ = 4 * α * ⟪w, w⟫ := by
      have e1 : ⟪c, w⟫ = ⟪c, g⟫ - ⟪c, v₀⟫ := by rw [hwdef, inner_sub_right]
      have e2 : ⟪w, w⟫ = ⟪g, g⟫ - 2 * ⟪g, v₀⟫ + ⟪v₀, v₀⟫ := by
        rw [hwdef]
        simp only [inner_sub_left, inner_sub_right]
        rw [real_inner_comm g v₀]; ring
      rw [e1, e2]
      linear_combination eG - eV - 4 * α * hv
    set t := -2 * ⟪w, v₀⟫ / ⟪w, w⟫ with htdef
    have ht : t * ⟪w, w⟫ = -2 * ⟪w, v₀⟫ := by
      rw [htdef]; field_simp
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    linear_combination (α * t - 4 * α) * ht - t * hcw - eV - 8 * α * hgv - 7 * α * hv
      + α * t * real_inner_comm w v₀

/-- 三个方程写成线性映射 ℝ × V → ℝ³，(α, c) ↦ 三个方程左边减右边。 -/
def eqsMap (R : ℝ) (v₀ g p : V) : (ℝ × V) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![2 * ⟪x.2, g⟫ - x.1 * (4 * ⟪g, g⟫ + R ^ 2),
              2 * ⟪x.2, p⟫ - x.1 * (4 * ⟪p, p⟫ + R ^ 2),
              2 * ⟪x.2, v₀⟫ - x.1 * (8 * ⟪g, v₀⟫ - 3 * R ^ 2)]
  map_add' x y := by
    ext i; fin_cases i <;> simp [inner_add_left] <;> ring
  map_smul' r x := by
    ext i; fin_cases i <;> simp [real_inner_smul_left] <;> ring

/-- 三个方程（四个未知数）总有不全为零的解（V 是三维空间时）。 -/
theorem exists_eqs [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 3) (R : ℝ) (v₀ g p : V) :
    ∃ (α : ℝ) (c : V), (α ≠ 0 ∨ c ≠ 0) ∧ Eqs R α v₀ g p c := by
  have hlt : Module.finrank ℝ (Fin 3 → ℝ) < Module.finrank ℝ (ℝ × V) := by
    rw [Module.finrank_prod, hV, Module.finrank_fin_fun, Module.finrank_self]; norm_num
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt hlt
    (f := eqsMap R v₀ g p))
  rw [LinearMap.mem_ker] at hx
  refine ⟨x.1, x.2, ?_, ?_⟩
  · by_contra hcon
    simp only [not_or, not_not] at hcon
    exact hx0 (Prod.ext hcon.1 hcon.2)
  · have h0 := congrFun hx 0
    have h1 := congrFun hx 1
    have h2 := congrFun hx 2
    simp [eqsMap] at h0 h1 h2
    refine ⟨?_, ?_, ?_⟩ <;> (try simp only [real_inner_self_eq_norm_sq]) <;> linarith

/-! ## 反方向：E、B、C 在球上 ⇒ 三个方程 -/

theorem eqG_of_onSphere_E (hg : g ≠ 0) (hR : R ≠ 0)
    (h : OnSphere R α c ((R ^ 2 / ⟪g, g⟫) • g)) :
    2 * ⟪c, g⟫ = α * (4 * ⟪g, g⟫ + R ^ 2) := by
  have hgg : ⟪g, g⟫ ≠ 0 := by
    rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero, norm_ne_zero_iff]
  unfold OnSphere at h
  have key : α * ⟪(R ^ 2 / ⟪g, g⟫) • g, (R ^ 2 / ⟪g, g⟫) • g⟫
      - 2 * ⟪c, (R ^ 2 / ⟪g, g⟫) • g⟫ + 4 * α * R ^ 2
      = (R ^ 2 / ⟪g, g⟫) * (α * R ^ 2 - 2 * ⟪c, g⟫ + 4 * α * ⟪g, g⟫) := by
    simp only [real_inner_smul_left, real_inner_smul_right]
    field_simp
  rw [key] at h
  have hne : R ^ 2 / ⟪g, g⟫ ≠ 0 := div_ne_zero (pow_ne_zero 2 hR) hgg
  have := (mul_eq_zero.mp h).resolve_left hne
  linarith

theorem eqP_of_onSphere_B (hp : p ≠ 0) (hR : R ≠ 0)
    (h : OnSphere R α c ((R ^ 2 / ⟪p, p⟫) • p)) :
    2 * ⟪c, p⟫ = α * (4 * ⟪p, p⟫ + R ^ 2) :=
  eqG_of_onSphere_E (g := p) hp hR h

theorem eqV_of_onSphere_C (hG : 2 * ⟪c, g⟫ = α * (4 * ⟪g, g⟫ + R ^ 2))
    (hv : ⟪v₀, v₀⟫ = R ^ 2) (h : OnSphere R α c ((4 : ℝ) • g - (3 : ℝ) • v₀)) :
    2 * ⟪c, v₀⟫ = α * (8 * ⟪g, v₀⟫ - 3 * R ^ 2) := by
  unfold OnSphere at h
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right] at h
  linear_combination (1 / 3 : ℝ) * h + (4 / 3 : ℝ) * hG + 4 * α * real_inner_comm g v₀
    - 3 * α * hv

/-- 三个方程对 α 是齐次的：α ≠ 0 时可以把 α 归一化为 1。 -/
theorem Eqs.normalize (h : Eqs R α v₀ g p c) (hα : α ≠ 0) : Eqs R 1 v₀ g p (α⁻¹ • c) := by
  obtain ⟨eG, eP, eV⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> simp only [real_inner_smul_left, one_mul] <;> field_simp
  · linear_combination eG
  · linear_combination eP
  · linear_combination eV

end GeometryResearch.SevenPoint.Algebra
