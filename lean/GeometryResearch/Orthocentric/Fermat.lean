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

/-! ## 第三步：标量核心 -/

/-- 若某个 fₓ = 1/2，则 bₓ = 0（于是在 aⱼ ≠ 0 时 fⱼ ≠ 1/2）。 -/
theorem half_aux {x y z w bx by' bz bw c C : ℝ} (hx : x = 1 / 2) (hy : 0 < y) (hz : 0 < z)
    (hw : 0 < w) (hs : x + y + z + w = 1)
    (Rx : c ^ 2 = x ^ 2 * (bx * (1 - 2 * x) + C)) (Ry : c ^ 2 = y ^ 2 * (by' * (1 - 2 * y) + C))
    (Rz : c ^ 2 = z ^ 2 * (bz * (1 - 2 * z) + C)) (Rw : c ^ 2 = w ^ 2 * (bw * (1 - 2 * w) + C))
    (hC : C = bx * x ^ 2 + by' * y ^ 2 + bz * z ^ 2 + bw * w ^ 2) : bx = 0 := by
  subst hx
  have hC4 : C = 4 * c ^ 2 := by nlinarith
  have key : ∀ {u b : ℝ}, 0 < u → u < 1 / 2 → c ^ 2 = u ^ 2 * (b * (1 - 2 * u) + C) →
      b * u ^ 2 = c ^ 2 * (1 + 2 * u) := by
    intro u b hu hu2 hR
    have hg : (1 - 2 * u) ≠ 0 := by intro h; linarith
    have : (1 - 2 * u) * (b * u ^ 2 - c ^ 2 * (1 + 2 * u)) = 0 := by
      rw [hC4] at hR; linear_combination -hR
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hg)
  have ky := key hy (by linarith) Ry
  have kz := key hz (by linarith) Rz
  have kw := key hw (by linarith) Rw
  nlinarith

set_option linter.style.longLine false in
/-- 定理 5 的代数证书（Singular 计算）：h₂h₃·M = q₁·CR + q₂·PR。
变量 f₀、f₁、f₂ 为 F 的三个重心坐标，f₃ = 1 − f₀ − f₁ − f₂。 -/
theorem fermat_cert {f0 f1 f2 c C p : ℝ}
    (hCR : C * (1 - 2 * f0) * (1 - 2 * f1) * (1 - 2 * f2) * (1 - 2 * (1 - f0 - f1 - f2)) - ((c ^ 2 - C * f0 ^ 2) * (1 - 2 * f1) * (1 - 2 * f2) * (1 - 2 * (1 - f0 - f1 - f2)) + (c ^ 2 - C * f1 ^ 2) * (1 - 2 * f0) * (1 - 2 * f2) * (1 - 2 * (1 - f0 - f1 - f2)) + (c ^ 2 - C * f2 ^ 2) * (1 - 2 * f0) * (1 - 2 * f1) * (1 - 2 * (1 - f0 - f1 - f2)) + (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) * (1 - 2 * f0) * (1 - 2 * f1) * (1 - 2 * f2)) = 0)
    (hPR : p * (f0 ^ 2 * (1 - 2 * f0) * (c ^ 2 - C * f1 ^ 2) * (c ^ 2 - C * f2 ^ 2) * (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) + f1 ^ 2 * (1 - 2 * f1) * (c ^ 2 - C * f0 ^ 2) * (c ^ 2 - C * f2 ^ 2) * (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) + f2 ^ 2 * (1 - 2 * f2) * (c ^ 2 - C * f0 ^ 2) * (c ^ 2 - C * f1 ^ 2) * (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) + (1 - f0 - f1 - f2) ^ 2 * (1 - 2 * (1 - f0 - f1 - f2)) * (c ^ 2 - C * f0 ^ 2) * (c ^ 2 - C * f1 ^ 2) * (c ^ 2 - C * f2 ^ 2)) + (c ^ 2 - C * f0 ^ 2) * (c ^ 2 - C * f1 ^ 2) * (c ^ 2 - C * f2 ^ 2) * (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) = 0) :
    (c ^ 2 - C * f2 ^ 2) * (c ^ 2 - C * (1 - f0 - f1 - f2) ^ 2) * (((c ^ 2 - C * f0 ^ 2) - C * f0 * (1 - 2 * f0)) * ((1 - 2 * f1) * (c ^ 2 - C * f1 ^ 2) + 2 * p * f1 ^ 2 * (1 - 2 * f1)) * (1 - 2 * f1) * (c ^ 2 - C * f0 ^ 2) - ((c ^ 2 - C * f1 ^ 2) - C * f1 * (1 - 2 * f1)) * ((1 - 2 * f0) * (c ^ 2 - C * f0 ^ 2) + 2 * p * f0 ^ 2 * (1 - 2 * f0)) * (1 - 2 * f0) * (c ^ 2 - C * f1 ^ 2)) = 0 := by
  linear_combination (-f0 ^ 4 * f1 * f2 * c ^ 2 * C ^ 2 * p-f0 ^ 3 * f1 ^ 2 * f2 * c ^ 2 * C ^ 2 * p+f0 ^ 2 * f1 ^ 3 * f2 * c ^ 2 * C ^ 2 * p+f0 * f1 ^ 4 * f2 * c ^ 2 * C ^ 2 * p-f0 ^ 3 * f1 * f2 ^ 2 * c ^ 2 * C ^ 2 * p+f0 * f1 ^ 3 * f2 ^ 2 * c ^ 2 * C ^ 2 * p+f0 ^ 4 * c ^ 4 * C * p+f0 ^ 3 * f1 * c ^ 4 * C * p-f0 * f1 ^ 3 * c ^ 4 * C * p-f1 ^ 4 * c ^ 4 * C * p+f0 ^ 3 * f2 * c ^ 4 * C * p+f0 ^ 2 * f1 * f2 * c ^ 4 * C * p-f0 * f1 ^ 2 * f2 * c ^ 4 * C * p-f1 ^ 3 * f2 * c ^ 4 * C * p+f0 ^ 2 * f2 ^ 2 * c ^ 4 * C * p-f1 ^ 2 * f2 ^ 2 * c ^ 4 * C * p-1/2 * f0 ^ 4 * f1 * c ^ 2 * C ^ 2 * p-1/2 * f0 ^ 3 * f1 ^ 2 * c ^ 2 * C ^ 2 * p+1/2 * f0 ^ 2 * f1 ^ 3 * c ^ 2 * C ^ 2 * p+1/2 * f0 * f1 ^ 4 * c ^ 2 * C ^ 2 * p+1/2 * f0 ^ 4 * f2 * c ^ 2 * C ^ 2 * p+2 * f0 ^ 3 * f1 * f2 * c ^ 2 * C ^ 2 * p-2 * f0 * f1 ^ 3 * f2 * c ^ 2 * C ^ 2 * p-1/2 * f1 ^ 4 * f2 * c ^ 2 * C ^ 2 * p+1/2 * f0 ^ 3 * f2 ^ 2 * c ^ 2 * C ^ 2 * p+1/2 * f0 ^ 2 * f1 * f2 ^ 2 * c ^ 2 * C ^ 2 * p-1/2 * f0 * f1 ^ 2 * f2 ^ 2 * c ^ 2 * C ^ 2 * p-1/2 * f1 ^ 3 * f2 ^ 2 * c ^ 2 * C ^ 2 * p-3 * f0 ^ 2 * c ^ 6 * p+3 * f1 ^ 2 * c ^ 6 * p-2 * f0 ^ 3 * c ^ 4 * C * p+2 * f1 ^ 3 * c ^ 4 * C * p-f0 ^ 2 * f2 * c ^ 4 * C * p+f1 ^ 2 * f2 * c ^ 4 * C * p+f0 ^ 3 * f1 * c ^ 2 * C ^ 2 * p-f0 * f1 ^ 3 * c ^ 2 * C ^ 2 * p-f0 ^ 3 * f2 * c ^ 2 * C ^ 2 * p-f0 ^ 2 * f1 * f2 * c ^ 2 * C ^ 2 * p+f0 * f1 ^ 2 * f2 * c ^ 2 * C ^ 2 * p+f1 ^ 3 * f2 * c ^ 2 * C ^ 2 * p-1/2 * f0 ^ 2 * f2 ^ 2 * c ^ 2 * C ^ 2 * p+1/2 * f1 ^ 2 * f2 ^ 2 * c ^ 2 * C ^ 2 * p+2 * f0 * c ^ 6 * p-2 * f1 * c ^ 6 * p+3/2 * f0 ^ 2 * c ^ 4 * C * p-3/2 * f1 ^ 2 * c ^ 4 * C * p-1/2 * f0 ^ 2 * f1 * c ^ 2 * C ^ 2 * p+1/2 * f0 * f1 ^ 2 * c ^ 2 * C ^ 2 * p+1/2 * f0 ^ 2 * f2 * c ^ 2 * C ^ 2 * p-1/2 * f1 ^ 2 * f2 * c ^ 2 * C ^ 2 * p-1/2 * f0 * c ^ 4 * C * p+1/2 * f1 * c ^ 4 * C * p) * hCR + (-4 * f0 ^ 2 * c ^ 2+4 * f1 ^ 2 * c ^ 2+4 * f0 * c ^ 2-4 * f1 * c ^ 2+f0 ^ 2 * C-f1 ^ 2 * C-f0 * C+f1 * C) * hPR

set_option linter.style.longLine false in
/-- 下标对 (0, 1)：αⱼ' = fⱼ(bⱼfⱼ − C)，βⱼ = 1/2 − fⱼ + p/bⱼ，则 α₀'β₁ = α₁'β₀。 -/
theorem fermat_pair {x0 x1 x2 x3 b0 b1 b2 b3 c C p : ℝ} (hs : x0 + x1 + x2 + x3 = 1)
    (hb0 : b0 ≠ 0) (hb1 : b1 ≠ 0) (hb2 : b2 ≠ 0) (hb3 : b3 ≠ 0)
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hx3 : x3 ≠ 0)
    (hg0 : 1 - 2 * x0 ≠ 0) (hg1 : 1 - 2 * x1 ≠ 0) (hg2 : 1 - 2 * x2 ≠ 0) (hg3 : 1 - 2 * x3 ≠ 0)
    (R0 : c ^ 2 = x0 ^ 2 * (b0 * (1 - 2 * x0) + C)) (R1 : c ^ 2 = x1 ^ 2 * (b1 * (1 - 2 * x1) + C))
    (R2 : c ^ 2 = x2 ^ 2 * (b2 * (1 - 2 * x2) + C)) (R3 : c ^ 2 = x3 ^ 2 * (b3 * (1 - 2 * x3) + C))
    (hC : C = b0 * x0 ^ 2 + b1 * x1 ^ 2 + b2 * x2 ^ 2 + b3 * x3 ^ 2)
    (hp : p * (1 / b0 + 1 / b1 + 1 / b2 + 1 / b3) = -1) :
    x0 * (b0 * x0 - C) * (1 / 2 - x1 + p / b1) = x1 * (b1 * x1 - C) * (1 / 2 - x0 + p / b0) := by
  have e0 : c ^ 2 - C * x0 ^ 2 = b0 * x0 ^ 2 * (1 - 2 * x0) := by rw [R0]; ring
  have e1 : c ^ 2 - C * x1 ^ 2 = b1 * x1 ^ 2 * (1 - 2 * x1) := by rw [R1]; ring
  have e2 : c ^ 2 - C * x2 ^ 2 = b2 * x2 ^ 2 * (1 - 2 * x2) := by rw [R2]; ring
  have e3 : c ^ 2 - C * x3 ^ 2 = b3 * x3 ^ 2 * (1 - 2 * x3) := by rw [R3]; ring
  have hh2 : c ^ 2 - C * x2 ^ 2 ≠ 0 := by rw [e2]; exact mul_ne_zero (mul_ne_zero hb2 (pow_ne_zero 2 hx2)) hg2
  have hh3 : c ^ 2 - C * x3 ^ 2 ≠ 0 := by rw [e3]; exact mul_ne_zero (mul_ne_zero hb3 (pow_ne_zero 2 hx3)) hg3
  have hCR : C * (1 - 2 * x0) * (1 - 2 * x1) * (1 - 2 * x2) * (1 - 2 * x3) -
      ((c ^ 2 - C * x0 ^ 2) * (1 - 2 * x1) * (1 - 2 * x2) * (1 - 2 * x3) +
        (c ^ 2 - C * x1 ^ 2) * (1 - 2 * x0) * (1 - 2 * x2) * (1 - 2 * x3) +
        (c ^ 2 - C * x2 ^ 2) * (1 - 2 * x0) * (1 - 2 * x1) * (1 - 2 * x3) +
        (c ^ 2 - C * x3 ^ 2) * (1 - 2 * x0) * (1 - 2 * x1) * (1 - 2 * x2)) = 0 := by
    rw [e0, e1, e2, e3, hC]; ring
  have hpp : p * (b1 * b2 * b3 + b0 * b2 * b3 + b0 * b1 * b3 + b0 * b1 * b2) =
      -(b0 * b1 * b2 * b3) := by
    field_simp at hp; linear_combination hp
  have hPR : p * (x0 ^ 2 * (1 - 2 * x0) * (c ^ 2 - C * x1 ^ 2) * (c ^ 2 - C * x2 ^ 2) *
        (c ^ 2 - C * x3 ^ 2) + x1 ^ 2 * (1 - 2 * x1) * (c ^ 2 - C * x0 ^ 2) *
        (c ^ 2 - C * x2 ^ 2) * (c ^ 2 - C * x3 ^ 2) + x2 ^ 2 * (1 - 2 * x2) *
        (c ^ 2 - C * x0 ^ 2) * (c ^ 2 - C * x1 ^ 2) * (c ^ 2 - C * x3 ^ 2) +
        x3 ^ 2 * (1 - 2 * x3) * (c ^ 2 - C * x0 ^ 2) * (c ^ 2 - C * x1 ^ 2) *
        (c ^ 2 - C * x2 ^ 2)) + (c ^ 2 - C * x0 ^ 2) * (c ^ 2 - C * x1 ^ 2) *
        (c ^ 2 - C * x2 ^ 2) * (c ^ 2 - C * x3 ^ 2) = 0 := by
    rw [e0, e1, e2, e3]
    linear_combination (x0 ^ 2 * x1 ^ 2 * x2 ^ 2 * x3 ^ 2 * (1 - 2 * x0) * (1 - 2 * x1) *
      (1 - 2 * x2) * (1 - 2 * x3)) * hpp
  have hx3' : x3 = 1 - x0 - x1 - x2 := by linarith
  subst hx3'
  have key := fermat_cert hCR hPR
  have hM := (mul_eq_zero.mp key).resolve_left (mul_ne_zero hh2 hh3)
  have hh0 : c ^ 2 - C * x0 ^ 2 ≠ 0 := by rw [e0]; exact mul_ne_zero (mul_ne_zero hb0 (pow_ne_zero 2 hx0)) hg0
  have hh1 : c ^ 2 - C * x1 ^ 2 ≠ 0 := by rw [e1]; exact mul_ne_zero (mul_ne_zero hb1 (pow_ne_zero 2 hx1)) hg1
  have a0 : x0 * (b0 * x0 - C) = ((c ^ 2 - C * x0 ^ 2) - C * x0 * (1 - 2 * x0)) / (1 - 2 * x0) := by
    rw [eq_div_iff hg0, e0]; ring
  have a1 : x1 * (b1 * x1 - C) = ((c ^ 2 - C * x1 ^ 2) - C * x1 * (1 - 2 * x1)) / (1 - 2 * x1) := by
    rw [eq_div_iff hg1, e1]; ring
  have β0 : 1 / 2 - x0 + p / b0 = ((1 - 2 * x0) * (c ^ 2 - C * x0 ^ 2) + 2 * p * x0 ^ 2 * (1 - 2 * x0)) /
      (2 * (c ^ 2 - C * x0 ^ 2)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hh0), e0]; field_simp
  have β1 : 1 / 2 - x1 + p / b1 = ((1 - 2 * x1) * (c ^ 2 - C * x1 ^ 2) + 2 * p * x1 ^ 2 * (1 - 2 * x1)) /
      (2 * (c ^ 2 - C * x1 ^ 2)) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero hh1), e1]; field_simp
  rw [a0, a1, β0, β1, div_mul_div_comm, div_mul_div_comm, div_eq_div_iff
    (mul_ne_zero hg0 (mul_ne_zero two_ne_zero hh1)) (mul_ne_zero hg1 (mul_ne_zero two_ne_zero hh0))]
  linear_combination (2 : ℝ) * hM

theorem exists_other : ∀ i j : Fin 4, i ≠ j →
    ∃ k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by decide

/-- 标量核心：αᵢ'βⱼ = αⱼ'βᵢ（对任意下标对）。 -/
theorem fermat_scalar (f a : Fin 4 → ℝ) (c C p : ℝ) (hs : ∑ j, f j = 1) (hf : ∀ j, 0 < f j)
    (ha : ∀ j, a j ≠ 0) (hR : ∀ j, c ^ 2 = f j ^ 2 * (a j * (1 - 2 * f j) + C))
    (hC : C = ∑ j, a j * f j ^ 2) (hp : p * ∑ j, 1 / a j = -1) (i j : Fin 4) :
    f i * (a i * f i - C) * (1 / 2 - f j + p / a j) =
      f j * (a j * f j - C) * (1 / 2 - f i + p / a i) := by
  rw [Fin.sum_univ_four] at hs hC hp
  -- 每个 fⱼ ≠ 1/2
  have g0 : 1 - 2 * f 0 ≠ 0 := fun hk => ha 0 (half_aux (by linarith) (hf 1) (hf 2) (hf 3)
    (by linarith) (hR 0) (hR 1) (hR 2) (hR 3) (by linarith))
  have g1 : 1 - 2 * f 1 ≠ 0 := fun hk => ha 1 (half_aux (by linarith) (hf 0) (hf 2) (hf 3)
    (by linarith) (hR 1) (hR 0) (hR 2) (hR 3) (by linarith))
  have g2 : 1 - 2 * f 2 ≠ 0 := fun hk => ha 2 (half_aux (by linarith) (hf 0) (hf 1) (hf 3)
    (by linarith) (hR 2) (hR 0) (hR 1) (hR 3) (by linarith))
  have g3 : 1 - 2 * f 3 ≠ 0 := fun hk => ha 3 (half_aux (by linarith) (hf 0) (hf 1) (hf 2)
    (by linarith) (hR 3) (hR 0) (hR 1) (hR 2) (by linarith))
  have hg : ∀ k, 1 - 2 * f k ≠ 0 := by
    intro k; fin_cases k
    exacts [g0, g1, g2, g3]
  by_cases hij : i = j
  · subst hij; ring
  obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := exists_other i j hij
  have e1 := sum_perm f hij hik hil hjk hjl hkl
  have e2 := sum_perm (fun m => a m * f m ^ 2) hij hik hil hjk hjl hkl
  have e3 := sum_perm (fun m => 1 / a m) hij hik hil hjk hjl hkl
  exact fermat_pair (x2 := f k) (x3 := f l) (b2 := a k) (b3 := a l) (by linarith)
    (ha i) (ha j) (ha k) (ha l) (hf i).ne' (hf j).ne' (hf k).ne' (hf l).ne'
    (hg i) (hg j) (hg k) (hg l) (hR i) (hR j) (hR k) (hR l) (by linarith) (by rw [e3]; exact hp)

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
  have hc0 : 0 < c := by rw [hcdef]; exact one_div_pos.mpr hσd
  have hfd : ∀ j, f j * d j = c := fun j => by simp only [f]; field_simp [(hd0 j).ne']
  have hΩ : ∑ k, ω k = C / c ^ 2 := by
    rw [hCdef, Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [ω, f]; field_simp [(hd0 j).ne', hc0.ne']
  have hC0 : C ≠ 0 := by
    intro h0; apply hW; rw [show (∑ j, A t j / d j ^ 2) = ∑ k, ω k from rfl, hΩ, h0, zero_div]
  have hcore : ∀ i j, α i * β j = α j * β i := by
    intro i j
    have key := fermat_scalar f (fun j => A t j) c C (p t) hf1 (fun j => by
        simp only [f]; exact div_pos hc0 (hd0 j)) hA
      (fun j => by
        have := hR j
        rw [← hfd j]
        rw [mul_pow, this]) (by simp only [hCdef])
      (by have := hsum; rw [Fin.sum_univ_four]; linear_combination this) i j
    have hα : ∀ m, α m = f m * (A t m * f m - C) / C := by
      intro m
      simp only [α, ω, hΩ, f]
      field_simp [(hd0 m).ne', hc0.ne', hC0]
    beta_reduce at key
    have e : α i * β j - α j * β i =
        (f i * (A t i * f i - C) * (1 / 2 - f j + p t / A t j) -
          f j * (A t j * f j - C) * (1 / 2 - f i + p t / A t i)) / C := by
      rw [hα i, hα j]; simp only [β, o]; ring
    rw [key, sub_self, zero_div, sub_eq_zero] at e
    exact e
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
