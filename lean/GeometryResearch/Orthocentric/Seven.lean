module

public import GeometryResearch.Orthocentric.Thirteen

/-!
# 定理 4（七线共点）的证明

以 H 为原点，vᵢ = Vᵢ − H，s = v₀ + v₁ + v₂ + v₃（于是 G − H = s/4，O − H = s/2）。
点 X − H = λ·s/4。

* 四条弦：Aᵢ、Bᵢ、X 都落在 vᵢ 与 s 张成的平面里，只需要三个内积
  ⟪vᵢ, vᵢ⟫ = N、⟪vᵢ, s⟫ = N + 3p、⟪s, s⟫ = S。
* 三条直线：μ₁ = mᵢⱼ − H，μ₂ = mₖₗ − H，s = 2(μ₁ + μ₂)，只需要 ⟪μ₁, μ₂⟫ = p。

共线用 Cauchy–Schwarz 取等号来表达：‖x − a‖²‖b − a‖² = ⟪x − a, b − a⟫²。
两个恒等式（共线、内积等于幂）都是纯有理恒等式，`field_simp` 加 `ring` 直接验证。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

namespace Alg

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Cauchy–Schwarz 取等号且 a ≠ b，则 x 在直线 ab 上。 -/
theorem mem_line_of_cs {a b x : V} (hab : a ≠ b)
    (h : ‖x - a‖ ^ 2 * ‖b - a‖ ^ 2 = ⟪x - a, b - a⟫ ^ 2) : x ∈ line[ℝ, a, b] := by
  have hn : ‖b - a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hab.symm))
  set τ := ⟪x - a, b - a⟫ / ‖b - a‖ ^ 2 with hτ
  have key : ‖(x - a) - τ • (b - a)‖ ^ 2 = 0 := by
    have e1 : τ * ‖b - a‖ ^ 2 = ⟪x - a, b - a⟫ := by rw [hτ, div_mul_cancel₀ _ hn]
    rw [@norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have : (‖x - a‖ ^ 2 - 2 * (τ * ⟪x - a, b - a⟫) + τ ^ 2 * ‖b - a‖ ^ 2) * ‖b - a‖ ^ 2 = 0 := by
      linear_combination h + (τ * ‖b - a‖ ^ 2 - ⟪x - a, b - a⟫) * e1
    exact (mul_eq_zero.mp this).resolve_right hn
  have hz : x - a - τ • (b - a) = 0 := by
    rw [← norm_eq_zero]; exact (pow_eq_zero_iff two_ne_zero).mp key
  have : x = AffineMap.lineMap a b τ := by
    rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    rw [sub_sub, sub_eq_zero] at hz
    rw [hz]; abel
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair τ a b

/-- 两个向量 e、f 张成的平面里的内积公式。 -/
theorem ip2 {e f : V} {E M F : ℝ} (he : ⟪e, e⟫ = E) (hef : ⟪e, f⟫ = M) (hf : ⟪f, f⟫ = F)
    (c₁ c₂ d₁ d₂ : ℝ) :
    ⟪c₁ • e + c₂ • f, d₁ • e + d₂ • f⟫ = c₁ * d₁ * E + (c₁ * d₂ + c₂ * d₁) * M + c₂ * d₂ * F := by
  have hfe : ⟪f, e⟫ = M := by rw [real_inner_comm]; exact hef
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    he, hef, hfe, hf]
  ring

theorem nm2 {e f : V} {E M F : ℝ} (he : ⟪e, e⟫ = E) (hef : ⟪e, f⟫ = M) (hf : ⟪f, f⟫ = F)
    (c₁ c₂ : ℝ) :
    ‖c₁ • e + c₂ • f‖ ^ 2 = c₁ * c₁ * E + (c₁ * c₂ + c₂ * c₁) * M + c₂ * c₂ * F := by
  rw [← real_inner_self_eq_norm_sq, ip2 he hef hf]

/-- 弦部分的 Aᵢ − H = ψ(Gᵢ) − H。 -/
def chordA (p : ℝ) (vi s : V) : V :=
  (p / ‖(1 / 3 : ℝ) • (s - vi)‖ ^ 2) • ((1 / 3 : ℝ) • (s - vi))

/-- 弦部分的 Bᵢ − H：从 Vᵢ 沿 G − Vᵢ 方向与外接球的第二交点。 -/
def chordB (vi s : V) : V :=
  (-2 * ⟪(1 / 4 : ℝ) • s - vi, vi - (1 / 2 : ℝ) • s⟫ /
    ⟪(1 / 4 : ℝ) • s - vi, (1 / 4 : ℝ) • s - vi⟫) • ((1 / 4 : ℝ) • s - vi) + vi

set_option maxRecDepth 20000 in
/-- 四条弦：共线（Cauchy–Schwarz 取等号）和内积等于 X 对外接球的幂。 -/
theorem chord {vi s : V} {p N S : ℝ} (hN : ⟪vi, vi⟫ = N) (hvs : ⟪vi, s⟫ = N + 3 * p)
    (hS : ⟪s, s⟫ = S) (hp : p ≠ 0) (hA : N ≠ p) (hD : 3 * S / 8 - 3 * p ≠ 0) :
    let x := (3 * p / (3 * S / 8 - 3 * p)) • ((1 / 4 : ℝ) • s)
    let a := chordA p vi s
    let b := chordB vi s
    (‖x - a‖ ^ 2 * ‖b - a‖ ^ 2 = ⟪x - a, b - a⟫ ^ 2) ∧
    ⟪a - x, b - x⟫ = ‖x - (1 / 2 : ℝ) • s‖ ^ 2 - (S / 4 - 3 * p) := by
  intro x a b
  have hsv : ⟪s, vi⟫ = N + 3 * p := by rw [real_inner_comm]; exact hvs
  have ip := ip2 hN hvs hS
  have nm := nm2 hN hvs hS
  have hg : ‖(1 / 3 : ℝ) • (s - vi)‖ ^ 2 = (S - N - 6 * p) / 9 := by
    rw [show (1 / 3 : ℝ) • (s - vi) = (-1 / 3 : ℝ) • vi + (1 / 3 : ℝ) • s by module, nm]; ring
  have hg0 : S - N - 6 * p ≠ 0 := by
    intro h0
    have h1 : (1 / 3 : ℝ) • (s - vi) = 0 := by
      rw [← norm_eq_zero]; exact (pow_eq_zero_iff two_ne_zero).mp (by rw [hg, h0]; simp)
    have h2 := congrArg (fun z => ⟪vi, z⟫) h1
    simp only [inner_zero_right, real_inner_smul_right, inner_sub_right, hN, hvs] at h2
    exact hp (by linarith)
  have hd : ⟪(1 / 4 : ℝ) • s - vi, (1 / 4 : ℝ) • s - vi⟫ = S / 16 + N / 2 - 3 * p / 2 := by
    rw [show (1 / 4 : ℝ) • s - vi = (-1 : ℝ) • vi + (1 / 4 : ℝ) • s by module, ip]; ring
  have hd0 : S / 16 + N / 2 - 3 * p / 2 ≠ 0 := by
    intro h0
    rw [h0] at hd
    have h1 := inner_self_eq_zero.mp hd
    have h2 := congrArg (fun z => ⟪vi, z⟫) h1
    simp only [inner_zero_right, real_inner_smul_right, inner_sub_right, hN, hvs] at h2
    exact hA (by linarith)
  have hdn : ⟪(1 / 4 : ℝ) • s - vi, vi - (1 / 2 : ℝ) • s⟫ = 3 * (N + 3 * p) / 4 - S / 8 - N := by
    rw [show (1 / 4 : ℝ) • s - vi = (-1 : ℝ) • vi + (1 / 4 : ℝ) • s by module,
      show vi - (1 / 2 : ℝ) • s = (1 : ℝ) • vi + (-1 / 2 : ℝ) • s by module, ip]; ring
  set α := p / ‖(1 / 3 : ℝ) • (s - vi)‖ ^ 2 with hα
  set τ := -2 * ⟪(1 / 4 : ℝ) • s - vi, vi - (1 / 2 : ℝ) • s⟫ /
    ⟪(1 / 4 : ℝ) • s - vi, (1 / 4 : ℝ) • s - vi⟫ with hτ
  set l := 3 * p / (3 * S / 8 - 3 * p) with hl
  have ea : a = (-α / 3) • vi + (α / 3) • s := by
    simp only [a, chordA]; rw [← hα]; module
  have eb : b = (1 - τ) • vi + (τ / 4) • s := by
    simp only [b, chordB]; rw [← hτ]; module
  have ex : x = (0 : ℝ) • vi + (l / 4) • s := by simp only [x]; module
  have e1 : x - a = (α / 3) • vi + (l / 4 - α / 3) • s := by rw [ex, ea]; module
  have e2 : b - a = (1 - τ + α / 3) • vi + (τ / 4 - α / 3) • s := by rw [eb, ea]; module
  have e3 : a - x = (-α / 3) • vi + (α / 3 - l / 4) • s := by rw [ex, ea]; module
  have e4 : b - x = (1 - τ) • vi + (τ / 4 - l / 4) • s := by rw [ex, eb]; module
  have e5 : x - (1 / 2 : ℝ) • s = (0 : ℝ) • vi + (l / 4 - 1 / 2) • s := by rw [ex]; module
  have hα' : α = 9 * p / (S - N - 6 * p) := by
    rw [hα, hg, div_eq_div_iff (div_ne_zero hg0 (by norm_num)) hg0]; ring
  have hd1 : S + 8 * N - 24 * p ≠ 0 := by intro h0; apply hd0; linarith
  have hτ' : τ = (4 * S + 8 * N - 72 * p) / (S + 8 * N - 24 * p) := by
    rw [hτ, hd, hdn, div_eq_div_iff hd0 hd1]; ring
  have hD1 : S - 8 * p ≠ 0 := by intro h0; apply hD; linarith
  have hl' : l = 8 * p / (S - 8 * p) := by rw [hl, div_eq_div_iff hD hD1]; ring
  have k1 : S - N - p * 6 ≠ 0 := by intro h0; apply hg0; linarith
  have k2 : S + N * 8 - p * 24 ≠ 0 := by intro h0; apply hd1; linarith
  have k3 : S - p * 8 ≠ 0 := by intro h0; apply hD1; linarith
  constructor
  · rw [e1, e2, nm, nm, ip, hα', hτ', hl']
    field_simp
    ring
  · rw [e3, e4, e5, ip, nm, hα', hτ', hl']
    field_simp
    ring

/-- ψ 的向量形式：ψ(H + μ) − H。 -/
def psiv (p : ℝ) (μ : V) : V := (p / ‖μ‖ ^ 2) • μ

/-- 三条直线：ψ(mᵢⱼ) ≠ ψ(mₖₗ)，共线，内积等于 X 对中点球的幂。 -/
theorem midline {μ₁ μ₂ : V} {p n₁ n₂ : ℝ} (h11 : ⟪μ₁, μ₁⟫ = n₁) (h22 : ⟪μ₂, μ₂⟫ = n₂)
    (h12 : ⟪μ₁, μ₂⟫ = p) (hp : p ≠ 0) (hne : μ₁ ≠ μ₂)
    (hD : 3 * (4 * (n₁ + n₂ + 2 * p)) / 8 - 3 * p ≠ 0) :
    let s := (2 : ℝ) • (μ₁ + μ₂)
    let x := (3 * p / (3 * (4 * (n₁ + n₂ + 2 * p)) / 8 - 3 * p)) • ((1 / 4 : ℝ) • s)
    let a := psiv p μ₁
    let b := psiv p μ₂
    a ≠ b ∧ (‖x - a‖ ^ 2 * ‖b - a‖ ^ 2 = ⟪x - a, b - a⟫ ^ 2) ∧
    ⟪a - x, b - x⟫ = ‖x - (1 / 4 : ℝ) • s‖ ^ 2 - ‖μ₁ - (1 / 4 : ℝ) • s‖ ^ 2 := by
  intro s x a b
  have ip := ip2 h11 h12 h22
  have nm := nm2 h11 h12 h22
  have hn1 : n₁ ≠ 0 := by
    intro h0; rw [h0] at h11
    rw [inner_self_eq_zero.mp h11, inner_zero_left] at h12; exact hp h12.symm
  have hn2 : n₂ ≠ 0 := by
    intro h0; rw [h0] at h22
    rw [inner_self_eq_zero.mp h22, inner_zero_right] at h12; exact hp h12.symm
  have hq : n₁ + n₂ - 2 * p ≠ 0 := by
    intro h0
    apply hne
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ),
      show μ₁ - μ₂ = (1 : ℝ) • μ₁ + (-1 : ℝ) • μ₂ by module, ip]
    linarith
  have e1 : ‖μ₁‖ ^ 2 = n₁ := by rw [← real_inner_self_eq_norm_sq, h11]
  have e2 : ‖μ₂‖ ^ 2 = n₂ := by rw [← real_inner_self_eq_norm_sq, h22]
  set l := 3 * p / (3 * (4 * (n₁ + n₂ + 2 * p)) / 8 - 3 * p) with hl
  have ea : a = (p / n₁) • μ₁ + (0 : ℝ) • μ₂ := by simp only [a, psiv, e1]; module
  have eb : b = (0 : ℝ) • μ₁ + (p / n₂) • μ₂ := by simp only [b, psiv, e2]; module
  have ex : x = (l / 2) • μ₁ + (l / 2) • μ₂ := by simp only [x, s]; module
  have f1 : x - a = (l / 2 - p / n₁) • μ₁ + (l / 2) • μ₂ := by rw [ex, ea]; module
  have f2 : b - a = (-(p / n₁)) • μ₁ + (p / n₂) • μ₂ := by rw [eb, ea]; module
  have f3 : a - x = (p / n₁ - l / 2) • μ₁ + (-(l / 2)) • μ₂ := by rw [ex, ea]; module
  have f4 : b - x = (-(l / 2)) • μ₁ + (p / n₂ - l / 2) • μ₂ := by rw [ex, eb]; module
  have f5 : x - (1 / 4 : ℝ) • s = (l / 2 - 1 / 2) • μ₁ + (l / 2 - 1 / 2) • μ₂ := by
    rw [ex]; simp only [s]; module
  have f6 : μ₁ - (1 / 4 : ℝ) • s = (1 / 2 : ℝ) • μ₁ + (-1 / 2 : ℝ) • μ₂ := by
    simp only [s]; module
  have hD1 : n₁ + n₂ ≠ 0 := by intro h0; apply hD; linarith
  have hl' : l = 2 * p / (n₁ + n₂) := by rw [hl, div_eq_div_iff hD hD1]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    have h := congrArg (fun z => ⟪z - b, z - b⟫) hab
    simp only [sub_self, inner_zero_left] at h
    rw [show a - b = (p / n₁) • μ₁ + (-(p / n₂)) • μ₂ by rw [ea, eb]; module, ip] at h
    field_simp at h
    apply hq
    have hpp : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
    have : p ^ 2 * (n₁ + n₂ - 2 * p) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left hpp
  · rw [f1, f2, nm, nm, ip, hl']
    field_simp
    ring
  · rw [f3, f4, f5, f6, ip, nm, nm, hl']
    field_simp
    ring

end Alg

/-! ## 接到四面体上 -/

variable (t : Affine.Simplex ℝ E3 3)

set_option linter.flexible false in
/-- 中点球：六个棱中点到 G 等距（`Statement.lean` 中 `dist_mid_G` 的证明）。 -/
theorem dist_mid_G_aux (ho : IsOrthocentric t) {i j : Fin 4} (hij : i ≠ j) :
    dist (mid t i j) (G t) = rMid t := by
  obtain ⟨h02, h03, h12, h13, h23⟩ := Alg.mid_eq (hyp t ho)
  have key : ∀ a b : Fin 4, a < b → dist (mid t a b) (G t) = rMid t := by
    intro a b hab
    rw [rMid, dist_eq_norm, dist_eq_norm, mid_sub_G, mid_sub_G]
    fin_cases a <;> fin_cases b <;> simp at hab ⊢ <;>
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq] <;> assumption
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · rw [mid, midpoint_comm]; exact key j i h

/-- s = v₀ + v₁ + v₂ + v₃。 -/
abbrev sv : E3 := v t 0 + v t 1 + v t 2 + v t 3

/-- G − H = s/4。 -/
theorem G_sub_H : G t - H t = (1 / 4 : ℝ) • sv t := by
  rw [show G t - H t = (G t - O t) - (H t - O t) by abel, G_sub_O, H_sub_O]
  simp only [sv, v, pt_sub_H, Alg.w]
  module

theorem inner_v_s (ho : IsOrthocentric t) (i : Fin 4) :
    ⟪v t i, sv t⟫ = p t + A t i + 3 * p t := by
  rw [sv, split4 (v t) i]
  simp only [inner_add_right, inner_v_self,
    inner_pt_H t ho (Fin.succAbove_ne i 0).symm, inner_pt_H t ho (Fin.succAbove_ne i 1).symm,
    inner_pt_H t ho (Fin.succAbove_ne i 2).symm]
  ring

/-- R² = ⟪s, s⟫/4 − 3p。 -/
theorem R_sq (ho : IsOrthocentric t) : R t ^ 2 = ⟪sv t, sv t⟫ / 4 - 3 * p t := by
  have hR : R t = dist (t.points 0) (O t) := (t.dist_circumcenter_eq_circumradius 0).symm
  rw [hR, dist_eq_norm, show t.points 0 - O t = v t 0 - (O t - H t) by simp only [v]; abel,
    O_sub_H, show v t 0 - (1 / 2 : ℝ) • (v t 0 + v t 1 + v t 2 + v t 3) =
      (1 : ℝ) • v t 0 + (-1 / 2 : ℝ) • sv t by simp only [sv]; module,
    Alg.nm2 (inner_v_self t 0) (inner_v_s t ho 0) rfl]
  ring

theorem dist_HG_sq : dist (H t) (G t) ^ 2 = ⟪sv t, sv t⟫ / 16 := by
  rw [dist_comm, dist_eq_norm, G_sub_H, ← real_inner_self_eq_norm_sq, real_inner_smul_left,
    real_inner_smul_right]
  ring

theorem denom_ne (ho : IsOrthocentric t) : 3 * ⟪sv t, sv t⟫ / 8 - 3 * p t ≠ 0 := by
  have h1 := R_sq t ho
  have h2 : 0 < R t ^ 2 := pow_pos t.circumradius_pos 2
  have h3 : 0 ≤ ⟪sv t, sv t⟫ := real_inner_self_nonneg
  intro h0; nlinarith

/-- X − H = λ·s/4，λ = 3p/(3S/8 − 3p)。 -/
theorem X_sub_H (ho : IsOrthocentric t) :
    AffineMap.lineMap (H t) (G t) ((4 * dist (H t) (G t) ^ 2 - R t ^ 2) /
        (2 * dist (H t) (G t) ^ 2 + R t ^ 2)) - H t =
      (3 * p t / (3 * ⟪sv t, sv t⟫ / 8 - 3 * p t)) • ((1 / 4 : ℝ) • sv t) := by
  rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, G_sub_H,
    dist_HG_sq, R_sq t ho]
  congr 1
  congr 1 <;> ring

/-- 定理 4 的四条弦。 -/
theorem chord_main (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j) (i : Fin 4) :
    let X := AffineMap.lineMap (H t) (G t) ((4 * dist (H t) (G t) ^ 2 - R t ^ 2) /
      (2 * dist (H t) (G t) ^ 2 + R t ^ 2))
    let Ai := ψ t (Gface t i)
    let Bi := (Ω t).secondInter (t.points i) (G t -ᵥ t.points i)
    (Ai ≠ Bi → X ∈ line[ℝ, Ai, Bi]) ∧ (Ai = Bi → ⟪X - Ai, Ai - O t⟫ = 0) ∧
      ⟪Ai - X, Bi - X⟫ = (Ω t).power X := by
  intro X Ai Bi
  obtain ⟨hp0, -, -⟩ := rel t ho hH
  have hA := A_ne t ho hH
  obtain ⟨hcs, hpow⟩ := Alg.chord (vi := v t i) (s := sv t) (N := p t + A t i)
    (S := ⟪sv t, sv t⟫) (inner_v_self t i) (inner_v_s t ho i) rfl hp0
    (by intro h; apply hA i; linarith) (denom_ne t ho)
  have hs : sv t = v t i + v t (i.succAbove 0) + v t (i.succAbove 1) + v t (i.succAbove 2) :=
    split4 (v t) i
  have hc : (Ω t).center = O t := t.circumsphere_center
  have hOH : O t - H t = (1 / 2 : ℝ) • sv t := O_sub_H t
  -- 三个点相对 H 的向量
  have hx : X - H t = (3 * p t / (3 * ⟪sv t, sv t⟫ / 8 - 3 * p t)) • ((1 / 4 : ℝ) • sv t) :=
    X_sub_H t ho
  have ha : Ai - H t = Alg.chordA (p t) (v t i) (sv t) := by
    have hg : Gface t i - H t = (1 / 3 : ℝ) • (sv t - v t i) := by
      rw [show Gface t i = (t.faceOpposite i).centroid from rfl, faceCentroid_sub_H, hs]
      congr 1; abel
    simp only [Ai, ψ, add_sub_cancel_left, Alg.chordA, hg]
  have hGV : G t -ᵥ t.points i = (1 / 4 : ℝ) • sv t - v t i := by
    rw [vsub_eq_sub, show G t - t.points i = (G t - H t) - v t i by simp only [v]; abel,
      G_sub_H]
  have hVO : t.points i -ᵥ (Ω t).center = v t i - (1 / 2 : ℝ) • sv t := by
    rw [hc, vsub_eq_sub, show t.points i - O t = v t i - (O t - H t) by simp only [v]; abel, hOH]
  have hb : Bi - H t = Alg.chordB (v t i) (sv t) := by
    simp only [Bi, Sphere.secondInter, hGV, hVO, vadd_eq_add, Alg.chordB]
    simp only [v]; abel
  have hpw : (Ω t).power X = ‖(X - H t) - (1 / 2 : ℝ) • sv t‖ ^ 2 -
      (⟪sv t, sv t⟫ / 4 - 3 * p t) := by
    rw [Sphere.power, hc, Ω, Affine.Simplex.circumsphere_radius, ← R, R_sq t ho, dist_eq_norm,
      show X - O t = (X - H t) - (O t - H t) by abel, hOH]
  have d1 : Ai - X = (Ai - H t) - (X - H t) := by abel
  have d2 : Bi - X = (Bi - H t) - (X - H t) := by abel
  have d3 : X - Ai = (X - H t) - (Ai - H t) := by abel
  have d4 : Bi - Ai = (Bi - H t) - (Ai - H t) := by abel
  have key : ⟪Ai - X, Bi - X⟫ = (Ω t).power X := by
    rw [d1, d2, ha, hb, hx, hpw, hx]; exact hpow
  refine ⟨fun hab => ?_, fun hab => ?_, key⟩
  · apply Alg.mem_line_of_cs hab
    rw [d3, d4, ha, hb, hx]; exact hcs
  · -- 切线情形：Aᵢ = Bᵢ 在外接球上，幂等式给出 ⟪X − A, A − O⟫ = 0
    have hBΩ : Bi ∈ Ω t := (Sphere.secondInter_mem _).mpr (t.mem_circumsphere i)
    have hBO : ‖Bi - O t‖ = R t := by
      rw [← dist_eq_norm, ← hc]; exact mem_sphere.mp hBΩ
    rw [← hab] at hBO
    have k := key
    rw [← hab, Sphere.power, hc, Ω, Affine.Simplex.circumsphere_radius, ← R, dist_eq_norm,
      show X - O t = (X - Ai) + (Ai - O t) by abel, @norm_add_sq_real, hBO] at k
    rw [show Ai - X = -(X - Ai) by abel, inner_neg_neg, real_inner_self_eq_norm_sq] at k
    linarith

/-- 四个两两不同的下标，求和等于 Fin 4 上的和。 -/
theorem sum_perm {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    f i + f j + f k + f l = f 0 + f 1 + f 2 + f 3 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp at * <;> abel

/-- 定理 4 的三条直线。 -/
theorem midline_main (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) :
    let X := AffineMap.lineMap (H t) (G t) ((4 * dist (H t) (G t) ^ 2 - R t ^ 2) /
      (2 * dist (H t) (G t) ^ 2 + R t ^ 2))
    ψ t (mid t i j) ≠ ψ t (mid t k l) ∧ X ∈ line[ℝ, ψ t (mid t i j), ψ t (mid t k l)] ∧
      ⟪ψ t (mid t i j) - X, ψ t (mid t k l) - X⟫ = powMid t X := by
  intro X
  obtain ⟨hp0, -, -⟩ := rel t ho hH
  have hA := A_ne t ho hH
  set μ₁ : E3 := (1 / 2 : ℝ) • (v t i + v t j)
  set μ₂ : E3 := (1 / 2 : ℝ) • (v t k + v t l)
  have h12 : ⟪μ₁, μ₂⟫ = p t := by
    simp only [μ₁, μ₂, real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_add_right, inner_pt_H t ho hik, inner_pt_H t ho hil, inner_pt_H t ho hjk,
      inner_pt_H t ho hjl]
    ring
  have hs : sv t = (2 : ℝ) • (μ₁ + μ₂) := by
    rw [sv, ← sum_perm (v t) hij hik hil hjk hjl hkl]; simp only [μ₁, μ₂]; module
  have hne : μ₁ ≠ μ₂ := by
    intro h
    have h' := congrArg (fun z => ⟪v t i, z⟫) h
    simp only [μ₁, μ₂, real_inner_smul_right, inner_add_right, inner_v_self,
      inner_pt_H t ho hij, inner_pt_H t ho hik, inner_pt_H t ho hil] at h'
    exact hA i (by linarith)
  have hS : ⟪sv t, sv t⟫ = 4 * (⟪μ₁, μ₁⟫ + ⟪μ₂, μ₂⟫ + 2 * p t) := by
    rw [hs, show (2 : ℝ) • (μ₁ + μ₂) = (2 : ℝ) • μ₁ + (2 : ℝ) • μ₂ by module,
      Alg.ip2 rfl h12 rfl]
    ring
  have hD := denom_ne t ho
  rw [hS] at hD
  obtain ⟨hab, hcs, hpow⟩ := Alg.midline (μ₁ := μ₁) (μ₂ := μ₂) rfl rfl h12 hp0 hne hD
  have hx : X - H t = (3 * p t / (3 * (4 * (⟪μ₁, μ₁⟫ + ⟪μ₂, μ₂⟫ + 2 * p t)) / 8 - 3 * p t)) •
      ((1 / 4 : ℝ) • ((2 : ℝ) • (μ₁ + μ₂))) := by
    rw [X_sub_H t ho, hS, hs]
  have hm : ∀ a b : Fin 4, mid t a b - H t = (1 / 2 : ℝ) • (v t a + v t b) := by
    intro a b; simp only [mid, midpoint_eq_smul_add, v, invOf_eq_inv]; module
  have hψ1 : ψ t (mid t i j) - H t = Alg.psiv (p t) μ₁ := by
    simp only [ψ, add_sub_cancel_left, Alg.psiv, hm, μ₁]
  have hψ2 : ψ t (mid t k l) - H t = Alg.psiv (p t) μ₂ := by
    simp only [ψ, add_sub_cancel_left, Alg.psiv, hm, μ₂]
  have hG : G t - H t = (1 / 4 : ℝ) • ((2 : ℝ) • (μ₁ + μ₂)) := by rw [G_sub_H, hs]
  have hpm : powMid t X = ‖(X - H t) - (1 / 4 : ℝ) • ((2 : ℝ) • (μ₁ + μ₂))‖ ^ 2 -
      ‖μ₁ - (1 / 4 : ℝ) • ((2 : ℝ) • (μ₁ + μ₂))‖ ^ 2 := by
    rw [powMid, ← dist_mid_G_aux t ho hij, dist_eq_norm, dist_eq_norm,
      show X - G t = (X - H t) - (G t - H t) by abel,
      show mid t i j - G t = (mid t i j - H t) - (G t - H t) by abel, hG, hm]
  refine ⟨?_, ?_, ?_⟩
  · intro h; apply hab
    rw [← hψ1, ← hψ2, h]
  · apply Alg.mem_line_of_cs
    · intro h; apply hab; rw [← hψ1, ← hψ2, h]
    · rw [show X - ψ t (mid t i j) = (X - H t) - (ψ t (mid t i j) - H t) by abel,
        show ψ t (mid t k l) - ψ t (mid t i j) =
          (ψ t (mid t k l) - H t) - (ψ t (mid t i j) - H t) by abel, hψ1, hψ2, hx]
      exact hcs
  · rw [show ψ t (mid t i j) - X = (ψ t (mid t i j) - H t) - (X - H t) by abel,
      show ψ t (mid t k l) - X = (ψ t (mid t k l) - H t) - (X - H t) by abel, hψ1, hψ2,
      hpm, hx]
    exact hpow

end GeometryResearch.Orthocentric
