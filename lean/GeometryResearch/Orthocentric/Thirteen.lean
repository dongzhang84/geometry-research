module

public import GeometryResearch.Orthocentric.Model

/-!
# 定理 1（十三点球）的证明

以 H 为原点，vᵢ = Vᵢ − H，面 i 的三个顶点记 w₀, w₁, w₂。球 Σ（球心 c，H 对它的幂 κ）上的点
x 满足 ⟪x, x⟫ − 2⟪x, c − H⟫ + κ = 0。已知 Vᵢ 和面 i 的三个棱中点在 Σ 上，再用核心关系
Σ vⱼ/aⱼ = 0、p·Σ 1/aⱼ = −1，解出 κ = 3p/2，然后逐个验证三个新点。
-/

@[expose] public noncomputable section

open EuclideanGeometry
open scoped RealInnerProductSpace

namespace GeometryResearch.Orthocentric

namespace Alg

/-- 纯标量部分：由 Vᵢ 和三个棱中点的四个方程以及两条核心关系，解出 κ、C 和 ΣD。 -/
theorem thirteen_scalar {p A B0 B1 B2 C D0 D1 D2 κ : ℝ} (hA : A ≠ 0) (hB0 : B0 ≠ 0)
    (hB1 : B1 ≠ 0) (hB2 : B2 ≠ 0)
    (hV : p + A - 2 * C + κ = 0)
    (m0 : (4 * p + B1 + B2) / 4 - (D1 + D2) + κ = 0)
    (m1 : (4 * p + B0 + B2) / 4 - (D0 + D2) + κ = 0)
    (m2 : (4 * p + B0 + B1) / 4 - (D0 + D1) + κ = 0)
    (hrel : 1 / A * C + 1 / B0 * D0 + 1 / B1 * D1 + 1 / B2 * D2 = 0)
    (hsum : p * (1 / A + 1 / B0 + 1 / B1 + 1 / B2) = -1) :
    κ = 3 * p / 2 ∧ C = 5 * p / 4 + A / 2 ∧ D0 + D1 + D2 = 15 * p / 4 + (B0 + B1 + B2) / 4 := by
  have hC : C = (p + A + κ) / 2 := by linarith
  have hD0 : D0 = p / 2 + B0 / 4 + κ / 2 := by linarith
  have hD1 : D1 = p / 2 + B1 / 4 + κ / 2 := by linarith
  have hD2 : D2 = p / 2 + B2 / 4 + κ / 2 := by linarith
  have eA : 1 / A * C = (p + κ) / 2 * (1 / A) + 1 / 2 := by rw [hC]; field_simp; ring
  have e0 : 1 / B0 * D0 = (p + κ) / 2 * (1 / B0) + 1 / 4 := by rw [hD0]; field_simp; ring
  have e1 : 1 / B1 * D1 = (p + κ) / 2 * (1 / B1) + 1 / 4 := by rw [hD1]; field_simp; ring
  have e2 : 1 / B2 * D2 = (p + κ) / 2 * (1 / B2) + 1 / 4 := by rw [hD2]; field_simp; ring
  have key : (p + κ) / 2 * (1 / A + 1 / B0 + 1 / B1 + 1 / B2) + 5 / 4 = 0 := by
    linear_combination hrel - eA - e0 - e1 - e2
  have hκ : κ = 3 * p / 2 := by linear_combination (-2 * p) * key + (p + κ) * hsum
  refine ⟨hκ, ?_, ?_⟩ <;> linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- 向量部分。`P x = ⟪x, x⟫ − 2⟪x, c⟫ + κ` 是点 H + x 对球 Σ 的幂（c 为球心减 H）。 -/
theorem thirteen_vec {vi w0 w1 w2 c : V} {p A B0 B1 B2 κ : ℝ}
    (hA : A ≠ 0) (hB0 : B0 ≠ 0) (hB1 : B1 ≠ 0) (hB2 : B2 ≠ 0) (hp : p ≠ 0)
    (hii : ⟪vi, vi⟫ = p + A) (h00 : ⟪w0, w0⟫ = p + B0) (h11 : ⟪w1, w1⟫ = p + B1)
    (h22 : ⟪w2, w2⟫ = p + B2) (hi0 : ⟪vi, w0⟫ = p) (hi1 : ⟪vi, w1⟫ = p) (hi2 : ⟪vi, w2⟫ = p)
    (h01 : ⟪w0, w1⟫ = p) (h02 : ⟪w0, w2⟫ = p) (h12 : ⟪w1, w2⟫ = p)
    (hrelv : (1 / A) • vi + (1 / B0) • w0 + (1 / B1) • w1 + (1 / B2) • w2 = 0)
    (hsum : p * (1 / A + 1 / B0 + 1 / B1 + 1 / B2) = -1)
    (hV : ⟪vi, vi⟫ - 2 * ⟪vi, c⟫ + κ = 0)
    (hm0 : ⟪(1 / 2 : ℝ) • (w1 + w2), (1 / 2 : ℝ) • (w1 + w2)⟫ -
      2 * ⟪(1 / 2 : ℝ) • (w1 + w2), c⟫ + κ = 0)
    (hm1 : ⟪(1 / 2 : ℝ) • (w0 + w2), (1 / 2 : ℝ) • (w0 + w2)⟫ -
      2 * ⟪(1 / 2 : ℝ) • (w0 + w2), c⟫ + κ = 0)
    (hm2 : ⟪(1 / 2 : ℝ) • (w0 + w1), (1 / 2 : ℝ) • (w0 + w1)⟫ -
      2 * ⟪(1 / 2 : ℝ) • (w0 + w1), c⟫ + κ = 0) :
    κ = 3 * p / 2 ∧
    (⟪(1 / 2 : ℝ) • (w0 + w1 + w2), (1 / 2 : ℝ) • (w0 + w1 + w2)⟫ -
      2 * ⟪(1 / 2 : ℝ) • (w0 + w1 + w2), c⟫ + κ = 0) ∧
    (let g := (1 / 3 : ℝ) • (w0 + w1 + w2)
     ⟪(p / ‖g‖ ^ 2) • g, (p / ‖g‖ ^ 2) • g⟫ - 2 * ⟪(p / ‖g‖ ^ 2) • g, c⟫ + κ = 0) ∧
    (∀ σ : ℝ, σ * (p + A) = 3 * p →
      ⟪(σ / 2) • vi, (σ / 2) • vi⟫ - 2 * ⟪(σ / 2) • vi, c⟫ + κ = 0) := by
  have h10 : ⟪w1, w0⟫ = p := by rw [real_inner_comm]; exact h01
  have h20 : ⟪w2, w0⟫ = p := by rw [real_inner_comm]; exact h02
  have h21 : ⟪w2, w1⟫ = p := by rw [real_inner_comm]; exact h12
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    h00, h11, h22, h01, h02, h12, h10, h20, h21] at hm0 hm1 hm2
  have hr := congrArg (fun z => ⟪z, c⟫) hrelv
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hr
  obtain ⟨hκ, hC, hD⟩ := thirteen_scalar (C := ⟪vi, c⟫) (D0 := ⟪w0, c⟫) (D1 := ⟪w1, c⟫)
    (D2 := ⟪w2, c⟫) (κ := κ) hA hB0 hB1 hB2 (by rw [hii] at hV; linarith) (by linarith)
    (by linarith) (by linarith) hr hsum
  refine ⟨hκ, ?_, ?_, ?_⟩
  · simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      h00, h11, h22, h01, h02, h12, h10, h20, h21]
    linarith
  · intro g
    have hgc : ⟪g, c⟫ = (15 * p / 4 + (B0 + B1 + B2) / 4) / 3 := by
      simp only [g, real_inner_smul_left, inner_add_left]; linarith
    have hn : ‖g‖ ^ 2 = (9 * p + B0 + B1 + B2) / 9 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [g, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        h00, h11, h22, h01, h02, h12, h10, h20, h21]
      ring
    have hvg : ⟪vi, g⟫ = p := by
      simp only [g, real_inner_smul_right, inner_add_right, hi0, hi1, hi2]; ring
    have hn0 : ‖g‖ ^ 2 ≠ 0 := by
      intro h0
      have : g = 0 := by
        rw [← real_inner_self_eq_norm_sq] at h0; exact inner_self_eq_zero.mp h0
      rw [this, inner_zero_right] at hvg
      exact hp hvg.symm
    clear_value g
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hgc, hκ, hn]
    have hn9 : 9 * p + B0 + B1 + B2 ≠ 0 := by
      intro h; apply hn0; rw [hn, h]; simp
    field_simp
    linear_combination (-36 * p) * mul_inv_cancel₀ hn9
  · intro σ hσ
    simp only [real_inner_smul_left, real_inner_smul_right, hii]
    linear_combination (σ / 4 - 1 / 2) * hσ - σ * hC + hκ

end Alg

/-! ## 接到四面体上 -/

variable (t : Affine.Simplex ℝ E3 3)

/-- 半径非负的球 s 上的点：X ∈ s ⟺ ⟪X − Q, X − Q⟫ − 2⟪X − Q, c − Q⟫ + pow_s(Q) = 0。 -/
theorem mem_iff_pow {s : Sphere E3} (hr : 0 ≤ s.radius) (Q X : E3) :
    X ∈ s ↔ ⟪X - Q, X - Q⟫ - 2 * ⟪X - Q, s.center - Q⟫ + s.power Q = 0 := by
  rw [mem_sphere, Sphere.power, dist_eq_norm, dist_eq_norm, ← sq_eq_sq₀ (norm_nonneg _) hr,
    show X - s.center = (X - Q) - (s.center - Q) by abel, @norm_sub_sq_real,
    show Q - s.center = -(s.center - Q) by abel, norm_neg, real_inner_self_eq_norm_sq]
  constructor <;> intro h <;> linarith

/-- Fin 4 上的和拆成第 i 项加对面三项。 -/
theorem split4 {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) (i : Fin 4) :
    f 0 + f 1 + f 2 + f 3 =
      f i + f (i.succAbove 0) + f (i.succAbove 1) + f (i.succAbove 2) := by
  have := Fin.sum_univ_succAbove f i
  rw [Fin.sum_univ_four, Fin.sum_univ_three] at this
  rw [this]; abel

theorem face_point (i : Fin 4) (m : Fin 3) :
    (t.faceOpposite i).points m = t.points (i.succAbove m) := by
  rw [Affine.Simplex.faceOpposite_point_eq_point_succAbove]; rfl

/-- 面 i 的重心减 H = (w₀ + w₁ + w₂)/3。 -/
theorem faceCentroid_sub_H (i : Fin 4) :
    (t.faceOpposite i).centroid - H t =
      (1 / 3 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1) + v t (i.succAbove 2)) := by
  rw [Affine.Simplex.centroid, centroid_sub (t.faceOpposite i).points (H t), Fin.sum_univ_three,
    face_point, face_point, face_point]
  norm_num

/-- O − H = (v₀ + v₁ + v₂ + v₃)/2。 -/
theorem O_sub_H : O t - H t = (1 / 2 : ℝ) • (v t 0 + v t 1 + v t 2 + v t 3) := by
  rw [show O t - H t = -(H t - O t) by abel, H_sub_O]
  simp only [v, pt_sub_H, Alg.w]
  module

/-- 定理 1 的证明。 -/
theorem thirteen_main (ho : IsOrthocentric t) (hH : ∀ j, H t ≠ t.points j)
    (i : Fin 4) (s : Sphere E3) (hV : t.points i ∈ s)
    (hN : ∀ X ∈ facePlane t i, X ∈ (t.faceOpposite i).ninePointCircle → X ∈ s) :
    ψ t (Gface t i) ∈ s ∧
    midpoint ℝ (H t) (AffineMap.homothety (O t) (-1 : ℝ) (t.points i)) ∈ s ∧
    midpoint ℝ (H t) ((Ω t).secondInter (t.points i) (H t -ᵥ t.points i)) ∈ s ∧
    s.power (H t) = 3 / 2 * p t := by
  obtain ⟨hp0, hsum4, hrel4⟩ := rel t ho hH
  have hA := A_ne t ho hH
  have hr : 0 ≤ s.radius := (mem_sphere.mp hV) ▸ dist_nonneg
  have hmem := mem_iff_pow hr (H t)
  set c := s.center - H t
  set κ := s.power (H t)
  -- 下标
  have hi0 : i ≠ i.succAbove 0 := (Fin.succAbove_ne i 0).symm
  have hi1 : i ≠ i.succAbove 1 := (Fin.succAbove_ne i 1).symm
  have hi2 : i ≠ i.succAbove 2 := (Fin.succAbove_ne i 2).symm
  have h01 : i.succAbove 0 ≠ i.succAbove 1 := Fin.succAbove_right_injective.ne (by decide)
  have h02 : i.succAbove 0 ≠ i.succAbove 2 := Fin.succAbove_right_injective.ne (by decide)
  have h12 : i.succAbove 1 ≠ i.succAbove 2 := Fin.succAbove_right_injective.ne (by decide)
  -- 核心关系按 i 和对面三点重排
  have hrelv := hrel4
  rw [split4 (fun k => (1 / A t k) • v t k) i] at hrelv
  have hsum := hsum4
  rw [split4 (fun k => 1 / A t k) i] at hsum
  -- 面 i 的棱中点
  set F := t.faceOpposite i
  have hg := faceCentroid_sub_H t i
  have hmid : ∀ m : Fin 3, F.faceOppositeCentroid m ∈ s ∧
      F.faceOppositeCentroid m - H t =
        (1 / 2 : ℝ) • (F.centroid - H t - (F.points m - H t)) + (F.centroid - H t) := by
    intro m
    refine ⟨hN _ ?_ (F.faceOppositeCentroid_mem_ninePointCircle m), ?_⟩
    · exact F.affineSpan_faceOpposite_le m (F.faceOppositeCentroid_mem_affineSpan_face m)
    · rw [Affine.Simplex.faceOppositeCentroid_eq_smul_vsub_vadd_point]
      simp only [vsub_eq_sub, vadd_eq_add]
      norm_num
      abel
  obtain ⟨hm0s, hm0⟩ := hmid 0
  obtain ⟨hm1s, hm1⟩ := hmid 1
  obtain ⟨hm2s, hm2⟩ := hmid 2
  rw [hg, face_point] at hm0 hm1 hm2
  rw [hmem, hm0] at hm0s
  rw [hmem, hm1] at hm1s
  rw [hmem, hm2] at hm2s
  -- 记号：vᵢ 与对面三点 w₀, w₁, w₂（都以 H 为原点）
  have e0 : (1 / 2 : ℝ) • ((1 / 3 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1) +
      v t (i.succAbove 2)) - v t (i.succAbove 0)) + (1 / 3 : ℝ) • (v t (i.succAbove 0) +
      v t (i.succAbove 1) + v t (i.succAbove 2)) =
      (1 / 2 : ℝ) • (v t (i.succAbove 1) + v t (i.succAbove 2)) := by module
  have e1 : (1 / 2 : ℝ) • ((1 / 3 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1) +
      v t (i.succAbove 2)) - v t (i.succAbove 1)) + (1 / 3 : ℝ) • (v t (i.succAbove 0) +
      v t (i.succAbove 1) + v t (i.succAbove 2)) =
      (1 / 2 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 2)) := by module
  have e2 : (1 / 2 : ℝ) • ((1 / 3 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1) +
      v t (i.succAbove 2)) - v t (i.succAbove 2)) + (1 / 3 : ℝ) • (v t (i.succAbove 0) +
      v t (i.succAbove 1) + v t (i.succAbove 2)) =
      (1 / 2 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1)) := by module
  rw [e0] at hm0s
  rw [e1] at hm1s
  rw [e2] at hm2s
  have hVs := (hmem _).mp hV
  obtain ⟨hκ, hanti, hψ, hY⟩ := Alg.thirteen_vec (vi := v t i) (c := c) (κ := κ)
    (hA i) (hA _) (hA _) (hA _) hp0
    (inner_v_self t i) (inner_v_self t _) (inner_v_self t _) (inner_v_self t _)
    (inner_pt_H t ho hi0) (inner_pt_H t ho hi1) (inner_pt_H t ho hi2)
    (inner_pt_H t ho h01) (inner_pt_H t ho h02) (inner_pt_H t ho h12)
    hrelv hsum hVs hm0s hm1s hm2s
  -- O − H 用 vᵢ 和对面三点表示
  have hOH := O_sub_H t
  rw [split4 (v t) i] at hOH
  refine ⟨?_, ?_, ?_, by rw [hκ]; ring⟩
  · -- ψ(Gᵢ)
    rw [hmem, show ψ t (Gface t i) - H t =
      (p t / ‖Gface t i - H t‖ ^ 2) • (Gface t i - H t) by simp [ψ]]
    rw [show Gface t i = F.centroid from rfl, hg]
    exact hψ
  · -- H 与 Vᵢ 的对径点的中点
    rw [hmem, show midpoint ℝ (H t) (AffineMap.homothety (O t) (-1 : ℝ) (t.points i)) - H t =
        (1 / 2 : ℝ) • (v t (i.succAbove 0) + v t (i.succAbove 1) + v t (i.succAbove 2)) by
      rw [midpoint_eq_smul_add, AffineMap.homothety_apply,
        show O t = H t + (O t - H t) by abel, hOH]
      simp only [vsub_eq_sub, vadd_eq_add, invOf_eq_inv, v]
      module]
    exact hanti
  · -- H 与 Yᵢ 的中点
    have hNi : ⟪v t i, v t i⟫ ≠ 0 := by
      intro h0
      exact hH i (sub_eq_zero.mp (inner_self_eq_zero.mp h0)).symm
    set τ := -2 * ⟪H t -ᵥ t.points i, t.points i -ᵥ (Ω t).center⟫ /
      ⟪H t -ᵥ t.points i, H t -ᵥ t.points i⟫ with hτ
    have hc : (Ω t).center = O t := t.circumsphere_center
    have hin : ⟪H t -ᵥ t.points i, t.points i -ᵥ (Ω t).center⟫ =
        -(p t + A t i) / 2 + 3 * p t / 2 := by
      rw [hc, vsub_eq_sub, vsub_eq_sub,
        show H t - t.points i = -v t i by simp [v],
        show t.points i - O t = v t i - (O t - H t) by simp [v], hOH, inner_neg_left,
        inner_sub_right, real_inner_smul_right, inner_v_self, inner_add_right, inner_add_right,
        inner_add_right, inner_v_self, inner_pt_H t ho hi0, inner_pt_H t ho hi1,
        inner_pt_H t ho hi2]
      ring
    have hnn : ⟪H t -ᵥ t.points i, H t -ᵥ t.points i⟫ = p t + A t i := by
      rw [vsub_eq_sub, show H t - t.points i = -v t i by simp [v], inner_neg_neg, inner_v_self]
    have hNi' : p t + A t i ≠ 0 := by rwa [← inner_v_self]
    rw [hmem, show midpoint ℝ (H t) ((Ω t).secondInter (t.points i) (H t -ᵥ t.points i)) - H t =
        ((1 - τ) / 2) • v t i by
      rw [midpoint_eq_smul_add, Sphere.secondInter]
      simp only [vsub_eq_sub, vadd_eq_add, invOf_eq_inv, v]
      module]
    apply hY
    rw [hτ, hin, hnn]
    field_simp
    ring

end GeometryResearch.Orthocentric
