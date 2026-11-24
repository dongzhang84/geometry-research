module

public import Mathlib

/-! 冒烟测试：确认 `lake build` 真的在检查证明。 -/

open RealInnerProductSpace

example {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [norm_add_sq_real]
