import Mathlib

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (f g : α → β) (h : Measurable f ∧ Measurable g)

example : Measurable f := by
  fun_prop --does not work

example : Measurable f := by
  fun_prop [h.left] --does not work

example : Measurable f := by
  have := h.left
  fun_prop --works

example : Measurable f := by
  have := h.left
  fun_prop [h.left]--works
