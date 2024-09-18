import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring

namespace Example

def Measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) : Prop :=
  ∀ (t : Set β), MeasurableSet t → MeasurableSet (f ⁻¹' t)

theorem add_sub_cancel (a b : ℝ) : b + a - b = a := by
  rw [add_comm]
  rw [add_sub_assoc]
  rw [sub_self]
  exact add_zero a

-- Example of a wrong proof
-- example (a b : ℝ) : b + a - b = a := by
--   exact add_zero a

example (a b : ℝ) : b + a - b = a := by
  rw [add_comm, add_sub_assoc, sub_self, add_zero]

example (a b : ℝ) : b + a - b = a := by
  ring

example (a b : ℝ) (ha_pos : 0 < a) (hb_pos : 0 < b) : 0 < a + b := by
  exact add_pos ha_pos hb_pos

end Example
