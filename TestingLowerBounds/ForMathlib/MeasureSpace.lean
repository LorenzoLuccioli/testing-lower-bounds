import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace MeasureTheory.Measure.AbsolutelyContinuous

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

--TODO: PR this, it should go under MeasureTheory.Measure.AbsolutelyContinuous.zero
#check MeasureTheory.Measure.AbsolutelyContinuous.zero

@[simp]
lemma eq_zero_of_ac_zero (h : μ ≪ 0) : μ = 0 := measure_univ_eq_zero.mp (h rfl)
