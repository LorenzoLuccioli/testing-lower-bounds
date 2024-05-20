import Mathlib.MeasureTheory.Function.L1Space

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] [h : IsEmpty β]
    {f : α → β} {μ : Measure α}

--TODO: put this in mathlib, maybe just after:
#check Integrable.of_finite

@[simp]
lemma Integrable.of_empty {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] [IsEmpty α]
    (f : α → β) (μ : Measure α) : Integrable f μ := Integrable.of_finite μ f

@[simp]
lemma Integrable.of_empty_codomain {α β : Type*} [MeasurableSpace α] [NormedAddCommGroup β] [IsEmpty β]
    {f : α → β} {μ : Measure α} : Integrable f μ := by
  have : IsEmpty α := f.isEmpty
  exact Integrable.of_empty f μ
