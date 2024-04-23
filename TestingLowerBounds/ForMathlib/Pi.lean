import Mathlib.MeasureTheory.Constructions.Pi

open Real MeasureTheory Filter MeasurableSpace

namespace MeasureTheory.Measure
open MeasureTheory.Measure

--TODO: I define the instances for Measure.pi to be finite or a probability measure, I think they are not in mathlib, or at least I didn't find them. if we keep them we should check the names
--we could put them just below MeasureTheory.Measure.pi.sigmaFinite
#check MeasureTheory.Measure.pi.sigmaFinite

variable {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : ι) → Measure (α i))

instance pi.instIsFiniteMeasure [∀ i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (Measure.pi μ) := by
  constructor
  rw [Measure.pi_univ]
  exact ENNReal.prod_lt_top (fun i _ ↦ measure_ne_top (μ i) _)

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsFiniteMeasure (volume : Measure (α i))] :
    IsFiniteMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsFiniteMeasure _

instance pi.instIsProbabilityMeasure [∀ i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) := by
  constructor
  simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]

instance {α : ι → Type*} [∀ i, MeasureSpace (α i)] [∀ i, IsProbabilityMeasure (volume : Measure (α i))] :
    IsProbabilityMeasure (volume : Measure (∀ i, α i)) :=
  pi.instIsProbabilityMeasure _
