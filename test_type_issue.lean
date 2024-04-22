import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


open MeasureTheory


variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e : ι ≃ ι'} {β : ι' → Type*} [∀ i', MeasurableSpace (β i')] {μ : (i : ι') → Measure (β i)} [∀ (i' : ι'), IsProbabilityMeasure (μ i')]

def em1 : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) := MeasurableEquiv.piCongrLeft (fun i ↦ β i) e

theorem my_theorem : (Measure.pi fun i ↦ μ (e i)) = Measure.map (⇑em1.symm) (Measure.pi μ) := by
  convert Measure.pi_eq ?_
  · infer_instance
  intro s hs
  rw [Measure.map_apply (by measurability)]
  swap; exact MeasurableSet.univ_pi hs
  let s' : (i : ι') → Set (β i) := by
    convert fun i ↦ s (e.symm i)
    exact (Equiv.symm_apply_eq e).mp rfl
  have : em1.symm ⁻¹' Set.pi Set.univ s = Set.pi Set.univ s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    apply e.forall_congr
    intro i
    simp [s', em1, MeasurableEquiv.piCongrLeft]
    convert Iff.rfl

    sorry


  sorry
