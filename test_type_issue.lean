import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {e : ι ≃ ι'} {β : ι' → Type*} [∀ i', MeasurableSpace (β i')]
  {μ : (i : ι') → Measure (β i)} [∀ (i' : ι'), IsProbabilityMeasure (μ i')]

def e_meas : ((i : ι) → β (e i)) ≃ᵐ ((i' : ι') → β i') := MeasurableEquiv.piCongrLeft β e

lemma piCongrLeft_apply_apply' :
    (MeasurableEquiv.piCongrLeft (fun i' => β i') e) x (e i) = x i := by
  simp only [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk]
  rw [Equiv.piCongrLeft_apply_apply]


lemma my_theorem : Measure.pi (fun i ↦ μ (e i)) = Measure.map e_meas.symm (Measure.pi μ) := by
  suffices Measure.map e_meas (Measure.pi (fun i ↦ μ (e i))) = Measure.pi μ by
    rw [← this, MeasurableEquiv.map_symm_map]
  symm
  refine Measure.pi_eq (fun s _ ↦ ?_)
  rw [e_meas.measurableEmbedding.map_apply]
  let s' : (i : ι) → Set (β (e i)) := fun i ↦ s (e i)
  have : e_meas ⁻¹' Set.pi Set.univ s = Set.pi Set.univ s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, s']
    symm
    apply e.forall_congr
    intro i
    rw [e_meas]
    convert Iff.rfl
    rw [piCongrLeft_apply_apply']
  rw [this, Measure.pi_pi, Finset.prod_equiv e.symm]
  · simp
  intro i _
  unfold_let s'
  simp only
  congr
  all_goals rw [e.apply_symm_apply]
