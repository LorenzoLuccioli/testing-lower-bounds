import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

namespace MeasurableSpace

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/--I'm not sure this is the right way to state those facts, maybe they should just be lemmas?
I cannot put the Nonempty α as a hypothesis because then α would not be mentioned in the thesis
and that is not allowed in a typeclass instance. Anyway I feel that in this way they are not very
useful because it seems that the typeclass inference is not able to use them.-/

instance instOrIsEmptyCountableOfProd [h : Countable (α × β)] : IsEmpty α ∨ Countable β := by
  by_contra! h1
  rw [not_isEmpty_iff, not_countable_iff] at h1
  rcases h1 with ⟨_, _⟩
  have h' : Uncountable (α × β) := instUncountableProdOfNonempty_1
  rw [← not_countable_iff] at h'
  exact h' h

instance instOrCountableIsEmptyOfProd [h : Countable (α × β)] : Countable α ∨ IsEmpty β := by
  by_contra! h1
  rw [not_isEmpty_iff, not_countable_iff] at h1
  rcases h1 with ⟨_, _⟩
  have h' : Uncountable (α × β) := inferInstance
  rw [← not_countable_iff] at h'
  exact h' h

instance {γ : Type*} [MeasurableSpace γ] [h : CountableOrCountablyGenerated (α × β) γ] :
    IsEmpty β ∨ CountableOrCountablyGenerated α γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · by_cases hβ : IsEmpty β
    · exact Or.inl hβ
    simp only [hβ, false_or]
    refine ⟨Or.inl ?_⟩
    have := instOrCountableIsEmptyOfProd (h := h)
    tauto
  · right
    infer_instance

instance {γ : Type*} [MeasurableSpace γ] [h : CountableOrCountablyGenerated (α × β) γ] :
    IsEmpty α ∨ CountableOrCountablyGenerated β γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · by_cases hα : IsEmpty α
    · exact Or.inl hα
    simp only [hα, false_or]
    refine ⟨Or.inl ?_⟩
    have := instOrIsEmptyCountableOfProd (h := h)
    tauto
  · right
    infer_instance
