import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

namespace MeasurableSpace

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-I'm not sure this is the right way to state those facts, maybe they should just be lemmas?
I cannot put the Nonempty α as a hypothesis because then α would not be mentioned in the thesis
and that is not allowed in a typeclass instance. Anyway I feel that in this way they are not very
useful because it seems that the typeclass inference is not able to use them.-/
--solution: state those as lemmas

lemma countable_left_of_prod_of_nonempty [Nonempty β] (h : Countable (α × β)) : Countable α := by
  contrapose h
  rw [not_countable_iff] at *
  infer_instance

lemma countable_right_of_prod_of_nonempty [Nonempty α] (h : Countable (α × β)) : Countable β := by
  contrapose h
  rw [not_countable_iff] at *
  infer_instance

--TODO: what name should we use? in this name the first 'left' refers to the fact that we are talking about `α`, which is the left factor in the product, the second 'left' refers to the fact that the product is on the left argument of `CountableOrCountablyGenerated`
lemma countableOrCountablyGenerated_left_of_prod_left_of_nonempty [Nonempty β]
    [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated α γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · have := countable_left_of_prod_of_nonempty h
    infer_instance
  · infer_instance

lemma countableOrCountablyGenerated_right_of_prod_left_of_nonempty [Nonempty α]
    [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated β γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · have := countable_right_of_prod_of_nonempty h
    infer_instance
  · infer_instance

--it would be nice to have also the following lemmas. I think they are true, but I cannot be sure,
--because I cannot prove them even informally.
--this seems like exactly what I'm looking for:
--https://math.stackexchange.com/questions/3413063/if-product-sigma-field-is-countably-generated-is-each-factor
--is it worth it to formalize that proof? I may need to formalize also the hint, if I don't find it on mathlib, this may take a bit of time but I think it may be worth it. However I have to decide whether to do it now or later.

lemma countablyGenerated_left_of_prod_of_nonempty [Nonempty β] (h : CountablyGenerated (α × β)) : CountablyGenerated α := by
  -- contrapose h
  sorry

lemma countablyGenerated_right_of_prod_of_nonempty [Nonempty α] (h : CountablyGenerated (α × β)) : CountablyGenerated β := by
  -- contrapose h
  sorry


lemma countableOrCountablyGenerated_right_of_prod_right_of_nonempty [Nonempty β]
    [h : CountableOrCountablyGenerated α (β × γ)] :
    CountableOrCountablyGenerated α γ := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · infer_instance
  · have := countablyGenerated_right_of_prod_of_nonempty h
    infer_instance

lemma countableOrCountablyGenerated_left_of_prod_right_of_nonempty [Nonempty γ]
    [h : CountableOrCountablyGenerated α (β × γ)] :
    CountableOrCountablyGenerated α β := by
  rcases h.countableOrCountablyGenerated with (h | h)
  · infer_instance
  · have := countablyGenerated_left_of_prod_of_nonempty h
    infer_instance


instance [Countable (α × β)] : Countable (β × α) :=
  Countable.of_equiv _ (Equiv.prodComm α β)

instance [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated (β × α) γ := by
  rcases h with (h | h)
  · exact ⟨Or.inl inferInstance⟩
  · exact ⟨Or.inr h⟩

--TODO: prove this, it may be useful to prove the analogous of Countable.of_equiv for CountablyGenerated, this may require a measurable equivalence. It should be a useful result to have in mathlib anyway.
instance [CountablyGenerated (α × β)] : CountablyGenerated (β × α) := by
  sorry

instance [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated (β × α) γ := by
  rcases h with (h | h)
  · exact ⟨Or.inl inferInstance⟩
  · exact ⟨Or.inr h⟩
