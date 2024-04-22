import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

example {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (s : (i : ι) → Set (β i)) (h : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.pi Set.univ s) := by
  -- measurability --this should be able to close the goal, but is doesn't
  exact MeasurableSet.univ_pi h
