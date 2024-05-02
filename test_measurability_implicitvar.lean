import Mathlib.Probability.Kernel.Basic

open Real MeasureTheory

variable {α : Type*} {μ : Measure ℝ} {k : ProbabilityTheory.kernel ℝ ℝ}

lemma my_lemma1 (k : ProbabilityTheory.kernel ℝ ℝ) : StronglyMeasurable fun x ↦ x * log x := by
  measurability

/-
my_lemma1 {k : ↥(ProbabilityTheory.kernel ℝ ℝ)} (k : ↥(ProbabilityTheory.kernel ℝ ℝ)) :
  StronglyMeasurable fun x => x * log x
-/
#check my_lemma1
-- In this case the argument k is repeated


lemma my_lemma2 (k : ProbabilityTheory.kernel ℝ ℝ) : StronglyMeasurable fun x ↦ x * log x := by
  refine stronglyMeasurable_id.mul measurable_log.stronglyMeasurable

/-
my_lemma2 (k : ↥(ProbabilityTheory.kernel ℝ ℝ)) : StronglyMeasurable fun x => x * log x
-/
#check my_lemma2
-- The problem does not appear if we avoid using the measurability tactic, it is likely caused by
-- the fact that measurability automatically gives a name to the kernel that we defined implicitely,
-- so, even if it is not used in the lemma, it becomes an argument.


lemma my_lemma3 (μ : Measure ℝ) : StronglyMeasurable fun x ↦ x * log x := by
  measurability

/-
my_lemma3 {k : ↥(ProbabilityTheory.kernel ℝ ℝ)} (μ : Measure ℝ) : StronglyMeasurable fun x => x * log x
-/
#check my_lemma3
-- Here we can notice that the same thing does not happen with the measure, moreover, even if k is
-- not mentioned again in the statement, measurability still picks it up, so it becomes an argument.
