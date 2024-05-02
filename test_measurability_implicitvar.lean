import Mathlib.Probability.Kernel.Basic

/-Issue: if we use the tactic `measurability` in the proof of some result when there is a kernel
already defined as a variable in our environment, then this kernel becomes a required argument for
the lemma, even if it is otherwise never mentioned in the statement or proof of the lemma -/

open Real MeasureTheory

variable {α : Type*} {μ : Measure ℝ} {k : ProbabilityTheory.kernel ℝ ℝ}

lemma my_lemma1 : Measurable fun (x : ℝ) ↦ x := by
  measurability

/-
my_lemma1 {k : ↥(ProbabilityTheory.kernel ℝ ℝ)} : Measurable fun x => x
-/
#check my_lemma1
-- In this case k is required as an argument, even if it does not appear in the lemma at all


lemma my_lemma2 : Measurable fun (x : ℝ) ↦ x := by
  exact fun ⦃t⦄ a => a

/-
my_lemma2 : Measurable fun x => x
-/
#check my_lemma2
/- The problem does not appear if we avoid using the measurability tactic; it is likely caused by
the fact that measurability automatically gives a name to the kernel that we defined implicitely,
so, even if it is not used in the lemma, it becomes an argument. -/


lemma my_lemma3 {k : ProbabilityTheory.kernel ℝ ℝ} : Measurable fun (x : ℝ) ↦ x := by
  measurability

/-
my_lemma3 {k k : ↥(ProbabilityTheory.kernel ℝ ℝ)} : Measurable fun x => x
-/
#check my_lemma3
/- If we try to declare the kernel as an argument explicitly in the statement, we end up with a
lemma that requires both kernels (and they have the same name) -/

/- Note that this does not happen with the measure μ, that is also defined as a variable, just like
k, so the problem has likely something to do with kernels in  particular. -/
