/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd
import TestingLowerBounds.ForMathlib.IntegralCongr2
import TestingLowerBounds.ForMathlib.KernelFstSnd
import TestingLowerBounds.ForMathlib.MulLog

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal BigOperators

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

open MeasureTheory



variable {f g : α → β}
variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

--This is a generalization of the next lemma, the proof doesn't work, though, there is some kind of type problem
-- lemma MeasureTheory.AEStronglyMeasurable_add_iff_integrable_right [TopologicalSpace β] [Add β] [ContinuousAdd β] [Neg β] [ContinuousNeg β] [AddCommGroup β] {f g : α → β} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (f + g) μ ↔ AEStronglyMeasurable g μ := by
--   constructor <;> intro h
--   · have : g = f + g + (-f) := by
--       ext a
--       simp only [Pi.add_apply, Pi.neg_apply]
--       convert (add_neg_cancel_comm (f a) (g a)).symm using 2

--       rw [add_neg_cancel_comm (f a) (g a)]
--       simp [add_neg_cancel_comm, add_zero]
--     rw [this]
--     exact h.add hf.neg
--   · exact hf.add h

--TODO: put this in te right place, and PR this to mathlib, moreover write similar results for measurable, aemeasurable ecc...
--TODO: this result shouold not require β to be a NormedAddCommGroup, it should be enough to have a topological space and a few other hypothesys on the  continuity of the sum and the negation, but for some reason it doesn't work, there seems to be some type problem
lemma AEStronglyMeasurable_add_iff_integrable_right [NormedAddCommGroup β] {f g : α → β} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (f + g) μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun h ↦ show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h ↦ hf.add h⟩

lemma AEStronglyMeasurable_add_iff_integrable_left [NormedAddCommGroup β]  {f g : α → β} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (g + f) μ ↔ AEStronglyMeasurable g μ := by
  rw [add_comm, AEStronglyMeasurable_add_iff_integrable_right hf]

--decide what to do with this, then do the same for measurable, strongly measurable, aemeasurable ecc...

--there is also another question, the lemmas in the strongly_measurable file have the attribute to_additive, should I do the same here? is it even true in the multiplicative case? because I guess I would have to add some commutativity hypothesis
--maybe they can be put in the same section as:
#check MeasureTheory.AEStronglyMeasurable.mul

end MeasureTheory
