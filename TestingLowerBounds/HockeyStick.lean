/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Testing.Binary
import TestingLowerBounds.FDiv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Deriv
import TestingLowerBounds.ForMathlib.MonotoneOnTendsto
import TestingLowerBounds.ForMathlib.LeftRightDeriv

/-!
# Hockey-stick divergence

## Main definitions

## Main statements

## Notation

## Implementation details

-/

open MeasureTheory


open Set Filter

open Topology

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

--we still have to figure out if the right condition is γ < 1 or γ ≤ 1
noncomputable
def hockeyStickFun (γ x : ℝ) : ℝ := if γ < 1 then max 0 (γ - x) else max 0 (x - γ)

noncomputable
def eGamma (γ : ℝ) (μ ν : Measure 𝒳) : EReal := fDiv (hockeyStickFun γ) μ ν
  -- right_continuous' _ := sorry

noncomputable
def curvatureMeasure (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : Measure ℝ :=
  (StieltjesFunction.rightDeriv_of_convex f hf).measure




#check Monotone.ae_hasDerivAt --this should solve the problem in the proof where we were not sure how to proceed
lemma generalized_taylor (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) {a b : ℝ} :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x, |b - x| ∂(curvatureMeasure f hf) := --the statement is wrong, the integral should go only from min a b to max a b, but I need to understand how to write this, since now the domain of the measure is s, not ℝ. Don't do it like this, because then every time we would have to rewrite that min and max, instead do 2 versions of the theorem, one for a < b and one for a > b
  sorry


lemma fun_eq_interal_hockeyStickFun_curvatureMeasure (f : ℝ → ℝ) (hf_cvx : ConvexOn ℝ univ f) (hf_one : f 1 = 0) (hfderiv_one : _root_.rightDeriv f 1 = 0) :
    f = fun x ↦ ∫ y, hockeyStickFun y x ∂(curvatureMeasure f hf_cvx) :=
  sorry

/-things needed:
- the right derivative of a function ✓
  - the right derivative of a convex function at a point is greater than its left derivative ✓
- the fact that if f is convex its right derivative is a stieltjes function ✓
- the stieltjes file only handles functions ℝ → ℝ, do we do the same or do we want to generalize to functions on subsets of ℝ? for example we may want to only consider functions on (0,∞), as they do in the paper Phi-divergences, sufficiency..., moreover the functions we have for the f divergences are convex only on half the real line, so it may be necessary to generalize the stieltjes file. solution: do everything on ℝ, then we can show that for every convex function on (0,∞) we can find a convex function on ℝ that coincides with the original on (0,∞) just by extending it to a linear function with slope equal to the right derivative at 0 on the negavites
- how to handle the integral in the generalized taylor theorem, since the measure is defined on a subset of ℝ, not on all of ℝ and I need to further restrict that to the interval [min a b, max a b]
-/


end ProbabilityTheory
-- strange error:
--Error while replacing abbreviation: Error: TextEditor#edit not possible on closed editors
