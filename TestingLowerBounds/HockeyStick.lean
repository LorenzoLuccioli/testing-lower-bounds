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
#check Monotone.tendsto_rightLim

#check hasDerivWithinAt_iff_tendsto_slope
--put this in the right namespace, or better find the equivalent definition in mathlib
noncomputable
def rightDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Set.Ioi x) x

lemma rightDeriv_def (f : ℝ → ℝ) (x : ℝ) : rightDeriv f x = derivWithin f (Set.Ioi x) x := rfl

noncomputable
def leftDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Set.Iio x) x

lemma leftDeriv_def (f : ℝ → ℝ) (x : ℝ) : leftDeriv f x = derivWithin f (Set.Iio x) x := rfl

lemma rightDeriv_eq_leftDeriv (f : ℝ → ℝ) (x : ℝ) :
    rightDeriv f x = - leftDeriv (f ∘ fun y ↦ -y) (-x) := by
  have h_map : MapsTo (fun y ↦ -y) (Set.Iio (-x)) (Set.Ioi x) :=
    fun _ hy ↦ mem_Ioi.mpr (lt_neg_of_lt_neg hy)
  have h_map' : MapsTo (fun y ↦ -y) (Set.Ioi x) (Set.Iio (-x)) :=
    fun _ hy ↦ mem_Iio.mpr (neg_lt_neg hy)
  by_cases hf_diff : DifferentiableWithinAt ℝ f (Ioi x) x
  swap
  · rw [rightDeriv_def, leftDeriv_def, derivWithin_zero_of_not_differentiableWithinAt hf_diff,
      derivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    contrapose! hf_diff
    convert DifferentiableWithinAt.comp x hf_diff ((differentiable_neg _).differentiableWithinAt)
      h_map' using 1
    simp [Function.comp.assoc]
  simp_rw [leftDeriv]
  rw [derivWithin.comp _ ((neg_neg x).symm ▸ hf_diff) (differentiable_neg _).differentiableWithinAt
    h_map (uniqueDiffWithinAt_Iio (-x)), neg_neg, ← rightDeriv_def, derivWithin_neg]
  swap; · exact uniqueDiffWithinAt_Iio _
  simp only [mul_neg, mul_one, neg_neg]

--need some hp on the existence of the limit? We probabily don't need this lemma
lemma slope_tendsto_rightDeriv (f : ℝ → ℝ) (x : ℝ) : Filter.Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by sorry

namespace Convex

section Slope

variable {𝕜 : Type*} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}

--this could be put either in `Mathlib.Analysis.Convex.Slope` or in `Mathlib.LinearAlgebra.AffineSpace.Slope`, but either way I would have to import the other file. Maybe there is some more suitable file that already imports both.
-- try to do a draft PR in mathlib adding it to Convex.Slope, the github bot should tell us how much of a change it is to add the import, then we can decide if it's worth it
lemma slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) : MonotoneOn (slope f x) (s \ {x}) := by
  intro y hy z hz hz'
  simp_rw [slope_def_field]
  exact ConvexOn.secant_mono hfc hx (mem_of_mem_diff hy) (mem_of_mem_diff hz)
    (not_mem_of_mem_diff hy :) (not_mem_of_mem_diff hz :) hz'

lemma bddBelow_slope_Ioi_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨(slope f x (x - 1)), fun y ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc trivial (by simp) (mem_diff_of_mem trivial (mem_Ioi.mp hz).ne')
    (by linarith [mem_Ioi.mp hz])

lemma bddAbove_slope_Iio_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    BddAbove (slope f x '' Iio x) := by
  refine bddAbove_iff_subset_Iic.mpr ⟨(slope f x (x + 1)), fun y ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  exact slope_mono hfc (mem_univ x) (mem_diff_of_mem trivial (mem_Iio.mp hz).ne) (by simp)
    (by linarith [mem_Iio.mp hz])

end Slope


#check convexOn_iff_slope_mono_adjacent

-- TODO: this can be generalized to a set S, where the function is convex, but I still need to figure out what hp to require, since the minimal assumption I think is that there exist a right interval of x that is contained in S (so x itself does not have to be in S), i.e. (x, y) ⊆ S, I don't know if. To generalize we will need MonotoneOn.tendsto_nhdsWithin_Ioo_right. However there are dirrerent kinds of sufficient conditions that could be given, for example S open and x in S or x in the interior of S. Discuss this with Remy. Maybe the minimal hp I described is not sufficient, I also need to assure some kind of boundedness of the slope, this should be assured if x is in the interior of S, because then we can take a point to the left of x but still inside S and use the monotonicity of the solpe in S, but can we do better?
--maybe this should be modified to use hasderivwithinat instead of differentiablewithinat, and then prove this using that version, so we already have the info of what is the derivative
lemma hasRightDerivAt_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Set.Ioi x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Set.Ioi x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y hy z hz hz' ↦ ?_
    simp_rw [slope_def_field]
    exact ConvexOn.secant_mono hfc trivial trivial trivial (Ne.symm (ne_of_lt hy))
      (Ne.symm (ne_of_lt hz)) hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Ioi h_mono (bddBelow_slope_Ioi_of_convexOn x hfc)

--maybe this isn0t even really needed, anyway it may be worth it to change the name, same with the left version
lemma hasRightDerivAt_of_convexOn' {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    DifferentiableWithinAt ℝ f (Set.Ioi x) x :=
  (hasRightDerivAt_of_convexOn x hfc).differentiableWithinAt

lemma hasLeftDerivAt_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    HasDerivWithinAt f (sSup (slope f x '' Iio x)) (Set.Iio x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Set.Iio x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y hy z hz hz' ↦ ?_
    simp_rw [slope_def_field]
    exact ConvexOn.secant_mono hfc trivial trivial trivial (Ne.symm (ne_of_gt hy))
      (Ne.symm (ne_of_gt hz)) hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Iio h_mono (bddAbove_slope_Iio_of_convexOn x hfc)

lemma hasLeftDerivAt_of_convexOn' {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    DifferentiableWithinAt ℝ f (Set.Iio x) x :=
  (hasLeftDerivAt_of_convexOn x hfc).differentiableWithinAt

lemma rightDeriv_eq_sInf_slope_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    rightDeriv f x = sInf (slope f x '' Ioi x) :=
  (hasRightDerivAt_of_convexOn x hfc).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma leftDeriv_eq_sSup_slope_of_convexOn {f : ℝ → ℝ} (x : ℝ) (hfc : ConvexOn ℝ univ f) :
    leftDeriv f x = sSup (slope f x '' Iio x) :=
  (hasLeftDerivAt_of_convexOn x hfc).derivWithin (uniqueDiffWithinAt_Iio x)

--we want some version of ConvexOn.monotoneOn_derivWithin that works for the right derivative, we cannot directly use this because here the set S is fixed, while in our case it depends on x
--but first we need to show that the function is actually differentiable. maybe for now I prove this lemma with this hp and then we prove the differentiability and remove the hp
#check ConvexOn.monotoneOn_derivWithin
#check ConvexOn.right_deriv_le_slope
#check ConvexOn.slope_le_left_deriv
-- lemma monotoneOn_derivWithin (hfc : ConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
--     MonotoneOn (derivWithin f S) S := by
--   intro x hx y hy hxy
--   rcases eq_or_lt_of_le hxy with rfl | hxy'
--   · rfl
--   exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
--     (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

lemma monotoneOn_rightDeriv {S : Set ℝ} {f : ℝ → ℝ} (hfc : ConvexOn ℝ S f)
    (hfrd : ∀ x ∈ S, DifferentiableWithinAt ℝ f (Set.Ioi x) x)
    (hfld : ∀ x ∈ S, DifferentiableWithinAt ℝ f (Set.Iio x) x) :
    MonotoneOn (rightDeriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  unfold rightDeriv
  have h1 := ConvexOn.right_deriv_le_slope hfc hx hy hxy' (hfrd x hx)
  have h2 := ConvexOn.slope_le_left_deriv hfc hx hy hxy' (hfld y hy)
  have h3 := h1.trans h2
  refine h3.trans ?_





  sorry

  -- exact (hfc.rightDeriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_rightDeriv hx hy hxy' (hfd y hy))


lemma rightDeriv_mono (f : ℝ → ℝ) (h : ConvexOn ℝ Set.univ f) (x y : ℝ) (hxy : x ≤ y) : rightDeriv f x ≤ rightDeriv f y := by

  sorry


#check convexOn_iff_slope_mono_adjacent
#check ConvexOn.right_deriv_le_slope

noncomputable
def _root_.StieltjesFunction.rightDeriv_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) : StieltjesFunction where
  toFun := rightDeriv f
  mono' _ _ := by
    -- refine ConvexOn.monotoneOn_derivWithin ?_ ?_
    sorry
  right_continuous' _ := by sorry


end Convex


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
def curvatureMeasure (f : ℝ → ℝ) {s : Set ℝ} (hf : ConvexOn ℝ s f) : Measure s := sorry
-- (StieltjesFunction.rightDeriv f hf).measure




#check Monotone.ae_hasDerivAt --this should solve the problem in the proof where we were not sure how to proceed
lemma generalized_taylor (f : ℝ → ℝ) {s : Set ℝ} (hf : ConvexOn ℝ s f) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x, |b - x| ∂(curvatureMeasure f hf) := --the statement is wrong, the integral should go only from min a b to max a b, but I need to understand how to write this, since now the domain of the measure is s, not ℝ
  sorry


lemma fun_eq_interal_hockeyStickFun_curvatureMeasure (f : ℝ → ℝ) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_one : f 1 = 0) (hfderiv_one : _root_.rightDeriv f 1 = 0) :
    f = fun x ↦ ∫ y, hockeyStickFun y x ∂(curvatureMeasure f hf_cvx) :=
  sorry

/-things needed:
- the right derivative of a function
  - the right derivative of a convex function at a point is greater than its left derivative
- the fact that if f is convex its right derivative is a stieltjes function
- the stieltjes file only handles functions ℝ → ℝ, do we do the same or do we want to generalize to functions on subsets of ℝ? for example we may want to only consider functions on (0,∞), as they do in the paper Phi-divergences, sufficiency..., moreover the functions we have for the f divergences are convex only on half the real line, so it may be necessary to generalize the stieltjes file. solution: do everything on ℝ, then we can show that for every convex function on (0,∞) we can find a convex function on ℝ that coincides with the original on (0,∞) just by extending it to a linear function with slope equal to the right derivative at 0 on the negavites
- how to handle the integral in the generalized taylor theorem, since the measure is defined on a subset of ℝ, not on all of ℝ and I need to further restrict that to the interval [min a b, max a b]
-/


end ProbabilityTheory
