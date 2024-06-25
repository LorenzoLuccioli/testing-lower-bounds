/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.Stieltjes
import Mathlib.MeasureTheory.Integral.FundThmCalculus


/-!
# Hockey-stick divergence

## Main definitions

## Main statements

## Notation

## Implementation details

-/

open MeasureTheory


open Set Filter

open Topology StieltjesFunction

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {f : ℝ → ℝ} {γ x t : ℝ}

noncomputable
def statInfoFun (β γ x : ℝ) : ℝ := if γ ≤ β then max 0 (γ - β * x) else max 0 (β * x - γ)

--TODO: for now I will leave the continuity assumption in some lemmas, it should be derived from the convexity but the lemma is not yet in mathlib, when it gets there we can remove this assumption

--There are two ways to separate the cases: `γ ≤ 1` and `γ > 1` or `γ < 1` and `γ > 1`. The first one seems the correct one for now.

--we still have to figure out if the right condition is γ < 1 or γ ≤ 1
noncomputable
def hockeyStickFun (γ x : ℝ) : ℝ := if γ ≤ 1 then max 0 (γ - x) else max 0 (x - γ)

lemma hockeyStickFun_nonneg (γ x : ℝ) : 0 ≤ hockeyStickFun γ x := by
  simp_rw [hockeyStickFun]
  split_ifs <;> simp

lemma hockeyStickFun_of_le_one (h : γ ≤ 1) : hockeyStickFun γ x = max 0 (γ - x) := if_pos h

lemma hockeyStickFun_of_one_lt (h : 1 < γ) : hockeyStickFun γ x = max 0 (x - γ) := if_neg h.not_le

lemma hockeyStickFun_of_le_one_of_le (h : γ ≤ 1) (hx : x ≤ γ) : hockeyStickFun γ x = γ - x :=
  hockeyStickFun_of_le_one h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma hockeyStickFun_of_le_one_of_ge (h : γ ≤ 1) (hx : x ≥ γ) : hockeyStickFun γ x = 0 :=
  hockeyStickFun_of_le_one h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma hockeyStickFun_of_one_lt_of_le (h : 1 < γ) (hx : x ≤ γ) : hockeyStickFun γ x = 0 :=
  hockeyStickFun_of_one_lt h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma hockeyStickFun_of_one_lt_of_ge (h : 1 < γ) (hx : x ≥ γ) : hockeyStickFun γ x = x - γ :=
  hockeyStickFun_of_one_lt h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

noncomputable
def eGamma (γ : ℝ) (μ ν : Measure 𝒳) : EReal := fDiv (hockeyStickFun γ) μ ν
  -- right_continuous' _ := sorry

--should we define this to be some junk value if f is not convex? this way we could avoid having to state the convexity every time
noncomputable
def curvatureMeasure (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : Measure ℝ :=
  (StieltjesFunction.rightDeriv_of_convex f hf).measure

lemma generalized_taylor (hf : ConvexOn ℝ univ f) (hf_cont : Continuous f) {a b : ℝ} :
    f b - f a - (rightDeriv f a) * (b - a)  = ∫ x in a..b, b - x ∂(curvatureMeasure f hf) := by
  have h_int : IntervalIntegrable (rightDeriv f) ℙ a b := hf.rightDeriv_mono.intervalIntegrable
  rw [← intervalIntegral.integral_eq_sub_of_hasDeriv_right hf_cont.continuousOn
    (fun x _ ↦ hf.hadDerivWithinAt_rightDeriv_of_convexOn x) h_int]
  simp_rw [← neg_sub _ b, intervalIntegral.integral_neg, curvatureMeasure,
    mul_neg, sub_neg_eq_add, mul_comm _ (a - b)]
  let g := StieltjesFunction.id + StieltjesFunction.const (-b)
  have hg : g = fun x ↦ x - b := rfl
  rw [← hg, integral_stieltjes_meas_by_parts g (rightDeriv_of_convex f hf)]
  simp only [Real.volume_eq_stieltjes_id, add_apply, id_apply, id_eq, const_apply, add_right_neg,
    zero_mul, zero_sub, measure_add, measure_const, add_zero, neg_sub, sub_neg_eq_add, g]
  rfl

lemma fun_eq_integral_hockeyStickFun_curvatureMeasure_of_one_le (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    f t = ∫ y, hockeyStickFun y t ∂(curvatureMeasure f hf_cvx) := by
  have h :
      f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure f hf_cvx) :=
    generalized_taylor hf_cvx hf_cont
  rw [hf_one, hfderiv_one, sub_zero, zero_mul, sub_zero] at h
  rw [h]
  rcases le_total t 1 with (ht | ht)
  · simp_rw [intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
    have h : ∀ x ∈ Ioc t 1, x - t = max 0 (x - t) :=
      fun x hx ↦ (max_eq_right (sub_nonneg.mpr hx.1.le)).symm
    rw [setIntegral_congr measurableSet_Ioc h,
      ← setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Iic Ioc_subset_Iic_self]
    swap
    · intro _ ⟨_, _⟩
      simp_all
    have h : ∀ x ∈ Iic 1, max 0 (x - t) = hockeyStickFun x t :=
      fun x hx ↦ (hockeyStickFun_of_le_one hx).symm
    rw [setIntegral_congr measurableSet_Iic h,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_]
    rw [mem_Iic, not_le] at hx
    rw [hockeyStickFun_of_one_lt_of_le hx (ht.trans hx.le)]
  · simp_rw [intervalIntegral.integral_of_le ht]
    have h : ∀ x ∈ Ioc 1 t, t - x = max 0 (t - x) := by aesop
    rw [setIntegral_congr measurableSet_Ioc h,
      ← setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self]
    swap
    · intro _ ⟨_, hxt⟩
      simp_all only [mem_Ioc, mem_Ioi, true_and, not_le, max_eq_left_iff, tsub_le_iff_right, zero_add]
      exact hxt.le
    have h : ∀ x ∈ Ioi 1, max 0 (t - x) = hockeyStickFun x t :=
      fun _ (hx : 1 < _) ↦ (hockeyStickFun_of_one_lt hx).symm
    rw [setIntegral_congr measurableSet_Ioi h,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_]
    rw [mem_Ioi, not_lt] at hx
    exact hockeyStickFun_of_le_one_of_ge hx (hx.trans ht)

--next steps:
-- define statInfoFun and refactor everything in terms of that, delete the hockeystick function




/-things needed:
- the stieltjes file only handles functions ℝ → ℝ, do we do the same or do we want to generalize to functions on subsets of ℝ? for example we may want to only consider functions on (0,∞), as they do in the paper Phi-divergences, sufficiency..., moreover the functions we have for the f divergences are convex only on half the real line, so it may be necessary to generalize the stieltjes file. solution: do everything on ℝ, then we can show that for every convex function on (0,∞) we can find a convex function on ℝ that coincides with the original on (0,∞) just by extending it to a linear function with slope equal to the right derivative at 0 on the negavites
- how to handle the integral in the generalized taylor theorem, since the measure is defined on a subset of ℝ, not on all of ℝ and I need to further restrict that to the interval [min a b, max a b]
-/


end ProbabilityTheory
-- strange error:
--Error while replacing abbreviation: Error: TextEditor#edit not possible on closed editors
--TODO: when finished with these proof remember to update the blueprint and also add the proofs to the blueprint
--todo write StieltjesFunction.measure_Ioi
