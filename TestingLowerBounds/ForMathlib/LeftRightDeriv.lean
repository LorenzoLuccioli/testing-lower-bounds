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


open Set Filter Topology

open scoped ENNReal NNReal

/-- The right derivative of a real function. -/
noncomputable
def rightDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Ioi x) x

lemma rightDeriv_def (f : ℝ → ℝ) (x : ℝ) : rightDeriv f x = derivWithin f (Ioi x) x := rfl

/-- The left derivative of a real function. -/
noncomputable
def leftDeriv (f : ℝ → ℝ) : ℝ → ℝ := fun x ↦ derivWithin f (Iio x) x

lemma leftDeriv_def (f : ℝ → ℝ) (x : ℝ) : leftDeriv f x = derivWithin f (Iio x) x := rfl

lemma rightDeriv_eq_leftDeriv_apply (f : ℝ → ℝ) (x : ℝ) :
    rightDeriv f x = - leftDeriv (fun x ↦ f (-x)) (-x) := by
  change rightDeriv f x = -leftDeriv (f ∘ Neg.neg) (-x)
  have h_map : MapsTo Neg.neg (Iio (-x)) (Ioi x) := fun _ (h : _ < -x) ↦ lt_neg_of_lt_neg h
  have h_map' : MapsTo Neg.neg (Ioi x) (Iio (-x)) := fun _ (h : x < _) ↦ neg_lt_neg h
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

lemma rightDeriv_eq_leftDeriv (f : ℝ → ℝ) :
    rightDeriv f = fun x ↦ - leftDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [rightDeriv_eq_leftDeriv_apply]

lemma leftDeriv_eq_rightDeriv_apply (f : ℝ → ℝ) (x : ℝ) :
    leftDeriv f x = - rightDeriv (fun y ↦ f (-y)) (-x) := by
  simp [rightDeriv_eq_leftDeriv_apply, Function.comp.assoc]

lemma leftDeriv_eq_rightDeriv (f : ℝ → ℝ) :
    leftDeriv f = fun x ↦ - rightDeriv (fun y ↦ f (-y)) (-x) := by
  ext x
  simp [leftDeriv_eq_rightDeriv_apply]

namespace ConvexOn

section Slope

variable {𝕜 : Type*} [LinearOrderedField 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}

--This has already been merged in Mathlib, see #14015. When we bump remove this
lemma slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) : MonotoneOn (slope f x) (s \ {x}) :=
  (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' ↦ hfc.secant_mono hx (mem_of_mem_diff hy)
    (mem_of_mem_diff hz) (not_mem_of_mem_diff hy :) (not_mem_of_mem_diff hz :) hz'

lemma bddBelow_slope_Ioi_of_convexOn {f : ℝ → ℝ} (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddBelow (slope f x '' Ioi x) := by
  refine bddBelow_iff_subset_Ici.mpr ⟨(slope f x (x - 1)), fun y ⟨z, (hz : x < z), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  exact slope_mono hfc trivial (by simp) ⟨trivial, hz.ne'⟩ (by linarith)

lemma bddAbove_slope_Iio_of_convexOn {f : ℝ → ℝ} (hfc : ConvexOn ℝ univ f) (x : ℝ) :
    BddAbove (slope f x '' Iio x) := by
  refine bddAbove_iff_subset_Iic.mpr ⟨(slope f x (x + 1)), fun y ⟨z, (hz : z < x), hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  exact slope_mono hfc (mem_univ x) ⟨trivial, hz.ne⟩ (by simp) (by linarith)

end Slope

variable {f : ℝ → ℝ} (hfc : ConvexOn ℝ univ f)

-- TODO: this can be generalized to a set S, where the function is convex, but I still need to figure out what hp to require, since the minimal assumption I think is that there exist a right interval of x that is contained in S (so x itself does not have to be in S), i.e. (x, y) ⊆ S, I don't know if. To generalize we will need MonotoneOn.tendsto_nhdsWithin_Ioo_right. However there are dirrerent kinds of sufficient conditions that could be given, for example S open and x in S or x in the interior of S. Discuss this with Remy. Maybe the minimal hp I described is not sufficient, I also need to assure some kind of boundedness of the slope, this should be assured if x is in the interior of S, because then we can take a point to the left of x but still inside S and use the monotonicity of the solpe in S, but can we do better? For now we can leave it like this
lemma hasRightDerivAt_of_convexOn (x : ℝ) :
    HasDerivWithinAt f (sInf (slope f x '' Ioi x)) (Ioi x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Ioi x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y hy z hz hz' ↦ ?_
    simp_rw [slope_def_field]
    exact ConvexOn.secant_mono hfc trivial trivial trivial (Ne.symm (ne_of_lt hy))
      (Ne.symm (ne_of_lt hz)) hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Ioi h_mono (bddBelow_slope_Ioi_of_convexOn hfc x)

lemma differentiableWithinAt_Ioi_of_convexOn (x : ℝ) : DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hasRightDerivAt_of_convexOn hfc x).differentiableWithinAt

lemma hadDerivWithinAt_rightDeriv_of_convexOn (x : ℝ) :
    HasDerivWithinAt f (rightDeriv f x) (Ioi x) x :=
  (differentiableWithinAt_Ioi_of_convexOn hfc x).hasDerivWithinAt

lemma hasLeftDerivAt_of_convexOn (x : ℝ) :
    HasDerivWithinAt f (sSup (slope f x '' Iio x)) (Iio x) x := by
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) (Iio x) := by
    refine monotoneOn_iff_forall_lt.mpr fun y hy z hz hz' ↦ ?_
    simp_rw [slope_def_field]
    exact ConvexOn.secant_mono hfc trivial trivial trivial (Ne.symm (ne_of_gt hy))
      (Ne.symm (ne_of_gt hz)) hz'.le
  exact MonotoneOn.tendsto_nhdsWithin_Iio h_mono (bddAbove_slope_Iio_of_convexOn hfc x)

lemma differentiableWithinAt_Iio_of_convexOn (x : ℝ) : DifferentiableWithinAt ℝ f (Iio x) x :=
  (hasLeftDerivAt_of_convexOn hfc x).differentiableWithinAt

lemma hadDerivWithinAt_leftDeriv_of_convexOn (x : ℝ) :
    HasDerivWithinAt f (leftDeriv f x) (Iio x) x :=
  (differentiableWithinAt_Iio_of_convexOn hfc x).hasDerivWithinAt

lemma rightDeriv_eq_sInf_slope_of_convexOn (x : ℝ) : rightDeriv f x = sInf (slope f x '' Ioi x) :=
  (hasRightDerivAt_of_convexOn hfc x).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma leftDeriv_eq_sSup_slope_of_convexOn (x : ℝ) : leftDeriv f x = sSup (slope f x '' Iio x) :=
  (hasLeftDerivAt_of_convexOn hfc x).derivWithin (uniqueDiffWithinAt_Iio x)

lemma rightDeriv_mono : Monotone (rightDeriv f) := by
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [rightDeriv_eq_sInf_slope_of_convexOn hfc]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi_of_convexOn hfc x)
    ⟨y, by simp [hxy]⟩ (le_csInf nonempty_of_nonempty_subtype ?_)
  rintro _ ⟨z, yz, rfl⟩
  rw [slope_comm]
  exact slope_mono hfc trivial ⟨trivial, hxy.ne⟩ ⟨trivial, Ne.symm (ne_of_lt yz)⟩ (hxy.trans yz).le

lemma leftDeriv_mono : Monotone (leftDeriv f) := by
  rw [leftDeriv_eq_rightDeriv]
  change Monotone (- rightDeriv (f ∘ Neg.neg) ∘ Neg.neg)
  refine (Monotone.comp_antitone ?_ fun _ _ h ↦ neg_le_neg_iff.mpr h).neg
  exact rightDeriv_mono (ConvexOn.comp_neg hfc)

lemma leftDeriv_le_rightDeriv : leftDeriv f ≤ rightDeriv f := by
  intro x
  rw [rightDeriv_eq_sInf_slope_of_convexOn hfc, leftDeriv_eq_sSup_slope_of_convexOn hfc]
  refine csSup_le nonempty_of_nonempty_subtype ?_
  rintro _ ⟨z, (zx : z < x), rfl⟩
  refine le_csInf nonempty_of_nonempty_subtype ?_
  rintro _ ⟨y, xy, rfl⟩
  exact slope_mono hfc trivial ⟨trivial, zx.ne⟩ ⟨trivial, (Ne.symm (ne_of_lt xy))⟩ (zx.trans xy).le

lemma rightDeriv_right_continuous_of_convexOn (w : ℝ) :
    ContinuousWithinAt (rightDeriv f) (Ici w) w := by
  simp_rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  have h_lim := MonotoneOn.tendsto_nhdsWithin_Ioi ((rightDeriv_mono hfc).monotoneOn (Ioi w))
    (Monotone.map_bddBelow (rightDeriv_mono hfc) bddBelow_Ioi)
  set l := sInf (rightDeriv f '' Ioi w)
  convert h_lim
  refine (LE.le.le_iff_eq ?_).mp ?_ --any better way to split an equality goal into the two inequalitites?
  · rw [rightDeriv_eq_sInf_slope_of_convexOn hfc]
    refine le_csInf nonempty_of_nonempty_subtype ?_ --is there any way to avoid the rintro here? if I just use fun inside the refine it does not work, it seems that the rfl inside the pattern is not supported by the refine tactic
    rintro _ ⟨y, (wy : w < y), rfl⟩
    have slope_lim : Tendsto (slope f y) (𝓝[>] w) (𝓝 (slope f y w)) := by
      have hf_cont : ContinuousWithinAt f (Ioi w) w := -- I would like to replace this with a lemma that derives the continuity from the convexity, it seems that this result is still not in mathlib, see https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Continuity.20.20of.20convex.20functions, they are in the process of proving it in the LeanCamCombi project
        DifferentiableWithinAt.continuousWithinAt (differentiableWithinAt_Ioi_of_convexOn hfc w)
      exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀
        (sub_ne_zero.2 <| ne_of_lt wy)).smul
        (hf_cont.sub continuousWithinAt_const) |>.tendsto
    rw [slope_comm] at slope_lim
    refine le_of_tendsto_of_tendsto h_lim slope_lim ?_
    rw [← nhdsWithin_Ioo_eq_nhdsWithin_Ioi wy]
    refine eventually_nhdsWithin_of_forall fun z hz ↦ ?_
    rw [slope_comm, rightDeriv_eq_sInf_slope_of_convexOn hfc]
    exact csInf_le (bddBelow_slope_Ioi_of_convexOn hfc z) ⟨y, hz.2, rfl⟩
  · exact ge_of_tendsto h_lim <| eventually_nhdsWithin_of_forall
      fun y hy ↦ rightDeriv_mono hfc (le_of_lt hy)

lemma leftDeriv_left_continuous_convexOn (w : ℝ) : ContinuousWithinAt (leftDeriv f) (Iic w) w := by
  have h_map : MapsTo Neg.neg (Iic w) (Ici (-w)) := fun _ (h : _ ≤ w) ↦ (neg_le_neg_iff.mpr h)
  rw [leftDeriv_eq_rightDeriv]
  change ContinuousWithinAt (- rightDeriv (f ∘ Neg.neg) ∘ Neg.neg) (Iic w) w
  refine ContinuousWithinAt.comp ?_ continuousWithinAt_neg h_map |>.neg
  exact rightDeriv_right_continuous_of_convexOn hfc.comp_neg (-w)

/-- The right derivative of a convex real function is a Stieltjes function. -/
noncomputable
def rightDerivStieltjes (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) :
    StieltjesFunction where
  toFun := rightDeriv f
  mono' _ _ := fun h ↦ ConvexOn.rightDeriv_mono hf h
  right_continuous' _ := ConvexOn.rightDeriv_right_continuous_of_convexOn hf _

end ConvexOn
