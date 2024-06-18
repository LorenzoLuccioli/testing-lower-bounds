/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Testing.Binary
import TestingLowerBounds.FDiv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Convex.Deriv

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

--need some hp on the existence of the limit?
lemma slope_tendsto_rightDeriv (f : ℝ → ℝ) (x : ℝ) : Filter.Tendsto (fun y ↦ (f y - f x) / (y - x)) (𝓝[>] x) (𝓝 (rightDeriv f x)) := by sorry

example (f : ℝ → ℝ)  : rightDeriv f = 0 := by
  ext x
  unfold rightDeriv
  unfold derivWithin
  unfold fderivWithin
  simp

  sorry

#check Monotone.tendsto_nhdsWithin_Iio
-- theorem Monotone.tendsto_nhdsWithin_Iio {α β : Type*} [LinearOrder α] [TopologicalSpace α]
--     [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
--     {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
--   rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
--   refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
--   · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
--       simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
--         exists_lt_of_lt_csSup (h.image _) hl
--     exact mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun y hy => lz.trans_le (Mf hy.1.le)
--   · refine mem_of_superset self_mem_nhdsWithin fun _ hy => lt_of_le_of_lt ?_ hm
--     exact le_csSup (Mf.map_bddAbove bddAbove_Iio) (mem_image_of_mem _ hy)
-- #align monotone.tendsto_nhds_within_Iio Monotone.tendsto_nhdsWithin_Iio

lemma MonotoneOn.tendsto_nhdsWithin_Iio {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x : α} (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAbove (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h.image _) hl
    exact mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun y hy => lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

--This alternative version works with monotonicity on finite intervals, but requires the first space to be densely ordered to handle the case where Ioo y x = ∅
lemma MonotoneOn.tendsto_nhdsWithin_Iio' {α β : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Mf : MonotoneOn f (Ioo y x))
    (h_bdd : BddAbove (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x))) := by
  -- rcases eq_empty_or_nonempty (Ioo y x) with (h | h)
  -- · exact (not_nonempty_empty (h ▸ nonempty_Ioo.mpr hxy)).elim
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : ∃ a : α, a ∈ Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    refine mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun w hw => ?_
    exact lz.trans_le <| Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  ·
    have ⟨_, ha, hb⟩ := h_nonempty
    have hxy : y < x := by exact h_nonempty.2.1.trans h_nonempty.2.2
    refine mem_of_superset (Ioo_mem_nhdsWithin_Iio' hxy) fun w hw => lt_of_le_of_lt ?_ hm
    refine le_csSup h_bdd (mem_image_of_mem _ ?_)
    simp [hw]

--this may be something to write on zulip, there should not be any bugs with (kernel)
lemma MonotoneOn.tendsto_nhdsWithin_Iio' {α β : Type*} [LinearOrder α]
    {x y : α} (h_nonempty : (Ioo y x).Nonempty) :
    True := by
  have ⟨_, ha, hb⟩ := h_nonempty
  have hxy : y < x := by exact ha.trans hb --this works
  have hxy : y < x := by exact h_nonempty.2.1.trans h_nonempty.2.2 --this does not work
  simp

--this is already in mathlib, this is just an alternative proof using the more general version, if we substitute it remove the prime (') at the end of the name
/-- A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (Iio x))`. -/
theorem Monotone.tendsto_nhdsWithin_Iio' {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsWithin_Iio (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

namespace Convex

lemma hasRightDerivAt_of_convexOn {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hfc : ConvexOn ℝ S f) (hx : x ∈ S) :
    DifferentiableWithinAt ℝ f (Set.Ioi x) x := by
  unfold DifferentiableWithinAt
  simp_rw [hasFDerivWithinAt_iff_hasDerivWithinAt]
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]


  --we need some lemma that says that if a function is monotone then it has a right limit at every point, we have

  use 0
  --say that the incremental ratio is increasing

  -- have h_monotone :
  --so there exist a limit

  --use that limit as f'
  --show that the limit satisfies the definition of derivative
  sorry

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

lemma hasRightDerivAt_of_convexOn {S : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hfc : ConvexOn ℝ S f) (hx : x ∈ S) :
    DifferentiableWithinAt ℝ f (Set.Ioi x) x := by

  --say that the incremental ratio is increasing

  -- have h_monotone :
  --so there exist a limit

  --use that limit as f'
  --show that the limit satisfies the definition of derivative
  sorry

#check convexOn_iff_slope_mono_adjacent
#check ConvexOn.right_deriv_le_slope

noncomputable
def _root_.StieltjesFunction.rightDeriv_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) : StieltjesFunction where
  toFun := rightDeriv f
  mono' _ _ := by
    refine ConvexOn.monotoneOn_derivWithin ?_ ?_
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
  right_continuous' _ := sorry

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
