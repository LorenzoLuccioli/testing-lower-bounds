/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.ForMathlib.ByParts
import TestingLowerBounds.ForMathlib.LeftRightDeriv
import TestingLowerBounds.ForMathlib.Stieltjes
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Tactic.FunProp.Measurable
import Mathlib.MeasureTheory.Constructions.Prod.Integral

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
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} {f : ℝ → ℝ} {β γ x t : ℝ}

-- To play with this function go to https://www.geogebra.org/calculator/jaymzqtm, there the notation is: b for β, c for γ, X for x. h is statInfoFun seen as a function of x, f is statInfoFun seen as a function of γ.
noncomputable
def statInfoFun (β γ x : ℝ) : ℝ := if γ ≤ β then max 0 (γ - β * x) else max 0 (β * x - γ)

lemma statInfoFun_nonneg (β γ x : ℝ) : 0 ≤ statInfoFun β γ x := by
  simp_rw [statInfoFun]
  split_ifs <;> simp

@[simp]
lemma statInfoFun_of_one : statInfoFun 1 γ x = if γ ≤ 1 then max 0 (γ - x) else max 0 (x - γ) := by
  simp_rw [statInfoFun, one_mul]

@[simp]
lemma statInfoFun_of_zero : statInfoFun 0 γ x = 0 := by simp_all [statInfoFun, le_of_lt]

--TODO: for now I will leave the continuity assumption in some lemmas, it should be derived from the convexity but the lemma is not yet in mathlib, when it gets there we can remove this assumption

--There are two ways to separate the cases: `γ ≤ 1` and `γ > 1` or `γ < 1` and `γ > 1`. The first one seems the correct one for now.

--TODO: separate these lemmas in some sections, maybe we could put together the lemmas that see `γ` as the variable and the ones that see `x` as the variable, and under those we could further separate the lemmas that have β = 1

section Measurability

lemma stronglymeasurable_statInfoFun : StronglyMeasurable statInfoFun.uncurry.uncurry := by
  apply Measurable.stronglyMeasurable
  change Measurable (fun (p : (ℝ × ℝ) × ℝ) ↦ if p.1.2 ≤ p.1.1 then max 0 (p.1.2 - p.1.1 * p.2)
    else max 0 (p.1.1 * p.2 - p.1.2))
  apply Measurable.ite
  · exact measurableSet_le (by fun_prop) (by fun_prop)
  · fun_prop
  · fun_prop

lemma measurable_statInfoFun2 : Measurable fun γ ↦ statInfoFun β γ x := by
  change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (γ : ℝ) ↦ ((β, γ), x)))
  exact stronglymeasurable_statInfoFun.measurable.comp (by fun_prop)

lemma measurable_statInfoFun3 : Measurable fun x ↦ statInfoFun β γ x := by
  change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (x : ℝ) ↦ ((β, γ), x)))
  exact stronglymeasurable_statInfoFun.measurable.comp (by fun_prop)

end Measurability

section statInfoFun_x
-- Lemmas useful when we want to consider `statInfoFun` as a function of `x`

lemma statInfoFun_of_le (h : γ ≤ β) : statInfoFun β γ x = max 0 (γ - β * x) := if_pos h

lemma statInfoFun_of_gt (h : γ > β) : statInfoFun β γ x = max 0 (β * x - γ) := if_neg h.not_le

lemma statInfoFun_of_pos_of_le_of_le (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (le_div_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_le_of_ge (hβ : 0 < β) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_le hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (div_le_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_le (hβ : 0 < β) (hγ : γ > β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_gt hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (le_div_iff' hβ).mp hx

lemma statInfoFun_of_pos_of_gt_of_ge (hβ : 0 < β) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff' hβ).mp hx

lemma statInfoFun_of_neg_of_le_of_le (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_le hγ ▸  max_eq_left_iff.mpr <| sub_nonpos.mpr <| (le_div_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_le_of_ge (hβ : β < 0) (hγ : γ ≤ β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = γ - β * x :=
  statInfoFun_of_le hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (div_le_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_gt_of_le (hβ : β < 0) (hγ : γ > β) (hx : x ≤ γ / β) :
    statInfoFun β γ x = β * x - γ :=
  statInfoFun_of_gt hγ ▸ max_eq_right_iff.mpr <| sub_nonneg.mpr <| (le_div_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_neg_of_gt_of_ge (hβ : β < 0) (hγ : γ > β) (hx : x ≥ γ / β) :
    statInfoFun β γ x = 0 :=
  statInfoFun_of_gt hγ ▸ max_eq_left_iff.mpr <| sub_nonpos.mpr <| (div_le_iff_of_neg' hβ).mp hx

lemma statInfoFun_of_one_of_le_one (h : γ ≤ 1) : statInfoFun 1 γ x = max 0 (γ - x) :=
  statInfoFun_of_one ▸ if_pos h

lemma statInfoFun_of_one_of_one_lt (h : 1 < γ) : statInfoFun 1 γ x = max 0 (x - γ) :=
  statInfoFun_of_one ▸ if_neg h.not_le

lemma statInfoFun_of_one_of_le_one_of_le (h : γ ≤ 1) (hx : x ≤ γ) : statInfoFun 1 γ x = γ - x :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma statInfoFun_of_one_of_le_one_of_ge (h : γ ≤ 1) (hx : x ≥ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_le_one h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_le (h : 1 < γ) (hx : x ≤ γ) : statInfoFun 1 γ x = 0 :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_left_iff.mpr (sub_nonpos.mpr hx)

lemma statInfoFun_of_one_of_one_lt_of_ge (h : 1 < γ) (hx : x ≥ γ) : statInfoFun 1 γ x = x - γ :=
  statInfoFun_of_one_of_one_lt h ▸ max_eq_right_iff.mpr (sub_nonneg.mpr hx)

lemma statInfoFun_of_nonneg_of_right_le_one (hβ : 0 ≤ β) (hx : x ≤ 1) :
    statInfoFun β γ x = (Ioc (β * x) β).indicator (fun y ↦ y - β * x) γ := by
  by_cases hγβ : γ ≤ β
  · by_cases hβxγ : β * x < γ
    · simp [statInfoFun, indicator, hβxγ, hβxγ.le]
    · simp [statInfoFun, hγβ, hβxγ, (le_of_not_gt hβxγ)]
  · simp only [statInfoFun, hγβ, ↓reduceIte, indicator, mem_Ioc, and_false, max_eq_left_iff,
      tsub_le_iff_right, zero_add]
    exact (mul_le_of_le_one_right hβ hx).trans (le_of_not_ge hγβ)

lemma statInfoFun_of_nonneg_of_one_le_right (hβ : 0 ≤ β) (hx : 1 ≤ x) :
    statInfoFun β γ x = (Ioc β (β * x)).indicator (fun y ↦ β * x - y) γ := by
  by_cases hγβ : γ ≤ β
  · simp [statInfoFun, hγβ, indicator, hγβ.trans (le_mul_of_one_le_right hβ hx), hγβ.not_lt]
  · by_cases hγβx : γ ≤ β * x
    · simp [statInfoFun, hγβ, hγβx, lt_of_not_ge hγβ]
    · simp [statInfoFun, hγβ, hγβx, le_of_not_ge hγβx]

lemma statInfoFun_of_nonpos_of_right_le_one (hβ : β ≤ 0) (hx : x ≤ 1) :
    statInfoFun β γ x = (Ioc β (β * x)).indicator (fun y ↦ β * x - y) γ := by
  by_cases hγβ : γ ≤ β
  · simp only [statInfoFun, hγβ, ↓reduceIte, indicator, mem_Ioc, hγβ.not_lt, false_and,
      max_eq_left_iff, tsub_le_iff_right, zero_add]
    suffices -β * x ≤ -γ from by simpa only [neg_mul, neg_le_neg_iff]
    exact (mul_le_of_le_one_right (neg_nonneg.mpr hβ) hx).trans (neg_le_neg_iff.mpr hγβ)
  · by_cases hγβx : γ ≤ β * x
    · simp [statInfoFun, hγβx, lt_of_not_ge hγβ]
    · simp [statInfoFun, hγβ, hγβx, le_of_not_ge hγβx]

lemma statInfoFun_of_nonpos_of_one_le_right (hβ : β ≤ 0) (hx : 1 ≤ x) :
    statInfoFun β γ x = (Ioc (β * x) β).indicator (fun y ↦ y - β * x) γ := by
  by_cases hγβ : γ ≤ β
  · by_cases hβxγ : β * x < γ
    · simp [statInfoFun, indicator, hβxγ, hβxγ.le]
    · simp [statInfoFun, hγβ, hβxγ, (le_of_not_gt hβxγ)]
  · simp only [statInfoFun, hγβ, ↓reduceIte, mem_Ioc, and_false, not_false_eq_true,
      indicator_of_not_mem, max_eq_left_iff, tsub_le_iff_right, zero_add]
    suffices -β * x ≥ -γ from by simpa only [neg_mul, neg_le_neg_iff]
    exact ((neg_lt_neg_iff.mpr (lt_of_not_ge hγβ)).trans_le
      ((le_mul_of_one_le_right (neg_nonneg.mpr hβ) hx))).le

lemma statInfoFun_of_one_of_one_le_right (h : 1 ≤ x) :
    statInfoFun 1 γ x = (Ioc 1 x).indicator (fun y ↦ x - y) γ := by
  convert statInfoFun_of_nonneg_of_one_le_right _ h <;> simp

lemma statInfoFun_of_one_of_right_le_one (h : x ≤ 1) :
    statInfoFun 1 γ x = (Ioc x 1).indicator (fun y ↦ y - x) γ := by
  convert statInfoFun_of_nonneg_of_right_le_one _ h <;> simp

lemma statInfoFun_le_of_nonneg_of_right_le_one (hβ : 0 ≤ β) (hx : x ≤ 1) :
    statInfoFun β γ x ≤ (Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ := by
  rw [statInfoFun_of_nonneg_of_right_le_one hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨_, hγ⟩ ↦ ?_
  simp [hγ]

lemma statInfoFun_le_of_nonneg_of_one_le_right (hβ : 0 ≤ β) (hx : 1 ≤ x) :
    statInfoFun β γ x ≤ (Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ := by
  rw [statInfoFun_of_nonneg_of_one_le_right hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨hβγ, _⟩ ↦ ?_
  simp only [sub_eq_add_neg, add_le_add_iff_left, neg_le_neg_iff, hβγ.le]

lemma statInfoFun_le_of_nonpos_of_right_le_one (hβ : β ≤ 0) (hx : x ≤ 1) :
    statInfoFun β γ x ≤ (Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ := by
  rw [statInfoFun_of_nonpos_of_right_le_one hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨hγβ, _⟩ ↦ ?_
  simp only [sub_eq_add_neg, add_le_add_iff_left, neg_le_neg_iff, hγβ.le]

lemma statInfoFun_le_of_nonpos_of_one_le_right (hβ : β ≤ 0) (hx : 1 ≤ x) :
    statInfoFun β γ x ≤ (Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ := by
  rw [statInfoFun_of_nonpos_of_one_le_right hβ hx]
  refine indicator_rel_indicator le_rfl fun ⟨_, hγ⟩ ↦ ?_
  simp [hγ]

--PR this to mathlib replacing uIoc_of_lt, is it ok to replace a lemma? the olter lemma has #align from the port, should it be removed?
@[simp] lemma uIoc_of_ge {α : Type u_1} [LinearOrder α] {a b : α} (h : b ≤ a) :
  Ι a b = Ioc b a := by simp [uIoc, h]
--PR this also to mathlib
lemma uIoc_subset_uIcc {α : Type u_1} [LinearOrder α] {a b : α} :
    Ι a b ⊆ uIcc a b := Ioc_subset_Icc_self

lemma lintegral_nnnorm_statInfoFun_le {μ : Measure ℝ} (β x : ℝ) :
    ∫⁻ γ, ↑‖statInfoFun β γ x‖₊ ∂μ ≤ (μ (uIoc (β * x) β)) * (ENNReal.ofReal |β - β * x|) := by
  simp_rw [Real.nnnorm_of_nonneg (statInfoFun_nonneg _ _ _),
    ← ENNReal.ofReal_eq_coe_nnreal (statInfoFun_nonneg _ _ _)]
  rcases le_total β 0 with (hβ | hβ) <;> rcases le_total x 1 with (hx | hx)
  · have hββx : β ≤ β * x := by exact le_mul_of_le_one_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonpos_of_right_le_one hβ hx
      _ = ∫⁻ γ,  ((Ioc β (β * x)).indicator (fun _ ↦ ENNReal.ofReal (β * x - β)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β * x - β) * μ (Ioc β (β * x)) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_of_ge hββx, mul_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hββx)]
  · have hβxβ : β * x ≤ β := by exact mul_le_of_one_le_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonpos_of_one_le_right hβ hx
      _ = ∫⁻ γ,  ((Ioc (β * x) β).indicator (fun _ ↦ ENNReal.ofReal (β - β * x)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β - β * x) * μ (Ioc (β * x) β) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_comm, uIoc_of_ge hβxβ, abs_of_nonneg (sub_nonneg.mpr hβxβ), mul_comm]
  · have hββx : β * x ≤ β := by exact mul_le_of_le_one_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc (β * x) β).indicator (fun _ ↦ β - β * x) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonneg_of_right_le_one hβ hx
      _ = ∫⁻ γ,  ((Ioc (β * x) β).indicator (fun _ ↦ ENNReal.ofReal (β - β * x)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β - β * x) * μ (Ioc (β * x) β) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_comm, uIoc_of_ge hββx, abs_of_nonneg (sub_nonneg.mpr hββx), mul_comm]
  · have hβxβ : β ≤ β * x := by exact le_mul_of_one_le_right hβ hx
    calc
      _ ≤ ∫⁻ γ, ENNReal.ofReal ((Ioc β (β * x)).indicator (fun _ ↦ β * x - β) γ) ∂μ :=
        lintegral_mono fun _ ↦ ENNReal.ofReal_le_ofReal <|
          statInfoFun_le_of_nonneg_of_one_le_right hβ hx
      _ = ∫⁻ γ,  ((Ioc β (β * x)).indicator (fun _ ↦ ENNReal.ofReal (β * x - β)) γ) ∂μ := by
        simp [Set.comp_indicator]
      _ ≤ ENNReal.ofReal (β * x - β) * μ (Ioc β (β * x)) := lintegral_indicator_const_le _ _
      _ = μ (Ι (β * x) β) * ENNReal.ofReal |β - β * x| := by
        rw [uIoc_of_ge hβxβ, mul_comm, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hβxβ)]

lemma integrable_statInfoFun {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] (β x : ℝ) :
    Integrable (fun γ ↦ statInfoFun β γ x) μ := by
  refine ⟨measurable_statInfoFun2.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  refine ((lintegral_nnnorm_statInfoFun_le _ _).trans_lt ?_)
  refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_ne_top
  exact (measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top |>.ne

noncomputable-- maybe this will not be needed, eGamma will be defined from the risk
def eGamma (γ : ℝ) (μ ν : Measure 𝒳) : EReal := fDiv (statInfoFun 1 γ) μ ν

--should we define this to be some junk value if f is not convex? this way we could avoid having to state the convexity every time
-- this may be put in some other place, maybe directly in the stieltjes file
noncomputable
def curvatureMeasure (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : Measure ℝ :=
  (StieltjesFunction.rightDeriv_of_convex f hf).measure

instance (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) : IsLocallyFiniteMeasure (curvatureMeasure f hf) := by
  unfold curvatureMeasure
  infer_instance

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

lemma fun_eq_integral_statInfoFun_curvatureMeasure (hf_cvx : ConvexOn ℝ univ f)
    (hf_cont : Continuous f) (hf_one : f 1 = 0) (hfderiv_one : rightDeriv f 1 = 0) :
    f t = ∫ y, statInfoFun 1 y t ∂(curvatureMeasure f hf_cvx) := by
  have h :
      f t - f 1 - (rightDeriv f 1) * (t - 1) = ∫ x in (1)..t, t - x ∂(curvatureMeasure f hf_cvx) :=
    generalized_taylor hf_cvx hf_cont
  rw [hf_one, hfderiv_one, sub_zero, zero_mul, sub_zero] at h
  rw [h]
  rcases le_total t 1 with (ht | ht)
  · simp_rw [statInfoFun_of_one_of_right_le_one ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_ge ht, ← integral_neg, neg_sub]
  · simp_rw [statInfoFun_of_one_of_one_le_right ht, integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le ht]

lemma fDiv_eq_integral_fDiv_statInfoFun_curvatureMeasure_of_absolutelyContinuous [SigmaFinite ν]
    (hf_cvx : ConvexOn ℝ univ f) (hf_cont : Continuous f) (hf_one : f 1 = 0)
    (hfderiv_one : rightDeriv f 1 = 0) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_ac : μ ≪ ν) :
    fDiv f μ ν = ∫ x, (fDiv (statInfoFun 1 x) μ ν).toReal ∂(curvatureMeasure f hf_cvx) := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap
  · rw [fDiv_of_not_integrable h_int]
    --clearly this is not possible because the rhs must be finite, so this integrability condition should be put as a hypothesis, but I would like to understand if it it enough to assume this in order to obtain also the other integrability condition needed or if I should assume other things
    sorry

  --I'm not sure if this is actually true, for now I am going to assume it is, maybe I have to derive it from the other assumptions, or maybe it is necessary to assume it or some other thing that implies it
  -- also if needed it is enough to assume this a.e. wrt ∂curvatureMeasure f hf_cvx
  have h_int' (γ : ℝ) : Integrable (fun x ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal) ν := by

    sorry

  classical
  rw [fDiv_of_absolutelyContinuous h_ac, if_pos h_int, EReal.coe_eq_coe_iff]
  simp_rw [fDiv_of_absolutelyContinuous h_ac, if_pos (h_int' _), EReal.toReal_coe,
    fun_eq_integral_statInfoFun_curvatureMeasure hf_cvx hf_cont hf_one hfderiv_one]
  --now we have to apply tonelli's theorem, first we have to convert the integral to a lintegral integral_eq_lintegral_of_nonneg_ae
  --then we can use lintegral_lintegral_swap

  -- we could use this to directly swap the two integrals, the problem is that then we need to prove the joint integrability of `fun x y ↦ statInfoFun 1 y ((∂μ/∂ν) x).toReal)` and I'm not sure if it is easier than the other way
  -- refine MeasureTheory.integral_integral_swap ?_


  -- this is an attempt to apply tonellli's theorem instead of Fubini's theorem, we don't need the integrability, but it seems to be more complicated, because we have to go from the Bochner integral to the lintegral for 4 separate integrals,
  have h_meas : Measurable (fun x γ ↦ statInfoFun 1 γ ((∂μ/∂ν) x).toReal).uncurry := by
    change Measurable (statInfoFun.uncurry.uncurry ∘ (fun (xγ : 𝒳 × ℝ) ↦ ((1, xγ.2), ((∂μ/∂ν) xγ.1).toReal)))
    refine stronglymeasurable_statInfoFun.measurable.comp ?_
    refine (measurable_const.prod_mk measurable_snd).prod_mk ?_
    exact ((Measure.measurable_rnDeriv μ ν).comp measurable_fst).ennreal_toReal
  have int_eq_lint : ∫ x, ∫ γ, statInfoFun 1 γ ((∂μ/∂ν) x).toReal ∂curvatureMeasure f hf_cvx ∂ν
      = (∫⁻ x, ∫⁻ γ, ENNReal.ofReal (statInfoFun 1 γ ((∂μ/∂ν) x).toReal)
        ∂curvatureMeasure f hf_cvx ∂ν).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    rotate_left
    · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
    · refine (StronglyMeasurable.integral_prod_left ?_).aestronglyMeasurable
      exact (measurable_swap_iff.mpr h_meas).stronglyMeasurable
    congr with x --if needed here we can have a ν-a.e. equality
    rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun y ↦ statInfoFun_nonneg _ _ _)
      h_meas.of_uncurry_left.stronglyMeasurable.aestronglyMeasurable]
    refine  ENNReal.ofReal_toReal ?_
    --maybe we need some other hp?
    sorry

  rw [int_eq_lint, lintegral_lintegral_swap h_meas.ennreal_ofReal.aemeasurable,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact eventually_of_forall fun _ ↦ (integral_nonneg (fun _ ↦ statInfoFun_nonneg _ _ _))
  · exact h_meas.stronglyMeasurable.integral_prod_left.aestronglyMeasurable
  congr with γ --if needed here we can have a `curvatureMeasure f hf_cvx`-a.e. equality and use a filter_upwards
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun _ ↦ statInfoFun_nonneg _ _ _)
    h_meas.of_uncurry_right.stronglyMeasurable.aestronglyMeasurable]
  rw [ENNReal.ofReal_toReal]
  have h_lt_top := (h_int' γ).hasFiniteIntegral
  simp_rw [HasFiniteIntegral, lt_top_iff_ne_top] at h_lt_top
  convert h_lt_top
  rw [← ENNReal.toReal_eq_toReal ENNReal.ofReal_ne_top ENNReal.coe_ne_top, toReal_coe_nnnorm,
    ENNReal.toReal_ofReal (statInfoFun_nonneg _ _ _),
    Real.norm_of_nonneg (statInfoFun_nonneg _ _ _)]



/-things needed:
- the stieltjes file only handles functions ℝ → ℝ, do we do the same or do we want to generalize to functions on subsets of ℝ? for example we may want to only consider functions on (0,∞), as they do in the paper Phi-divergences, sufficiency..., moreover the functions we have for the f divergences are convex only on half the real line, so it may be necessary to generalize the stieltjes file. solution: do everything on ℝ, then we can show that for every convex function on (0,∞) we can find a convex function on ℝ that coincides with the original on (0,∞) just by extending it to a linear function with slope equal to the right derivative at 0 on the negavites
- how to handle the integral in the generalized taylor theorem, since the measure is defined on a subset of ℝ, not on all of ℝ and I need to further restrict that to the interval [min a b, max a b]
-/

--this will be useful later
#check fDiv_eq_add_withDensity_singularPart

end ProbabilityTheory
-- strange error:
--Error while replacing abbreviation: Error: TextEditor#edit not possible on closed editors
--TODO: when finished with these proof remember to update the blueprint and also add the proofs to the blueprint
--todo write StieltjesFunction.measure_Ioi
