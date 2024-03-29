/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.DerivAtTop
import TestingLowerBounds.SoonInMathlib.RadonNikodym
import TestingLowerBounds.ForMathlib.RnDeriv

/-!

# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation

## Implementation details

The most natural type for `f` is `ℝ≥0∞ → EReal` since we apply it to an `ℝ≥0∞`-values RN derivative,
and its value can be in general both positive or negative, and potentially +∞.
However, we use `ℝ → ℝ` instead, for the following reasons:
* domain: convexity results like `ConvexOn.map_average_le` don't work for `ℝ≥0∞` because they
  require a normed space with scalars in `ℝ`, but `ℝ≥0∞` is a module over `ℝ≥0`.
  Also, the RN derivative is almost everywhere finite for σ-finite measures, so losing ∞ in the
  domain is not an issue.
* codomain: `EReal` is underdeveloped, and all functions we will actually use are finite anyway.

Most results will require these conditions on `f`:
`(hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)`

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α β : Type*} {m mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : kernel α β} {f g : ℝ → ℝ}

lemma integrable_toReal_iff {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_ne_top : ∀ᵐ x ∂μ, f x ≠ ∞) :
    Integrable (fun x ↦ (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ ≠ ∞ := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrable_toReal_of_lintegral_ne_top hf h⟩
  rw [Integrable, HasFiniteIntegral] at h
  have : ∀ᵐ x ∂μ, f x = ↑‖(f x).toReal‖₊ := by
    filter_upwards [hf_ne_top] with x hx
    rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]
  rw [lintegral_congr_ae this]
  exact h.2.ne

lemma integrable_f_rnDeriv_of_derivAtTop_ne_top (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_deriv : derivAtTop f ≠ ⊤) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ/∂ν) x).toReal)
    (g₁ := fun x ↦ c * ((∂μ/∂ν) x).toReal + c')
    (g₂ := fun x ↦ (derivAtTop f).toReal * ((∂μ/∂ν) x).toReal + f 0)
    ?_ ?_ ?_ ?_ ?_
  · exact (hf.comp_measurable (μ.measurable_rnDeriv ν).ennreal_toReal).aestronglyMeasurable
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · refine ae_of_all _ (fun x ↦ ?_)
    have h := le_add_derivAtTop'' hf_cvx hf_deriv le_rfl
      (ENNReal.toReal_nonneg : 0 ≤ ((∂μ/∂ν) x).toReal)
    rwa [zero_add, add_comm] at h
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv
  · refine (Integrable.const_mul ?_ _).add (integrable_const _)
    exact Measure.integrable_toReal_rnDeriv

open Classical in
/-- f-Divergence of two measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : EReal :=
  if ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν then ⊤
  else ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ

lemma fDiv_of_not_integrable (hf : ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ := if_pos hf

lemma fDiv_of_integrable (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ :=
  if_neg (not_not.mpr hf)

lemma fDiv_of_mul_eq_top (h : derivAtTop f * μ.singularPart ν Set.univ = ⊤) :
    fDiv f μ ν = ⊤ := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv, if_neg (not_not.mpr hf), h, EReal.coe_add_top]
  · exact fDiv_of_not_integrable hf

lemma fDiv_ne_bot [IsFiniteMeasure μ] : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    simp [derivAtTop_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), measure_ne_top]
  · simp

lemma fDiv_ne_bot_of_derivAtTop_nonneg (hf : 0 ≤ derivAtTop f) : fDiv f μ ν ≠ ⊥ := by
  rw [fDiv]
  split_ifs with h
  · simp only [ne_eq, EReal.add_eq_bot_iff, EReal.coe_ne_bot, false_or]
    rw [EReal.mul_eq_bot]
    simp [derivAtTop_ne_bot, not_lt.mpr (EReal.coe_ennreal_nonneg _), not_lt.mpr hf]
  · simp

@[simp]
lemma fDiv_zero (μ ν : Measure α) : fDiv (fun _ ↦ 0) μ ν = 0 := by simp [fDiv]

@[simp]
lemma fDiv_const (c : ℝ) (μ ν : Measure α) [IsFiniteMeasure ν] :
    fDiv (fun _ ↦ c) μ ν = ν Set.univ * c := by
  rw [fDiv_of_integrable (integrable_const c), integral_const]
  simp only [smul_eq_mul, EReal.coe_mul, derivAtTop_const, zero_mul, add_zero]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_const' {c : ℝ} (hc : 0 ≤ c) (μ ν : Measure α) :
    fDiv (fun _ ↦ c) μ ν = ν Set.univ * c := by
  by_cases hν : IsFiniteMeasure ν
  · exact fDiv_const c μ ν
  · have : ν Set.univ = ∞ := by
      by_contra h_univ
      exact absurd ⟨Ne.lt_top h_univ⟩ hν
    rw [this]
    by_cases hc0 : c = 0
    · simp [hc0]
    rw [fDiv_of_not_integrable]
    · simp only [EReal.coe_ennreal_top]
      rw [EReal.top_mul_of_pos]
      refine lt_of_le_of_ne ?_ (Ne.symm ?_)
      · exact mod_cast hc
      · exact mod_cast hc0
    · rw [integrable_const_iff]
      simp [hc0, this]

lemma fDiv_self (hf_one : f 1 = 0) (μ : Measure α) [SigmaFinite μ] : fDiv f μ μ = 0 := by
  have h : (fun x ↦ f (μ.rnDeriv μ x).toReal) =ᵐ[μ] 0 := by
    filter_upwards [Measure.rnDeriv_self μ] with x hx
    rw [hx, ENNReal.one_toReal, hf_one]
    rfl
  rw [fDiv_of_integrable]
  swap; · rw [integrable_congr h]; exact integrable_zero _ _ _
  rw [integral_congr_ae h]
  simp only [Pi.zero_apply, integral_zero, EReal.coe_zero, zero_add]
  rw [Measure.singularPart_self]
  simp

lemma fDiv_id (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv id μ ν = μ Set.univ := by
  by_cases h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int]
    simp only [id_eq, derivAtTop_id, one_mul]
    rw [← integral_univ, Measure.set_integral_toReal_rnDeriv_eq_withDensity]
    have h_ne_top : (Measure.withDensity ν (∂μ/∂ν)) Set.univ ≠ ∞ := by
      rw [withDensity_apply _ MeasurableSet.univ, set_lintegral_univ]
      rwa [integrable_toReal_iff] at h_int
      · exact (μ.measurable_rnDeriv ν).aemeasurable
      · exact μ.rnDeriv_ne_top ν
    rw [EReal.coe_ennreal_toReal h_ne_top]
    norm_cast
    conv_rhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  · rw [fDiv_of_not_integrable h_int]
    norm_cast
    symm
    by_contra h_ne_top
    have : IsFiniteMeasure μ := ⟨Ne.lt_top ?_⟩
    swap; · rw [← EReal.coe_ennreal_top] at h_ne_top; exact mod_cast h_ne_top
    refine h_int ?_
    refine integrable_toReal_of_lintegral_ne_top (μ.measurable_rnDeriv ν).aemeasurable ?_
    exact (Measure.lintegral_rnDeriv_lt_top _ _).ne

lemma fDiv_id' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x) μ ν = μ Set.univ := fDiv_id μ ν

lemma fDiv_mul {c : ℝ} (hc : 0 ≤ c) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f)
    (μ ν : Measure α) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap; · exact h_int.const_mul _
    rw [integral_mul_left, derivAtTop_const_mul hf_cvx (lt_of_le_of_ne hc (Ne.symm hc0)),
      EReal.coe_mul, EReal.coe_mul_add_of_nonneg hc, mul_assoc]
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    · rw [EReal.mul_top_of_pos]
      norm_cast
      exact lt_of_le_of_ne hc (Ne.symm hc0)
    · refine fun h ↦ h_int ?_
      have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ c⁻¹ * (c * f ((∂μ/∂ν) x).toReal)) := by
        ext; rw [← mul_assoc, inv_mul_cancel hc0, one_mul]
      rw [this]
      exact h.const_mul _

lemma fDiv_mul_of_ne_top (c : ℝ) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_top : derivAtTop f ≠ ⊤)
    (μ ν : Measure α) [IsFiniteMeasure μ] (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv (fun x ↦ c * f x) μ ν = c * fDiv f μ ν := by
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [fDiv_of_integrable h_int, fDiv_of_integrable]
  swap; · exact h_int.const_mul _
  rw [integral_mul_left, derivAtTop_const_mul_of_ne_top hf_cvx h_top c]
  lift derivAtTop f to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  ring

-- TODO: in the case where both functions are convex, integrability of the sum is equivalent to
-- integrability of both, and we don't need hf and hg.
lemma fDiv_add [IsFiniteMeasure μ] (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (hg : Integrable (fun x ↦ g ((∂μ/∂ν) x).toReal) ν)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hg_cvx : ConvexOn ℝ (Set.Ici 0) g) :
    fDiv (fun x ↦ f x + g x) μ ν = fDiv f μ ν + fDiv g μ ν := by
  rw [fDiv_of_integrable (hf.add hg), integral_add hf hg, fDiv_of_integrable hf,
    fDiv_of_integrable hg, derivAtTop_add hf_cvx hg_cvx]
  simp only [EReal.coe_add]
  rw [add_assoc, add_assoc]
  congr 1
  conv_rhs => rw [← add_assoc, add_comm, ← add_assoc, add_comm]
  congr 1
  rw [← EReal.coe_ennreal_toReal]
  · rw [add_comm, EReal.add_mul_coe_of_nonneg ENNReal.toReal_nonneg]
  · exact measure_ne_top _ _

lemma fDiv_add_linear' {c : ℝ} (hc : 0 ≤ c) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν
      = fDiv f μ ν + c * ((μ Set.univ).toReal - (ν Set.univ).toReal) := by
  rw [fDiv_add hf _ hf_cvx _]
  · simp_rw [sub_eq_add_neg]
    rw [fDiv_mul hc, fDiv_add Measure.integrable_toReal_rnDeriv (integrable_const _),
      fDiv_const, fDiv_id']
    rotate_left
    · exact convexOn_id (convex_Ici 0)
    · exact convexOn_const _ (convex_Ici 0)
    · exact (convexOn_id (convex_Ici 0)).add (convexOn_const _ (convex_Ici 0))
    simp only [EReal.coe_neg, EReal.coe_one, mul_neg, mul_one]
    congr
    · rw [EReal.coe_ennreal_toReal]
      exact measure_ne_top _ _
    · rw [EReal.coe_ennreal_toReal]
      exact measure_ne_top _ _
  · exact (Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c
  · exact ((convexOn_id (convex_Ici 0)).sub (concaveOn_const _ (convex_Ici 0))).smul hc

lemma fDiv_add_linear {c : ℝ} (hc : 0 ≤ c) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (h_eq : μ Set.univ = ν Set.univ) :
    fDiv (fun x ↦ f x + c * (x - 1)) μ ν = fDiv f μ ν := by
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add_linear' hc hf hf_cvx, h_eq, ← EReal.coe_sub, sub_self]
    simp
  · rw [fDiv_of_not_integrable hf,fDiv_of_not_integrable]
    refine fun h_int ↦ hf ?_
    have : (fun x ↦ f ((∂μ/∂ν) x).toReal)
        = fun x ↦ (f ((∂μ/∂ν) x).toReal + c * (((∂μ/∂ν) x).toReal - 1))
          - c * (((∂μ/∂ν) x).toReal - 1) := by
      ext x
      simp
    rw [this]
    exact h_int.add ((Measure.integrable_toReal_rnDeriv.sub (integrable_const _)).const_mul c).neg

lemma fDiv_of_mutuallySingular [SigmaFinite μ] [IsFiniteMeasure ν] (h : μ ⟂ₘ ν) :
    fDiv f μ ν = (f 0 : EReal) * ν Set.univ + derivAtTop f * μ Set.univ := by
  have : μ.singularPart ν = μ := (μ.singularPart_eq_self).mpr h
  have hf_rnDeriv : (fun x ↦ f ((∂μ/∂ν) x).toReal) =ᵐ[ν] fun _ ↦ f 0 := by
    filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h Measure.AbsolutelyContinuous.rfl]
      with x hx using by simp [hx]
  have h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
      rw [integrable_congr hf_rnDeriv]
      exact integrable_const _
  rw [fDiv_of_integrable h_int, integral_congr_ae hf_rnDeriv]
  simp only [integral_const, smul_eq_mul, EReal.coe_mul, this]
  rw [mul_comm]
  congr
  rw [EReal.coe_ennreal_toReal]
  exact measure_ne_top _ _

lemma fDiv_of_absolutelyContinuous
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)] (h : μ ≪ ν) :
    fDiv f μ ν = if Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      then (↑(∫ x, f ((∂μ/∂ν) x).toReal ∂ν) : EReal) else ⊤ := by
  split_ifs with h_int
  · rw [fDiv_of_integrable h_int, Measure.singularPart_eq_zero_of_ac h]
    simp only [Measure.zero_toOuterMeasure, OuterMeasure.coe_zero, Pi.zero_apply, mul_zero,
      ENNReal.zero_toReal, add_zero]
    simp [Measure.singularPart_eq_zero_of_ac h]
  · rw [fDiv_of_not_integrable h_int]

lemma fDiv_add_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x + c) μ ν = fDiv f μ ν + c * ν Set.univ := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_add hf_int (integrable_const _) hf_cvx, fDiv_const, mul_comm]
    exact convexOn_const _ (convex_Ici 0)
  · rw [fDiv_of_not_integrable hf_int, fDiv_of_not_integrable]
    · rw [← EReal.coe_ennreal_toReal, ← EReal.coe_mul, EReal.top_add_coe]
      exact measure_ne_top _ _
    · have : (fun x ↦ f ((∂μ/∂ν) x).toReal) = (fun x ↦ (f ((∂μ/∂ν) x).toReal + c) - c) := by
        ext; simp
      rw [this] at hf_int
      exact fun h_int ↦ hf_int (h_int.sub (integrable_const _))

lemma fDiv_sub_const (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (c : ℝ) :
    fDiv (fun x ↦ f x - c) μ ν = fDiv f μ ν - c * ν Set.univ := by
  have : f = fun x ↦ (f x - c) + c := by ext; simp
  conv_rhs => rw [this]
  rw [fDiv_add_const]
  · rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel]
  · exact hf_cvx.sub (concaveOn_const _ (convex_Ici 0))

lemma fDiv_eq_add_withDensity_singularPart
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + fDiv f (μ.singularPart ν) ν
      - f 0 * ν Set.univ := by
  have h_int_iff : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ f ((∂(ν.withDensity (∂μ/∂ν))/∂ν) x).toReal) ν := by
    refine integrable_congr ?_
    filter_upwards [Measure.rnDeriv_withDensity ν (μ.measurable_rnDeriv ν)] with x hx
    rw [hx]
  classical
  rw [fDiv_of_mutuallySingular (Measure.mutuallySingular_singularPart _ _)]
  by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _), if_pos,
      fDiv_of_integrable hf]
    swap
    · exact h_int_iff.mp hf
    rw [add_sub_assoc]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [Measure.rnDeriv_withDensity ν (μ.measurable_rnDeriv ν)] with x hx
      rw [hx]
    rw [← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul, EReal.add_sub_cancel']
  · rw [fDiv_of_not_integrable hf, fDiv_of_not_integrable]
    · rw [add_sub_assoc, ← EReal.coe_ennreal_toReal (measure_ne_top ν _), ← EReal.coe_mul,
        EReal.add_sub_cancel']
      by_cases h0 : μ.singularPart ν Set.univ = 0
      · simp [h0]
      · by_cases h_top : derivAtTop f = ⊤
        · rw [h_top, EReal.top_mul_ennreal_coe h0, EReal.top_add_top]
        · lift derivAtTop f to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with x
          rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), ← EReal.coe_mul, EReal.top_add_coe]
    · rwa [← h_int_iff]

lemma fDiv_eq_add_withDensity_singularPart'
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f μ ν = fDiv (fun x ↦ f x - f 0) (ν.withDensity (∂μ/∂ν)) ν
      + fDiv f (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg, sub_eq_add_neg, add_assoc]
  · congr 1
    rw [add_comm]
  · exact hf_cvx

lemma fDiv_eq_add_withDensity_singularPart''
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν
      + fDiv (fun x ↦ f x - f 0) (μ.singularPart ν) ν := by
  rw [fDiv_eq_add_withDensity_singularPart _ _, fDiv_sub_const, add_sub_assoc,
    sub_eq_add_neg]
  exact hf_cvx

lemma fDiv_eq_add_withDensity_derivAtTop
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f μ ν = fDiv f (ν.withDensity (∂μ/∂ν)) ν + derivAtTop f * μ.singularPart ν Set.univ := by
  rw [fDiv_eq_add_withDensity_singularPart'' μ ν hf_cvx,
    fDiv_of_mutuallySingular (Measure.mutuallySingular_singularPart _ _),
    derivAtTop_sub_const hf_cvx]
  simp

lemma fDiv_lt_top_of_ac [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  classical
  rw [fDiv_of_absolutelyContinuous h, if_pos h_int]
  simp

lemma fdiv_add_measure_le_of_ac {μ₁ μ₂ ν : Measure α} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν)
    (hf : StronglyMeasurable f) (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν ≤ fDiv f μ₁ ν + derivAtTop f * μ₂ Set.univ := by
  classical
  by_cases hμ₂0 : μ₂ = 0
  · simp [hμ₂0]
  by_cases h_top : derivAtTop f = ⊤
  · rw [h_top, EReal.top_mul_of_pos, EReal.add_top_of_ne_bot]
    · exact le_top
    · refine fDiv_ne_bot_of_derivAtTop_nonneg ?_
      simp [h_top]
    · simp [hμ₂0]
  have h_int : Integrable (fun x ↦ f ((∂μ₁/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_int_add : Integrable (fun x ↦ f ((∂μ₁ + μ₂/∂ν) x).toReal) ν :=
    integrable_f_rnDeriv_of_derivAtTop_ne_top _ _ hf hf_cvx h_top
  have h_le : ∀ᵐ x ∂ν, f ((∂μ₁ + μ₂/∂ν) x).toReal
      ≤ f ((∂μ₁/∂ν) x).toReal + (derivAtTop f).toReal * ((∂μ₂/∂ν) x).toReal := by
    have h_add := Measure.rnDeriv_add' μ₁ μ₂ ν
    filter_upwards [h_add, μ₁.rnDeriv_lt_top ν, μ₂.rnDeriv_lt_top ν] with x hx hx₁ hx₂
    rw [hx, Pi.add_apply, ENNReal.toReal_add hx₁.ne hx₂.ne]
    exact le_add_derivAtTop'' hf_cvx h_top ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [fDiv_of_absolutelyContinuous (Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩),
    if_pos h_int_add, fDiv_of_absolutelyContinuous h₁, if_pos h_int]
  lift derivAtTop f to ℝ using ⟨h_top, derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  calc ∫ x, f ((∂μ₁ + μ₂/∂ν) x).toReal ∂ν
    ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal + df * ((∂μ₂/∂ν) x).toReal ∂ν := by
        refine integral_mono_ae h_int_add ?_ h_le
        exact h_int.add (Measure.integrable_toReal_rnDeriv.const_mul _)
  _ ≤ ∫ x, f ((∂μ₁/∂ν) x).toReal ∂ν + df * (μ₂ Set.univ).toReal := by
        rw [integral_add h_int (Measure.integrable_toReal_rnDeriv.const_mul _),
          integral_mul_left, Measure.integral_toReal_rnDeriv h₂]

lemma fDiv_absolutelyContinuous_add_mutuallySingular {μ₁ μ₂ ν : Measure α}
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν] (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ⟂ₘ ν)
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    fDiv f (μ₁ + μ₂) ν = fDiv f μ₁ ν + derivAtTop f * μ₂ Set.univ := by
  rw [fDiv_eq_add_withDensity_derivAtTop  _ _ hf_cvx, Measure.singularPart_add,
    Measure.singularPart_eq_zero_of_ac h₁, Measure.singularPart_eq_self.mpr h₂, zero_add]
  congr
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ₁ ν h₁]
  refine withDensity_congr_ae ?_
  refine (Measure.rnDeriv_add' _ _ _).trans ?_
  filter_upwards [Measure.rnDeriv_eq_zero_of_mutuallySingular h₂ Measure.AbsolutelyContinuous.rfl]
    with x hx
  simp [hx]

section derivAtTopTop

lemma fDiv_of_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤) (hμν : ¬ μ ≪ ν) :
    fDiv f μ ν = ⊤ := by
  rw [fDiv]
  split_ifs with h_int
  · rw [hf]
    suffices Measure.singularPart μ ν Set.univ ≠ 0 by
      rw [EReal.top_mul_of_pos, EReal.coe_add_top]
      refine lt_of_le_of_ne (EReal.coe_ennreal_nonneg _) ?_
      exact mod_cast this.symm
    simp only [ne_eq, Measure.measure_univ_eq_zero]
    rw [Measure.singularPart_eq_zero]
    exact hμν
  · rfl

lemma fDiv_lt_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ ↔ μ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ fDiv_lt_top_of_ac h h_int⟩
  by_contra h_not_ac
  refine h.ne (fDiv_of_not_ac hf h_not_ac)

lemma fDiv_ne_top_iff_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν ≠ ⊤ ↔ μ ≪ ν := by
  rw [← fDiv_lt_top_iff_ac hf h_int, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_not_ac [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν = ⊤ ↔ ¬ μ ≪ ν := by
  rw [← fDiv_ne_top_iff_ac hf h_int, not_not]

lemma fDiv_of_derivAtTop_eq_top [SigmaFinite μ] [SigmaFinite ν] (hf : derivAtTop f = ⊤)
    [Decidable (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)] :
    fDiv f μ ν = if (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν)
      then ((∫ x, f ((∂μ/∂ν) x).toReal ∂ν : ℝ) : EReal)
      else ⊤ := by
  split_ifs with h
  · rw [fDiv_of_integrable h.1, Measure.singularPart_eq_zero_of_ac h.2]
    simp
  · push_neg at h
    by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · exact fDiv_of_not_ac hf (h hf_int)
    · exact fDiv_of_not_integrable hf_int

end derivAtTopTop

lemma fDiv_lt_top_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) (h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) :
    fDiv f μ ν < ⊤ := by
  rw [fDiv_of_integrable h_int]
  refine EReal.add_lt_top ?_ ?_
  · simp
  · have : μ.singularPart ν Set.univ < (⊤ : EReal) := by
      rw [← EReal.coe_ennreal_top]
      norm_cast
      exact measure_lt_top _ _
    rw [ne_eq, EReal.mul_eq_top]
    simp only [derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot, and_false, hf,
      EReal.coe_ennreal_pos, Measure.measure_univ_pos, ne_eq, EReal.coe_ennreal_eq_top_iff,
      false_or, not_and]
    exact fun _ ↦ measure_ne_top _ _

lemma fDiv_lt_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν < ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨fun h ↦ ?_, fDiv_lt_top_of_derivAtTop_ne_top hf⟩
  by_contra h_not_int
  rw [fDiv_of_not_integrable h_not_int] at h
  simp at h

lemma fDiv_ne_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν ≠ ⊤ ↔ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_lt_top_iff_of_derivAtTop_ne_top hf, lt_top_iff_ne_top]

lemma fDiv_eq_top_iff_of_derivAtTop_ne_top [IsFiniteMeasure μ] [SigmaFinite ν]
    (hf : derivAtTop f ≠ ⊤) :
    fDiv f μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  rw [← fDiv_ne_top_iff_of_derivAtTop_ne_top hf, not_not]

lemma fDiv_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν = ⊤
      ↔ (¬ Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∨ (derivAtTop f = ⊤ ∧ ¬ μ ≪ ν) := by
  by_cases h : derivAtTop f = ⊤
  · simp only [h, true_and]
    by_cases hf : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
    · simp only [hf, not_true_eq_false, false_or]
      exact fDiv_eq_top_iff_not_ac h hf
    · simp [hf, fDiv_of_not_integrable hf]
  · simp only [h, false_and, or_false]
    exact fDiv_eq_top_iff_of_derivAtTop_ne_top h

lemma fDiv_ne_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv f μ ν ≠ ⊤
      ↔ (Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν) ∧ (derivAtTop f = ⊤ → μ ≪ ν) := by
  rw [ne_eq, fDiv_eq_top_iff]
  push_neg
  rfl

lemma integrable_of_fDiv_ne_top (h : fDiv f μ ν ≠ ⊤) :
    Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν := by
  by_contra h_not
  exact h (fDiv_of_not_integrable h_not)

lemma fDiv_of_ne_top (h : fDiv f μ ν ≠ ⊤) :
    fDiv f μ ν = ∫ x, f ((∂μ/∂ν) x).toReal ∂ν + derivAtTop f * μ.singularPart ν Set.univ := by
  rw [fDiv_of_integrable]
  exact integrable_of_fDiv_ne_top h

lemma toReal_fDiv_of_integrable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν)
    (h_deriv : derivAtTop f = ⊤ → μ ≪ ν) :
    (fDiv f μ ν).toReal = ∫ y, f ((∂μ/∂ν) y).toReal ∂ν
        + (derivAtTop f * μ.singularPart ν Set.univ).toReal := by
  rw [fDiv_of_integrable hf_int, EReal.toReal_add]
  rotate_left
  · simp
  · simp
  · simp only [ne_eq, EReal.mul_eq_top, derivAtTop_ne_bot, false_and, EReal.coe_ennreal_ne_bot,
      and_false, EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_ennreal_eq_top_iff,
      measure_ne_top, or_false, false_or, not_and, not_not]
    intro h_top
    simp [h_top, Measure.singularPart_eq_zero_of_ac (h_deriv h_top)]
  · simp only [ne_eq, EReal.mul_eq_bot, derivAtTop_ne_bot, EReal.coe_ennreal_pos,
      Measure.measure_univ_pos, false_and, EReal.coe_ennreal_ne_bot, and_false,
      EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_false, false_or, not_and, not_lt]
    exact fun _ ↦ EReal.coe_ennreal_nonneg _
  rfl

-- todo: generalize: remove hμν, then use this to prove fDiv_nonneg
lemma le_fDiv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  by_cases hf_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  swap; · rw [fDiv_of_not_integrable hf_int]; exact le_top
  rw [fDiv_of_integrable hf_int, Measure.singularPart_eq_zero_of_ac hμν]
  simp only [Measure.zero_toOuterMeasure, OuterMeasure.coe_zero, Pi.zero_apply,
    EReal.coe_ennreal_zero, mul_zero, add_zero, EReal.coe_le_coe_iff]
  calc f (μ Set.univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

lemma f_measure_univ_le_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) :
    f (μ Set.univ).toReal
      ≤ f (ν.withDensity (∂μ/∂ν) Set.univ).toReal + derivAtTop f * μ.singularPart ν Set.univ := by
  by_cases hf_top : derivAtTop f = ⊤
  · rw [hf_top]
    by_cases hμν : μ ≪ ν
    · rw [Measure.singularPart_eq_zero_of_ac hμν]
      simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ,
        Measure.zero_toOuterMeasure, OuterMeasure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero,
        mul_zero, add_zero, EReal.coe_le_coe_iff]
      rw [Measure.lintegral_rnDeriv hμν]
    · rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
      have h_pos : 0 < (μ.singularPart ν Set.univ).toReal := by
        rw [ENNReal.toReal_pos_iff]
        simp [Measure.singularPart_eq_zero, hμν, measure_lt_top]
      rw [EReal.top_mul_coe_of_pos h_pos, EReal.coe_add_top]
      exact le_top
  have h := le_add_derivAtTop hf_cvx hf_top (ENNReal.toReal_nonneg : 0 ≤ (μ Set.univ).toReal)
    (ENNReal.toReal_nonneg : 0 ≤ (ν.withDensity (∂μ/∂ν) Set.univ).toReal)
  lift derivAtTop f to ℝ using ⟨hf_top, derivAtTop_ne_bot⟩ with df
  rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  norm_cast
  refine h.trans_eq ?_
  congr
  rw [sub_eq_iff_eq_add, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  conv_lhs => rw [μ.haveLebesgueDecomposition_add ν]

lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  refine (f_measure_univ_le_add μ ν hf_cvx).trans ?_
  rw [fDiv_eq_add_withDensity_singularPart'' μ _ hf_cvx,
    fDiv_of_mutuallySingular  (Measure.mutuallySingular_singularPart μ ν),
    derivAtTop_sub_const hf_cvx]
  simp only [MeasurableSet.univ, withDensity_apply, Measure.restrict_univ, sub_self, EReal.coe_zero,
    measure_univ, EReal.coe_ennreal_one, mul_one, zero_add]
  gcongr
  rw [← set_lintegral_univ, ← withDensity_apply _ MeasurableSet.univ]
  exact le_fDiv_of_ac hf_cvx hf_cont (withDensity_absolutelyContinuous _ _)

lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0) :
    0 ≤ fDiv f μ ν := by
  calc (0 : EReal) = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ fDiv f μ ν := le_fDiv hf_cvx hf_cont

lemma fDiv_map_measurableEmbedding [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α → β} (hg : MeasurableEmbedding g) :
    fDiv f (μ.map g) (ν.map g) = fDiv f μ ν := by
  by_cases h_int : Integrable (fun x ↦ f ((∂μ/∂ν) x).toReal) ν
  · rw [fDiv_of_integrable h_int, fDiv_of_integrable]
    swap
    · rw [hg.integrable_map_iff]
      refine (integrable_congr ?_).mpr h_int
      filter_upwards [hg.rnDeriv_map μ ν] with a ha
      simp [ha]
    rw [hg.integral_map]
    congr 2
    · refine integral_congr_ae ?_
      filter_upwards [hg.rnDeriv_map μ ν] with a ha
      simp [ha]
    · rw [hg.singularPart_map μ ν, hg.map_apply]
      simp
  · rw [fDiv_of_not_integrable h_int, fDiv_of_not_integrable]
    rw [hg.integrable_map_iff]
    rwa [(integrable_congr ?_)]
    filter_upwards [hg.rnDeriv_map μ ν] with a ha
    simp [ha]

lemma fDiv_restrict_of_integrable (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {s : Set α} (hs : MeasurableSet s) (h_int : IntegrableOn (fun x ↦ f ((∂μ/∂ν) x).toReal) s ν) :
    fDiv f (μ.restrict s) ν = ∫ x in s, f ((∂μ/∂ν) x).toReal ∂ν
        + f 0 * ν sᶜ + derivAtTop f * (μ.singularPart ν s) := by
  classical
  have h : (fun x ↦ f ((∂μ.restrict s/∂ν) x).toReal)
      =ᵐ[ν] s.piecewise (fun x ↦ f ((∂μ/∂ν) x).toReal) (fun _ ↦ f 0) := by
    filter_upwards [Measure.rnDeriv_restrict μ ν hs] with a ha
    rw [ha]
    by_cases has : a ∈ s <;> simp [has]
  rw [fDiv_of_integrable, μ.singularPart_restrict ν hs, Measure.restrict_apply_univ]
  swap;
  · rw [integrable_congr h]
    exact Integrable.piecewise hs h_int (integrable_const _)
  congr 1
  rw [integral_congr_ae h, integral_piecewise hs h_int (integrable_const _), integral_const]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, smul_eq_mul, EReal.coe_add,
    EReal.coe_mul]
  rw [EReal.coe_ennreal_toReal, mul_comm]
  exact measure_ne_top _ _

end ProbabilityTheory
