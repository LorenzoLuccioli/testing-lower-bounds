/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
-- theorem foo (n : Nat) : 0 ≤ n := by exact? -- trick to make exact? work TODO : erase this when we are done
-- import LeanCopilot

import TestingLowerBounds.FDiv.Basic
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Helliger divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details

-/

open Real MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- todo: rename and move.
lemma integral_rpow_rnDeriv (ha_pos : 0 < a) (ha : a ≠ 1) [SigmaFinite μ] [SigmaFinite ν] :
    ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
  let p := ∂μ/∂(μ + ν)
  let q := ∂ν/∂(μ + ν)
  calc ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν
    = ∫ x, ((p/q) x).toReal ^ a ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_eq_div μ ν] with x hx
        simp only [hx, Pi.div_apply, p, q]
  _ = ∫ x, (q x).toReal * ((p/q) x).toReal ^ a ∂(μ + ν) := by
        rw [← integral_rnDeriv_smul (_ : ν ≪ μ + ν)]
        · simp
        · rw [add_comm]
          exact Measure.AbsolutelyContinuous.rfl.add_right μ
  _ = ∫ x, (p x).toReal * ((q/p) x).toReal ^ (1 - a) ∂(μ + ν) := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_lt_top μ (μ + ν), Measure.rnDeriv_lt_top ν (μ + ν)]
          with x hp_top hq_top
        by_cases hp : p x = 0
        · simp [hp, ha_pos.ne']
        by_cases hq : q x = 0
        · simp only [hq, ENNReal.zero_toReal, Pi.div_apply, zero_mul, ENNReal.zero_div,
            zero_eq_mul, le_refl]
          refine Or.inr ?_
          rw [zero_rpow]
          rwa [ne_eq, sub_eq_zero, Eq.comm]
        simp only [Pi.div_apply, ENNReal.toReal_div, div_eq_mul_inv, ENNReal.toReal_mul,
          mul_rpow ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ENNReal.toReal_inv,
          inv_rpow ENNReal.toReal_nonneg, ← rpow_neg ENNReal.toReal_nonneg, neg_sub]
        rw [mul_comm, mul_assoc, mul_comm _ ((p x).toReal ^ (a - 1)), ← mul_assoc (p x).toReal]
        congr
        · have : a = 1 + (a - 1) := by abel
          conv_lhs => rw [this]
          rw [rpow_add, rpow_one]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hp, hp_top⟩
        · rw [mul_comm, rpow_sub, rpow_one, rpow_neg ENNReal.toReal_nonneg, div_eq_mul_inv]
          rw [ENNReal.toReal_pos_iff]
          exact ⟨zero_le'.lt_of_ne' hq, hq_top⟩
  _ = ∫ x, ((q/p) x).toReal ^ (1 - a) ∂μ := by
        rw [← integral_rnDeriv_smul (_ : μ ≪ μ + ν)]
        · simp
        · exact Measure.AbsolutelyContinuous.rfl.add_right ν
  _ = ∫ x, ((∂ν/∂μ) x).toReal ^ (1 - a) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [Measure.rnDeriv_eq_div ν μ] with x hx
        rw [add_comm] at hx
        simp only [hx, Pi.div_apply, p, q]

lemma integrable_rpow_rnDeriv_iff [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν)
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) μ
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν := by
  rw [← integrable_rnDeriv_smul_iff hμν]
  refine integrable_congr ?_
  filter_upwards [Measure.rnDeriv_ne_top μ ν] with x hx
  simp only [smul_eq_mul]
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [h_zero, ENNReal.zero_toReal, zero_mul]
    rw [zero_rpow]
    linarith
  · rw [rpow_add (ENNReal.toReal_pos h_zero hx), rpow_one]

section HellingerFun

/--Hellinger function, defined as `x ↦ (a - 1)⁻¹ * (x ^ a - 1)` for `a : ℝ`.-/
noncomputable
def hellingerFun (a : ℝ) : ℝ → ℝ := fun x ↦ (a - 1)⁻¹ * (x ^ a - 1)

lemma hellingerFun_one : hellingerFun 1 = fun x ↦ 0 := by
  ext x
  simp [hellingerFun]

lemma continuous_rpow_const (ha_pos : 0 < a) : Continuous fun (x : ℝ) ↦ x ^ a := by
  rw [continuous_iff_continuousAt]
  exact fun _ ↦ continuousAt_rpow_const _ _ (Or.inr ha_pos)

lemma continuous_hellingerFun (ha_pos : 0 < a) : Continuous (hellingerFun a) :=
  continuous_const.mul ((continuous_rpow_const ha_pos).sub continuous_const)

lemma stronglyMeasurable_hellingerFun (ha_pos : 0 < a) : StronglyMeasurable (hellingerFun a) :=
  (continuous_hellingerFun ha_pos).stronglyMeasurable

@[simp]
lemma hellingerFun_one_eq_zero : hellingerFun a 1 = 0 := by simp [hellingerFun]

lemma convexOn_hellingerFun (ha_pos : 0 < a) : ConvexOn ℝ (Set.Ici 0) (hellingerFun a) := by
  cases le_total a 1 with
  | inl ha =>
    have : hellingerFun a = - (fun x ↦ (1 - a)⁻¹ • (x ^ a - 1)) := by
      ext x
      simp only [Pi.neg_apply]
      rw [smul_eq_mul, ← neg_mul, neg_inv, neg_sub, hellingerFun]
    rw [this]
    refine ConcaveOn.neg ?_
    exact ((Real.concaveOn_rpow ha_pos.le ha).sub (convexOn_const _ (convex_Ici 0))).smul
      (by simp [ha])
  | inr ha =>
    have h := convexOn_rpow ha
    unfold hellingerFun
    simp_rw [← smul_eq_mul]
    refine ConvexOn.smul (by simp [ha]) ?_
    exact h.sub (concaveOn_const _ (convex_Ici 0))

lemma tendsto_hellingerFun_div_atTop_of_one_lt (ha : 1 < a) :
    Tendsto (fun x ↦ hellingerFun a x / x) atTop atTop := by
  sorry

lemma tendsto_hellingerFun_div_atTop_of_lt_one (ha : a < 1) :
    Tendsto (fun x ↦ hellingerFun a x / x) atTop (𝓝 0) := by
  sorry

lemma derivAtTop_hellingerFun_of_one_lt (ha : 1 < a) : derivAtTop (hellingerFun a) = ⊤ := by
  rw [derivAtTop, if_pos]
  exact tendsto_hellingerFun_div_atTop_of_one_lt ha

lemma derivAtTop_hellingerFun_of_lt_one (ha : a < 1) :
    derivAtTop (hellingerFun a) = 0 :=
  derivAtTop_of_tendsto (tendsto_hellingerFun_div_atTop_of_lt_one ha)

lemma derivAtTop_hellingerFun_of_le_one (ha : a ≤ 1) :
    derivAtTop (hellingerFun a) = 0 := by
  by_cases ha_eq : a = 1
  · exact ha_eq.symm ▸ hellingerFun_one.symm ▸ derivAtTop_const 0
  · exact derivAtTop_hellingerFun_of_lt_one <| lt_of_le_of_ne ha ha_eq

lemma integrable_hellingerFun_iff_integrable_rpow (ha : a ≠ 1) [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν
      ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  simp_rw [hellingerFun]
  rw [integrable_const_mul_iff]
  swap; · simp [sub_eq_zero, ha]
  simp_rw [sub_eq_add_neg, integrable_add_const_iff]

lemma integrable_hellingerFun_rnDeriv_of_le_one (ha_pos : 0 < a) (ha : a ≤ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine integrable_f_rnDeriv_of_derivAtTop_ne_top μ ν ?_ ?_ ?_
  · exact stronglyMeasurable_hellingerFun ha_pos
  · exact convexOn_hellingerFun ha_pos
  · rw [derivAtTop_hellingerFun_of_le_one ha]
    exact EReal.zero_ne_top

lemma integrable_rpow_rnDeriv_of_lt_one (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν := by
  rw [← integrable_hellingerFun_iff_integrable_rpow ha.ne]
  exact integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha.le

end HellingerFun

/-- Hellinger divergence of order `a`. Meaningful for `a ∈ (0, 1) ∪ (1, ∞)`. -/
noncomputable def hellingerDiv (a : ℝ) (μ ν : Measure α) : EReal := fDiv (hellingerFun a) μ ν

/--Note that the correct definition of Hellinger divergence at `a = 1` would be to be equal to the
KL divergence, not the f divergence with `f = fun x ↦ 0`. -/
@[simp] lemma hellingerDiv_one (μ ν : Measure α) : hellingerDiv 1 μ ν = 0 := by
  rw [hellingerDiv, hellingerFun_one, fDiv_zero]

section HellingerEq

/--If `a ≤ 1` use `hellingerDiv_eq_integral_of_integrable_of_le_one` or
`hellingerDiv_eq_integral_of_le_one`, as they have fewer hypotheses.-/
lemma hellingerDiv_eq_integral_of_integrable_of_ac
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) (h_ac : 1 < a → μ ≪ ν) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  rw [hellingerDiv, fDiv_of_integrable h_int]
  rcases (lt_or_ge 1 a) with ha | ha
  · rw [Measure.singularPart_eq_zero_of_ac <| h_ac ha]
    norm_num
  · rw [derivAtTop_hellingerFun_of_le_one ha]
    norm_num

lemma hellingerDiv_eq_integral_of_integrable_of_le_one (ha : a ≤ 1)
    (h_int : Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
  hellingerDiv_eq_integral_of_integrable_of_ac h_int ha.not_lt.elim

lemma hellingerDiv_eq_integral_of_le_one (ha_pos : 0 < a) (ha : a ≤ 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν :=
  hellingerDiv_eq_integral_of_integrable_of_ac
    (integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha) ha.not_lt.elim

lemma hellingerDiv_of_not_integrable
    (h : ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν) :
    hellingerDiv a μ ν = ⊤ := fDiv_of_not_integrable h

lemma hellingerDiv_of_one_lt_not_ac (ha : 1 < a) (h_ac : ¬ μ ≪ ν) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤ := fDiv_of_not_ac (derivAtTop_hellingerFun_of_one_lt ha) h_ac

lemma hellingerDiv_eq_top_iff (a : ℝ) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ (1 < a ∧ ¬ μ ≪ ν) := by
  constructor
  · contrapose!
    rintro ⟨h_int, h_ac⟩
    rw [hellingerDiv_eq_integral_of_integrable_of_ac h_int h_ac]
    exact EReal.coe_ne_top _
  · rintro (h | ⟨ha, h_ac⟩)
    · exact hellingerDiv_of_not_integrable h
    · exact hellingerDiv_of_one_lt_not_ac ha h_ac

lemma hellingerDiv_ne_top_iff (a : ℝ) (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ (1 < a → μ ≪ ν) := by
  rw [ne_eq, hellingerDiv_eq_top_iff]
  push_neg
  rfl

lemma hellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν = ⊤
      ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
  rw [hellingerDiv_eq_top_iff, and_iff_right ha]

lemma hellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    hellingerDiv a μ ν ≠ ⊤
      ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_one_lt ha]
  push_neg
  rfl

lemma hellingerDiv_eq_top_iff_of_le_one (ha : a ≤ 1) (μ ν : Measure α) :
    hellingerDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  refine ⟨?_, fun h ↦ hellingerDiv_of_not_integrable h⟩
  contrapose!
  rintro h_int
  rw [hellingerDiv_eq_integral_of_integrable_of_le_one ha h_int]
  exact EReal.coe_ne_top _

lemma hellingerDiv_ne_top_iff_of_le_one (ha : a ≤ 1) (μ ν : Measure α) :
    hellingerDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν := by
  rw [ne_eq, hellingerDiv_eq_top_iff_of_le_one ha, not_not]

lemma hellingerDiv_ne_top_of_le_one (ha_pos : 0 < a) (ha : a ≤ 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≠ ⊤ := by
  rw [hellingerDiv_ne_top_iff_of_le_one ha]
  exact integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha

lemma hellingerDiv_eq_integral_of_ne_top (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ] [SigmaFinite ν]
    (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = ∫ x, hellingerFun a ((∂μ/∂ν) x).toReal ∂ν := by
  rw [hellingerDiv, fDiv_of_ne_top h]
  cases lt_or_gt_of_ne ha_ne_one with
  | inl ha_lt => rw [derivAtTop_hellingerFun_of_lt_one ha_lt, zero_mul, add_zero]
  | inr ha_gt =>
    rw [hellingerDiv_ne_top_iff_of_one_lt ha_gt] at h
    rw [Measure.singularPart_eq_zero_of_ac h.2]
    simp

lemma hellingerDiv_eq_integral_of_ne_top' (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν Set.univ := by
  rw [hellingerDiv_eq_integral_of_ne_top ha_ne_one h]
  simp_rw [hellingerFun, integral_mul_left]
  rw [integral_sub _ (integrable_const _),
    integral_const, smul_eq_mul, mul_one, mul_sub, EReal.coe_sub, EReal.coe_mul, EReal.coe_mul,
    EReal.coe_ennreal_toReal (measure_ne_top _ _)]
  rw [← integrable_hellingerFun_iff_integrable_rpow ha_ne_one]
  by_contra h_not_int
  exact h (hellingerDiv_of_not_integrable h_not_int)

lemma hellingerDiv_eq_integral_of_ne_top'' (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsProbabilityMeasure ν] (h : hellingerDiv a μ ν ≠ ⊤) :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ := by
  rw [hellingerDiv_eq_integral_of_ne_top' ha_ne_one h]
  simp

lemma hellingerDiv_eq_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν = (a - 1)⁻¹ * ∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν - (a - 1)⁻¹ * ν Set.univ :=
  hellingerDiv_eq_integral_of_ne_top' ha.ne (hellingerDiv_ne_top_of_le_one ha_pos ha.le μ ν)

end HellingerEq

--Maybe we could write something like this for the conditional case? Would it be useful?
lemma hellingerDiv_le_of_lt_one (ha_pos : 0 < a) (ha : a < 1) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    hellingerDiv a μ ν ≤ (1 - a)⁻¹ * ν Set.univ := by
  rw [hellingerDiv]
  refine (fDiv_le_zero_add_top (stronglyMeasurable_hellingerFun ha_pos)
    (convexOn_hellingerFun ha_pos)).trans_eq ?_
  rw [derivAtTop_hellingerFun_of_lt_one ha, hellingerFun, zero_rpow ha_pos.ne']
  simp only [zero_sub, mul_neg, mul_one, zero_mul, add_zero]
  rw [neg_inv, neg_sub]

lemma hellingerDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ := by
  rw [hellingerDiv_eq_integral_of_lt_one' ha_pos ha, hellingerDiv_eq_integral_of_lt_one']
  rotate_left
  · linarith
  · linarith
  simp only [sub_sub_cancel_left]
  simp_rw [← EReal.coe_ennreal_toReal (measure_ne_top _ _), h_eq]
  norm_cast
  simp_rw [mul_sub, ← mul_assoc]
  have : (1 - a) * (a - 1)⁻¹ = a * (-a)⁻¹ := by
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel, inv_neg, mul_comm, neg_mul,
      inv_mul_cancel ha_pos.ne']
    linarith
  rw [integral_rpow_rnDeriv ha_pos ha.ne]
  congr

lemma hellingerDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
  hellingerDiv_symm' ha_pos ha (by simp)

lemma hellingerDiv_nonneg (ha_pos : 0 < a) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ hellingerDiv a μ ν :=
  fDiv_nonneg (convexOn_hellingerFun ha_pos) (continuous_hellingerFun ha_pos).continuousOn
    hellingerFun_one_eq_zero

section Conditional

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : kernel α β}

lemma hellingerDiv_ae_ne_top_iff (a : ℝ) (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ⊤)
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ (1 < a → ∀ᵐ x ∂μ, (κ x) ≪ (η x)) := by
  simp_rw [hellingerDiv_ne_top_iff, eventually_and, eventually_all]

lemma hellingerDiv_ae_ne_top_iff_of_le_one (ha : a ≤ 1) (κ η : kernel α β) :
    (∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ⊤)
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) := by
  simp_rw [hellingerDiv_ne_top_iff_of_le_one ha]

/--Use this version only for the case `1 < a` or when one of the kernels is not finite, otherwise
use `integrable_hellingerDiv_iff_of_lt_one`, as it is strictly more general.-/
lemma integrable_hellingerDiv_iff
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : 1 < a → ∀ᵐ x ∂μ, κ x ≪ η x) :
    Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
      ↔ Integrable (fun x ↦ ∫ b, hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  apply integrable_congr
  filter_upwards [h_int, eventually_all.mpr h_ac] with x hx_int hx_ac
  rw [hellingerDiv_eq_integral_of_integrable_of_ac hx_int hx_ac, EReal.toReal_coe]

lemma integrable_hellingerDiv_iff_of_le_one (ha_pos : 0 < a) (ha : a ≤ 1)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
      ↔ Integrable (fun x ↦ ∫ b, hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  refine integrable_congr (eventually_of_forall fun x ↦ ?_)
  simp_rw [hellingerDiv_eq_integral_of_le_one ha_pos ha, EReal.toReal_coe]

lemma integrable_hellingerDiv_iff' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : 1 < a → ∀ᵐ x ∂μ, κ x ≪ η x) :
    Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
      ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  have h_fin : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ⊤ := by
    filter_upwards [h_int, eventually_all.mpr h_ac] with x hx_int hx_ac
    rcases lt_or_gt_of_ne ha_ne_one with h_lt | h_gt
    · exact hellingerDiv_ne_top_of_le_one ha_pos h_lt.le _ _
    · exact hellingerDiv_ne_top_iff_of_one_lt h_gt _ _ |>.mpr ⟨hx_int, hx_ac h_gt⟩
  have h_eq_eq : ∀ᵐ x ∂μ, (hellingerDiv a (κ x) (η x)).toReal =
      (a - 1)⁻¹ * ((∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) - ((η x) Set.univ).toReal) := by
    filter_upwards [h_fin] with x hx
    rw [hellingerDiv_eq_integral_of_ne_top' ha_ne_one hx, ← EReal.coe_mul,
      EReal.toReal_sub (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe,
      EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal, mul_sub]
    · refine (EReal.mul_eq_top _ _).mp.mt ?_
      push_neg
      exact ⟨fun _ ↦ EReal.coe_ennreal_nonneg _, ⟨fun _ ↦ EReal.coe_ennreal_ne_bot _,
        ⟨by simp only [EReal.coe_ne_top, IsEmpty.forall_iff],
        fun _ ↦ EReal.coe_ennreal_eq_top_iff.mp.mt (measure_ne_top _ _)⟩⟩⟩
    · refine (EReal.mul_eq_bot _ _).mp.mt ?_
      push_neg
      exact ⟨by simp only [EReal.coe_ne_bot, IsEmpty.forall_iff],
        ⟨fun _ ↦ EReal.coe_ennreal_ne_bot _, ⟨fun _ ↦ EReal.coe_ennreal_nonneg _,
        fun _ ↦ EReal.coe_ennreal_eq_top_iff.mp.mt (measure_ne_top _ _)⟩⟩⟩
  rw [integrable_congr h_eq_eq, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr <| (ne_eq _ _).mpr
    <| inv_eq_zero.mp.mt <| sub_ne_zero_of_ne ha_ne_one)]
  obtain ⟨C, ⟨hC_finite, hC⟩⟩ := IsFiniteKernel.exists_univ_le (κ := η)
  refine integrable_add_iff_integrable_left <| (integrable_const C.toReal).mono' ?_ ?_
  · exact kernel.measurable_coe η MeasurableSet.univ |>.ennreal_toReal.neg.aestronglyMeasurable
  refine eventually_of_forall (fun x ↦ ?_)
  rw [norm_eq_abs, abs_neg, abs_eq_self.mpr ENNReal.toReal_nonneg, ENNReal.toReal_le_toReal
    (measure_ne_top _ _) (lt_top_iff_ne_top.mp hC_finite)]
  exact hC x

lemma integrable_hellingerDiv_iff'_of_lt_one (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ
      ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
  integrable_hellingerDiv_iff' ha_pos ha.ne (eventually_of_forall
    (fun _ ↦ integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha.le)) (not_lt_of_gt ha).elim

/-- Conditional Hellinger divergence of order `a`. Meaningful for `a ∈ (0, 1) ∪ (1, ∞)`. -/
noncomputable def condHellingerDiv (a : ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  condFDiv (hellingerFun a) κ η μ

/-! There are multiple combinations of hypotheses that give rise to slightly different versions of
the following lemmas. The ones we will consider as a normal form are when we assume that `μ`, `κ`
and `η` are all finite and `a ∈ (0, 1) ∪ (1, +∞)`.

Consider the following conditions:
1. `condHellingerDiv a κ η μ ≠ ⊤`
2. `condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ`
3.a `∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)` (`h_int`)
3.b `∀ᵐ x ∂μ, (κ x) ≪ (η x)` (`h_ac`)
3.c `Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ` (`h_int'`)
4. `condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ - (a - 1)⁻¹ * ∫ x, ((η x) Set.univ).toReal ∂μ`

Then the following hold:
- 1. ↔ 2. (`condHellingerDiv_eq_integral_iff_ne_top`)
- if `1 < a`:
  - 1. ↔ 3.a ∧ 3.b ∧ 3.c (`condHellingerDiv_ne_top_iff_of_one_lt`)
  - 2. ↔ 3.a ∧ 3.b ∧ 3.c (`condHellingerDiv_eq_integral_iff_of_one_lt`)
  - 3.a ∧ 3.b ∧ 3.c → 4. (`condHellingerDiv_eq_integral'_of_one_lt`)
- if `a < 1`:
  - 1. ↔ 3.c (`condHellingerDiv_ne_top_iff_of_lt_one`)
  - 2. ↔ 3.c (`condHellingerDiv_eq_integral_iff_of_lt_one`)
  - 3.c → 4. (`condHellingerDiv_eq_integral'_of_lt_one`)

The implications 4. → 1./2./3. are not explicitely stated but, if needed, it should be immediate to
prove 4. → 1. and then have all the other implications for free.
-/
section CondHellingerEq

lemma condHellingerDiv_of_not_ae_finite (h_ae : ¬ ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ⊤) :
    condHellingerDiv a κ η μ = ⊤ := condFDiv_of_not_ae_finite h_ae

lemma condHellingerDiv_of_not_ae_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) :
    condHellingerDiv a κ η μ = ⊤ := condFDiv_of_not_ae_integrable h_int

lemma condHellingerDiv_of_not_ae_integrable_of_le_one (ha : a ≤ 1)
    (h_int : ¬ ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)) :
    condHellingerDiv a κ η μ = ⊤ := by
  apply condHellingerDiv_of_not_ae_finite
  rw [hellingerDiv_ae_ne_top_iff_of_le_one ha]
  exact h_int

lemma condHellingerDiv_of_not_ae_ac_of_one_lt (ha : 1 < a) [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_ac : ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x)) :
    condHellingerDiv a κ η μ = ⊤ := by
  apply condHellingerDiv_of_not_ae_finite
  rw [hellingerDiv_ae_ne_top_iff]
  tauto

lemma condHellingerDiv_of_not_integrable
    (h_int : ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
    condHellingerDiv a κ η μ = ⊤ := condFDiv_of_not_integrable h_int

lemma condHellingerDiv_of_not_integrable' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int' : ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = ⊤ := by
  by_cases h_int2 : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x)
  swap; exact condHellingerDiv_of_not_ae_integrable h_int2
  by_cases h_ac : 1 < a → ∀ᵐ x ∂μ, κ x ≪ η x
  swap
  · push_neg at h_ac
    exact condHellingerDiv_of_not_ae_ac_of_one_lt h_ac.1 h_ac.2
  apply condHellingerDiv_of_not_integrable
  rwa [integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int2 h_ac]

lemma condHellingerDiv_of_ae_finite_of_integrable (h_ae : ∀ᵐ x ∂μ, hellingerDiv a (κ x) (η x) ≠ ⊤)
    (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  condFDiv_eq' h_ae h_int2

lemma condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : 1 < a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  condHellingerDiv_of_ae_finite_of_integrable
    ((hellingerDiv_ae_ne_top_iff _ _ _).mpr ⟨h_int, h_ac⟩) h_int2

lemma condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : 1 < a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  condHellingerDiv_of_ae_finite_of_integrable
    ((hellingerDiv_ae_ne_top_iff _ _ _).mpr ⟨h_int, h_ac⟩)
    (integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int h_ac |>.mpr h_int')

lemma condHellingerDiv_of_ae_integrable_of_integrable_of_le_one (ha : a ≤ 1)
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_int2 : Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ) :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  condHellingerDiv_of_ae_finite_of_integrable
    ((hellingerDiv_ae_ne_top_iff_of_le_one ha _ _).mpr h_int) h_int2

lemma condHellingerDiv_of_integrable'_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ :=
  condHellingerDiv_of_ae_finite_of_integrable
    ((hellingerDiv_ae_ne_top_iff_of_le_one ha.le _ _).mpr
      (eventually_of_forall <| fun _ ↦ integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha.le))
    (integrable_hellingerDiv_iff'_of_lt_one ha_pos ha |>.mpr h_int')

lemma condHellingerDiv_eq_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∨ (1 < a ∧ ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∨ ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
  constructor
  · contrapose!
    rintro ⟨h_int, h_ac, h_int2⟩
    rw [condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable h_int h_ac h_int2]
    exact EReal.coe_ne_top _
  · rintro (h_int | ⟨ha, h_ac⟩ | h_int2)
    · exact condHellingerDiv_of_not_ae_integrable h_int
    · exact condHellingerDiv_of_not_ae_ac_of_one_lt ha h_ac
    · exact condHellingerDiv_of_not_integrable h_int2

lemma condHellingerDiv_ne_top_iff [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ (1 < a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∧ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
  rw [ne_eq, condHellingerDiv_eq_top_iff]
  push_neg
  rfl

lemma condHellingerDiv_ne_top_iff' (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ (1 < a → ∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  simp_rw [condHellingerDiv_ne_top_iff]
  refine and_congr_right (fun h_int ↦ and_congr_right (fun h_ac ↦ ?_))
  rw [integrable_hellingerDiv_iff' ha_pos ha_ne_one h_int h_ac]

lemma condHellingerDiv_ne_top_iff_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ (∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  simp_rw [condHellingerDiv_ne_top_iff' (zero_lt_one.trans ha) ha.ne.symm, ha, true_implies]

lemma condHellingerDiv_eq_top_iff_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∨ (1 < a ∧ ¬ ∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∨ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [← not_not (a := _ = ⊤), ← ne_eq, condHellingerDiv_ne_top_iff_of_one_lt ha]
  tauto

lemma condHellingerDiv_eq_top_iff_of_le_one (ha : a ≤ 1) [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∨ ¬ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
  simp only [condHellingerDiv_eq_top_iff, not_eventually, ha.not_lt, false_and, false_or]

lemma condHellingerDiv_ne_top_iff_of_le_one (ha : a ≤ 1) [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ Integrable (fun x ↦ (hellingerDiv a (κ x) (η x)).toReal) μ := by
  simp only [condHellingerDiv_ne_top_iff, ha.not_lt, false_implies, true_and]

lemma condHellingerDiv_eq_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ⊤
      ↔ ¬ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  simp_rw [condHellingerDiv_eq_top_iff_of_le_one ha.le,
    (eventually_of_forall <| fun _ ↦ integrable_hellingerFun_rnDeriv_of_le_one ha_pos ha.le),
    integrable_hellingerDiv_iff'_of_lt_one ha_pos ha, not_true, false_or]

lemma condHellingerDiv_ne_top_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤ ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ := by
  rw [ne_eq, condHellingerDiv_eq_top_iff_of_lt_one ha_pos ha, not_not]

lemma condHellingerDiv_eq_integral_iff_ne_top (ha_pos : 0 < a) (ha_ne_one : a ≠ 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ ≠ ⊤
      ↔ condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ EReal.coe_ne_top _⟩
  rw [condHellingerDiv_ne_top_iff' ha_pos ha_ne_one] at h
  exact condHellingerDiv_of_ae_integrable_of_ae_ac_of_integrable' ha_pos ha_ne_one h.1 h.2.1 h.2.2

lemma condHellingerDiv_eq_integral_iff_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ (∀ᵐ x ∂μ, (κ x) ≪ (η x))
        ∧ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
  (condHellingerDiv_eq_integral_iff_ne_top (zero_lt_one.trans ha) ha.ne.symm).symm.trans
    (condHellingerDiv_ne_top_iff_of_one_lt ha)

lemma condHellingerDiv_eq_integral_iff_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    condHellingerDiv a κ η μ = ∫ x, (hellingerDiv a (κ x) (η x)).toReal ∂μ
      ↔ Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ :=
  (condHellingerDiv_eq_integral_iff_ne_top ha_pos ha.ne).symm.trans
    (condHellingerDiv_ne_top_iff_of_lt_one ha_pos ha)

lemma condHellingerDiv_eq_integral'_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ * ∫ x, ((η x) Set.univ).toReal ∂μ := by
  rw [condHellingerDiv_eq_integral_iff_of_one_lt ha |>.mpr ⟨h_int, h_ac, h_int'⟩]
  norm_cast
  calc
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        - (a - 1)⁻¹ * ((η x) Set.univ).toEReal).toReal ∂μ := by
      apply integral_congr_ae
      filter_upwards [h_int, h_ac] with x hx_int hx_ac
      congr
      exact hellingerDiv_eq_integral_of_ne_top' ha.ne.symm <|
        hellingerDiv_ne_top_iff_of_one_lt ha _ _ |>.mpr ⟨hx_int, hx_ac⟩
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        - (a - 1)⁻¹ * ((η x) Set.univ).toReal) ∂μ := by
      refine integral_congr_ae (eventually_of_forall fun x ↦ ?_)
      dsimp
      rw [EReal.toReal_sub (ne_of_beq_false (by rfl)) (ne_of_beq_false (by rfl))]
      congr
      rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
      all_goals
        simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, EReal.coe_ne_bot, false_and,
          EReal.coe_neg', EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ne_top,
          EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_pos,
          EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_self, not_false_eq_true]
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) ∂μ
        - ∫ x, ((a - 1)⁻¹ * ((η x) Set.univ).toReal) ∂μ :=
      integral_sub (Integrable.const_mul h_int' _)
        (Integrable.const_mul (Integrable.kernel _ MeasurableSet.univ) _)
    _ = _ := by
      rw [integral_mul_left, integral_mul_left]

lemma condHellingerDiv_eq_integral'_of_one_lt' (ha : 1 < a) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ * (μ Set.univ).toReal := by
  simp_rw [condHellingerDiv_eq_integral'_of_one_lt ha h_int h_ac h_int', measure_univ,
    ENNReal.one_toReal, integral_const, smul_eq_mul, mul_one]

lemma condHellingerDiv_eq_integral'_of_one_lt'' (ha : 1 < a) [IsProbabilityMeasure μ]
    [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ := by
  rw [condHellingerDiv_eq_integral'_of_one_lt' ha h_int h_ac h_int', measure_univ,
    ENNReal.one_toReal, EReal.coe_one, mul_one]

lemma condHellingerDiv_eq_integral'_of_lt_one (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ * ∫ x, ((η x) Set.univ).toReal ∂μ := by
  rw [condHellingerDiv_eq_integral_iff_of_lt_one ha_pos ha |>.mpr h_int']
  norm_cast
  calc
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x
        - (a - 1)⁻¹ * ((η x) Set.univ).toEReal).toReal ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      congr
      exact hellingerDiv_eq_integral_of_lt_one' ha_pos ha _ _
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x --from here to the end the proof is the same as the one of `condHellingerDiv_eq_integral'_of_one_lt`, consider separating this part as a lemma
        - (a - 1)⁻¹ * ((η x) Set.univ).toReal) ∂μ := by
      refine integral_congr_ae (eventually_of_forall fun x ↦ ?_)
      dsimp
      rw [EReal.toReal_sub (ne_of_beq_false (by rfl)) (ne_of_beq_false (by rfl))]
      congr
      rw [EReal.toReal_mul, EReal.toReal_coe, EReal.toReal_coe_ennreal]
      all_goals
        simp only [ne_eq, EReal.mul_eq_top, EReal.mul_eq_bot, EReal.coe_ne_bot, false_and,
          EReal.coe_neg', EReal.coe_ennreal_ne_bot, and_false, EReal.coe_ne_top,
          EReal.coe_ennreal_pos, Measure.measure_univ_pos, EReal.coe_pos,
          EReal.coe_ennreal_eq_top_iff, measure_ne_top, or_self, not_false_eq_true]
    _ = ∫ x, ((a - 1)⁻¹ * ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) ∂μ
        - ∫ x, ((a - 1)⁻¹ * ((η x) Set.univ).toReal) ∂μ :=
      integral_sub (Integrable.const_mul h_int' _)
        (Integrable.const_mul (Integrable.kernel _ MeasurableSet.univ) _)
    _ = _ := by
      rw [integral_mul_left, integral_mul_left]

lemma condHellingerDiv_eq_integral'_of_lt_one' (ha_pos : 0 < a) (ha : a < 1) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ * (μ Set.univ).toReal := by
  simp_rw [condHellingerDiv_eq_integral'_of_lt_one ha_pos ha h_int', measure_univ,
    ENNReal.one_toReal, integral_const, smul_eq_mul, mul_one]

lemma condHellingerDiv_eq_integral'_of_lt_one'' (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsFiniteKernel κ] [IsMarkovKernel η]
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condHellingerDiv a κ η μ = (a - 1)⁻¹ * ∫ x, ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x ∂μ
      - (a - 1)⁻¹ := by
  rw [condHellingerDiv_eq_integral'_of_lt_one' ha_pos ha h_int', measure_univ,
    ENNReal.one_toReal, EReal.coe_one, mul_one]

end CondHellingerEq

lemma hellingerDiv_compProd_left [MeasurableSpace.CountableOrCountablyGenerated α β]
    (ha_pos : 0 < a) (μ : Measure α) [IsFiniteMeasure μ] (κ η : kernel α β) [IsFiniteKernel κ]
    [∀ x, NeZero (κ x)] [IsFiniteKernel η] :
    hellingerDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η) = condHellingerDiv a κ η μ := by
  rw [hellingerDiv, condHellingerDiv, fDiv_compProd_left _ _ _
    (stronglyMeasurable_hellingerFun ha_pos) (convexOn_hellingerFun ha_pos)]

end Conditional

end ProbabilityTheory
--TODO: generalize the definition of hellinger to 0, 1 and maybe infinity. at 1 it should be kl, at 0 see the renyi div, at ∞ see if there is anything useful in the renyi divergence paper
--there are some results that we will have to show for `a < 1` and `a > 1` separately and then propagate to the general case by continuity
