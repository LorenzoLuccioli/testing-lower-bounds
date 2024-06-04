/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.KullbackLeibler
import TestingLowerBounds.Hellinger
import TestingLowerBounds.ForMathlib.ERealLogExp
import Mathlib.Probability.Moments
import Mathlib.Data.Real.Sign
import LeanCopilot

/-!
# Rényi divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation


## Implementation details


-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {a : ℝ}

-- todo: move
lemma exp_mul_llr [SigmaFinite μ] [SigmaFinite ν] (hνμ : ν ≪ μ) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos' hνμ] with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

-- todo: move
lemma exp_mul_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (a * llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal ^ a := by
  filter_upwards [hμν <| Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_pos hμν]
    with x hx_lt_top hx_pos
  simp only [llr_def]
  have h_pos : 0 < ((∂μ/∂ν) x).toReal :=  ENNReal.toReal_pos hx_pos.ne' hx_lt_top.ne
  rw [← log_rpow h_pos, exp_log (rpow_pos_of_pos h_pos _)]

--attempt at proving an auxiliary lemma for the DPI, it seems there are some difficulties related to the fact that log is not monotone everywhere, but only in the positive reals, in particular it's not monotone in 0, but the qualtity that we put inside the log can be 0, at least when the two measures are mutually singular. how should we do? Shall we define the Renyi div with the new extended log? that should be at least monotone on all the ENNReals, even though I don't know wether this is already proven or not

-- --find a better name
-- lemma monotone_const_mul_log_const_add_const_mul₂ (b c : ℝ) :
--     Monotone (fun x ↦ c⁻¹ * log (b + c * x)) := by
--   rcases lt_trichotomy c 0 with (h | rfl | h)
--   ·

--     sorry
--   · simp [monotone_const]
--   ·
--     refine Monotone.const_mul ?inr.inr.hf (inv_nonneg_of_nonneg h.le)
--     apply?

--     sorry





--     sorry


-- lemma monotone_mul_log_add_mul₂ (a₁ b₁ a₂ b₂ c : ℝ) (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
--     c⁻¹ * log (a₁ + c * b₁) ≤ c⁻¹ * log (a₂ + c * b₂) := by
--   rcases lt_trichotomy c 0 with (h | rfl | h)
--   ·
--     sorry
--   · norm_num
--   ·
--     gcongr c⁻¹ * log (?_ + c * ?_)

--     sorry

-- variable (x : Real) (y : ENNReal) (z : EReal)
-- #check x * z
-- #check x * y
-- #check y * x
-- #check y * z
-- #check x + y
-- #check y + x
-- #check x + z
-- #check y + z
-- #check y.toReal
-- #check z.toReal
-- #check x.toNNReal
-- -- #check z.toENNreal

-- variable (a : ℝ) (μ ν : Measure α)

-- #check (hellingerDiv a μ ν)
-- #check (a - 1) * (hellingerDiv a μ ν)
-- #check (ν Set.univ)
-- -- #check (ν Set.univ) + (a - 1) * (hellingerDiv a μ ν)

/-- Rényi divergence of order `a`. If `a = 1`, it is defined as `kl μ ν`, otherwise as
`(a - 1)⁻¹ * log (ν(α) + (a - 1) * Hₐ(μ, ν))`.
If `ν` is a probability measure then this becomes the more usual definition
`(a - 1)⁻¹ * log (1 + (a - 1) * Hₐ(μ, ν))`, but this definition maintains some useful properties
also for a general finite measure `ν`, in particular the integral form
`Rₐ(μ, ν) = (a - 1)⁻¹ * log (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)`. -/
noncomputable def renyiDiv (a : ℝ) (μ ν : Measure α) : EReal :=
  if a = 1 then kl μ ν
  else (a - 1)⁻¹ * EReal.log ((↑(ν Set.univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal)

@[simp]
lemma renyiDiv_zero (μ ν : Measure α) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv 0 μ ν = - EReal.log (ν {x | 0 < (∂μ/∂ν) x}) := by
  rw [renyiDiv, if_neg zero_ne_one]
  simp only [zero_sub, ← neg_inv, inv_one, EReal.coe_neg, EReal.coe_one, EReal.coe_zero, neg_mul,
    one_mul, ← sub_eq_add_neg, neg_inj]
  congr
  rw [hellingerDiv_zero'', sub_eq_add_neg, EReal.neg_sub, ← add_assoc, ← sub_eq_add_neg,
    EReal.sub_self, zero_add, EReal.toENNReal_coe]
    <;> simp only [ne_eq, EReal.coe_ennreal_eq_top_iff, EReal.coe_ennreal_ne_bot,measure_ne_top,
      not_false_eq_true, or_self]

@[simp]
lemma renyiDiv_one (μ ν : Measure α) : renyiDiv 1 μ ν = kl μ ν := by
  rw [renyiDiv, if_pos rfl]

lemma renyiDiv_of_ne_one (ha_ne_one : a ≠ 1) (μ ν : Measure α) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * EReal.log ((↑(ν Set.univ) + (a - 1) * (hellingerDiv a μ ν)).toENNReal) := by
  rw [renyiDiv, if_neg ha_ne_one]

@[simp]
lemma renyiDiv_zero_measure (ν : Measure α) [IsFiniteMeasure ν] :
    renyiDiv a 0 ν = sign (a - 1) * ⊥ := by
  by_cases ha : a = 1
  · simp [ha]
  rw_mod_cast [renyiDiv_of_ne_one ha, hellingerDiv_zero_measure, ← mul_assoc, ← neg_sub a 1,
    ← neg_inv, ← neg_mul_eq_mul_neg, mul_inv_cancel (sub_ne_zero.mpr ha)]
  simp only [EReal.coe_neg, EReal.coe_one, neg_mul, one_mul, ← sub_eq_add_neg,
    EReal.sub_self_le_zero, EReal.toENNReal_of_nonpos, EReal.log_zero]
  rcases lt_or_gt_of_ne ha with (ha | ha)
  · simp [sub_neg.mpr ha, Real.sign_of_neg, EReal.mul_bot_of_neg]
  · simp [sub_pos.mpr ha, Real.sign_of_pos, EReal.mul_bot_of_pos]

@[simp]
lemma renyiDiv_zero_measure_right (μ : Measure α) [NeZero μ] :
    renyiDiv a μ 0 = ⊤ := by
  rcases lt_trichotomy a 1 with (ha | rfl | ha)
  · rw [renyiDiv_of_ne_one ha.ne, hellingerDiv_zero_measure_right_of_lt_one ha]
    simp [sub_neg.mpr ha, Real.sign_of_neg, EReal.mul_bot_of_neg]
  · simp
  · rw [renyiDiv_of_ne_one ha.ne', hellingerDiv_zero_measure_right_of_one_le ha.le,
      EReal.mul_top_of_pos (by exact_mod_cast sub_pos.mpr ha)]
    simp only [Measure.coe_zero, Pi.zero_apply, EReal.coe_ennreal_zero, zero_add,
      EReal.toENNReal_top, EReal.log_top]
    rw [EReal.mul_top_of_pos]
    simp [ha]

section RenyiEq

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top' (ha_ne_one : a ≠ 1) (h : hellingerDiv a μ ν = ⊤) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv, if_neg ha_ne_one]
  rcases lt_or_gt_of_ne ha_ne_one with (ha | ha)
  · rw [h, EReal.mul_top_of_neg, EReal.add_bot, EReal.toENNReal_of_nonpos bot_le, EReal.log_zero,
      EReal.mul_bot_of_neg]
      <;> norm_cast <;> simp [ha]
  · rw [h, EReal.mul_top_of_pos, EReal.add_top_of_ne_bot (EReal.coe_ennreal_ne_bot _), EReal.toENNReal_top,
      EReal.log_top, EReal.mul_top_of_pos]
      <;> norm_cast <;> simp [ha]

lemma renyiDiv_eq_top_of_hellingerDiv_eq_top [SigmaFinite μ] [SigmaFinite ν]
    (h : hellingerDiv a μ ν = ⊤) :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha : a = 1
  · rw [← h, ha, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_of_hellingerDiv_eq_top' ha h

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt (ha : 1 < a) [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ renyiDiv_eq_top_of_hellingerDiv_eq_top' ha.ne' h⟩
  contrapose! h
  rw [renyiDiv_of_ne_one ha.ne']
  apply (EReal.mul_eq_top _ _).mp.mt
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_neg', inv_lt_zero, sub_neg, not_lt_of_gt ha,
    EReal.coe_ne_top, EReal.coe_pos, inv_pos, sub_pos, ha, EReal.log_eq_top_iff,
    EReal.toENNReal_eq_top_iff, true_and, false_or]
  apply EReal.add_ne_top
  · simp [measure_ne_top]
  · apply (EReal.mul_eq_top _ _).mp.mt
    simp only [h, and_false, or_false, not_or, not_and, not_lt]
    have h1 : a.toEReal - 1 ≥ 0 := by
      norm_cast
      simp only [sub_nonneg, ha.le]
    have h2 : a.toEReal - 1 ≠ ⊥ := by
      intro _
      simp_all only [le_bot_iff, EReal.zero_ne_bot]
    have h3 : a.toEReal - 1 ≠ ⊤ := mod_cast EReal.coe_ne_top _
    simp [h1, h2, h3]

lemma renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (ha : 1 ≤ a)
    [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ hellingerDiv a μ ν = ⊤ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one, hellingerDiv_one]
  · exact renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_lt
      (lt_of_le_of_ne ha fun h ↦ ha_one h.symm)

lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by
  simp_rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha.le,
    ← integrable_hellingerFun_iff_integrable_rpow ha.ne', hellingerDiv_eq_top_iff, ha.le, true_and]

lemma renyiDiv_ne_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊤ ↔ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∧ μ ≪ ν := by
  rw [ne_eq, renyiDiv_eq_top_iff_of_one_lt ha]
  simp

-- the only advantage of these two lemmas over the previous ones is that they also work for `a = 1`,
-- but I don't think it's worth it to keep them, it's probaly better to switch to the convention of
-- using only `(fun x ↦ ((∂μ/∂ν) x).toReal ^ a)` and not `hellingerFun`

-- lemma renyiDiv_eq_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
--     [SigmaFinite μ] [IsFiniteMeasure ν] :
--     renyiDiv a μ ν = ⊤
--       ↔ ¬ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∨ ¬ μ ≪ ν := by
--   rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha, hellingerDiv_eq_top_iff_of_one_le ha]

-- lemma renyiDiv_ne_top_iff_of_one_le (ha : 1 ≤ a) (μ ν : Measure α)
--     [SigmaFinite μ] [IsFiniteMeasure ν] :
--     renyiDiv a μ ν ≠ ⊤
--       ↔ Integrable (fun x ↦ hellingerFun a ((∂μ/∂ν) x).toReal) ν ∧ μ ≪ ν := by
--   rw [ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le ha,
--     hellingerDiv_eq_top_iff_of_one_le ha]
--   push_neg
--   rfl


/-TODO: prove that this ↓ holds forall a, we can use the monotonocity of the Renyi div, but we would
have to prove it before.
Maybe it's not true actually, see `Theorem 24` of the paper `Renyi divergence and Kullback-Leibler divergence`.
It says that `μ ⟂ ν` is equivalent to the fact that for every a `Rₐ(μ, ν) = ⊤`, but it may happen
that `Rₐ(μ, ν) = ⊤` for some `a ≥ 1`, but not for all `a`, it may not imply that `μ ⟂ ν`. Actually
this is most likely the case, otherwise we would have that `Rₐ(μ, ν) = ⊤` for some `a` iff
`Rₐ(μ, ν) = ⊤` for all `a`, which  think is not true.
-/
lemma renyiDiv_eq_top_iff_mutuallySingular_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ ↔ μ ⟂ₘ ν := by
  rw [renyiDiv_of_ne_one ha.ne, EReal.mul_eq_top,
    ← toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_lt_one ha_nonneg ha]
  simp [ha, not_lt_of_gt ha]

lemma renyiDiv_ne_bot_of_le_one (ha : a ≤ 1) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊥ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_ne_bot μ ν
  replace ha : a < 1 := lt_of_le_of_ne ha ha_one
  rw [renyiDiv_of_ne_one ha_one, ne_eq, EReal.mul_eq_bot]
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_pos, inv_pos, sub_pos, not_lt_of_gt ha,
    EReal.coe_ne_top, EReal.coe_neg', inv_lt_zero, sub_neg, ha, EReal.log_eq_top_iff,
    EReal.toENNReal_eq_top_iff, true_and, false_or]
  exact meas_univ_add_mul_hellingerDiv_ne_top_of_lt_one ha

lemma renyiDiv_eq_bot_iff_of_one_lt (ha : 1 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊥ ↔ μ = 0 := by
  rw [renyiDiv_of_ne_one ha.ne', EReal.mul_eq_bot]
  simp only [EReal.coe_ne_bot, false_and, EReal.coe_pos, inv_pos, sub_pos, ha, EReal.log_eq_bot_iff,
    true_and, EReal.coe_ne_top, EReal.coe_neg', inv_lt_zero, sub_neg, not_lt_of_gt ha,
    EReal.log_eq_top_iff, EReal.toENNReal_eq_top_iff, or_self, or_false, false_or]
  exact toENNReal_meas_univ_add_mul_hellingerDiv_eq_zero_iff_of_one_lt ha

lemma renyiDiv_ne_bot [hμ : NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν ≠ ⊥ := by
  rcases le_or_lt a 1 with (ha | ha)
  · exact renyiDiv_ne_bot_of_le_one ha
  · exact (renyiDiv_eq_bot_iff_of_one_lt ha).mp.mt hμ.out

-- lemma renyiDiv_eq_top_iff_of_one_lt (ha : 1 < a) [SigmaFinite μ] [IsFiniteMeasure ν] :
--     renyiDiv a μ ν = ⊤ ↔ ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν ∨ ¬ μ ≪ ν := by

/- TODO: it may be possible to handle also the cases where `ν` is infinite in many of the lemmas
in this section, since in this case, if `a < 1`, then `Rₐ(μ, ν) = ⊥`, it is likely possible to
prove similar properties in the case where `1 < a`. Maybe something similar is possible also for
`μ`, but for now I'm not sure how. -/

lemma renyiDiv_of_mutuallySingular (ha_nonneg : 0 ≤ a) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ⟂ₘ ν) :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha : a < 1
  · rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha]
    exact hμν
  · rw [renyiDiv_eq_top_iff_hellingerDiv_eq_top_of_one_le (le_of_not_lt ha)]
    exact hellingerDiv_of_mutuallySingular_of_one_le (le_of_not_lt ha) hμν

lemma renyiDiv_of_one_lt_of_not_integrable (ha : 1 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : ¬ Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) :
    renyiDiv a μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inl h_int

lemma renyiDiv_of_one_le_of_not_ac (ha : 1 ≤ a) (h_ac : ¬ μ ≪ ν)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = ⊤ := by
  by_cases ha_one : a = 1
  · rw [ha_one, renyiDiv_one]
    exact kl_of_not_ac h_ac
  replace ha : 1 < a := lt_of_le_of_ne ha fun h ↦ ha_one h.symm
  rw [renyiDiv_eq_top_iff_of_one_lt ha]
  exact Or.inr h_ac

end RenyiEq

lemma renyiDiv_eq_top_forall_of_eq_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) [NeZero μ]
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : renyiDiv a μ ν = ⊤) :
    ∀ a', 0 ≤ a' → renyiDiv a' μ ν = ⊤ := by
  rw [renyiDiv_eq_top_iff_mutuallySingular_of_lt_one ha_nonneg ha] at h
  exact fun _ ha' ↦ renyiDiv_of_mutuallySingular ha' h

section IntegralForm

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`. -/
lemma renyiDiv_eq_log_integral_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    renyiDiv a μ ν = (a - 1)⁻¹ * EReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)) := by
  rw [renyiDiv_of_ne_one ha.ne, meas_univ_add_mul_hellingerDiv_eq ha_pos.ne' ha.ne]
  · rfl
  · exact hellingerDiv_ne_top_of_lt_one ha_pos.le ha _ _

/-- The Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `ν`.
If `a < 1`, use `renyiDiv_eq_log_integral_of_lt_one` instead. -/
lemma renyiDiv_eq_log_integral (ha_pos : 0 < a) (ha_ne_one : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν = (a - 1)⁻¹ * EReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ a ∂ν)) := by
  rw [renyiDiv_of_ne_one ha_ne_one, meas_univ_add_mul_hellingerDiv_eq (by linarith) ha_ne_one]
  · rfl
  rcases lt_or_gt_of_ne ha_ne_one with (ha | ha)
  · exact hellingerDiv_ne_top_of_lt_one ha_pos.le ha _ _
  · exact (hellingerDiv_ne_top_iff_of_one_lt ha _ _).mpr ⟨h_int, h_ac⟩

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`. -/
lemma renyiDiv_eq_log_integral_of_lt_one' (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * EReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ)) := by
  rw [renyiDiv_eq_log_integral_of_lt_one ha_pos ha, integral_rpow_rnDeriv ha_pos ha.ne]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

/-- If `μ ≪ ν`, the Rényi divergence `renyiDiv a μ ν` can be written as the log of an integral
with respect to `μ`.
If `a < 1`, use `renyiDiv_eq_log_integral_of_lt_one'` instead. -/
lemma renyiDiv_eq_log_integral' (ha_pos : 0 < a) (ha : a ≠ 1) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ a) ν) (h_ac : μ ≪ ν) :
    renyiDiv a μ ν
      = (a - 1)⁻¹ * EReal.log (ENNReal.ofReal (∫ x, ((∂μ/∂ν) x).toReal ^ (a - 1) ∂μ)) := by
  rw [renyiDiv_eq_log_integral ha_pos ha h_int h_ac, integral_rpow_rnDeriv ha_pos ha]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [Measure.inv_rnDeriv h_ac] with x hx
  rw [← hx, Pi.inv_apply, ENNReal.toReal_inv, inv_rpow ENNReal.toReal_nonneg,
    ← rpow_neg ENNReal.toReal_nonneg, neg_sub]

end IntegralForm

lemma renyiDiv_symm' (ha_pos : 0 < a) (ha : a < 1) (h_eq : μ Set.univ = ν Set.univ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ := by
  rw [renyiDiv_of_ne_one ha.ne, renyiDiv_of_ne_one (by linarith)]
  simp only [sub_sub_cancel_left, neg_mul]
  rw [← mul_assoc, ← mul_assoc]
  have h : (1 - a) * hellingerDiv a μ ν = a * hellingerDiv (1 - a) ν μ :=
    hellingerDiv_symm' ha_pos ha h_eq
  have : (1 - (a : EReal)) * ↑(a - 1)⁻¹ = -1 := by
    norm_cast
    rw [← neg_neg (1 - a), neg_sub, neg_mul, mul_inv_cancel]
    · simp
    · linarith
  rw [this, ← EReal.coe_mul, inv_neg, mul_neg, mul_inv_cancel ha_pos.ne', h_eq]
  simp only [EReal.coe_neg, EReal.coe_one, one_mul]
  congr 4
  norm_cast
  simp only [EReal.coe_sub, EReal.coe_one, sub_sub_cancel_left, EReal.coe_neg, neg_mul, ← h]
  rw_mod_cast [← neg_mul, neg_sub]

lemma renyiDiv_symm (ha_pos : 0 < a) (ha : a < 1)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (1 - a) * renyiDiv a μ ν = a * renyiDiv (1 - a) ν μ :=
  renyiDiv_symm' ha_pos ha (by simp)

#check EReal.log_ofReal_of_pos
#check integral_rpow_rnDeriv_eq_zero_iff_mutuallySingular

-- todo: `ν ≪ μ` is necessary (?) due to the llr being 0 when `(∂μ/∂ν) x = 0`.
-- In that case, `exp (llr μ ν x) = 1 ≠ 0 = (∂μ/∂ν) x`.
lemma coe_cgf_llr_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [hν : NeZero ν] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * renyiDiv a μ ν := by
  rw_mod_cast [renyiDiv_eq_log_integral_of_lt_one ha_pos ha, ← mul_assoc,
    mul_inv_cancel (by linarith), one_mul, cgf, mgf]
  have h_ms : ¬ μ ⟂ₘ ν := by
    intro h
    exact hν.out <| Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hνμ h.symm
  rw [EReal.log_ofReal_of_pos]
  swap
  · refine integral_rpow_rnDeriv_pos_iff_mutuallySingular ha_pos.ne' ?_ |>.mpr h_ms
    exact integrable_rpow_rnDeriv_of_lt_one ha_pos.le ha
  congr 2
  exact integral_congr_ae (exp_mul_llr hνμ)

lemma cgf_llr_of_lt_one (ha_pos : 0 < a) (ha : a < 1)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≪ μ) :
    cgf (llr μ ν) ν a = (a - 1) * (renyiDiv a μ ν).toReal := by
  by_cases hν : NeZero ν
  swap
  · have ha' : a - 1 < 0 := by linarith
    rw [not_neZero.mp hν]
    by_cases hμ : NeZero μ
    swap; simp [not_neZero.mp hμ, ha', Real.sign_of_neg]
    simp [ha'.ne]
  have : (a - 1) * (renyiDiv a μ ν).toReal = ((a - 1) * renyiDiv a μ ν).toReal := by
    rw [EReal.toReal_mul, ← EReal.coe_one, ← EReal.coe_sub, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr_of_lt_one ha_pos ha hνμ, EReal.toReal_coe]

lemma coe_cgf_llr' (ha_pos : 0 < a) [hν : NeZero μ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν) (hμν : μ ≪ ν) :
    cgf (llr μ ν) μ a = a * renyiDiv (1 + a) μ ν := by
  rw_mod_cast [renyiDiv_eq_log_integral' (by linarith) (by linarith) h_int hμν, ← mul_assoc,
    add_sub_cancel_left, mul_inv_cancel ha_pos.ne', one_mul, cgf, mgf]
  have h_ms : ¬ μ ⟂ₘ ν := by
    intro h
    exact hν.out <| Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hμν h
  rw [EReal.log_ofReal_of_pos]
  swap;
  · rw [← integral_rnDeriv_smul hμν]
    simp_rw [smul_eq_mul, mul_comm ((∂μ/∂ν) _).toReal,
      ← Real.rpow_add_one' ENNReal.toReal_nonneg (by linarith), add_comm a]
    exact integral_rpow_rnDeriv_pos_iff_mutuallySingular (by linarith) h_int |>.mpr h_ms
  congr 2
  refine integral_congr_ae (exp_mul_llr' hμν)


lemma cgf_llr' (ha_pos : 0 < a) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_int : Integrable (fun x ↦ ((∂μ/∂ν) x).toReal ^ (1 + a)) ν) (hμν : μ ≪ ν) :
    cgf (llr μ ν) μ a = a * (renyiDiv (1 + a) μ ν).toReal := by
  by_cases hμ : NeZero μ
  swap
  · rw [not_neZero.mp hμ]
    simp [ha_pos.ne', sign_of_pos ha_pos]
  have : a * (renyiDiv (1 + a) μ ν).toReal = (a * renyiDiv (1 + a) μ ν).toReal := by
    rw [EReal.toReal_mul, EReal.toReal_coe]
  rw [this, ← coe_cgf_llr' ha_pos h_int hμν, EReal.toReal_coe]

section RenyiMeasure

/-- Density of the Rényi measure `renyiMeasure a μ ν` with respect to `μ + ν`. -/
noncomputable
def renyiDensity (a : ℝ) (μ ν : Measure α) (x : α) : ℝ≥0∞ :=
  ((∂μ/∂(μ + ν)) x) ^ a * ((∂ν/∂(μ + ν)) x) ^ (1 - a)
    * ENNReal.ofReal (exp (- (a - 1) * (renyiDiv a μ ν).toReal))

/-- Tilted measure of `μ` with respect to `ν` parametrized by `a`. -/
noncomputable
def renyiMeasure (a : ℝ) (μ ν : Measure α) : Measure α :=
  (μ + ν).withDensity (renyiDensity a μ ν)

end RenyiMeasure

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : kernel α β}


/-- Rényi divergence between two kernels κ and η conditional to a measure μ.
It is defined as `Rₐ(κ, η | μ) := Rₐ(μ ⊗ₘ κ, μ ⊗ₘ η)`. -/
noncomputable
def condRenyiDiv (a : ℝ) (κ η : kernel α β) (μ : Measure α) : EReal :=
  renyiDiv a (μ ⊗ₘ κ) (μ ⊗ₘ η)

/-Maybe this can be stated in a nicer way, but I didn't find a way to do it. It's probably good
enough to use `condRenyiDiv_of_lt_one`.-/
lemma condRenyiDiv_zero (κ η : kernel α β) (μ : Measure α) [IsFiniteMeasure μ]
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    condRenyiDiv 0 κ η μ = - log ((μ ⊗ₘ η) {x | 0 < (∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x}).toReal := by
  rw [condRenyiDiv, renyiDiv_zero]

@[simp]
lemma condRenyiDiv_one [CountableOrCountablyGenerated α β] (κ η : kernel α β) (μ : Measure α)
    [IsMarkovKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv 1 κ η μ = condKL κ η μ := by
  rw [condRenyiDiv, renyiDiv_one, kl_compProd_left]

section TopAndBounds

lemma condRenyiDiv_eq_top_iff_of_one_le [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤
      ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∨ ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ
        ∨ ¬ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_one_le ha,
    kernel.Measure.absolutelyContinuous_compProd_right_iff, integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))]
  tauto

lemma condRenyiDiv_ne_top_iff_of_one_le [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤
      ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
        ∧ Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ
        ∧ ∀ᵐ x ∂μ, κ x ≪ η x := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_one_le ha]
  push_neg
  rfl

lemma condRenyiDiv_eq_top_iff_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha : a < 1) (κ η : kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = ⊤
    ↔ ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
      ∨ ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  rw [condRenyiDiv, renyiDiv_eq_top_iff_of_lt_one ha, integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))]
  tauto

lemma condRenyiDiv_ne_top_iff_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha : a < 1) (κ η : kernel α β) (μ : Measure α)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤
    ↔ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
      ∧ Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ := by
  rw [ne_eq, condRenyiDiv_eq_top_iff_of_lt_one ha_nonneg ha]
  push_neg
  rfl

lemma condRenyiDiv_ne_top_of_lt_one (ha_nonneg : 0 ≤ a) (ha : a < 1) (κ η : kernel α β)
    (μ : Measure α) [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ ≠ ⊤ := by
  rw [condRenyiDiv, ne_eq, renyiDiv_eq_top_iff_hellingerDiv_eq_top]
  exact hellingerDiv_ne_top_of_lt_one ha_nonneg ha _ _

lemma condRenyiDiv_of_not_ae_integrable [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬ (∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))) :
    condRenyiDiv a κ η μ = ⊤ := by
  by_cases ha : a < 1
  · have := integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha (μ := μ ⊗ₘ κ) (ν := μ ⊗ₘ η)
    rw [integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))] at this
    exfalso
    exact h_int this.1
  · rw [condRenyiDiv_eq_top_iff_of_one_le (le_of_not_lt ha)]
    left
    exact h_int

lemma condRenyiDiv_of_not_integrable [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ¬Integrable (fun x ↦ ∫ (b : β), hellingerFun a ((∂κ x/∂η x) b).toReal ∂η x) μ) :
    condRenyiDiv a κ η μ = ⊤ := by
  by_cases ha : a < 1
  · have := integrable_hellingerFun_rnDeriv_of_lt_one ha_nonneg ha (μ := μ ⊗ₘ κ) (ν := μ ⊗ₘ η)
    rw [integrable_f_rnDeriv_compProd_right_iff
      (stronglyMeasurable_hellingerFun (by linarith)) (convexOn_hellingerFun (by linarith))] at this
    exfalso
    exact h_int this.2
  · rw [condRenyiDiv_eq_top_iff_of_one_le (le_of_not_lt ha)]
    exact Or.inr (Or.inl h_int)

lemma condRenyiDiv_of_one_le_of_not_ac [CountableOrCountablyGenerated α β] (ha : 1 ≤ a)
    [IsFiniteKernel κ] [IsFiniteKernel η] [IsFiniteMeasure μ] (h_ac : ¬ ∀ᵐ x ∂μ, κ x ≪ η x) :
    condRenyiDiv a κ η μ = ⊤ := by
  rw [condRenyiDiv_eq_top_iff_of_one_le ha]
  exact Or.inr (Or.inr h_ac)

lemma condRenyiDiv_of_lt_one [CountableOrCountablyGenerated α β] (ha_nonneg : 0 ≤ a)
    (ha_lt_one : a < 1) (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ] :
    condRenyiDiv a κ η μ = (a - 1)⁻¹
      * log (((μ ⊗ₘ η) Set.univ).toReal + (a - 1) * (condHellingerDiv a κ η μ).toReal) := by
  rw [condRenyiDiv, renyiDiv_of_lt_one ha_nonneg ha_lt_one, hellingerDiv_compProd_left ha_nonneg _]

lemma condRenyiDiv_of_one_lt_of_ac [CountableOrCountablyGenerated α β] (ha_one_lt : 1 < a)
    (κ η : kernel α β) (μ : Measure α) [IsFiniteKernel κ] [∀ x, NeZero (κ x)]
    [IsFiniteKernel η] [IsFiniteMeasure μ]
    (h_int : ∀ᵐ x ∂μ, Integrable (fun b ↦ hellingerFun a ((∂κ x/∂η x) b).toReal) (η x))
    (h_ac : ∀ᵐ x ∂μ, (κ x) ≪ (η x))
    (h_int' : Integrable (fun x ↦ ∫ b, ((∂κ x/∂η x) b).toReal ^ a ∂η x) μ) :
    condRenyiDiv a κ η μ = (a - 1)⁻¹
      * log (((μ ⊗ₘ η) Set.univ).toReal + (a - 1) * (condHellingerDiv a κ η μ).toReal) := by
  have ha_pos : 0 < a := by linarith
  rw [condRenyiDiv, renyiDiv_of_one_lt_of_integrable_of_ac ha_one_lt _ _,
    hellingerDiv_compProd_left ha_pos.le _]
  · refine (integrable_f_rnDeriv_compProd_right_iff (stronglyMeasurable_hellingerFun ha_pos.le)
      (convexOn_hellingerFun ha_pos.le)).mpr ⟨h_int, ?_⟩
    apply (integrable_hellingerDiv_iff h_int fun _ ↦ h_ac).mp
    exact (integrable_hellingerDiv_iff' ha_pos ha_one_lt.ne' h_int fun _ ↦ h_ac).mpr h_int'
  · exact kernel.Measure.absolutelyContinuous_compProd_iff.mpr ⟨fun _ a ↦ a, h_ac⟩

end TopAndBounds


end Conditional

section DataProcessingInequality

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : kernel α β}

--failed attempt at proving the data processing inequality for the Rényi divergence, see also the comment at the beginning of the file about `monotone_const_mul_log_const_add_const_mul₂`

-- lemma le_renyiDiv_of_le_hellingerDiv


-- lemma le_renyiDiv_compProd [CountableOrCountablyGenerated α β] (ha_pos : 0 < a)
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] :
--     renyiDiv a μ ν ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) := by



--   le_fDiv_compProd μ ν κ η (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

-- lemma renyiDiv_fst_le [Nonempty β] [StandardBorelSpace β] (ha_pos : 0 < a)
--     (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     renyiDiv a μ.fst ν.fst ≤ renyiDiv a μ ν :=
--   fDiv_fst_le _ _ (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

-- lemma renyiDiv_snd_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
--     (μ ν : Measure (α × β)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
--     renyiDiv a μ.snd ν.snd ≤ renyiDiv a μ ν :=
--   fDiv_snd_le _ _ (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

-- lemma renyiDiv_comp_le_compProd [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
--     renyiDiv a (μ ∘ₘ κ) (ν ∘ₘ η) ≤ renyiDiv a (μ ⊗ₘ κ) (ν ⊗ₘ η) :=
--   fDiv_comp_le_compProd μ ν κ η (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

-- lemma renyiDiv_comp_left_le [Nonempty α] [StandardBorelSpace α]
--     [CountableOrCountablyGenerated α β] (ha_pos : 0 < a) (μ : Measure α) [IsFiniteMeasure μ]
--     (κ η : kernel α β) [IsFiniteKernel κ] [∀ a, NeZero (κ a)] [IsFiniteKernel η] :
--     renyiDiv a (μ ∘ₘ κ) (μ ∘ₘ η) ≤ condrenyiDiv a κ η μ :=
--   fDiv_comp_left_le μ κ η (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

-- /--The Data Processing Inequality for the Hellinger divergence. -/
-- lemma renyiDiv_comp_right_le [Nonempty α] [StandardBorelSpace α] (ha_pos : 0 < a)
--     [CountableOrCountablyGenerated α β]
--     (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
--     (κ : kernel α β) [IsMarkovKernel κ] :
--     renyiDiv a (μ ∘ₘ κ) (ν ∘ₘ κ) ≤ renyiDiv a μ ν :=
--   fDiv_comp_right_le μ ν κ (stronglyMeasurable_hellingerFun ha_pos.le)
--     (convexOn_hellingerFun ha_pos.le) (continuous_hellingerFun ha_pos).continuousOn

end DataProcessingInequality

end ProbabilityTheory
--finish the refactoring of Renyi, prove the DPI. Then try the new category theory approach, we want at first to define the category of measurable spaces with kernels as morphisms and then we would like to have the string diagram widget.
--Some useful flies for that: `Mathlib/MeasureTheory/Category/MeasCat.lean`, `Mathlib/Tactic/CategoryTheory/Coherence.lean`, `Mathlib/Tactic/CategoryTheory/MonoidalComp.lean`
