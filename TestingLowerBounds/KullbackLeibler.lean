/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- theorem foo (n : Nat) : 0 ≤ n := by exact? -- trick to make exact? work TODO : erase this when we are done
import LeanCopilot

import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd
import TestingLowerBounds.ForMathlib.IntegralCongr2
import TestingLowerBounds.ForMathlib.KernelFstSnd

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

section move_this

lemma integrable_rnDeriv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)
    [SigmaFinite μ] {f : α → E} (hf : Integrable f μ) :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal • f x) ν :=
  (integrable_rnDeriv_smul_iff hμν).mpr hf

end move_this

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable def kl (μ ν : Measure α) : EReal :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ↑(∫ x, llr μ ν x ∂μ) else ⊤

lemma kl_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    kl μ ν = ∫ x, llr μ ν x ∂μ := if_pos ⟨h1, h2⟩

@[simp]
lemma kl_of_not_ac (h : ¬ μ ≪ ν) : kl μ ν = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma kl_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : kl μ ν = ⊤ :=
  if_neg (not_and_of_not_right _ h)

lemma derivAtTop_mul_log : derivAtTop (fun x ↦ x * log x) = ⊤ := by
  rw [derivAtTop_eq_top_iff]
  refine (tendsto_congr' ?_).mp tendsto_log_atTop
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  refine ⟨1, fun x hx ↦ ?_⟩
  rw [mul_div_cancel_left₀ _ (zero_lt_one.trans_le hx).ne']

lemma fDiv_mul_log_eq_top_iff [IsFiniteMeasure μ] [SigmaFinite ν] :
    fDiv (fun x ↦ x * log x) μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  rw [fDiv_eq_top_iff]
  simp only [derivAtTop_mul_log, true_and]
  by_cases hμν : μ ≪ ν
  · simp [hμν, integrable_rnDeriv_mul_log_iff hμν]
  · simp [hμν]

lemma kl_eq_fDiv [SigmaFinite μ] [SigmaFinite ν] :
    kl μ ν = fDiv (fun x ↦ x * log x) μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  swap; · rw [fDiv_of_not_ac derivAtTop_mul_log hμν, kl_of_not_ac hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [fDiv_of_derivAtTop_eq_top derivAtTop_mul_log, kl_of_ac_of_integrable hμν h_int,
      if_pos ⟨(integrable_rnDeriv_mul_log_iff hμν).mpr h_int, hμν⟩]
    simp_rw [← smul_eq_mul]
    rw [integral_rnDeriv_smul hμν]
    rfl
  · rw [kl_of_not_integrable h_int, fDiv_of_not_integrable]
    rwa [integrable_rnDeriv_mul_log_iff hμν]

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  rw [kl_eq_fDiv, fDiv_self (by norm_num)]

@[simp]
lemma kl_zero_left : kl 0 ν = 0 := by
  convert kl_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp only [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma kl_zero_right [NeZero μ] : kl μ 0 = ⊤ :=
  kl_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma kl_eq_top_iff : kl μ ν = ⊤ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h <;> push_neg at *
  · contrapose! h
    rw [kl_of_ac_of_integrable h.1 h.2]
    exact EReal.coe_ne_top _
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma kl_ne_top_iff : kl μ ν ≠ ⊤ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  rw [ne_eq, kl_eq_top_iff]
  push_neg
  rfl

lemma kl_ne_top_iff' : kl μ ν ≠ ⊤ ↔ kl μ ν = ∫ x, llr μ ν x ∂μ := by
  constructor
  · rw [kl_ne_top_iff]
    rintro ⟨h1, h2⟩
    rw [kl_of_ac_of_integrable h1 h2]
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

lemma measurable_kl {β : Type*} [MeasurableSpace β] [CountablyGenerated β] (κ η : kernel α β)
    [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (fun a ↦ kl (κ a) (η a)) := by
  simp_rw [kl_eq_fDiv]
  exact measurable_fDiv _ _ (by measurability)

section kl_nonneg

@[simp]
lemma kl_ne_bot (μ ν : Measure α) : kl μ ν ≠ ⊥ := by
  rw [kl]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ kl μ ν :=
  (le_fDiv_of_ac Real.convexOn_mul_log Real.continuous_mul_log.continuousOn hμν).trans_eq
    kl_eq_fDiv.symm

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [kl_of_ac_of_integrable hμν h_int]
  norm_cast
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [ν', Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have hμν' : μ ≪ ν' := by
    refine Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul ?_)
    simp [measure_ne_top ν]
  have h := kl_ge_mul_log' hμν'
  rw [kl_of_ac_of_integrable hμν', integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  norm_cast at h
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν]; simp
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int]; simp
  calc 0
    = ((μ Set.univ).toReal : EReal) * log ((μ Set.univ).toReal / (ν Set.univ).toReal) := by simp
  _ ≤ kl μ ν := kl_ge_mul_log _ _

lemma kl_eq_zero_iff [SigmaFinite μ] [SigmaFinite ν] : kl μ ν = 0 ↔ μ = ν := by
  constructor <;> intro h
  · by_cases hμν : μ ≪ ν
    swap; · rw [kl_of_not_ac hμν] at h; simp_all only [EReal.top_ne_zero]
    by_cases h_int : Integrable (llr μ ν) μ
    swap; · rw [kl_of_not_integrable h_int] at h; simp_all only [EReal.top_ne_zero]
    sorry -- TODO : decide what proof strategy to use here, maybe we could use the fact that jensen's inequality is an equality iff the function is constant a.e., but I don't know wether this is in mathlib
  · exact h ▸ kl_self ν

end kl_nonneg

section Conditional

variable {β γ : Type*} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {κ η : kernel α β}

/--Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one.-/
lemma kl_ae_ne_top_iff : (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [ne_eq, kl_eq_top_iff, Classical.not_imp_iff_and_not, Classical.not_not, Filter.eventually_and]

/--Equivalence between two possible versions of the second condition for the finiteness of the
conditional KL divergence, the first version is the preferred one.-/
lemma integrable_kl_iff (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  apply integrable_congr
  filter_upwards [h_ac, h_int] with a ha1 ha2
  rw [kl_of_ac_of_integrable ha1 ha2, EReal.toReal_coe]

open Classical in

/--
Kullback-Leibler divergence between two kernels κ and η conditional to a measure μ.
It is defined as KL(κ, η | μ) := ∫ x, KL(κ x, η x) dμ.
-/
noncomputable
def condKL (κ η : kernel α β) (μ : Measure α) : EReal :=
  if (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    ∧ (Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ)
  then ((μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) : EReal)
  else ⊤

lemma condKL_of_ae_ne_top_of_integrable (h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)
    (h2 : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := if_pos ⟨h1, h2⟩

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) :=
  condKL_of_ae_ne_top_of_integrable (kl_ae_ne_top_iff.mpr ⟨h_ac, h_ae_int⟩) h_int

lemma condKL_of_ae_ac_of_ae_integrable_of_integrable' (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a)
    (h_ae_int : ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    (h_int : Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = (μ[fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)] : ℝ) := by
  rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h_ac h_ae_int h_int]
  congr 1
  apply integral_congr_ae
  filter_upwards [h_ac, h_ae_int] with a ha1 ha2
  rw [kl_of_ac_of_integrable ha1 ha2, EReal.toReal_coe]

@[simp]
lemma condKL_of_not_ae_ne_top (h : ¬ (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤)) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma condKL_of_not_ae_ac (h : ¬ ∀ᵐ a ∂μ, κ a ≪ η a) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_ne_top
  rw [kl_ae_ne_top_iff]
  tauto

@[simp]
lemma condKL_of_not_ae_integrable (h : ¬ ∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) :
    condKL κ η μ = ⊤ := by
  apply condKL_of_not_ae_ne_top
  rw [kl_ae_ne_top_iff]
  tauto

@[simp]
lemma condKL_of_not_integrable (h : ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ) :
    condKL κ η μ = ⊤ := if_neg (not_and_of_not_right _ h)

@[simp]
lemma condKL_of_not_integrable' (h : ¬ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ) :
    condKL κ η μ = ⊤ := by
  by_cases h_ne_top : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap; exact condKL_of_not_ae_ne_top h_ne_top
  apply condKL_of_not_integrable
  rwa [integrable_kl_iff (kl_ae_ne_top_iff.mp h_ne_top).1 (kl_ae_ne_top_iff.mp h_ne_top).2]

lemma condKL_eq_top_iff : condKL κ η μ = ⊤ ↔
    ¬ (∀ᵐ a ∂μ, κ a ≪ η a) ∨ ¬ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    ∨ ¬ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  constructor <;> intro h
  · contrapose! h
    rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h.1 h.2.1 h.2.2]
    simp only [ne_eq, EReal.coe_ne_top, not_false_eq_true]
  · rcases h with (h | h | h) <;> simp [h]

lemma condKL_ne_top_iff : condKL κ η μ ≠ ⊤ ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a))
    ∧ Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ := by
  rw [ne_eq, condKL_eq_top_iff]
  push_neg
  rfl

lemma condKL_ne_top_iff' : condKL κ η μ ≠ ⊤
    ↔ condKL κ η μ = (μ[fun a ↦ (kl (κ a) (η a)).toReal] : ℝ) := by
  constructor
  · rw [condKL_ne_top_iff]
    rintro ⟨h1, h2, h3⟩
    rw [condKL_of_ae_ac_of_ae_integrable_of_integrable h1 h2 h3]
  · simp_all only [ne_eq, EReal.coe_ne_top, not_false_eq_true, implies_true]

lemma condKL_eq_condFDiv [IsFiniteKernel κ] [IsFiniteKernel η] :
    condKL κ η μ = condFDiv (fun x ↦ x * log x) κ η μ := by
  by_cases h1 : ∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤
  swap
  · simp [h1]
    refine (condFDiv_of_not_ae_finite ?_).symm
    convert h1 using 4 with a
    rw [kl_eq_fDiv]
  by_cases h2 : Integrable (fun x ↦ (kl (κ x) (η x)).toReal) μ
  swap
  · simp [h2]
    refine (condFDiv_of_not_integrable ?_).symm
    convert h2 using 4 with a
    rw [← kl_eq_fDiv]
  simp only [ne_eq, h1, h2, condKL_of_ae_ne_top_of_integrable, ← kl_eq_fDiv, condFDiv_eq']

@[simp]
lemma condKL_self (κ : kernel α β) (μ : Measure α) [IsFiniteKernel κ] : condKL κ κ μ = 0 := by
  simp only [kl_self, ne_eq, not_false_eq_true, eventually_true, EReal.toReal_zero, integrable_zero,
    condKL_of_ae_ne_top_of_integrable, integral_zero, EReal.coe_zero, EReal.zero_ne_top]

@[simp]
lemma condKL_zero_left : condKL 0 η μ = 0 := by
  rw [condKL_of_ae_ne_top_of_integrable _ _]
  · simp only [kernel.zero_apply, kl_zero_left, EReal.toReal_zero, integral_zero, EReal.coe_zero]
  · simp only [kernel.zero_apply, kl_zero_left, ne_eq, EReal.zero_ne_top, not_false_eq_true,
      eventually_true]
  · simp only [kernel.zero_apply, kl_zero_left, EReal.toReal_zero, integrable_zero]

@[simp]
lemma condKL_zero_right [NeZero μ] (h : ∃ᵐ a ∂μ, κ a ≠ 0) : condKL κ 0 μ = ⊤ := by
  simp [h]

@[simp]
lemma condKL_zero_measure : condKL κ η 0 = 0 := by
  have hf_ae : ∀ᵐ a ∂(0 : Measure α), kl (κ a) (η a) ≠ ⊤ := by
    simp only [ne_eq, ae_zero, eventually_bot]
  rw [condKL_of_ae_ne_top_of_integrable hf_ae integrable_zero_measure]
  simp only [integral_zero_measure, EReal.coe_zero]

lemma condKL_ne_bot (κ η : kernel α β) (μ : Measure α) : condKL κ η μ ≠ ⊥ := by
  rw [condKL]
  split_ifs with h
  · simp only [ne_eq, EReal.coe_ne_bot, not_false_eq_true]
  · norm_num

lemma condKL_nonneg (κ η : kernel α β) [IsMarkovKernel κ] [IsMarkovKernel η] (μ : Measure α) :
    0 ≤ condKL κ η μ := by
  rw [condKL_eq_condFDiv]
  apply condFDiv_nonneg
  · exact Real.convexOn_mul_log
  · exact Real.continuous_mul_log.continuousOn
  · norm_num

lemma condKL_const {ξ : Measure β} [IsFiniteMeasure ξ] [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    condKL (kernel.const β μ) (kernel.const β ν) ξ = (kl μ ν) * ξ Set.univ := by
  have h := kl_ne_bot μ ν
  rw [condKL_eq_condFDiv, kl_eq_fDiv] at *
  exact condFDiv_const

--consider generalizing this with 3 kerneks instead of 2, then we could have `Integrable (llr (κ a) (η a)) (ξ a)`, moreover think about changing the arguments of the lemma and making them implicit
lemma measurableSet_integrable_llr (κ η : kernel α β) [IsSFiniteKernel κ] (μ : Measure α) :
    MeasurableSet {a | Integrable (llr (κ a) (η a)) (κ a)} := by
  apply ProbabilityTheory.measurableSet_kernel_integrable -- this may simplify the proof, but it requires κ to be SFinite, moreover I'm note sure how to proceed to prove the measurability of uncurry ...
  simp [llr_def]

  sorry
  -- simp_rw [Integrable]
  -- have h (a : α) : AEStronglyMeasurable (llr (κ a) (η a)) (κ a) :=
  --   StronglyMeasurable.aestronglyMeasurable (stronglyMeasurable_llr (κ a) (η a))
  -- simp only [h, true_and]
  -- refine measurableSet_lt ?hf ?hg
  -- ·
  --   sorry
  -- · simp only [measurable_const]



#check Measure.ae_compProd_iff
#check condKL_eq_top_iff
#check condKL_of_ae_ac_of_ae_integrable_of_integrable

--TODO: the following lemma may be generalized, infact the hypothesys of being markov kernels is only used to prove that `Integrable (fun x ↦ ∫ (y : β), ‖EReal.toReal (kl (κ (x, y)) (η (x, y)))‖ ∂ξ x) μ` is true, given that `Integrable (fun x ↦ ∫ (y : β), EReal.toReal (kl (κ (x, y)) (η (x, y))) ∂ξ x` but if
--this is to handle the case when the lhs is ⊤, in this case the rhs is 'morally' also ⊤, so the equality holds
lemma condKL_compProd_meas_eq_top [CountablyGenerated γ] [SFinite μ] {ξ : kernel α β} [IsSFiniteKernel ξ] {κ η : kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] :
    condKL κ η (μ ⊗ₘ ξ) = ⊤
      ↔ ¬ (∀ᵐ a ∂μ, condKL (kernel.snd' κ a) (kernel.snd' η a) (ξ a) ≠ ⊤)
        ∨ ¬ Integrable (fun x ↦ (condKL (kernel.snd' κ x) (kernel.snd' η x) (ξ x)).toReal) μ := by
  rw [condKL_eq_top_iff]
  constructor
  · by_cases h_ae : ∀ᵐ x ∂(μ ⊗ₘ ξ), κ x ≪ η x --consider putting here explicitly the hp unfolded with ae_compProd_iff, I think I cannot do that, since then the simp_all below will not work
    swap
    · rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ae
      simp_rw [condKL_ne_top_iff]
      simp only [kernel.snd'_apply, eventually_and, not_and, not_eventually]
      tauto
    by_cases h_int : ∀ᵐ x ∂μ ⊗ₘ ξ, Integrable (llr (κ x) (η x)) (κ x)
    swap
    · rw [Measure.ae_compProd_iff] at h_int
      simp_rw [condKL_ne_top_iff]
      swap; sorry
      simp only [kernel.snd'_apply, eventually_and, not_and, not_eventually]
      tauto
    simp_all only [not_true_eq_false, false_or, ne_eq, not_eventually, not_not]
    rw [Measure.integrable_compProd_iff]
    swap; sorry
    push_neg
    intro h
    by_cases h_int2 : ∀ᵐ a ∂μ, Integrable (fun b ↦ EReal.toReal (kl (κ (a, b)) (η (a, b)))) (ξ a)
    swap
    · left
      contrapose! h_int2
      rw [not_frequently] at h_int2
      filter_upwards [h_int2] with a ha_int2
      simp only [condKL_ne_top_iff, kernel.snd'_apply] at ha_int2
      exact ha_int2.2.2
    right
    rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _)] at h_ae
    rw [Measure.ae_compProd_iff] at h_int
    swap; sorry --write this as a separate lemma
    apply Integrable.congr.mt
    swap; exact fun a ↦ ∫ b, EReal.toReal (kl (κ (a, b)) (η (a, b))) ∂(ξ a)
    push_neg
    constructor
    · filter_upwards [h_ae, h_int, h_int2] with a ha_ae ha_int ha_int2
      rw [condKL_of_ae_ac_of_ae_integrable_of_integrable]
      · simp only [EReal.toReal_coe, kernel.snd'_apply]
      · filter_upwards [ha_ae] with b hb using kernel.snd'_apply _ _ _ ▸ hb
      · filter_upwards [ha_int] with b hb using kernel.snd'_apply _ _ _ ▸ hb
      · simp_rw [kernel.snd'_apply]
        exact ha_int2
    · replace h := h h_int2
      contrapose! h
      convert h with a b
      simp only [norm_eq_abs, abs_eq_self]
      apply EReal.toReal_nonneg
      exact kl_nonneg _ _
  · rw [Measure.ae_compProd_iff (kernel.measurableSet_absolutelyContinuous _ _), Measure.ae_compProd_iff]
    swap; sorry
    rw [Measure.integrable_compProd_iff]
    swap; sorry
    rintro h
    contrapose! h
    constructor
    · filter_upwards [h.1, h.2.1, h.2.2.1] with a ha_ae ha_int ha_int2
      apply condKL_ne_top_iff.mpr
      simp only [kernel.snd'_apply]
      exact ⟨ha_ae, ⟨ha_int, ha_int2⟩⟩
    · apply Integrable.congr
      rotate_right; exact fun a ↦ ∫ b, EReal.toReal (kl (κ (a, b)) (η (a, b))) ∂(ξ a)
      · replace h := h.2.2.2
        apply MeasureTheory.Integrable.mono h
        · #check MeasureTheory.Integrable.integral_compProd' --this should be put before, since now we don't hace the explicit hypothesis that we need to use it, but before we had it
          sorry
        refine ae_of_all μ ?mpr.inr.hf.h.a
        intro a
        calc ‖∫ (b : β), EReal.toReal (kl (κ (a, b)) (η (a, b))) ∂ξ a‖
        _ ≤ ∫ (b : β), ‖EReal.toReal (kl (κ (a, b)) (η (a, b)))‖ ∂ξ a :=
          MeasureTheory.norm_integral_le_integral_norm _
        _ = _ := by
          simp only [norm_eq_abs]
          apply (abs_of_nonneg _).symm
          positivity
      · filter_upwards [h.1, h.2.1, h.2.2.1] with a ha_ae ha_int ha_int2 --this part is copied from above, maybe put it as a have before?
        rw [condKL_of_ae_ac_of_ae_integrable_of_integrable]
        · simp only [EReal.toReal_coe, kernel.snd'_apply]
        · filter_upwards [ha_ae] with b hb using kernel.snd'_apply _ _ _ ▸ hb
        · filter_upwards [ha_int] with b hb using kernel.snd'_apply _ _ _ ▸ hb
        · simp_rw [kernel.snd'_apply]
          exact ha_int2

-- TODO: find a better name and finish this, I had to stop because there is not yet the def of κ(x,⬝) for a kernel, I have to look for it
--stated like this it's wrong, find the right formulation
lemma condKL_compProd_meas [CountablyGenerated γ] [SFinite μ] {ξ : kernel α β} [IsSFiniteKernel ξ]
    {κ η : kernel (α × β) γ} [IsMarkovKernel κ] [IsMarkovKernel η] (h : condKL κ η (μ ⊗ₘ ξ) ≠ ⊤) :
    condKL κ η (μ ⊗ₘ ξ) = ∫ x, (condKL (kernel.snd' κ x) (kernel.snd' η x) (ξ x)).toReal ∂μ := by
  rw [condKL_ne_top_iff'.mp h, Measure.integral_compProd (condKL_ne_top_iff.mp h).2.2]
  replace h := condKL_compProd_meas_eq_top.mpr.mt h
  push_neg at h
  norm_cast
  apply integral_congr_ae
  filter_upwards [h.1] with a ha
  simp_rw [condKL_ne_top_iff'.mp ha, EReal.toReal_coe, kernel.snd'_apply]

-- TODO: generalize this to fdiv

lemma kl_compProd_left [CountablyGenerated β] [IsFiniteMeasure μ] [IsMarkovKernel κ]
    [IsFiniteKernel η] :
    kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = condKL κ η μ := by
  rw [kl_eq_fDiv, condKL_eq_condFDiv]
  exact fDiv_compProd_left μ κ η (by measurability) Real.convexOn_mul_log

lemma kl_compProd_right (κ : kernel α β) [CountablyGenerated β] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] [IsMarkovKernel κ] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ κ) = kl μ ν := by
  rw [kl_eq_fDiv, kl_eq_fDiv]
  exact fDiv_compProd_right μ ν κ (by measurability) Real.convexOn_mul_log

section IntegralLemma
#check MeasurableEquiv.piOptionEquivProd
--TODO: put this lemma in a separate file, then PR it to mathlib, I'm not sure it can just go in the same file as integral_congr_ae, since it uses the kernels. maybe we could do a simpler version with 2 probability measures instead of kernels. decide what to do with the 2 vertions, are they both useful?
--I could have proven the second one using the first, but it is probabily easier to do them separately, also in this way we can put them in separate files without worring about dependencies
--also about the names, if we put the two lemmas under different namespaces (the first one could go under something that contains kernel) we can give them the same name
variable {α β: Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {μ : Measure α} {ν : Measure β} {κ : kernel α β}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma integral_congr_ae₂ {f g : α → β → G} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with b hb using hb

--change the name of this one
lemma integral_congr_ae₂' {f g : α → β → G} (h : ∀ᵐ a ∂μ, f a =ᵐ[ν] g a) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with b hb using hb

-- #find_home! ProbabilityTheory.integral_congr_ae₂

end IntegralLemma


/--The chain rule for the KL divergence.-/
lemma kl_compProd [CountablyGenerated β] [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = kl μ ν + condKL κ η μ := by
  by_cases h_prod : (μ ⊗ₘ κ) ≪ (ν ⊗ₘ η)
  swap
  · simp only [h_prod, not_false_eq_true, kl_of_not_ac]
    have h := kernel.Measure.absolutelyContinuous_compProd_iff.mpr.mt h_prod
    set_option push_neg.use_distrib true in push_neg at h
    rcases h with (hμν | hκη)
    · simp only [hμν, not_false_eq_true, kl_of_not_ac]
      exact (EReal.top_add_of_ne_bot (condKL_ne_bot _ _ _)).symm
    · simp only [hκη, not_false_eq_true, condKL_of_not_ae_ac]
      exact (EReal.add_top_of_ne_bot (kl_ne_bot _ _)).symm
  have ⟨hμν, hκη⟩ := kernel.Measure.absolutelyContinuous_compProd_iff.mp h_prod
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · simp only [h_int, not_false_eq_true, kl_of_not_integrable]
    rw [integrable_llr_compProd_iff h_prod] at h_int
    set_option push_neg.use_distrib true in push_neg at h_int
    rcases h_int with ((h | h) | h) <;>
      simp [h, EReal.top_add_of_ne_bot, condKL_ne_bot, EReal.add_top_of_ne_bot, kl_ne_bot]
  have intμν := integrable_llr_of_integrable_llr_compProd h_prod h_int
  have intκη : Integrable (fun a ↦ ∫ (x : β), log (kernel.rnDeriv κ η a x).toReal ∂κ a) μ := by
    apply Integrable.congr (integrable_integral_llr_of_integrable_llr_compProd h_prod h_int)
    filter_upwards [hκη] with a ha
    apply integral_congr_ae
    filter_upwards [ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)] with x hx
    rw [hx, llr_def]
  have intκη2 := ae_integrable_llr_of_integrable_llr_compProd h_prod h_int
  calc kl (μ ⊗ₘ κ) (ν ⊗ₘ η) = ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ) :=
    kl_of_ac_of_integrable h_prod h_int
  _ = ∫ a, ∫ x, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) (a, x) ∂κ a ∂μ := mod_cast Measure.integral_compProd h_int
  _ = ∫ a, ∫ x, log (μ.rnDeriv ν a).toReal
      + log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ := by
    norm_cast
    have h := hμν.ae_le (Measure.ae_ae_of_ae_compProd (kernel.rnDeriv_measure_compProd μ ν κ η))
    apply integral_congr_ae₂
    filter_upwards [h, hκη, Measure.rnDeriv_toReal_pos hμν] with a ha hκηa hμν_pos
    have hμν_zero : (μ.rnDeriv ν a).toReal ≠ 0 := by linarith
    filter_upwards [kernel.rnDeriv_toReal_pos hκηa, hκηa.ae_le ha] with x hκη_pos hx
    have hκη_zero : (kernel.rnDeriv κ η a x).toReal ≠ 0 := by linarith
    rw [llr, hx, ENNReal.toReal_mul]
    exact Real.log_mul hμν_zero hκη_zero
  _ = ∫ a, ∫ _, log (μ.rnDeriv ν a).toReal ∂κ a ∂μ
      + ∫ a, ∫ x, log (kernel.rnDeriv κ η a x).toReal ∂κ a ∂μ := by
    norm_cast
    rw [← integral_add']
    simp only [Pi.add_apply]
    rotate_left
    · simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul, ← llr_def]
      exact intμν
    · exact intκη
    apply integral_congr_ae
    filter_upwards [hκη, intκη2] with a ha hκηa
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    rw [← integral_add']
    rotate_left
    · simp only [integrable_const]
    · apply Integrable.congr hκηa
      filter_upwards [h] with x hx
      rw [hx, llr_def]
    apply integral_congr_ae
    filter_upwards with a
    congr
  _ = ∫ a, log (μ.rnDeriv ν a).toReal ∂μ
      + ∫ a, ∫ x, log ((κ a).rnDeriv (η a) x).toReal ∂κ a ∂μ := by
    simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
    congr 2
    apply integral_congr_ae₂
    filter_upwards [hκη] with a ha
    have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
    filter_upwards [h] with x hx
    congr
  _ = kl μ ν + condKL κ η μ := by
    congr <;> simp_rw [← llr_def]
    · rw [← kl_of_ac_of_integrable hμν intμν]
    · rw [condKL_of_ae_ac_of_ae_integrable_of_integrable' hκη intκη2 _]
      apply (integrable_kl_iff hκη intκη2).mpr
      simp_rw [llr_def]
      apply Integrable.congr intκη
      filter_upwards [hκη] with a ha
      have h := ha.ae_le (kernel.rnDeriv_eq_rnDeriv_measure κ η a)
      apply integral_congr_ae
      filter_upwards [h] with x hx
      rw [hx]

/--The chain rule for the KL divergence.-/
lemma kl_fst_add_condKL [StandardBorelSpace β] [Nonempty β] {μ ν : Measure (α × β)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ.fst ν.fst + condKL μ.condKernel ν.condKernel μ.fst = kl μ ν := by
  rw [← kl_compProd, μ.compProd_fst_condKernel, ν.compProd_fst_condKernel]


end Conditional

section Tensorization

variable {β : Type*} {mβ : MeasurableSpace β}


--TODO: which of the two lemmas should go into the blueprint? or maybe both? for now I put both
lemma kl_prod_two' [CountablyGenerated β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsFiniteMeasure μ] [IsFiniteMeasure ν]:
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ * (μ Set.univ) := by
  simp only [← condKL_const, ← kl_compProd, compProd_const]

/--Tensorization property for KL divergence-/
lemma kl_prod_two [CountablyGenerated β] {ξ ψ : Measure β} [IsProbabilityMeasure ξ]
    [IsProbabilityMeasure ψ] [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    kl (μ.prod ξ) (ν.prod ψ) = kl μ ν + kl ξ ψ := by
  simp only [kl_prod_two', measure_univ, EReal.coe_ennreal_one, mul_one]

--TODO: I would like the hypothesys of being countably generated not on all the spaces, but on all the spaces except the first one
--if the general case turns out to be very hard to write and also to use, consider making a corollary where all the measures are probability measures and all the spaces are countabily generated

--TODO: look into the implementation of product of kernels and measure spaces in the RD_it branch of mathlib, there is a structure for the product of measure spaces and some API that may be useful to generalize the chain rule

--TODO: measurability should be able to solve something like this, maybe I should write this on zulip, see the file test_measurability
example {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (s : (i : ι) → Set (β i)) (h : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (Set.pi Set.univ s) := by
  -- measurability
  exact MeasurableSet.univ_pi h

--TODO: find a place for this, and a better name
--the hypothesis hι and hι' are not needed both, we can do with just one of them, but then the statement complains that it doesn't find the instance for the other, should we just leave it like this or find some way to circumvent it?
--should μ be an explicit argument?
lemma Measure.pi_map_CongrLeft {ι ι' : Type*} [hι : Fintype ι] [hι' : Fintype ι'] (e : ι ≃ ι')
    {β : ι' → Type*} [∀ i, MeasurableSpace (β i)] {μ : (i : ι') → Measure (β i)}
    [∀ i, SigmaFinite (μ i)] :
    Measure.map (MeasurableEquiv.piCongrLeft (fun i ↦ β i) e) (Measure.pi fun i ↦ μ (e i))
    = Measure.pi μ := by
  let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
    MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
  refine Measure.pi_eq (fun s _ ↦ ?_) |>.symm
  rw [e_meas.measurableEmbedding.map_apply]
  let s' : (i : ι) → Set (β (e i)) := fun i ↦ s (e i)
  have : e_meas ⁻¹' Set.pi Set.univ s = Set.pi Set.univ s' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, s']
    apply (e.forall_congr _).symm
    intro i
    convert Iff.rfl
    have piCongrLeft_apply_apply' :
        (MeasurableEquiv.piCongrLeft (fun i' => β i') e) x (e i) = x i := by
      simp only [MeasurableEquiv.piCongrLeft, MeasurableEquiv.coe_mk,
        Equiv.piCongrLeft_apply_apply]
    rw [piCongrLeft_apply_apply']
  rw [this, Measure.pi_pi, Finset.prod_equiv e.symm]
  · simp only [Finset.mem_univ, implies_true]
  intro i _
  simp only [s']
  congr
  all_goals rw [e.apply_symm_apply]

lemma kl_pi {ι : Type*} [hι : Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    [∀ i, CountablyGenerated (β i)] {μ ν : (i : ι) → Measure (β i)}
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    kl (Measure.pi μ) (Measure.pi ν) = ∑ i, kl (μ i) (ν i) := by
  refine Fintype.induction_empty_option (P := fun ι ↦ ∀ {β : ι → Type u_4}
    [(i : ι) → MeasurableSpace (β i)] [∀ (i : ι), CountablyGenerated (β i)]
    {μ ν : (i : ι) → Measure (β i)} [∀ (i : ι), IsProbabilityMeasure (μ i)]
    [∀ (i : ι), IsProbabilityMeasure (ν i)],
    kl (Measure.pi μ) (Measure.pi ν) = ∑ i : ι, kl (μ i) (ν i) ) ?_ ?_ ?_ ι
  · intro ι ι' hι' e h β _ _ μ ν _ _
    specialize h (β := fun i ↦ β (e i)) (μ := fun i ↦ μ (e i)) (ν := fun i ↦ ν (e i))
    let hι : Fintype ι := Fintype.ofEquiv _ e.symm
    rw [Fintype.sum_equiv e.symm _ (fun i ↦ kl (μ (e i)) (ν (e i))), ← h, kl_eq_fDiv, kl_eq_fDiv]
    let e_meas : ((b : ι) → β (e b)) ≃ᵐ ((a : ι') → β a) :=
      MeasurableEquiv.piCongrLeft (fun i ↦ β i) e
    have me := MeasurableEquiv.measurableEmbedding e_meas.symm
    convert (fDiv_map_measurableEmbedding me).symm
    <;> try {rw [← Measure.pi_map_CongrLeft e, MeasurableEquiv.map_symm_map]}
    <;> infer_instance
    intro i
    rw [Equiv.apply_symm_apply]
  · intro β _ _ μ ν _ _
    rw [Measure.pi_of_empty, Measure.pi_of_empty, kl_self, Finset.univ_eq_empty, Finset.sum_empty]
  · intro ι hι ind_h β _ _ μ ν _ _
    specialize ind_h (β := fun i ↦ β i) (μ := fun i ↦ μ i) (ν := fun i ↦ ν i)
    have h : kl (Measure.pi μ) (Measure.pi ν) = kl (Measure.prod (Measure.pi (fun (i : ι) ↦ μ i))
        (μ none)) (Measure.prod (Measure.pi (fun (i : ι) ↦ ν i)) (ν none)) := by
      rw [kl_eq_fDiv, kl_eq_fDiv]
      let e_meas : ((i : ι) → β (some i)) × β none ≃ᵐ ((i : Option ι) → β i) :=
        MeasurableEquiv.piOptionEquivProd.{_, _, u_3} β |>.symm
        --TODO: if I don't put the universe level it doesn't work, also if I put u_1 or u_2 it doesn't work, but if I put u_3 or u_4 it works. Maybe the problem is in the definition of piOptionEquivProd
        --u_3 and u_4 seem to be universes that are already needed by the other definitions in the theorem
        --I think I understand what happened now, even though I still don't know why this problem did not show up earlier. In the proof of MeasurableEquiv.piOptionEquivProd I was forced to make the universe of PUnit.{u_8 + 1} explicit, and in that situation I just put there a universe level that was not used anywhere else in the proof, but it wasn't a good idea, because in that way the lemma requires an additional useless universe level, and so when we use it we need to specifiy the additional universe. The fix for this is to change the universe inside the proof of MeasurableEquiv.piOptionEquivProd to one that is already used, like u_8. The problem is that this has already been PRed to mathlib, so we need to make another PR just to fix this bug.
        --for now I just leave the explicit universe level here, I will fix it later
        --I already made the branch of mathlib with the fix, now it's sufficient to make the PR, but first I want to discuss it, maybe there is a better way to fix it
        --PRed to mathlib, when we bump remember to remove the explicit universe level here
      have me := MeasurableEquiv.measurableEmbedding e_meas
      have hh (ξ : (i : Option ι) → Measure (β i)) [∀ (i : Option ι), IsProbabilityMeasure (ξ i)] :
      Measure.pi ξ = Measure.map (⇑e_meas) (Measure.prod (Measure.pi fun i ↦ ξ (some i)) (ξ none))
          := by
        refine Measure.pi_eq (fun s _ ↦ ?_)
        have : e_meas ⁻¹' Set.pi Set.univ s = (Set.pi Set.univ (fun i => s (some i))) ×ˢ (s none)
            := by
          ext x
          simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
          constructor; tauto
          intro h i
          rcases i <;> tauto
        simp only [me.map_apply, univ_option, Finset.le_eq_subset, Finset.prod_insertNone, this,
          Measure.prod_prod, Measure.pi_pi, mul_comm]
      convert fDiv_map_measurableEmbedding me
      <;> try {exact hh _} <;> infer_instance
    rw [Fintype.sum_option, h, add_comm, ← ind_h]
    convert kl_prod_two <;> tauto <;> infer_instance


-- is it ok to state it like this or should we use a specific fintype like Fin n, so we have the cardinality defined in the statement?
lemma kl_pi_const {ι : Type*} [hι : Fintype ι] [CountablyGenerated α] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    kl (Measure.pi (fun (_ : ι) ↦ μ)) (Measure.pi (fun (_ : ι) ↦ ν)) = hι.card * kl μ ν := by
  rw [kl_pi, Finset.sum_const, (Finset.card_eq_iff_eq_univ _).mpr, EReal.nsmul_eq_mul]
  rfl


end Tensorization

end ProbabilityTheory
