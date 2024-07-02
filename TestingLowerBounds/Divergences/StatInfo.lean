/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Testing.Binary

/-!
# Statistical information

## Main definitions

* `statInfo`

## Main statements

* `statInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

open MeasureTheory

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {𝒳 𝒳' : Type*} {m𝒳 : MeasurableSpace 𝒳} {m𝒳' : MeasurableSpace 𝒳'}
  {μ ν : Measure 𝒳} {p : ℝ≥0∞}

-- TODO: replace the min by a risk
noncomputable
def statInfo (μ ν : Measure 𝒳) (π : Measure Bool) : ℝ≥0∞ :=
  min (π {false} * μ Set.univ) (π {true} * ν Set.univ) - bayesBinaryRisk μ ν π

/-- **Data processing inequality** for the statistical information. -/
lemma statInfo_comp_le (μ ν : Measure 𝒳) (π : Measure Bool) (η : kernel 𝒳 𝒳') [IsMarkovKernel η] :
    statInfo (μ ∘ₘ η) (ν ∘ₘ η) π ≤ statInfo μ ν π := by
  refine tsub_le_tsub ?_ (bayesBinaryRisk_le_bayesBinaryRisk_comp _ _ _ _)
  simp_rw [Measure.comp_apply_univ]
  simp

@[simp]
lemma statInfo_self (μ : Measure 𝒳) (π : Measure Bool) : statInfo μ μ π = 0 := by
  rw [statInfo, bayesBinaryRisk_self, min_mul_mul_right, min_comm, tsub_self]

-- lemma toReal_statInfo_eq_toReal_sub (μ ν : Measure 𝒳) (π : Measure Bool) :
--     (statInfo μ ν π).toReal = (min (π {false} * μ Set.univ) (π {true} * μ Set.univ)).toReal
--       - (bayesBinaryRisk μ ν π).toReal := by
--   by_cases h : min (π {false} * μ Set.univ) (π {true} * μ Set.univ) = ⊤
--   ·
--     sorry
--   rw [statInfo, ENNReal.toReal_sub_of_le _ h]
--   exact bayesBinaryRisk_le_min _ _ _


end ProbabilityTheory
