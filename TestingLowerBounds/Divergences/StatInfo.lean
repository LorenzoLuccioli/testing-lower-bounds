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
  {μ ν : Measure 𝒳} {p : ℝ≥0∞} (π : Measure Bool)

-- TODO: replace the min by a risk
/-- The statistical information of the measures `μ` and `ν` with respect to
the prior `π ∈ ℳ({0,1})`. -/
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

lemma toReal_statInfo_eq_toReal_sub [IsFiniteMeasure ν] [IsFiniteMeasure π] :
    (statInfo μ ν π).toReal = (min (π {false} * μ Set.univ) (π {true} * ν Set.univ)).toReal
      - (bayesBinaryRisk μ ν π).toReal := by
  rw [statInfo, ENNReal.toReal_sub_of_le]
  · exact bayesBinaryRisk_le_min _ _ _
  · simp only [ne_eq, min_eq_top, not_and]
    exact fun _ ↦  ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top ν _)

lemma statInfo_le_min : statInfo μ ν π ≤ min (π {false} * μ Set.univ) (π {true} * ν Set.univ) :=
  tsub_le_self

lemma statInfo_symm : statInfo μ ν π = statInfo ν μ (π.map Bool.not) := by
  -- I just copied these haves from the proof of `bayesBinaryRisk_symm`, should we separate them?
  have : (Bool.not ⁻¹' {true}) = {false} := by ext x; simp
  have h1 : (Measure.map Bool.not π) {true} = π {false} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  have : (Bool.not ⁻¹' {false}) = {true} := by ext x; simp
  have h2 : (Measure.map Bool.not π) {false} = π {true} := by
    rw [Measure.map_apply (by exact fun _ a ↦ a) (by trivial), this]
  simp_rw [statInfo]
  rw [min_comm, bayesBinaryRisk_symm, h1, h2]

lemma statInfo_boolMeasure_le_statInfo {E : Set 𝒳} (hE : MeasurableSet E) :
    statInfo (Bool.boolMeasure (1 - μ E) (μ E)) (Bool.boolMeasure (1 - ν E) (ν E)) π
      ≤ statInfo μ ν π := by
  have h_meas : Measurable fun x ↦ Bool.ofNat (E.indicator 1 x) :=
    ((measurable_discrete _).comp' (measurable_one.indicator hE))
  let η : kernel 𝒳 Bool := kernel.deterministic (fun x ↦ Bool.ofNat (E.indicator 1 x)) h_meas
  convert statInfo_comp_le μ ν π η
  · ext
    · simp [η]
      rw [Measure.comp_deterministic_eq_map, Measure.map_apply h_meas (by trivial)]
      have : (fun x ↦ Bool.ofNat (E.indicator 1 x)) ⁻¹' {false} = Eᶜ := by
        ext x; simp [Bool.ofNat]
      rw [this]
      sorry
    · sorry
  sorry


end ProbabilityTheory
