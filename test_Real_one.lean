import Mathlib.MeasureTheory.Integral.IntegrableOn

/-This is a file with a MWE that I posted on Zulip, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60integrableOn_const.60.20makes.20.60Real.2Eone.60.20appear/near/440466749-/

open  MeasureTheory

variable (α : Type*) [MeasurableSpace α] (μ : Measure α) (s : Set α) (hs : MeasurableSet s)


example (h : Integrable (s.indicator (1 : α → ℝ)) μ) :
    False := by
  rw [integrable_indicator_iff hs] at h
  -- h : IntegrableOn 1 s μ
  apply integrableOn_const.mp at h
  -- h : Real.one = 0 ∨ μ s < ⊤
  -- I can't simplify this, because I cannot access `Real.one` and nothing I tried to throw at it worked
  sorry

example (h : Integrable (s.indicator (1 : α → ℝ)) μ) :
    False := by
  rw [integrable_indicator_iff hs] at h
  -- h : IntegrableOn 1 s μ
  change IntegrableOn (fun _ ↦ 1) _ _ at h
  -- h : IntegrableOn (fun x => 1) s μ
  apply integrableOn_const.mp at h
  -- h : 1 = 0 ∨ μ s < ⊤
  simp at h
  -- h : μ s < ⊤
  sorry

example (h : Integrable (s.indicator (1 : α → ℝ)) μ) :
    False := by
  rw [integrable_indicator_iff hs] at h
  -- h : IntegrableOn 1 s μ
  apply integrableOn_const.mp at h
  -- h : Real.one = 0 ∨ μ s < ⊤
  change 1 = 0 ∨ _ at h
  -- h : 1 = 0 ∨ μ s < ⊤
  simp at h
  -- h : μ s < ⊤
  sorry
