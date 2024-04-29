
import Mathlib.Probability.Kernel.Composition

#align_import probability.kernel.composition from "leanprover-community/mathlib"@"3b92d54a05ee592aa2c6181a4e76b1bb7cc45d0b"

/-!
# Product and composition of kernels

We define
* the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : kernel α β` and
  `η : kernel (α × β) γ`, a kernel from `α` to `β × γ`.
* the map and comap of a kernel along a measurable function.
* the composition `η ∘ₖ κ` of kernels `κ : kernel α β` and `η : kernel β γ`, kernel from `α` to
  `γ`.
* the product `κ ×ₖ η` of s-finite kernels `κ : kernel α β` and `η : kernel α γ`,
  a kernel from `α` to `β × γ`.

A note on names:
The composition-product `kernel α β → kernel (α × β) γ → kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

Kernels built from other kernels:
* `compProd (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
* `map (κ : kernel α β) (f : β → γ) (hf : Measurable f) : kernel α γ`
  `∫⁻ c, g c ∂(map κ f hf a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : kernel α β) (f : γ → α) (hf : Measurable f) : kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp (η : kernel β γ) (κ : kernel α β) : kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* `prod (κ : kernel α β) (η : kernel α γ) : kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_compProd`, `lintegral_map`, `lintegral_comap`, `lintegral_comp`, `lintegral_prod`:
  Lebesgue integral of a function against a composition-product/map/comap/composition/product of
  kernels.
* Instances of the form `<class>.<operation>` where class is one of `IsMarkovKernel`,
  `IsFiniteKernel`, `IsSFiniteKernel` and operation is one of `compProd`, `map`, `comap`,
  `comp`, `prod`. These instances state that the three classes are stable by the various operations.

## Notations

* `κ ⊗ₖ η = ProbabilityTheory.kernel.compProd κ η`
* `η ∘ₖ κ = ProbabilityTheory.kernel.comp η κ`
* `κ ×ₖ η = ProbabilityTheory.kernel.prod κ η`

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

variable {γ : Type*} {mγ : MeasurableSpace γ}

open scoped ProbabilityTheory

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

--I try to reproduce the code that is already there for kernel.fst and kernel.snd, but in this case the fst and snd are referred to the domain of the kernel, not the codomain
--for now I will use the names fst' and snd', maybe there are better ones

/-- Define a `kernel α γ` from a `kernel (α × β) γ` by taking the comap of TODO:what is this function called?. -/
noncomputable def fst' (κ : kernel (α × β)  γ) (b : β) : kernel α γ :=
  comap κ (fun a ↦ (a, b)) (measurable_id.prod_mk measurable_const)

theorem fst'_apply (κ : kernel (α × β)  γ) (b : β) (a : α) : fst' κ b a = κ (a, b) :=
  rfl

@[simp]
lemma fst_zero : fst (0 : kernel α (β × γ)) = 0 := by simp [fst]

theorem lintegral_fst (κ : kernel α (β × γ)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂fst κ a = ∫⁻ bc : β × γ, g bc.fst ∂κ a := by
  rw [fst, lintegral_map _ measurable_fst a hg]
#align probability_theory.kernel.lintegral_fst ProbabilityTheory.kernel.lintegral_fst

instance IsMarkovKernel.fst (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (fst κ) := by
  rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_markov_kernel.fst ProbabilityTheory.kernel.IsMarkovKernel.fst

instance IsFiniteKernel.fst (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (fst κ) := by
  rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_finite_kernel.fst ProbabilityTheory.kernel.IsFiniteKernel.fst

instance IsSFiniteKernel.fst (κ : kernel α (β × γ)) [IsSFiniteKernel κ] : IsSFiniteKernel (fst κ) :=
  by rw [kernel.fst]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.fst ProbabilityTheory.kernel.IsSFiniteKernel.fst

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_fst {κ : kernel α (β × γ)}
    [h : IsFiniteKernel (fst κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (fst κ) a Set.univ)⟩
  rw [fst_apply' _ _ MeasurableSet.univ]
  simp

lemma fst_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    fst (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ f hf := by
  ext x s hs
  rw [fst_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_fst hs

lemma fst_map_id_prod (κ : kernel α β) {γ : Type*} {mγ : MeasurableSpace γ}
    {f : β → γ} (hf : Measurable f) :
    fst (map κ (fun a ↦ (a, f a)) (measurable_id.prod_mk hf)) = κ := by
  rw [fst_map_prod _ measurable_id' hf, kernel.map_id']

@[simp]
lemma fst_compProd (κ : kernel α β) (η : kernel (α × β) γ) [IsSFiniteKernel κ] [IsMarkovKernel η] :
    fst (κ ⊗ₖ η) = κ := by
  ext x s hs
  rw [fst_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_fst hs
  simp only [Set.mem_setOf_eq]
  classical
  have : ∀ b : β, η (x, b) {_c | b ∈ s} = s.indicator (fun _ ↦ 1) b := by
    intro b
    by_cases hb : b ∈ s <;> simp [hb]
  simp_rw [this]
  rw [lintegral_indicator_const hs, one_mul]

lemma fst_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    fst (prodMkLeft δ κ) = prodMkLeft δ (fst κ) := rfl

lemma fst_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    fst (prodMkRight δ κ) = prodMkRight δ (fst κ) := rfl

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the second projection. -/
noncomputable def snd (κ : kernel α (β × γ)) : kernel α γ :=
  map κ Prod.snd measurable_snd
#align probability_theory.kernel.snd ProbabilityTheory.kernel.snd

theorem snd_apply (κ : kernel α (β × γ)) (a : α) : snd κ a = (κ a).map Prod.snd :=
  rfl
#align probability_theory.kernel.snd_apply ProbabilityTheory.kernel.snd_apply

theorem snd_apply' (κ : kernel α (β × γ)) (a : α) {s : Set γ} (hs : MeasurableSet s) :
    snd κ a s = κ a {p | p.2 ∈ s} := by rw [snd_apply, Measure.map_apply measurable_snd hs]; rfl
#align probability_theory.kernel.snd_apply' ProbabilityTheory.kernel.snd_apply'

@[simp]
lemma snd_zero : snd (0 : kernel α (β × γ)) = 0 := by simp [snd]

theorem lintegral_snd (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ c, g c ∂snd κ a = ∫⁻ bc : β × γ, g bc.snd ∂κ a := by
  rw [snd, lintegral_map _ measurable_snd a hg]
#align probability_theory.kernel.lintegral_snd ProbabilityTheory.kernel.lintegral_snd

instance IsMarkovKernel.snd (κ : kernel α (β × γ)) [IsMarkovKernel κ] : IsMarkovKernel (snd κ) := by
  rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_markov_kernel.snd ProbabilityTheory.kernel.IsMarkovKernel.snd

instance IsFiniteKernel.snd (κ : kernel α (β × γ)) [IsFiniteKernel κ] : IsFiniteKernel (snd κ) := by
  rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_finite_kernel.snd ProbabilityTheory.kernel.IsFiniteKernel.snd

instance IsSFiniteKernel.snd (κ : kernel α (β × γ)) [IsSFiniteKernel κ] : IsSFiniteKernel (snd κ) :=
  by rw [kernel.snd]; infer_instance
#align probability_theory.kernel.is_s_finite_kernel.snd ProbabilityTheory.kernel.IsSFiniteKernel.snd

instance (priority := 100) isFiniteKernel_of_isFiniteKernel_snd {κ : kernel α (β × γ)}
    [h : IsFiniteKernel (snd κ)] :
    IsFiniteKernel κ := by
  refine ⟨h.bound, h.bound_lt_top, fun a ↦ le_trans ?_ (measure_le_bound (snd κ) a Set.univ)⟩
  rw [snd_apply' _ _ MeasurableSet.univ]
  simp

lemma snd_map_prod (κ : kernel α β) {f : β → γ} {g : β → δ}
    (hf : Measurable f) (hg : Measurable g) :
    snd (map κ (fun x ↦ (f x, g x)) (hf.prod_mk hg)) = map κ g hg := by
  ext x s hs
  rw [snd_apply' _ _ hs, map_apply', map_apply' _ _ _ hs]
  · rfl
  · exact measurable_snd hs

lemma snd_map_prod_id (κ : kernel α β) {γ : Type*} {mγ : MeasurableSpace γ}
    {f : β → γ} (hf : Measurable f) :
    snd (map κ (fun a ↦ (f a, a)) (hf.prod_mk measurable_id)) = κ := by
  rw [snd_map_prod _ hf measurable_id', kernel.map_id']

lemma snd_prodMkLeft (δ : Type*) [MeasurableSpace δ] (κ : kernel α (β × γ)) :
    snd (prodMkLeft δ κ) = prodMkLeft δ (snd κ) := rfl

lemma snd_prodMkRight (κ : kernel α (β × γ)) (δ : Type*) [MeasurableSpace δ] :
    snd (prodMkRight δ κ) = prodMkRight δ (snd κ) := rfl

@[simp]
lemma fst_swapRight (κ : kernel α (β × γ)) : fst (swapRight κ) = snd κ := by
  ext a s hs
  rw [fst_apply' _ _ hs, swapRight_apply', snd_apply' _ _ hs]
  · rfl
  · exact measurable_fst hs

@[simp]
lemma snd_swapRight (κ : kernel α (β × γ)) : snd (swapRight κ) = fst κ := by
  ext a s hs
  rw [snd_apply' _ _ hs, swapRight_apply', fst_apply' _ _ hs]
  · rfl
  · exact measurable_snd hs

end FstSnd

end kernel

end ProbabilityTheory
