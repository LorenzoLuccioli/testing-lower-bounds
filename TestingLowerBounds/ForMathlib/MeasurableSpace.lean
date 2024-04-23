import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib

namespace MeasurableEquiv

open MeasureTheory MeasurableSpace

variable {α : Type*} {mα : MeasurableSpace α} {β : Type*} {mβ : MeasurableSpace β}


--TODO: PR this to mathlib, is this worthy of the simp attribute?
#check MeasurableEquiv.piFinsetUnion

/-- The measurable equivalence `(∀ i : Option δ, α i) ≃ᵐ (∀ (i : δ), α i) × α none`.-/
def piOptionEquivProd {δ : Type*} (α : Option δ → Type*) [∀ i, MeasurableSpace (α i)] :
    (∀ i, α i) ≃ᵐ (∀ (i : δ), α i) × α none := by
  let e : Option δ ≃ δ ⊕ PUnit := Equiv.optionEquivSumPUnit δ
  let em1 : ((i : δ ⊕ PUnit) → α (e.symm i)) ≃ᵐ ((a : Option δ) → α a) :=
    MeasurableEquiv.piCongrLeft α e.symm
  let em2 : ((i : δ ⊕ PUnit) → α (e.symm i)) ≃ᵐ ((i : δ) → α (e.symm (Sum.inl i)))
      × ((i' : PUnit) → α (e.symm (Sum.inr i'))) :=
    MeasurableEquiv.sumPiEquivProdPi (fun i ↦ α (e.symm i))
  let em3 : ((i : δ) → α (e.symm (Sum.inl i))) × ((i' : PUnit.{u_3 + 1}) → α (e.symm (Sum.inr i')))
      ≃ᵐ ((i : δ) → α (some i)) × α none :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((i : δ) → α (e.symm (Sum.inl i))))
      (MeasurableEquiv.piUnique fun i ↦ α (e.symm (Sum.inr i)))
  exact em1.symm.trans <| em2.trans em3

end MeasurableEquiv
