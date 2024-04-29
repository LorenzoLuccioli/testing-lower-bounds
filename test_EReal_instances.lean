import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd

--TODO: look for instances of EReal that should be there but are not, and add them, look at the page of ENNReals to see what is there, maybe some stuff is true even for EReals but hasn't been added yet

#check ENNReal.covariantClass_mul_le
--EReal is not covariant wrt the product, e.g. 1 ≤ 2, but -1 * 1 = -1 > -2 = -1 * 2
--however EReal is covariant wrt the product with a nonnegative number, would it make sense to add an instance for this?
--something like EReal.covariantClass_ENNReal_mul_le

#check ENNReal.hasMeasurablePow
--there is no such instance for EReal, but we can derive it from the fact that its a monoid, a mesaurable space and the instance MeasurableMul₂, but we still need to add this last instance
--for MeasurableMul₂ we could pass through ContinuousMul, is it even true for EReal? I think it's true, but I don't know how to add it, maybe it could be a possibility to pass through the fact that it is withTop.

#check ENNReal.instCanonicallyLinearOrderedAddCommMonoidENNReal
#check ENNReal.instCanonicallyOrderedCommSemiringENNReal
--this is not true for EReal, since the canonical order means that the order is the same as the one defined by subtraction, i.e. `x<y iff y=z+x`, but this is not true if we also have negative numbers


instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))
#synth CharZero EReal --new, I already put this in the EReal file for mathlib

-- instance : CanonicallyOrderedCommSemiring EReal := inferInstanceAs (CanonicallyOrderedCommSemiring (WithBot (WithTop ℝ)))
-- #synth CanonicallyOrderedCommSemiring EReal


-- #synth Coe EReal Real --already there

-- #synth CompleteLinearOrder EReal --already there

-- #synth ContinuousAdd EReal

-- #synth TopologicalSpace EReal
-- -- #synth NonUnitalSeminormedRing EReal
-- #synth BoundedOrder EReal
-- #synth CanonicallyOrderedAddCommMonoid Real
