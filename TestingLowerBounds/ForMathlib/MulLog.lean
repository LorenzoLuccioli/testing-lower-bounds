import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace Real


--This is probabilty not needed in mathlib, we can leave it in the project for now, but we are not going to PR it

lemma measurable_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id.mul measurable_log

lemma stronglyMeasurable_mul_log : MeasureTheory.StronglyMeasurable (fun x ↦ x * log x) :=
  stronglyMeasurable_id.mul measurable_log.stronglyMeasurable


#check measurable_mul_log.stronglyMeasurable
#check stronglyMeasurable_mul_log.measurable

end Real
