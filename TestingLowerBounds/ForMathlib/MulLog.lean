import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.Deriv

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

open scoped Topology

namespace Real


--TODO: PR this. First determine if this is actually needed, it would add 2 imports to the file, moreover each lemma can actually be used via the other lemma using just a simple dot notation, so maybe if we add them it would make sense to add just one of them to the file, so that only one additional import is needed, probabily it would make more sense to add the measurable one, since it's slightly shorter and more basic.
--even if we decide not to put this in mathlib it may be good to have the strongly measurable one in the kl file, since it gets used a bungh of times

lemma measurable_mul_log : Measurable (fun x ↦ x * log x) := by
  exact measurable_id.mul measurable_log

lemma stronglyMeasurable_mul_log : MeasureTheory.StronglyMeasurable (fun x ↦ x * log x) := by
  exact stronglyMeasurable_id.mul measurable_log.stronglyMeasurable


#check measurable_mul_log.stronglyMeasurable
#check stronglyMeasurable_mul_log.measurable

end Real
