import Mathlib.Data.Real.EReal
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import LeanCopilot

open scoped ENNReal NNReal

namespace EReal

instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))

lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
  lift x to ℝ≥0 using hx
  rfl

lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ := by
  by_cases hx_top : x = ∞
  · simp [hx_top]
  · rw [← coe_ennreal_toReal hx_top, top_mul_coe_of_pos]
    exact ENNReal.toReal_pos hx hx_top

lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [mul_comm, top_mul_ennreal_coe hx]

lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction' a, b using EReal.induction₂_symm with a b h x hx x hx x hx x y x hx
  · rw [mul_comm, h]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      <;> cases h with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  · simp
  · simp [EReal.top_mul_coe_of_pos hx, hx]
  · simp
  · simp [hx.le, EReal.top_mul_coe_of_neg hx]
  · simp
  · simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  · simp only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_top _
  · simp
  · simp [hx, EReal.coe_mul_bot_of_neg hx]
  · simp

lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  induction' a, b using EReal.induction₂_symm with a b h x hx x hx x hx x y x hx
  · rw [mul_comm, h]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      <;> cases h with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  · simp
  · simp [EReal.top_mul_coe_of_pos hx, hx.le]
  · simp
  · simp [hx, EReal.top_mul_coe_of_neg hx]
  · simp
  · simp [hx, EReal.coe_mul_bot_of_pos hx]
  · simp only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false]
    rw [← EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · simp
  · simp [hx.le, EReal.coe_mul_bot_of_neg hx]
  · simp

lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction' y using EReal.rec with y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction' z using EReal.rec with z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction' z using EReal.rec with z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]

lemma add_mul_coe_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ (x : EReal)]
  exact EReal.coe_mul_add_of_nonneg hx_nonneg y z

lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := by
  induction' x using EReal.rec with x
  · simp
  · norm_cast
    ring
  · simp

lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := by
  rw [add_comm, EReal.add_sub_cancel]

lemma top_add_of_ne_bot {x : EReal} (hx : x ≠ ⊥) : ⊤ + x = ⊤ := by
  by_cases hx_top : x = ⊤
  · simp [hx_top]
  · lift x to ℝ using ⟨hx_top, hx⟩
    simp

lemma add_top_of_ne_bot {x : EReal} (hx : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add_of_ne_bot hx]

lemma add_pos {x y : EReal} (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by
  induction' x, y using EReal.induction₂_symm with x y h x _ y _ _ _ x y
  · rw [add_comm]
    exact h hy hx
  · simp
  · simp
  · simp
  · simp
  · simp only [add_bot, not_lt_bot]
    exact not_lt_bot hy
  · simp only [add_bot, not_lt_bot]
    exact not_lt_bot hy
  · norm_cast
    refine _root_.add_pos ?_ ?_
    · exact mod_cast hx
    · exact mod_cast hy
  · simp only [zero_add, not_lt_bot]
    exact not_lt_bot hy
  · simp only [add_bot, not_lt_bot]
    exact not_lt_bot hy
  · simp only [add_bot, not_lt_bot]
    exact not_lt_bot hy

lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction' x, y using EReal.induction₂_symm with x y h x h y h _ _ x y
  · rw [add_comm, add_comm (⊤ * y)]
    exact h hy hx
  · simp
  · rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  · simp
  · refine absurd hy ?_
    exact mod_cast h.not_le
  · simp
  · simp
  · by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := by
      refine hx.lt_of_ne' ?_
      exact mod_cast hx0
    have hy_pos : 0 < (y : EReal) := by
      refine hy.lt_of_ne' ?_
      exact mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos]
    · simp
    · exact add_pos hx_pos hy_pos
  · simp
  · simp
  · simp

lemma mul_add_coe_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x * (y + z) = x * y + x * z := by
  by_cases hx_top : x = ⊤
  · rw [hx_top]
    exact top_mul_add_of_nonneg (mod_cast hy) (mod_cast hz)
  by_cases hx_bot : x = ⊥
  · rw [hx_bot]
    by_cases hy0 : y = 0
    · simp [hy0]
    by_cases hz0 : z = 0
    · simp [hz0]
    have hy_pos : 0 < (y : EReal) := lt_of_le_of_ne' (mod_cast hy) (mod_cast hy0)
    have hz_pos : 0 < (z : EReal) := lt_of_le_of_ne' (mod_cast hz) (mod_cast hz0)
    rw [bot_mul_of_pos hy_pos, bot_mul_of_pos hz_pos, bot_mul_of_pos]
    · simp
    · exact add_pos hy_pos hz_pos
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  norm_cast
  rw [mul_add]

lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz

lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  induction' x using EReal.rec with x
  · norm_num
  · simp only [toReal_coe]
    exact EReal.coe_nonneg.mp hx
  · norm_num

lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  induction' x using EReal.rec with x
  · norm_num
  · simp only [toReal_coe]
    exact EReal.coe_nonpos.mp hx
  · norm_num

lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  induction' x using EReal.rec with x <;> norm_num

lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  induction' x using EReal.rec with x <;> norm_num

@[simp]
lemma nsmul_eq_mul {n : ℕ} {x : EReal} : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]
    convert (EReal.coe_add_mul_of_nonneg x _ _).symm <;> simp

lemma lowerSemicontinuous_add : LowerSemicontinuous fun (p : EReal × EReal) ↦ p.1 + p.2 := by
  intro x
  by_cases hx1_bot : x.1 = ⊥
  · intro y
    simp [hx1_bot]
  by_cases hx2_bot : x.2 = ⊥
  · intro y
    simp [hx2_bot]
  refine ContinuousAt.lowerSemicontinuousAt ?_
  exact EReal.continuousAt_add (Or.inr hx2_bot) (Or.inl hx1_bot)

instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

instance : MeasurableMul₂ EReal := by
  constructor
  sorry

/-- Reinterpret an EReal number `x` as a NNReal number. Returns `0` if `x < 0` or `x = ⊤`. -/
noncomputable def toNNReal (x : EReal) : NNReal :=
  if x = ⊤ then 0
  else if h : 0 ≤ x then ⟨x.toReal, toReal_nonneg h⟩
  else 0

@[simp]
theorem toNNReal_top : (⊤ : EReal).toNNReal = 0 := rfl

@[simp]
theorem toNNReal_neg {x : EReal} (hx : x < 0) : x.toNNReal = 0 := by
  rw [toNNReal, if_neg hx.ne_top, dif_neg (not_le_of_gt hx)]

theorem toNNReal_of_nonneg_of_finite {x : EReal} (hx : 0 ≤ x) (h_top : x ≠ ⊤) :
    x.toNNReal = ⟨x.toReal, toReal_nonneg hx⟩ := by
  rw [toNNReal, if_neg h_top, dif_pos hx]

theorem coe_toNNReal {x : EReal} (hx : 0 ≤ x) (h_top : x ≠ ⊤) : (x.toNNReal : EReal) = x := by
  rw [toNNReal_of_nonneg_of_finite hx h_top, ← Real.toNNReal_of_nonneg, coe_nnreal_eq_coe_real,
    Real.coe_toNNReal _ (toReal_nonneg hx), coe_toReal h_top _]
  exact fun h ↦ by simp_all only [le_bot_iff, zero_ne_bot]

/-- Reinterpret an EReal number `x` as an ENNReal number. Returns `0` if `x < 0`. -/
noncomputable def toENNReal (x : EReal) : ENNReal :=
  if x = ⊤ then ⊤
  else x.toNNReal

@[simp]
theorem toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
theorem toENNReal_neg {x : EReal} (hx : x < 0) : x.toENNReal = 0 := by
  rw [toENNReal, if_neg hx.ne_top, toNNReal_neg hx]
  rfl

theorem coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  exact if_neg h_top ▸ coe_toNNReal hx h_top

end EReal

noncomputable instance : HMul ℝ ℝ≥0∞ EReal where
  hMul x y := (x : EReal) * y

noncomputable instance : HMul ℝ≥0∞ ℝ EReal where
  hMul x y := (x : EReal) * y

noncomputable instance : HAdd ℝ ℝ≥0∞ EReal where
  hAdd x y := (x : EReal) + y

noncomputable instance : HAdd ℝ≥0∞ ℝ EReal where
  hAdd x y := (x : EReal) + y

namespace ENNReal

lemma toEReal_sub {x y : ENNReal} (hy_top : y ≠ ⊤) (h_le : y ≤ x) :
    (x - y).toEReal = x.toEReal - y.toEReal := by
  by_cases hx_top : x = ⊤
  · lift y to ℝ≥0 using hy_top
    simp only [hx_top, top_sub_coe, EReal.coe_ennreal_top]
    norm_cast
  have h_top : x - y ≠ ⊤ := by
    simp only [ne_eq, sub_eq_top_iff, hx_top, hy_top, not_false_eq_true, and_true]
  nth_rw 2 [← ENNReal.ofReal_toReal_eq_iff.mpr hy_top, ← ENNReal.ofReal_toReal_eq_iff.mpr hx_top]
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr h_top]
  simp only [EReal.coe_ennreal_ofReal, ge_iff_le, toReal_nonneg, max_eq_left]
  rw [toReal_sub_of_le h_le hx_top]
  exact EReal.coe_sub _ _

end ENNReal
