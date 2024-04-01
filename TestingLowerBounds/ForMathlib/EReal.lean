import Mathlib.Data.Real.EReal

open scoped ENNReal NNReal

namespace EReal

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

end EReal
