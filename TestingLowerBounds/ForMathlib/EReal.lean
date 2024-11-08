import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
-- import LeanCopilot

open scoped ENNReal NNReal Topology
open Filter Set

namespace EReal
-- PRed, see #17087
instance : CharZero EReal := inferInstanceAs (CharZero (WithBot (WithTop ℝ)))
-- PRed, see #17087
instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    induction a <;> induction b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_top_of_neg, EReal.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.top_mul_of_pos, EReal.top_mul_of_neg, h]
-- PRed, see #17087
lemma coe_ennreal_toReal {x : ℝ≥0∞} (hx : x ≠ ∞) : (x.toReal : EReal) = x := by
  lift x to ℝ≥0 using hx
  rfl
-- PRed, see #17087 as lt_neg
lemma lt_neg_iff_lt_neg {x y : EReal} : x < -y ↔ y < -x := by
  nth_rw 1 [← neg_neg x, neg_lt_neg_iff]
-- PRed, see #17087 as le_neg
lemma le_neg_iff_le_neg {x y : EReal} : x ≤ -y ↔ y ≤ -x := by
  nth_rw 1 [← neg_neg x, neg_le_neg_iff]
-- PRed, see #17087 as neg_le
lemma neg_le_iff_neg_le {x y : EReal} : -x ≤ y ↔ -y ≤ x := by
  nth_rw 1 [← neg_neg y, neg_le_neg_iff]
-- PRed, see #17087 as top_mul_coe_ennreal
lemma top_mul_ennreal_coe {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ :=
  top_mul_of_pos <| coe_ennreal_pos.mpr <| pos_iff_ne_zero.mpr hx
-- PRed, see #17087 as coe_ennreal_mul_top
lemma ennreal_coe_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [mul_comm, top_mul_ennreal_coe hx]
-- PRed, see #17087
lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h =>
    rw [mul_comm, h]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      <;> cases h with
      | inl h => exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      | inr h => cases h with
        | inl h => exact Or.inl ⟨h.2, h.1⟩
        | inr h => cases h with
          | inl h => exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
          | inr h => exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simp only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false, EReal.coe_mul]
    exact EReal.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp
-- PRed, see #17087
lemma mul_ne_top (a b : EReal) :
    a * b ≠ ⊤ ↔ (a ≠ ⊥ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  set_option push_neg.use_distrib true in push_neg
  rfl
-- PRed, see #17087 PRed, see #17087
lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  rw [← neg_eq_top_iff, ← neg_mul, mul_eq_top, neg_eq_bot_iff, neg_eq_top_iff,
    EReal.neg_lt_iff_neg_lt, EReal.lt_neg_iff_lt_neg, neg_zero]
  tauto
-- PRed, see #17087
lemma mul_ne_bot (a b : EReal) :
    a * b ≠ ⊥ ↔ (a ≠ ⊥ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  set_option push_neg.use_distrib true in push_neg
  rfl
-- PRed, see #17087
lemma mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp
-- PRed, see #17087
lemma mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_iff_lt_neg, ← mul_neg, mul_pos_iff, neg_lt_iff_neg_lt, lt_neg_iff_lt_neg, neg_zero]
-- PRed, see #17087
lemma mul_nonneg_iff {a b : EReal} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto
-- PRed, see #17087
lemma mul_nonpos_iff {a b : EReal} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  nth_rw 1 [← neg_zero]
  rw [le_neg_iff_le_neg, ← mul_neg, mul_nonneg_iff, neg_le_iff_neg_le, le_neg_iff_le_neg, neg_zero]
-- PRed, see #17087
lemma add_ne_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  exact add_lt_top hx hy
-- PRed, see #17087
lemma add_ne_top_iff_of_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  refine ⟨?_, fun h ↦ add_ne_top h.1 h.2⟩
  induction x <;> simp_all
  induction y <;> simp_all
-- PRed, see #17087
lemma add_ne_top_iff_of_ne_bot_of_ne_top {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := by
  induction x <;> simp [add_ne_top_iff_of_ne_bot, hy, hy']
-- PRed, see #17087
@[simp]
lemma add_ne_bot_iff {x y : EReal} : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := WithBot.add_ne_bot

-- I did not PR this, it seems a bit redundant having add_ne_bot_iff as a simp lemma, now there are no occurrences of this in the project, it can be safely removed
-- lemma add_ne_bot {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) : x + y ≠ ⊥ :=
--   add_ne_bot_iff.mpr ⟨hx, hy⟩

@[simp]
lemma toReal_eq_toReal {x y : EReal} (hx_top : x ≠ ⊤) (hx_bot : x ≠ ⊥)
    (hy_top : y ≠ ⊤) (hy_bot : y ≠ ⊥) :
    x.toReal = y.toReal ↔ x = y := by
  lift x to ℝ using ⟨hx_top, hx_bot⟩
  lift y to ℝ using ⟨hy_top, hy_bot⟩
  simp

-- PRed, see #17087
lemma coe_mul_add_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx_pos : 0 < x := hx_nonneg.lt_of_ne' hx0
  induction y
  · simp [EReal.coe_mul_bot_of_pos hx_pos]
  · induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · norm_cast
      rw [mul_add]
    · simp only [coe_add_top, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.coe_add_top]
  · simp only [EReal.coe_mul_top_of_pos hx_pos]
    induction z
    · simp [EReal.coe_mul_bot_of_pos hx_pos]
    · simp only [top_add_coe, EReal.coe_mul_top_of_pos hx_pos]
      rw [← EReal.coe_mul, EReal.top_add_coe]
    · simp [EReal.coe_mul_top_of_pos hx_pos]
-- PRed, see #17087
lemma add_mul_coe_of_nonneg {x : ℝ} (hx_nonneg : 0 ≤ x) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simp_rw [mul_comm _ (x : EReal)]
  exact EReal.coe_mul_add_of_nonneg hx_nonneg y z
-- PRed, see #17087 as add_sub_cancel_right
lemma add_sub_cancel (x : EReal) (y : ℝ) : x + y - y = x := by
  induction x <;> norm_cast
  ring
-- PRed, see #17087 as add_sub_cancel_left
lemma add_sub_cancel' (x : EReal) (y : ℝ) : y + x - y = x := by
  rw [add_comm, EReal.add_sub_cancel]
-- PRed, see #17087
lemma sub_add_cancel (x : EReal) {y : EReal} (h_top : y ≠ ⊤) (h_bot : y ≠ ⊥) : x - y + y = x := by
  lift y to ℝ using ⟨h_top, h_bot⟩
  induction x <;> norm_cast
  ring
-- PRed, see #17087
@[simp]
lemma sub_self {x : EReal} (h_top : x ≠ ⊤) (h_bot : x ≠ ⊥) : x - x = 0 := by
  induction x <;> simp_all [← coe_sub]
-- PRed, see #17087
lemma sub_self_le_zero {x : EReal} : x - x ≤ 0 := by
  induction x <;> simp
-- PRed, see #17087
lemma top_sub_of_ne_top {x : EReal} (hx : x ≠ ⊤) : ⊤ - x = ⊤ := by
  induction x <;> tauto
-- PRed, see #17087
lemma top_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊤ * (x + y) = ⊤ * x + ⊤ * y := by
  induction x, y using EReal.induction₂_symm with
  | symm h =>
    rw [add_comm, add_comm (⊤ * _)]
    exact h hy hx
  | top_top => simp
  | top_pos _ h =>
    rw [top_add_coe, top_mul_top, top_mul_of_pos, top_add_top]
    exact mod_cast h
  | top_zero => simp
  | top_neg _ h => exact absurd hy <| mod_cast h.not_le
  | top_bot => simp
  | pos_bot => simp
  | coe_coe x y =>
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hy0 : y = 0
    · simp [hy0]
    have hx_pos : 0 < (x : EReal) := hx.lt_of_ne' <| mod_cast hx0
    have hy_pos : 0 < (y : EReal) := hy.lt_of_ne' <| mod_cast hy0
    rw [top_mul_of_pos hx_pos, top_mul_of_pos hy_pos, top_mul_of_pos (add_pos hx_pos hy_pos)]
    exact rfl
  | zero_bot => simp
  | neg_bot => simp
  | bot_bot => simp
-- PRed, see #17087
lemma add_mul_top_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) * ⊤ = x * ⊤ + y * ⊤ := by
  simp_rw [mul_comm _ ⊤, EReal.top_mul_add_of_nonneg hx hy]
-- PRed, see #17087
lemma bot_mul_add_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ⊥ * (x + y) = ⊥ * x + ⊥ * y := by
  simp_rw [← neg_top, neg_mul]
  rw [top_mul_add_of_nonneg hx hy, neg_add, ← sub_eq_add_neg]
  · rw [mul_ne_bot]
    simp [hx, bot_lt_iff_ne_bot.mp <| bot_lt_zero.trans_le hx]
  · rw [mul_ne_bot]
    simp [hy, bot_lt_iff_ne_bot.mp <| bot_lt_zero.trans_le hy]
-- PRed, see #17087
lemma add_mul_bot_of_nonneg {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) * ⊥ = x * ⊥ + y * ⊥ := by
  simp_rw [mul_comm _ ⊥, EReal.bot_mul_add_of_nonneg hx hy]
-- PRed, see #17087
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
-- PRed, see #17087
lemma coe_add_mul_of_nonneg (x : EReal) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (y + z) * x =  y * x + z * x := by
  simp_rw [mul_comm _ x]
  exact EReal.mul_add_coe_of_nonneg x hy hz
-- PRed, see #17087
lemma toReal_nonneg {x : EReal} (hx : 0 ≤ x) : 0 ≤ x.toReal := by
  induction x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonneg.mp hx
  · norm_num
-- PRed, see #17087
lemma toReal_nonpos {x : EReal} (hx : x ≤ 0) : x.toReal ≤ 0 := by
  induction x
  · norm_num
  · exact toReal_coe _ ▸ EReal.coe_nonpos.mp hx
  · norm_num
-- PRed, see #17087
lemma toReal_ne_zero_iff {x : EReal} : x.toReal ≠ 0 ↔ x ≠ 0 ∧ x ≠ ⊤ ∧ x ≠ ⊥ := by
  induction x <;> norm_num
-- PRed, see #17087
lemma toReal_eq_zero_iff {x : EReal} : x.toReal = 0 ↔ x = 0 ∨ x = ⊤ ∨ x = ⊥ := by
  induction x <;> norm_num
-- PRed, see #17087
lemma sub_nonneg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    0 ≤ x - y ↔ y ≤ x := by
  induction x <;> induction y <;> simp_all [← EReal.coe_sub]
-- PRed, see #17087
lemma sub_nonpos {x y : EReal} : x - y ≤ 0 ↔ x ≤ y := by
  induction x <;> induction y <;> simp [← EReal.coe_sub]
-- PRed, see #17087
lemma sub_pos {x y : EReal} : 0 < x - y ↔ y < x := by
  induction x <;> induction y <;> simp [← EReal.coe_sub]
-- PRed, see #17087
lemma sub_neg {x y : EReal} (h_top : x ≠ ⊤ ∨ y ≠ ⊤) (h_bot : x ≠ ⊥ ∨ y ≠ ⊥) :
    x - y < 0 ↔ x < y := by
  induction x <;> induction y <;> simp_all [← EReal.coe_sub]
-- PRed, see #17087
@[simp]
lemma nsmul_eq_mul (n : ℕ) (x : EReal) : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]
    convert (EReal.coe_add_mul_of_nonneg x _ _).symm <;> simp

-- PRed, see #17097
lemma lowerSemicontinuous_add : LowerSemicontinuous fun (p : EReal × EReal) ↦ p.1 + p.2 := by
  intro x
  by_cases hx1_bot : x.1 = ⊥
  · intro y
    simp [hx1_bot]
  by_cases hx2_bot : x.2 = ⊥
  · intro y
    simp [hx2_bot]
  exact EReal.continuousAt_add (Or.inr hx2_bot) (Or.inl hx1_bot) |>.lowerSemicontinuousAt
-- PRed, see #17097
instance : MeasurableAdd₂ EReal := ⟨EReal.lowerSemicontinuous_add.measurable⟩

--in the PR these I put the fact that ContinuousNeg implies MeasurableNeg in the right place as an instance generalizing an existing one, so there should be no need to prove these things explicitly, see PR #17082
instance : MeasurableNeg EReal := by
  refine ⟨?_⟩
  fun_prop

section MeasurableMul

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
-- PRed, see #17097
theorem measurable_from_prod_countable'' [Countable β] [MeasurableSingletonClass β]
    {f : β × α → γ} (hf : ∀ x, Measurable fun y => f (x, y)) :
    Measurable f := by
  change Measurable ((fun (p : α × β) ↦ f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable hf).comp measurable_swap
-- PRed, see #17097
theorem measurable_of_measurable_real_prod {f : EReal × β → γ}
    (h_real : Measurable fun p : ℝ × β ↦ f (p.1, p.2))
    (h_bot : Measurable fun x ↦ f (⊥, x)) (h_top : Measurable fun x ↦ f (⊤, x)) :
    Measurable f := by
  have : (univ : Set (EReal × β)) = ({⊥, ⊤} ×ˢ univ) ∪ ({⊥, ⊤}ᶜ ×ˢ univ) := by
    ext x
    simp only [mem_univ, mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, and_true,
      mem_compl_iff, not_or, true_iff]
    tauto
  refine measurable_of_measurable_union_cover ({⊥, ⊤} ×ˢ univ)
    ({⊥, ⊤}ᶜ ×ˢ univ) ?_ ?_ ?_ ?_ ?_
  · refine MeasurableSet.prod ?_ MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · refine (MeasurableSet.compl ?_).prod MeasurableSet.univ
    simp only [measurableSet_insert, MeasurableSet.singleton]
  · rw [this]
  · let e : ({⊥, ⊤} ×ˢ univ : Set (EReal × β)) ≃ᵐ ({⊥, ⊤} : Set EReal) × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤} : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.Set.univ β))
    have : ((fun (a : ({⊥, ⊤} : Set EReal) × β) ↦ f (a.1, a.2)) ∘ e)
        = fun (a : ({⊥, ⊤} ×ˢ univ : Set (EReal × β))) ↦ f a := rfl
    rw [← this]
    refine Measurable.comp ?_ e.measurable
    refine measurable_from_prod_countable'' fun y ↦ ?_
    simp only
    have h' := y.2
    simp only [mem_insert_iff, mem_singleton_iff, bot_ne_top, or_false, top_ne_bot, or_true] at h'
    cases h' with
    | inl h => rwa [h]
    | inr h => rwa [h]
  · let e : ({⊥, ⊤}ᶜ ×ˢ univ : Set (EReal × β)) ≃ᵐ ℝ × β :=
      (MeasurableEquiv.Set.prod ({⊥, ⊤}ᶜ : Set EReal) (univ : Set β)).trans
        (MeasurableEquiv.erealEquivReal.prodCongr (MeasurableEquiv.Set.univ β))
    rw [← MeasurableEquiv.measurable_comp_iff e.symm]
    exact h_real
-- PRed, see #17097
theorem measurable_of_measurable_real_real {f : EReal × EReal → β}
    (h_real : Measurable fun p : ℝ × ℝ ↦ f (p.1, p.2))
    (h_bot_left : Measurable fun r : ℝ ↦ f (⊥, r))
    (h_top_left : Measurable fun r : ℝ ↦ f (⊤, r))
    (h_bot_right : Measurable fun r : ℝ ↦ f (r, ⊥))
    (h_top_right : Measurable fun r : ℝ ↦ f (r, ⊤)) :
    Measurable f := by
  refine measurable_of_measurable_real_prod ?_ ?_ ?_
  · refine measurable_swap_iff.mp <| measurable_of_measurable_real_prod ?_ h_bot_right h_top_right
    exact h_real.comp measurable_swap
  · exact measurable_of_measurable_real h_bot_left
  · exact measurable_of_measurable_real h_top_left
-- PRed, see #17097
private lemma measurable_const_mul (c : EReal) : Measurable fun (x : EReal) ↦ c * x := by
  refine measurable_of_measurable_real ?_
  have h1 : (fun (p : ℝ) ↦ (⊥ : EReal) * p)
      = fun p ↦ if p = 0 then (0 : EReal) else (if p < 0 then ⊤ else ⊥) := by
    ext p
    split_ifs with h1 h2
    · simp [h1]
    · rw [bot_mul_coe_of_neg h2]
    · rw [bot_mul_coe_of_pos]
      exact lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
  have h2 : Measurable fun (p : ℝ) ↦ if p = 0 then (0 : EReal) else if p < 0 then ⊤ else ⊥ := by
    refine .piecewise (measurableSet_singleton _) ?_ (.piecewise measurableSet_Iio ?_ ?_)
      <;> exact measurable_const
  induction c with
  | h_bot => rwa [h1]
  | h_real c => exact (measurable_id.const_mul _).coe_real_ereal
  | h_top =>
    simp_rw [← neg_bot, neg_mul]
    apply Measurable.neg
    rwa [h1]
-- PRed, see #17097
instance : MeasurableMul₂ EReal := by
  refine ⟨measurable_of_measurable_real_real ?_ ?_ ?_ ?_ ?_⟩
  · exact (measurable_fst.mul measurable_snd).coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊥]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal
  · simp_rw [mul_comm _ ⊤]
    exact (measurable_const_mul _).comp measurable_coe_real_ereal

end MeasurableMul
-- PRed, see #17100
theorem nhdsWithin_top : 𝓝[≠] (⊤ : EReal) = (atTop).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to ℝ using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h1, h2.ne_top]
  · simp only [EReal.image_coe_Ici, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.coe_lt_top x, fun x ⟨(h1 : _ ≤ x), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.lt_top' fun a ↦ h2 a.symm]

-- PRed, see #17100
lemma nhdsWithin_bot : 𝓝[≠] (⊥ : EReal) = (atBot).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic, Set.subset_compl_singleton_iff, Set.mem_Ioc, lt_self_iff_false,
      bot_le, and_true, not_false_eq_true, true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to ℝ using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h2, h1.ne_bot]
  · simp only [EReal.image_coe_Iic, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.bot_lt_coe x, fun x ⟨(h1 : x ≤ _), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.bot_lt' fun a ↦ h2 a.symm]

-- PRed, see #17100
theorem tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[≠] ⊤) atTop := by
  rw [nhdsWithin_top, tendsto_map'_iff]
  exact tendsto_id

-- PRed, see #17100
theorem tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[≠] ⊥) atBot := by
  rw [nhdsWithin_bot, tendsto_map'_iff]
  exact tendsto_id

/-- Reinterpret an EReal number `x` as an ENNReal number. Returns `0` if `x < 0`. -/
noncomputable def toENNReal (x : EReal) : ENNReal :=
  if x = ⊤ then ⊤
  else ENNReal.ofReal x.toReal

@[simp]
theorem toENNReal_top : (⊤ : EReal).toENNReal = ⊤ := rfl

@[simp]
lemma toENNReal_of_ne_top {x : EReal} (hx : x ≠ ⊤) : x.toENNReal = ENNReal.ofReal x.toReal :=
  if_neg hx

@[simp]
theorem toENNReal_eq_top_iff {x : EReal} : x.toENNReal = ⊤ ↔ x = ⊤ := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toENNReal]

theorem toENNReal_ne_top_iff {x : EReal} : x.toENNReal ≠ ⊤ ↔ x ≠ ⊤ := toENNReal_eq_top_iff.not

@[simp]
theorem toENNReal_of_nonpos {x : EReal} (hx : x ≤ 0) : x.toENNReal = 0 := by
  rw [toENNReal, if_neg ?_]
  exact ENNReal.ofReal_of_nonpos (toReal_nonpos hx)
  intro h
  rw [h, top_le_iff] at hx
  exact zero_ne_top hx

theorem toENNReal_eq_zero_iff {x : EReal} : x.toENNReal = 0 ↔ x ≤ 0 := by
  induction x <;> simp [toENNReal]

theorem toENNReal_ne_zero_iff {x : EReal} : x.toENNReal ≠ 0 ↔ 0 < x := by
  simp [toENNReal_eq_zero_iff.not]

@[simp]
theorem coe_toENNReal {x : EReal} (hx : 0 ≤ x) : (x.toENNReal : EReal) = x := by
  rw [toENNReal]
  by_cases h_top : x = ⊤
  · rw [if_pos h_top, h_top]
    rfl
  rw [if_neg h_top]
  simp only [coe_ennreal_ofReal, ge_iff_le, hx, toReal_nonneg, max_eq_left]
  exact coe_toReal h_top fun _ ↦ by simp_all only [le_bot_iff, zero_ne_bot]

@[simp]
theorem toENNReal_coe {x : ENNReal} : (x : EReal).toENNReal = x := by
  by_cases h_top : x = ⊤
  · rw [h_top, coe_ennreal_top, toENNReal_top]
  rw [toENNReal, if_neg _, toReal_coe_ennreal, ENNReal.ofReal_toReal_eq_iff]
  · exact h_top
  · simp [h_top]

theorem toENNReal_le_toENNReal {x y : EReal} (h : x ≤ y) : x.toENNReal ≤ y.toENNReal := by
  induction x
  · simp
  · by_cases hy_top : y = ⊤
    · simp [hy_top]
    simp_all [h, toENNReal]
    refine ENNReal.ofReal_le_ofReal ?_
    refine EReal.toReal_le_toReal h (coe_ne_bot _) hy_top
  · simp_all

@[simp]
lemma real_coe_toENNReal (x : ℝ) : (x : EReal).toENNReal = ENNReal.ofReal x := rfl

@[simp]
lemma toReal_toENNReal {x : EReal} (hx : 0 ≤ x) : x.toENNReal.toReal = x.toReal := by
  by_cases h : x = ⊤
  · simp [h]
  · simp [h, toReal_nonneg hx]

@[measurability]
theorem _root_.measurable_ereal_toENNReal : Measurable EReal.toENNReal :=
  EReal.measurable_of_measurable_real (by simpa using ENNReal.measurable_ofReal)

@[measurability, fun_prop]
theorem _root_.Measurable.ereal_toENNReal {α : Type*} {_ : MeasurableSpace α}
    {f : α → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toENNReal :=
  measurable_ereal_toENNReal.comp hf

lemma toENNReal_add {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

lemma toENNReal_add_le {x y : EReal} : (x + y).toENNReal ≤ x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le

lemma toENNReal_sub {x y : EReal} (hy : 0 ≤ y) :
    (x - y).toENNReal = x.toENNReal - y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  · rename_i x y
    simp only [ne_eq, coe_ne_top, not_false_eq_true, toENNReal_of_ne_top, toReal_coe]
    by_cases hxy : x ≤ y
    · rw [toENNReal_of_nonpos]
      swap; · exact sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy
      simp_all
    · rw [toENNReal_of_ne_top, ← EReal.coe_sub, toReal_coe,
        ENNReal.ofReal_sub x (EReal.coe_nonneg.mp hy)]
      exact Ne.symm (ne_of_beq_false rfl)
  · rw [ENNReal.sub_eq_top_iff.mpr (by simp), top_sub_of_ne_top (coe_ne_top _), toENNReal_top]

lemma toENNReal_mul {x y : EReal} (hx : 0 ≤ x) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ENNReal.ofReal_mul, ← EReal.coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [EReal.mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg (EReal.coe_neg'.mpr ha)]
    · simp [ha]
    · simp_all [top_mul_of_pos (EReal.coe_pos.mpr ha)]

lemma toENNReal_mul' {x y : EReal} (hy : 0 ≤ y) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  rw [mul_comm, toENNReal_mul hy, mul_comm]

lemma continuous_toENNReal : Continuous EReal.toENNReal := by
  sorry

@[fun_prop]
lemma _root_.Continous.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    (hf : Continuous f) :
    Continuous fun x => (f x).toENNReal :=
  continuous_toENNReal.comp hf

@[fun_prop]
lemma _root_.ContinuousOn.ereal_toENNReal {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α → EReal} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).toENNReal) s :=
  continuous_toENNReal.comp_continuousOn hf

@[fun_prop]
lemma _root_.ContinuousWithinAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x).toENNReal) s x :=
  continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]
lemma _root_.ContinuousAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (f x).toENNReal) x :=
  continuous_toENNReal.continuousAt.comp hf

end EReal

namespace ENNReal

variable {a b c x y : ℝ≥0∞}

lemma toEReal_sub (hy_top : y ≠ ⊤) (h_le : y ≤ x) :
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

--PR these 2 lemmas to mathlib, just after ENNReal.mul_max
-- #check ENNReal.mul_max
theorem min_mul : min a b * c = min (a * c) (b * c) := mul_right_mono.map_min

theorem mul_min : a * min b c = min (a * b) (a * c) := mul_left_mono.map_min

@[simp]
lemma toReal_toEReal_of_ne_top (hx : x ≠ ⊤) : x.toReal.toEReal = x.toEReal := by
  cases x <;> tauto

end ENNReal
