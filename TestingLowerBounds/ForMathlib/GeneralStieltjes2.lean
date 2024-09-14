/-
Here I try to rewrite the Stieltjes.lean file from Mathlib, but putting EReal as the codomain of the function, this should allow any function that is monotone and right continuous on some interval to be extended to a Stieltjes function, by putting it to +∞ or -∞  outside the interval.
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LeftRightLim
import TestingLowerBounds.ForMathlib.EReal

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)


/-! ### Basic properties of Stieltjes functions -/


/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure StieltjesFunction where
  toFun : ℝ → EReal
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace StieltjesFunction

attribute [coe] toFun

instance instCoeFun : CoeFun StieltjesFunction fun _ => ℝ → EReal :=
  ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)

@[ext] lemma ext {f g : StieltjesFunction} (h : ∀ x, f x = g x) : f = g := by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

variable (f : StieltjesFunction)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

theorem rightLim_eq (f : StieltjesFunction) (x : ℝ) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

theorem iInf_Ioi_eq (f : StieltjesFunction) (x : ℝ) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
  rw [← neBot_iff]
  infer_instance

-- theorem iInf_rat_gt_eq (f : StieltjesFunction) (x : ℝ) :
--     ⨅ r : { r' : ℚ // x < r' }, f r = f x := by
--   rw [← iInf_Ioi_eq f x]
--   refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
--   refine ⟨f x, fun y => ?_⟩
--   rintro ⟨y, hy_mem, rfl⟩
--   exact f.mono (le_of_lt hy_mem)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
protected def id : StieltjesFunction where
  toFun := Real.toEReal
  mono' _ _ := EReal.coe_le_coe_iff.mpr
  right_continuous' _ := continuous_coe_real_ereal.continuousWithinAt

@[simp]
theorem id_leftLim (x : ℝ) : leftLim StieltjesFunction.id x = x :=
  tendsto_nhds_unique (StieltjesFunction.id.mono.tendsto_leftLim x) <|
    continuous_coe_real_ereal.continuousWithinAt

instance instInhabited : Inhabited StieltjesFunction :=
  ⟨StieltjesFunction.id⟩

/-- Constant functions are Stieltjes function. -/
protected def const (c : EReal) : StieltjesFunction where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

@[simp] lemma const_apply (c : EReal) (x : ℝ) : (StieltjesFunction.const c) x = c := rfl

--this is not true. Counterexample: f(x) = log x for x > 0, f(x) = ⊥  for x ≤ 0, g(x) = ⊤ for every x, then f, g are stieltjes, but f + g (x) = ⊤ for x > 0, f + g (x) = ⊥ for x ≤ 0, so f+g is not right continuous at 0.
-- that's unfortunate, because the fact that ⊤ + ⊥ = ⊥ actually makes things break, if we had ⊤ + ⊥ = ⊤, then the above example would actually be right continuous and I think the property would have been true, because since the functions are monotone you cannot have smething that tends to ⊤ from the right without being ⊤ at the right of x.
-- maybe if we prove Monotone.stieltjesFunction we could define the sum as the right limit of the sum of the functions, that is guaranteed to be monotone, before that however we need a lemma saying that the right limit is right continuous (under which conditions?) and that taking the right limit twice is the same as taking it once.
-- /-- The sum of two Stieltjes functions is a Stieltjes function. -/
-- protected def add (f g : StieltjesFunction) : StieltjesFunction where
--   toFun := fun x => f x + g x
--   mono' := f.mono.add g.mono
--   right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

-- instance : AddZeroClass StieltjesFunction where
--   add := StieltjesFunction.add
--   zero := StieltjesFunction.const 0
--   zero_add _ := ext fun _ ↦ zero_add _
--   add_zero _ := ext fun _ ↦ add_zero _

-- instance : AddCommMonoid StieltjesFunction where
--   nsmul n f := nsmulRec n f
--   add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
--   add_comm _ _ := ext fun _ ↦ add_comm _ _
--   __ := StieltjesFunction.instAddZeroClass

-- instance : Module ℝ≥0 StieltjesFunction where
--   smul c f := {
--     toFun := fun x ↦ c * f x
--     mono' := f.mono.const_mul c.2
--     right_continuous' := fun x ↦ (f.right_continuous x).const_smul c.1}
--   one_smul _ := ext fun _ ↦ one_mul _
--   mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
--   smul_zero _ := ext fun _ ↦ mul_zero _
--   smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
--   add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
--   zero_smul _ := ext fun _ ↦ zero_mul _

-- @[simp] lemma add_apply (f g : StieltjesFunction) (x : ℝ) : (f + g) x = f x + g x := rfl

--if we had this the next proof would be quite easy, but I'm not sure how to prove it
lemma rightLim_rightLim_eq {α β : Type*} [LinearOrder α] [TopologicalSpace β]
    [TopologicalSpace α] [OrderTopology α] [T2Space β] {f : α → β} {a : α} {y : β} :
    rightLim (rightLim f) a = rightLim f a := by

  sorry

--we need a lemma saying that taking the right limit twice is the same as taking it once
--maybe the fact that the right limit is right continuous can help, but we need to prove it before, it should be true, I hope also for functions in EReal, see https://math.stackexchange.com/questions/1651427/is-the-right-limit-function-always-right-continuous for a proof for real functions
-- /-- If a function `f : ℝ → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
-- at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
-- noncomputable def _root_.Monotone.stieltjesFunction {f : ℝ → EReal} (hf : Monotone f) :
--     StieltjesFunction where
--   toFun := rightLim f
--   mono' x y hxy := hf.rightLim hxy
--   right_continuous' := by
--     intro x s hs
--     by_cases h_top : rightLim f x = ⊤
--     ·
--       rw [h_top, EReal.mem_nhds_top_iff] at hs
--       obtain ⟨y, hy⟩ := hs
--       simp only [mem_map]

--       sorry
--     by_cases h_bot : rightLim f x = ⊥
--     ·
--       sorry
--     lift rightLim f x to ℝ using ⟨h_top, h_bot⟩ with y hy
--     obtain ⟨l, u, hlu, lus⟩ : ∃ l u : EReal, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
--       (mem_nhds_iff_exists_Ioo_subset' ⟨⊥, hy ▸ EReal.bot_lt_coe y⟩
--         ⟨⊤, hy ▸ EReal.coe_lt_top y⟩).mp (hy ▸ hs)
--     obtain ⟨y, xy, h'y⟩ : ∃ (y : ℝ), x < y ∧ Ioc x y ⊆ f ⁻¹' Ioo l u :=
--       mem_nhdsWithin_Ioi_iff_exists_Ioc_subset.1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
--     change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
--     filter_upwards [Ico_mem_nhdsWithin_Ici ⟨le_refl x, xy⟩] with z hz
--     apply lus
--     refine ⟨hlu.1.trans_le (hf.rightLim hz.1), ?_⟩
--     obtain ⟨a, za, ay⟩ : ∃ a : ℝ, z < a ∧ a < y := exists_between hz.2
--     calc
--       rightLim f z ≤ f a := hf.rightLim_le za
--       _ < u := (h'y ⟨hz.1.trans_lt za, ay.le⟩).2

-- theorem _root_.Monotone.stieltjesFunction_eq {f : ℝ → EReal} (hf : Monotone f) (x : ℝ) :
--     hf.stieltjesFunction x = rightLim f x :=
--   rfl

theorem countable_leftLim_ne (f : StieltjesFunction) : Set.Countable { x | leftLim f x ≠ f x } := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact tendsto_nhds_unique (f.mono.tendsto_leftLim x) (h'x.tendsto.mono_left nhdsWithin_le_nhds)

/-! ### The outer measure associated to a Stieltjes function -/


/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅ (a) (b) (_ : s ⊆ Ioc a b), (f b - f a).toENNReal

@[simp]
theorem length_empty : f.length ∅ = 0 := by
  refine nonpos_iff_eq_zero.1 <| iInf_le_of_le 0 <| iInf_le_of_le 0 ?_
  by_cases h : f 0 = ⊤
  · simp [h]
  by_cases h' : f 0 = ⊥
  · simp [h']
  rw [EReal.sub_self h h']
  simp

@[simp]
theorem length_Ioc (a b : ℝ) :
    f.length (Ioc a b) = (f b - f a).toENNReal := by
  refine le_antisymm (iInf_le_of_le a <| iInf₂_le b Subset.rfl)
    (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ?_)
  by_cases ha : f a = ⊤
  · simp [ha]
  by_cases hb : f b = ⊥
  · simp [hb]
  rcases le_or_lt b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos]
    · exact zero_le _
    rw [EReal.sub_nonpos]
    exact f.mono ab
  cases' (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂
  have ha' : f a' ≠ ⊤ := fun h ↦ ha <| top_le_iff.mp <| h ▸ f.mono h₂
  have hb' : f b' ≠ ⊥ := fun h ↦ hb <| le_bot_iff.mp <| h ▸ f.mono h₁
  simp only [ha, hb, or_self, ↓reduceIte, ha', hb', ge_iff_le]
  exact EReal.toENNReal_le_toENNReal <| EReal.sub_le_sub (f.mono h₁) (f.mono h₂)

theorem length_mono {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
  iInf_mono fun _ => biInf_mono fun _ => h.trans

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : OuterMeasure ℝ :=
  OuterMeasure.ofFunction f.length f.length_empty

theorem outer_le_length (s : Set ℝ) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ} (ss : Icc a b ⊆ ⋃ i, Ioo (c i) (d i)) :
    (f b - f a).toENNReal ≤ ∑' i, (f (d i) - f (c i)).toENNReal := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Ioo (c i) (d i)) →
      (f b - f a).toENNReal ≤ ∑ i ∈ s, (f (d i) - f (c i)).toENNReal by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Ioo _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i ∈ (hf.toFinset : Set ℕ), Ioo (c i) (d i) = ⋃ i ∈ s, Ioo (c i) (d i) := by
      simp only [Set.ext_iff, exists_prop, Finset.set_biUnion_coe, mem_iUnion, forall_const,
        iff_self_iff, Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e] )
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [EReal.toENNReal_of_nonpos]
    · exact zero_le _
    · exact EReal.sub_nonpos.mpr (f.mono ab)
  have := cv ⟨ab, le_rfl⟩
  simp only [Finset.mem_coe, gt_iff_lt, not_lt, mem_iUnion, mem_Ioo, exists_and_left,
    exists_prop] at this
  rcases this with ⟨i, cb, is, bd⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
  refine le_trans ?_ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) ?_) _)
  · have h := f.mono bd.le
    by_cases h_top : f (c i) = ⊤
    · have : f b = ⊤ := eq_top_iff.mpr <| h_top ▸ f.mono cb.le
      simp [h_top, this]
    by_cases h_bot : f (c i) = ⊥
    · generalize f (d i) = y at h ⊢
      induction y <;> try {· simp [h_bot]}
      simp [h_bot, le_bot_iff.mp h]
    refine le_trans (EReal.toENNReal_le_toENNReal ?_) EReal.toENNReal_add_le
    rw [← add_sub_assoc]
    refine EReal.sub_le_sub ?_ (le_refl _)
    rwa [EReal.sub_add_cancel _ h_top h_bot]
  · rintro x ⟨h₁, h₂⟩
    exact (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt And.left (not_lt_of_le h₂))

-- this really needs to be proven, because the definition of Stieltjes measure depends on it
-- @[simp]
-- theorem outer_Ioc (a b : ℝ) : f.outer (Ioc a b) = (f b - f a).toENNReal := by
--   /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
--     by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
--     intervals, while we would like to have a compact interval covered by open intervals to use
--     compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
--     the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
--     still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
--     (up to `ε/2`).
--     Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
--     very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
--     slightly to the right, then the `f`-length will change very little by right continuity, and we
--     will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
--     of the `f`-length of `s i`. -/
--   -- refine le_antisymm (f.length_Ioc _ _ ▸ outer_le_length _ _) (le_iInf₂ fun s hs => ?_)
--   -- by_cases h : f a = ⊤



--   have h_cont (x y : ℝ) (h : f x ≠ ⊤ ∨ f y ≠ ⊤) (h' : f x ≠ ⊥ ∨ f y ≠ ⊥) :
--       ContinuousWithinAt (fun r => f r - f y) (Ioi x) x := by
--     simp_rw [sub_eq_add_neg]
--     change ContinuousWithinAt ((fun z ↦ z.1 + z.2) ∘ fun r ↦ (f r, -f y)) (Ioi x) x
--     refine ContinuousAt.comp_continuousWithinAt ?_ ?_
--     · exact EReal.continuousAt_add (by simp [h]) (by simp [h'])
--     · exact (f.right_continuous x).mono Ioi_subset_Ici_self |>.prod continuousWithinAt_const

--   refine le_antisymm (f.length_Ioc _ _ ▸ outer_le_length _ _)
--       (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_)
--   let δ := ε / 2
--   have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
--   rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩

--   have : ∀ i, ∃ pq : ℝ × ℝ,
--       s i ⊆ Ioo pq.1 pq.2 ∧ (f pq.2 - f pq.1).toENNReal < f.length (s i) + ε' i := by
--     intro i
--     have hl :=
--       ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
--     conv at hl =>
--       lhs
--       rw [length]
--     simp only [iInf_lt_iff, exists_prop] at hl
--     rcases hl with ⟨p, q', spq, hq'⟩

--     by_cases h_bot : f p = ⊥ --or maybe the case should be split even before and this whole have is not true if f p = ⊥???
--     ·
--       sorry
--     -- divide the case where f p = ⊥ or the one where f q' = ⊥? I think I need to do it before this have, it's not true that it is continuous if for example f q' = ⊥
--     have : ContinuousWithinAt (fun r => (f r - f p).toENNReal) (Ioi q') q' := by
--       by_cases h_top : f p = ⊤
--       · simp [h_top, continuousWithinAt_const]
--       refine ContinuousWithinAt.ereal_toENNReal (h_cont _ _ (Or.inr h_top) ?_)

--       sorry
--       -- apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
--       -- refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
--       -- exact (f.right_continuous q').mono Ioi_subset_Ici_self
--     rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
--     exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩
--   choose g hg using this

--   obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
--     have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
--       refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
--       exact (f.right_continuous a).mono Ioi_subset_Ici_self
--     have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
--     exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists

--   have I_subset : Icc a' b ⊆ ⋃ i, Ioo (g i).1 (g i).2 :=
--     calc
--       Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
--       _ ⊆ ⋃ i, s i := hs
--       _ ⊆ ⋃ i, Ioo (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
--   calc
--     (f b - f a).toENNReal = (f b - f a' + (f a' - f a)).toENNReal := by rw [sub_add_sub_cancel]
--     _ ≤ (f b - f a').toENNReal + (f a' - f a).toENNReal := ENNReal.ofReal_add_le
--     _ ≤ ∑' i, (f (g i).2 - f (g i).1).toENNReal + ofReal δ :=
--       (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
--     _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
--       (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
--         (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
--     _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
--     _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
--     _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

theorem measurableSet_Ioi {c : ℝ} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  refine
    le_trans
      (add_le_add (f.length_mono <| inter_subset_inter_left _ h)
        (f.length_mono <| diff_subset_diff_left h)) ?_
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, _root_.sup_eq_max, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_diff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [Ioc_inter_Ioi, hac, sup_of_le_right, f.length_Ioc, Ioc_diff_Ioi, hbc, min_eq_right]
    generalize hfc : f c = y
    induction y
    · have := le_bot_iff.mp <| hfc ▸ f.mono hac
      simp [this]
    · rw [← EReal.toENNReal_add, add_sub,
        EReal.sub_add_cancel _ (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      <;> simp [EReal.sub_nonneg, hfc ▸ f.mono hbc, hfc ▸ f.mono hac]
    · have := top_le_iff.mp <| hfc ▸ f.mono hbc
      simp [this]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_diff_Ioi, f.length_empty,
      zero_add, or_true_iff, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_right, _root_.sup_eq_max,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

-- theorem outer_trim : f.outer.trim = f.outer := by
--   refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
--   rw [OuterMeasure.trim_eq_iInf]
--   refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
--   rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
--   refine le_trans ?_ (add_le_add_left (le_of_lt hε) _)
--   rw [← ENNReal.tsum_add]
--   choose g hg using
--     show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
--       intro i
--       have hl :=
--         ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
--       conv at hl =>
--         lhs
--         rw [length]
--       simp only [iInf_lt_iff] at hl
--       rcases hl with ⟨a, b, h₁, h₂⟩
--       rw [← f.outer_Ioc] at h₂
--       exact ⟨_, h₁, measurableSet_Ioc, le_of_lt <| by simpa using h₂⟩
--   simp only [ofReal_coe_nnreal] at hg
--   apply iInf_le_of_le (iUnion g) _
--   apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
--   apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
--   exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

theorem borel_le_measurable : borel ℝ ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp (config := { contextual := true }) [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/


-- /-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
-- interval `(a, b]`. -/
-- protected irreducible_def measure : Measure ℝ where
--   toOuterMeasure := f.outer
--   m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ (hs i)
--   trim_le := f.outer_trim.le

-- @[simp]
-- theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = (f b - f a).toENNReal := by
--   rw [StieltjesFunction.measure]
--   exact f.outer_Ioc a b

-- @[simp]
-- theorem measure_singleton (a : ℝ) : f.measure {a} = (f a - leftLim f a).toENNReal := by
--   obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
--     ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n : ℕ, u n < a) ∧ Tendsto u atTop (𝓝 a) :=
--     exists_seq_strictMono_tendsto a
--   have A : {a} = ⋂ n, Ioc (u n) a := by
--     refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
--     simp? at hx says simp only [mem_iInter, mem_Ioc] at hx
--     have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
--     simp [le_antisymm this (hx 0).2]
--   have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
--     rw [A]
--     refine tendsto_measure_iInter (fun n => measurableSet_Ioc.nullMeasurableSet)
--       (fun m n hmn => ?_) ?_
--     · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
--     · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
--   have L2 :
--       Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
--     simp only [measure_Ioc]
--     have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
--       apply (f.mono.tendsto_leftLim a).comp
--       exact
--         tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
--           (Eventually.of_forall fun n => u_lt_a n)
--     exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
--   exact tendsto_nhds_unique L1 L2

-- @[simp]
-- theorem measure_Icc (a b : ℝ) : f.measure (Icc a b) = (f b - leftLim f a).toENNReal := by
--   rcases le_or_lt a b with (hab | hab)
--   · have A : Disjoint {a} (Ioc a b) := by simp
--     simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
--       f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
--   · simp only [hab, measure_empty, Icc_eq_empty, not_le]
--     symm
--     simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]

-- @[simp]
-- theorem measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = (leftLim f b - f a).toENNReal := by
--   rcases le_or_lt b a with (hab | hab)
--   · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
--     symm
--     simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
--   · have A : Disjoint (Ioo a b) {b} := by simp
--     have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
--     have := f.measure_Ioc a b
--     simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
--       measure_union A (measurableSet_singleton b), Icc_self] at this
--     rw [D, ENNReal.ofReal_add, add_comm] at this
--     · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
--     · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
--     · simp only [f.mono.le_leftLim hab, sub_nonneg]

-- @[simp]
-- theorem measure_Ico (a b : ℝ) : f.measure (Ico a b) = (leftLim f b - leftLim f a).toENNReal := by
--   rcases le_or_lt b a with (hab | hab)
--   · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
--     symm
--     simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
--   · have A : Disjoint {a} (Ioo a b) := by simp
--     simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.mono.leftLim_le,
--       measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

-- theorem measure_Iic {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : ℝ) :
--     f.measure (Iic x) = (f x - l).toENNReal := by
--   refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
--   simp_rw [measure_Ioc]
--   exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)

-- theorem measure_Ici {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : ℝ) :
--     f.measure (Ici x) = (l - leftLim f x).toENNReal := by
--   refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
--   simp_rw [measure_Ico]
--   refine ENNReal.tendsto_ofReal (Tendsto.sub_const ?_ _)
--   have h_le1 : ∀ x, f (x - 1) ≤ leftLim f x := fun x => Monotone.le_leftLim f.mono (sub_one_lt x)
--   have h_le2 : ∀ x, leftLim f x ≤ f x := fun x => Monotone.leftLim_le f.mono le_rfl
--   refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hf.comp ?_) hf h_le1 h_le2
--   rw [tendsto_atTop_atTop]
--   exact fun y => ⟨y + 1, fun z hyz => by rwa [le_sub_iff_add_le]⟩

-- theorem measure_univ {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
--     f.measure univ = ofReal (u - l) := by
--   refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
--   simp_rw [measure_Iic f hfl]
--   exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

-- lemma isFiniteMeasure {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
--     IsFiniteMeasure f.measure := ⟨by simp [f.measure_univ hfl hfu]⟩

-- lemma isProbabilityMeasure (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
--     IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

-- instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure :=
--   ⟨fun x => ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), by simp⟩⟩

-- lemma eq_of_measure_of_tendsto_atBot (g : StieltjesFunction) {l : ℝ}
--     (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
--     f = g := by
--   ext x
--   have hf := measure_Iic f hfl x
--   rw [hfg, measure_Iic g hgl x, ENNReal.ofReal_eq_ofReal_iff, eq_comm] at hf
--   · simpa using hf
--   · rw [sub_nonneg]
--     exact Monotone.le_of_tendsto g.mono hgl x
--   · rw [sub_nonneg]
--     exact Monotone.le_of_tendsto f.mono hfl x

-- lemma eq_of_measure_of_eq (g : StieltjesFunction) {y : ℝ}
--     (hfg : f.measure = g.measure) (hy : f y = g y) :
--     f = g := by
--   ext x
--   cases le_total x y with
--   | inl hxy =>
--     have hf := measure_Ioc f x y
--     rw [hfg, measure_Ioc g x y, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
--     · simpa using hf
--     · rw [sub_nonneg]
--       exact g.mono hxy
--     · rw [sub_nonneg]
--       exact f.mono hxy
--   | inr hxy =>
--     have hf := measure_Ioc f y x
--     rw [hfg, measure_Ioc g y x, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
--     · simpa using hf
--     · rw [sub_nonneg]
--       exact g.mono hxy
--     · rw [sub_nonneg]
--       exact f.mono hxy

-- @[simp]
-- lemma measure_const (c : ℝ) : (StieltjesFunction.const c).measure = 0 :=
--   Measure.ext_of_Ioc _ _ (fun _ _ _ ↦ by simp)

-- @[simp]
-- lemma measure_add (f g : StieltjesFunction) : (f + g).measure = f.measure + g.measure := by
--   refine Measure.ext_of_Ioc _ _ (fun a b h ↦ ?_)
--   simp only [measure_Ioc, add_apply, Measure.coe_add, Pi.add_apply]
--   rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono h.le)) (sub_nonneg_of_le (g.mono h.le))]
--   ring_nf

-- @[simp]
-- lemma measure_smul (c : ℝ≥0) (f : StieltjesFunction) : (c • f).measure = c • f.measure := by
--   refine Measure.ext_of_Ioc _ _ (fun a b _ ↦ ?_)
--   simp only [measure_Ioc, Measure.smul_apply]
--   change ofReal (c * f b - c * f a) = c • ofReal (f b - f a)
--   rw [← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
--   rfl

end StieltjesFunction
