import FCAppendix.Affine.Tail04.TypicalHighPolicy

noncomputable section
namespace FCAppendix.Affine.Tail04.TypicalGuard
open MeasureTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal LocalHighCommon TypicalHighPolicy

def listMinimum {α : Type*} : List α → (α → ℝ) → ℝ
  | [],_ => 1
  | a::as,f => min (f a) (listMinimum as f)

lemma listMinimum_le {α : Type*} (as : List α) (f : α → ℝ) (a : α) (ha : a ∈ as) :
    listMinimum as f ≤ f a := by
  induction as with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with he | ht
    · subst a
      exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih ht)

lemma le_listMinimum {α : Type*} (as : List α) (f : α → ℝ) (a : ℝ)
    (h1 : a ≤ 1) (h : ∀ x ∈ as, a ≤ f x) : a ≤ listMinimum as f := by
  induction as with
  | nil => exact h1
  | cons x xs ih =>
    exact le_min (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma continuous_listMinimum {α P : Type*} [TopologicalSpace P]
    (as : List α) (f : P → α → ℝ) (hf : ∀ a ∈ as, Continuous (fun p => f p a)) :
    Continuous (fun p => listMinimum as (f p)) := by
  induction as with
  | nil => exact continuous_const
  | cons a as ih =>
    exact (hf a (by simp)).min (ih (fun b hb => hf b (by simp [hb])))

def finiteMinimum {α : Type*} [Fintype α] (f : α → ℝ) : ℝ := listMinimum Finset.univ.toList f

lemma finiteMinimum_le {α : Type*} [Fintype α] (f : α → ℝ) (a : α) :
    finiteMinimum f ≤ f a := listMinimum_le _ _ _ (by simp)

lemma le_finiteMinimum {α : Type*} [Fintype α] (f : α → ℝ) (a : ℝ)
    (h1 : a ≤ 1) (h : ∀ x, a ≤ f x) : a ≤ finiteMinimum f :=
  le_listMinimum _ _ _ h1 (fun x _ => h x)

lemma continuous_finiteMinimum {α P : Type*} [Fintype α] [TopologicalSpace P]
    (f : P → α → ℝ) (hf : ∀ a, Continuous (fun p => f p a)) :
    Continuous (fun p => finiteMinimum (f p)) :=
  continuous_listMinimum _ _ (fun a _ => hf a)

def realizationMargin (N H c : ℕ) (ξ B : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ) : ℝ :=
  finiteMinimum (fun z : Marks H =>
    min (multiplier N H c ξ regime O I b z-(1-ξ)*B)
      (1-multiplier N H c ξ regime O I b z))

def partialMargin (N H0 H1 c : ℕ) (ξ R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : ℝ :=
  if regime then
    min (meanMultiplier N H0 c ξ regime O0 I b ν0-Rp)
      (meanMultiplier N H1 c ξ regime O1 I b ν1-Rp)
  else
    min (R-meanMultiplier N H0 c ξ regime O0 I b ν0)
      (R-meanMultiplier N H1 c ξ regime O1 I b ν1)

def margin (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : ℝ :=
  min (min (realizationMargin N H0 c ξ B regime O0 I b)
      (realizationMargin N H1 c ξ B regime O1 I b))
    (partialMargin N H0 H1 c ξ R Rp regime I O0 O1 b ν0 ν1)

def weight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) : ℝ :=
  if Structural N H0 H1 c I O0 O1 then
    min 1 (max 0 (margin N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1 / width))
  else 0

lemma weight_bounds (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    weight N H0 H1 c ξ B R Rp width regime I O0 O1 b ν0 ν1 ∈ Icc (0:ℝ) 1 := by
  unfold weight
  split_ifs
  · exact ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩
  · norm_num

lemma positive_realizationMargin_guard (N H c : ℕ) (ξ B : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (b : Fin N → ℝ)
    (h : 0 < realizationMargin N H c ξ B regime O I b) :
    LocalGuard N H c ξ B regime O I b := by
  intro z
  have hz := h.trans_le (finiteMinimum_le
    (fun z : Marks H => min (multiplier N H c ξ regime O I b z-(1-ξ)*B)
      (1-multiplier N H c ξ regime O I b z)) z)
  have hh := lt_min_iff.mp hz
  constructor <;> linarith

lemma positive_margin_guard (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hs : Structural N H0 H1 c I O0 O1)
    (h : 0 < margin N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1) :
    Guard N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1 := by
  have hh := lt_min_iff.mp h
  have hh' := lt_min_iff.mp hh.1
  refine ⟨hs,positive_realizationMargin_guard _ _ _ _ _ _ _ _ _ hh'.1,
    positive_realizationMargin_guard _ _ _ _ _ _ _ _ _ hh'.2,?_⟩
  cases regime
  · have hp := lt_min_iff.mp hh.2
    constructor <;> linarith
  · have hp := lt_min_iff.mp hh.2
    constructor <;> linarith

theorem guard_of_weight_pos (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (regime : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (hw : 0 < width)
    (h : 0 < weight N H0 H1 c ξ B R Rp width regime I O0 O1 b ν0 ν1) :
    Guard N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1 := by
  have hs : Structural N H0 H1 c I O0 O1 := by
    by_contra hn
    simp [weight,hn] at h
  apply positive_margin_guard _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hs
  by_contra hn
  have hd : margin N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1 / width ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hw.le
  simp [weight,hs,max_eq_left hd] at h

theorem weight_eq_one (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (regime : Bool) (I O0 O1 : Finset (Fin N)) (b : Fin N → ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (hw : 0 < width)
    (hs : Structural N H0 H1 c I O0 O1)
    (hm : width ≤ margin N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1) :
    weight N H0 H1 c ξ B R Rp width regime I O0 O1 b ν0 ν1=1 := by
  have hd : 1 ≤ margin N H0 H1 c ξ B R Rp regime I O0 O1 b ν0 ν1 / width :=
    (le_div_iff₀ hw).mpr (by simpa using hm)
  rw [weight,if_pos hs,min_eq_left (hd.trans (le_max_right _ _))]

abbrev BidBox (N : ℕ) (B : ℝ) := Fin N → Icc (1:ℝ) B
def bids {N : ℕ} {B : ℝ} (b : BidBox N B) : Fin N → ℝ := fun i => (b i).1

lemma continuous_bids {N : ℕ} {B : ℝ} : Continuous (bids : BidBox N B → Fin N → ℝ) :=
  continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)

lemma continuous_reciprocal (N : ℕ) (B : ℝ) (I : Finset (Fin N)) :
    Continuous (fun b : BidBox N B => mixedReciprocalSum I (bids b)) := by
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.div (continuous_subtype_val.comp (continuous_apply i))
    (fun b => ne_of_gt ((by norm_num : (0:ℝ)<1).trans_le (b i).2.1))

lemma continuous_multiplier (N H c : ℕ) (ξ B : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (hI : I.Nonempty) (z : Marks H) :
    Continuous (fun b : BidBox N B => multiplier N H c ξ regime O I (bids b) z) := by
  have hW (b : BidBox N B) : mixedReciprocalSum I (bids b) ≠ 0 :=
    ne_of_gt (mixedReciprocalSum_pos I (bids b) hI
      (fun i _ => (by norm_num : (0:ℝ)<1).trans_le (b i).2.1))
  simp_rw [multiplier_formula]
  exact continuous_const.div (continuous_reciprocal N B I) hW

lemma continuous_meanMultiplier (N H c : ℕ) (ξ B : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (hI : I.Nonempty) (ν : FiniteLaw (Marks H)) :
    Continuous (fun b : BidBox N B => meanMultiplier N H c ξ regime O I (bids b) ν) := by
  unfold meanMultiplier FiniteLaw.expect
  apply continuous_finsetSum
  intro z hz
  exact continuous_const.mul (continuous_multiplier N H c ξ B regime O I hI z)

lemma continuous_realizationMargin (N H c : ℕ) (ξ B : ℝ) (regime : Bool)
    (O I : Finset (Fin N)) (hI : I.Nonempty) :
    Continuous (fun b : BidBox N B => realizationMargin N H c ξ B regime O I (bids b)) := by
  apply continuous_finiteMinimum
  intro z
  exact ((continuous_multiplier N H c ξ B regime O I hI z).sub continuous_const).min
    (continuous_const.sub (continuous_multiplier N H c ξ B regime O I hI z))

lemma continuous_partialMargin (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (hI : I.Nonempty)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Continuous (fun b : BidBox N B => partialMargin N H0 H1 c ξ R Rp regime I O0 O1 (bids b) ν0 ν1) := by
  cases regime
  · exact (continuous_const.sub (continuous_meanMultiplier N H0 c ξ B false O0 I hI ν0)).min
      (continuous_const.sub (continuous_meanMultiplier N H1 c ξ B false O1 I hI ν1))
  · exact ((continuous_meanMultiplier N H0 c ξ B true O0 I hI ν0).sub continuous_const).min
      ((continuous_meanMultiplier N H1 c ξ B true O1 I hI ν1).sub continuous_const)

lemma continuous_margin (N H0 H1 c : ℕ) (ξ B R Rp : ℝ) (regime : Bool)
    (I O0 O1 : Finset (Fin N)) (hI : I.Nonempty)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Continuous (fun b : BidBox N B => margin N H0 H1 c ξ B R Rp regime I O0 O1 (bids b) ν0 ν1) :=
  ((continuous_realizationMargin N H0 c ξ B regime O0 I hI).min
    (continuous_realizationMargin N H1 c ξ B regime O1 I hI)).min
      (continuous_partialMargin N H0 H1 c ξ B R Rp regime I O0 O1 hI ν0 ν1)

theorem continuous_weight (N H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (regime : Bool) (I O0 O1 : Finset (Fin N))
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Continuous (fun b : BidBox N B => weight N H0 H1 c ξ B R Rp width
      regime I O0 O1 (bids b) ν0 ν1) := by
  by_cases hs : Structural N H0 H1 c I O0 O1
  · simp only [weight,if_pos hs]
    exact continuous_const.min (continuous_const.max
      ((continuous_margin N H0 H1 c ξ B R Rp regime I O0 O1 hs.2.2.2.2.2 ν0 ν1).div_const width))
  · simp only [weight,if_neg hs]
    exact continuous_const

end FCAppendix.Affine.Tail04.TypicalGuard
