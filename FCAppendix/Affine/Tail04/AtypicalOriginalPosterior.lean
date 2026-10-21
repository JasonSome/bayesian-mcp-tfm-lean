import FCAppendix.Affine.Tail04.AllCountAtypical
import FCAppendix.Existence.R01PayOnceRowIntegration

set_option maxHeartbeats 500000

noncomputable section
namespace FCAppendix.Affine.Tail04.AtypicalOriginalPosterior
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon AtypicalUnequal AllCountAtypical

local instance (ι : Type*) : TopologicalSpace (Finset ι) := ⊥
local instance (ι : Type*) : DiscreteTopology (Finset ι) := ⟨rfl⟩
local instance (ι : Type*) : MeasurableSpace (Finset ι) := ⊤
local instance (ι : Type*) : BorelSpace (Finset ι) := ⟨borel_eq_top_of_discrete.symm⟩

def mean (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 j) R Rp Rm))
    (i : Fin N) : ℝ :=
  ∫ row, if Sum.inl i ∈ select N H0 H1 c ξ b j row then (1:ℝ) else 0 ∂θ

lemma measurable_indicator (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (i : Fin N) :
    Measurable (fun row : Row (ownCount H0 H1 j) R Rp Rm =>
      if Sum.inl i ∈ select N H0 H1 c ξ b j row then (1:ℝ) else 0) := by
  have hm : Measurable (fun row : Row (ownCount H0 H1 j) R Rp Rm => (b,row)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using (measurable_of_countable (fun S : Finset (Target N (ownCount H0 H1 j)) =>
    if Sum.inl i ∈ S then (1:ℝ) else 0)).comp
      ((measurable_select N H0 H1 c ξ j).comp hm)

lemma integrable_indicator (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 j) R Rp Rm))
    [IsProbabilityMeasure θ] (i : Fin N) :
    Integrable (fun row => if Sum.inl i ∈ select N H0 H1 c ξ b j row then (1:ℝ) else 0) θ :=
  Integrable.of_bound (measurable_indicator N H0 H1 c ξ b j i).aestronglyMeasurable 1
    (ae_of_all _ fun row => by split_ifs <;> norm_num)

theorem mean_bounds (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 j) R Rp Rm))
    [IsProbabilityMeasure θ] (i : Fin N) : mean N H0 H1 c ξ b j θ i ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun row => by split_ifs <;> norm_num)
  · calc
      mean N H0 H1 c ξ b j θ i ≤ ∫ _row, (1:ℝ) ∂θ :=
        integral_mono_ae (integrable_indicator N H0 H1 c ξ b j θ i) (integrable_const 1)
          (ae_of_all _ fun row => by dsimp only; split_ifs <;> norm_num)
      _ = 1 := by simp

lemma mean_eq_const_of_pointwise (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 j) R Rp Rm))
    [IsProbabilityMeasure θ] (i : Fin N) (a : ℝ)
    (h : ∀ row : Row (ownCount H0 H1 j) R Rp Rm, (if Sum.inl i ∈ select N H0 H1 c ξ b j row then (1:ℝ) else 0)=a) :
    mean N H0 H1 c ξ b j θ i=a := by
  unfold mean
  calc
    _ = ∫ _row, a ∂θ := integral_congr_ae (ae_of_all _ h)
    _ = a := by simp

def rowMarks {H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) : Marks H := marks (signal row)

lemma continuous_rowMarks {H : ℕ} {R Rp Rm : ℝ} :
    Continuous (rowMarks : Row H R Rp Rm → Marks H) := continuous_marks.comp continuous_signal

def markLaw {H : ℕ} {R Rp Rm : ℝ} (θ : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ] : FiniteLaw (Marks H) :=
  FiniteLaw.ofMeasure θ rowMarks continuous_rowMarks.measurable

lemma markLaw_expect {H : ℕ} {R Rp Rm : ℝ} (θ : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ] (f : Marks H → ℝ) :
    (markLaw θ).expect f = ∫ row, f (rowMarks row) ∂θ :=
  FiniteLaw.expect_ofMeasure θ rowMarks continuous_rowMarks.measurable f

lemma markLaw_eq_of_pushforward {H : ℕ} {R Rp Rm : ℝ}
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ] (ν : FiniteLaw (Marks H))
    (hν : θ.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν) :
    markLaw θ=ν :=
  FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure θ rowMarks continuous_rowMarks.measurable ν hν

def anyUpper {H : ℕ} (z : Marks H) : Prop := ∃ k, z k=true

lemma anyUpper_bound_of_coordinate {H : ℕ} (ν : FiniteLaw (Marks H)) (π : ℝ)
    (hmark : ∀ k, ν.prob (fun z => z k=true) ≤ π) :
    ν.prob anyUpper ≤ (H:ℝ)*π := by
  calc
    _ ≤ ∑ k : Fin H, ν.prob (fun z => z k=true) :=
      AtypicalUnequal.prob_exists_le_sum ν (fun k z => z k=true)
    _ ≤ ∑ _k : Fin H, π := Finset.sum_le_sum (fun k _ => hmark k)
    _ = _ := by simp

lemma upperPool_eq_empty_of_noUpper {N H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm)
    (h : ∀ k, rowMarks row k=false) : upperPool N row=∅ := by
  ext i
  cases i with
  | inl i => simp
  | inr k =>
    have hk : isUpper (signal row k) = false := h k
    simp only [upperPool, Finset.mem_image, Sum.inr.injEq, exists_eq_right,
      Finset.mem_filter, Finset.mem_univ, true_and, hk, Bool.false_eq_true,
      Finset.notMem_empty]

theorem no_upper_accepts_owner (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (row : Row (ownCount H0 H1 j) R Rp Rm)
    (hn : ¬ EitherSlack N H0 H1 c) (hover : ¬ N+H0+H1 ≤ 2*c)
    (hb : ∀ i, 1 ≤ b i) (hRp : Rp < 1)
    (hrow : ∀ k, rowMarks row k=false) :
    activeLift (ownCount H0 H1 j) (owners N H0 c b j) ⊆ select N H0 H1 c ξ b j row := by
  have hp := owners_partition N H0 H1 c b hn (by omega)
    (fun i => (by norm_num : (0:ℝ)<1).trans_le (hb i)) j
  have hempty := upperPool_eq_empty_of_noUpper (N := N) row hrow
  simp only [select,if_neg hn,if_neg hover]
  apply topSelection_contains_priority _ _ c (numericalBid b row)
  · exact Finset.subset_union_left
  · simpa using hp.2.2.1
  · intro i hi
    cases i with
    | inl i => exact (by norm_num : (0:ℝ)<1).trans_le (hb i)
    | inr k => simp at hi
  · intro i hi k hk hkO
    cases i with
    | inr i => simp at hi
    | inl i =>
      have hkP : k ∈ if N ≤ 2*c then privateAll N (ownCount H0 H1 j) else upperPool N row :=
        (Finset.mem_union.mp hk).resolve_left hkO
      by_cases hN : N ≤ 2*c
      · rw [if_pos hN] at hkP
        exact (private_nonupper_le b row k hkP (by simp [hempty])).trans_lt
          (hRp.trans_le (hb i))
      · simp [hN,hempty] at hkP

theorem mean_owner_lower (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 j) R Rp Rm))
    [IsProbabilityMeasure θ] (π : ℝ)
    (hn : ¬ EitherSlack N H0 H1 c) (hover : ¬ N+H0+H1 ≤ 2*c)
    (hb : ∀ i, 1 ≤ b i) (hRp : Rp < 1)
    (hany : (markLaw θ).prob anyUpper ≤ (ownCount H0 H1 j:ℝ)*π)
    (i : Fin N) (hi : i ∈ owners N H0 c b j) :
    1-(ownCount H0 H1 j:ℝ)*π ≤ mean N H0 H1 c ξ b j θ i := by
  let E : Marks (ownCount H0 H1 j) → Prop := fun z => ∀ k, z k=false
  have hprob : 1-(ownCount H0 H1 j:ℝ)*π ≤ (markLaw θ).prob E := by
    have hE : E = fun z => ¬ anyUpper z := by
      funext z
      apply propext
      simp only [E,anyUpper,not_exists]
      constructor
      · intro hz k hk
        simp [hz k] at hk
      · intro hz k
        cases hk : z k
        · rfl
        · exact (hz k hk).elim
    rw [hE,FiniteLaw.prob_compl]
    linarith
  apply hprob.trans
  rw [FiniteLaw.prob_eq_expect,markLaw_expect]
  have hE : Measurable (fun row : Row (ownCount H0 H1 j) R Rp Rm =>
      if E (rowMarks row) then (1:ℝ) else 0) :=
    (measurable_of_countable (fun z => if E z then (1:ℝ) else 0)).comp
      continuous_rowMarks.measurable
  apply integral_mono_ae
    (Integrable.of_bound hE.aestronglyMeasurable 1 (ae_of_all _ fun row => by split_ifs <;> norm_num))
    (integrable_indicator N H0 H1 c ξ b j θ i)
  exact ae_of_all _ fun row => by
    by_cases hr : E (rowMarks row)
    · have ha := no_upper_accepts_owner N H0 H1 c ξ b j row hn hover hb hRp hr
      have hi' := ha (show Sum.inl i ∈ activeLift (ownCount H0 H1 j) (owners N H0 c b j) from by simpa using hi)
      simp [hr,hi']
    · simp only [hr, if_false]
      split_ifs <;> norm_num

theorem mean_other_owner_zero (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 (!j)) R Rp Rm))
    [IsProbabilityMeasure θ]
    (hn : ¬ EitherSlack N H0 H1 c) (hover : ¬ N+H0+H1 ≤ 2*c)
    (hb : ∀ i, 0 < b i) (i : Fin N) (hi : i ∈ owners N H0 c b j) :
    mean N H0 H1 c ξ b (!j) θ i=0 := by
  have hp := owners_partition N H0 H1 c b hn (by omega) hb j
  apply mean_eq_const_of_pointwise N H0 H1 c ξ b (!j) θ i 0
  intro row
  have hnot : Sum.inl i ∉ select N H0 H1 c ξ b (!j) row := by
    intro his
    simp only [select,if_neg hn,if_neg hover] at his
    have hw := (topSelection_feasible (whitelist N H0 H1 c b (!j) row) c
      (numericalBid b row)).2 his
    have ho : i ∈ owners N H0 c b (!j) := by
      unfold whitelist at hw
      split_ifs at hw with hN <;> simpa using hw
    exact (Finset.disjoint_left.mp hp.1) hi ho
  simp [hnot]

theorem actual_opponent_bounds (N H0 H1 c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Bool) (θ : Measure (Row (ownCount H0 H1 (!j)) R Rp Rm))
    [IsProbabilityMeasure θ] (π : ℝ) (hb : ∀ i, 1 ≤ b i) (hRp : Rp < 1)
    (hany : (markLaw θ).prob anyUpper ≤ (otherCount H0 H1 j:ℝ)*π) :
    OpponentBounds N H0 H1 c ξ b (mean N H0 H1 c ξ b (!j) θ) j
      ((otherCount H0 H1 j:ℝ)*π) := by
  unfold OpponentBounds
  split_ifs with hsl hfit
  · intro hown i
    have hother : N+ownCount H0 H1 (!j) < c := by
      have hs := (eitherSlack_iff N H0 H1 c).mp hsl
      cases j <;> simp only [ownCount,Bool.not_false,Bool.not_true,Bool.false_eq_true,
        ite_false,ite_true] at * <;> omega
    apply mean_eq_const_of_pointwise N H0 H1 c ξ b (!j) θ i 1
    intro row
    simp [select,hsl,hother]
  · intro i
    apply mean_eq_const_of_pointwise N H0 H1 c ξ b (!j) θ i
      (if i ∈ fittingActive N H0 H1 c ξ b (!j) then 1 else 0)
    intro row
    simp [select,hsl,hfit]
  · constructor
    · intro i hi
      exact mean_other_owner_zero N H0 H1 c ξ b j θ hsl hfit
        (fun i => (by norm_num : (0:ℝ)<1).trans_le (hb i)) i hi
    · intro i hi
      exact mean_owner_lower N H0 H1 c ξ b (!j) θ π hsl hfit hb hRp hany i hi

theorem actual_optimal (N H0 H1 c : ℕ) {R Rp Rm B ξ : ℝ}
    (b : Fin N → ℝ) (j : Bool)
    (θ : Measure (Row (ownCount H0 H1 (!j)) R Rp Rm)) [IsProbabilityMeasure θ]
    (π : ℝ) (hπ : 0 ≤ π) (hξ : ξ ∈ Icc (0:ℝ) 1)
    (hb : ∀ i, b i ∈ Icc (1:ℝ) B) (hB : 1 ≤ B)
    (hR : 0 < R) (hRRp : R ≤ Rp) (hRp : Rp < 1) (hBRm : B < Rm)
    (hrare : (1-ξ)*B+ξ*B*((otherCount H0 H1 j:ℝ)*π) ≤ R)
    (hfirst : (1-ξ)*B < 1)
    (hany : (markLaw θ).prob anyUpper ≤ (otherCount H0 H1 j:ℝ)*π) :
    ∀ row : Row (ownCount H0 H1 j) R Rp Rm,
      Finite.Optimal c (receipt b (mean N H0 H1 c ξ b (!j) θ) ξ row)
        (select N H0 H1 c ξ b j row) := by
  intro row
  exact AllCountAtypical.optimal N H0 H1 c b (mean N H0 H1 c ξ b (!j) θ) j row
    ((otherCount H0 H1 j:ℝ)*π) hξ hb hB
    (mean_bounds N H0 H1 c ξ b (!j) θ)
    hR hRRp hRp hBRm (mul_nonneg (by positivity) hπ) hrare hfirst
    (actual_opponent_bounds N H0 H1 c ξ b j θ π (fun i => (hb i).1) hRp hany)

end FCAppendix.Affine.Tail04.AtypicalOriginalPosterior
