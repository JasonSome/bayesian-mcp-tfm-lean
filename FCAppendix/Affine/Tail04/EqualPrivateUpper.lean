import FCAppendix.Affine.Tail04.EqualPrivateSignal
import FCAppendix.Affine.Tail04.TopSelection
import FCAppendix.Existence.R01PayOncePhysicalTypes

set_option maxHeartbeats 600000
noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateUpper
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

abbrev Row (H : ℕ) (R Rp Rm : ℝ) := Fin H → (Ici Rm ⊕ Icc R Rp)

def signalEntry {R Rp Rm : ℝ} : Ici Rm ⊕ Icc R Rp → Unit ⊕ Icc R Rp
  | .inl _ => .inl ()
  | .inr b => .inr b

def numericalEntry {R Rp Rm : ℝ} : Ici Rm ⊕ Icc R Rp → ℝ
  | .inl b => b.1
  | .inr b => b.1

lemma continuous_signalEntry {R Rp Rm : ℝ} : Continuous (@signalEntry R Rp Rm) :=
  continuous_sum_dom.mpr ⟨continuous_const,continuous_inr⟩

lemma continuous_numericalEntry {R Rp Rm : ℝ} : Continuous (@numericalEntry R Rp Rm) :=
  continuous_sum_dom.mpr ⟨continuous_subtype_val,continuous_subtype_val⟩

def signal {H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) : Signal H R Rp :=
  fun j => signalEntry (row j)

lemma continuous_signal {H : ℕ} {R Rp Rm : ℝ} :
    Continuous (signal : Row H R Rp Rm → Signal H R Rp) :=
  continuous_pi fun j => continuous_signalEntry.comp (continuous_apply j)

def upperPool (N : ℕ) {H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) :
    Finset (Target N H) :=
  (Finset.univ.filter fun j => isUpper (signal row j)=true).image Sum.inr

@[simp] lemma inl_not_mem_upperPool {N H : ℕ} {R Rp Rm : ℝ}
    (row : Row H R Rp Rm) (i : Fin N) : Sum.inl i ∉ upperPool N row := by
  simp [upperPool]

@[simp] lemma inr_mem_upperPool {N H : ℕ} {R Rp Rm : ℝ}
    (row : Row H R Rp Rm) (j : Fin H) :
    Sum.inr j ∈ upperPool N row ↔ isUpper (signal row j)=true := by
  simp [upperPool]

lemma upperPool_card {N H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) :
    (upperPool N row).card=upperCount (marks (signal row)) := by
  rw [upperPool,Finset.card_image_of_injective _ Sum.inr_injective]
  rfl

lemma continuous_upperPool {N H : ℕ} {R Rp Rm : ℝ} :
    Continuous (upperPool N : Row H R Rp Rm → Finset (Target N H)) := by
  let f : Marks H → Finset (Target N H) := fun z =>
    (Finset.univ.filter fun j => z j=true).image Sum.inr
  exact (continuous_of_discreteTopology (f := f)).comp
    (continuous_marks.comp continuous_signal)

def receipt {N H : ℕ} {R Rp Rm : ℝ} (b q : Fin N → ℝ) (ξ : ℝ)
    (row : Row H R Rp Rm) : Target N H → ℝ
  | .inl i => b i*(1-ξ*q i)
  | .inr j => numericalEntry (row j)

lemma continuous_receipt {N H : ℕ} {R Rp Rm : ℝ} (ξ : ℝ) (i : Target N H) :
    Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) × Row H R Rp Rm =>
      receipt z.1 z.2.1 ξ z.2.2 i) := by
  cases i with
  | inl i =>
    exact ((continuous_apply i).comp continuous_fst).mul
      (continuous_const.sub (continuous_const.mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd))))
  | inr j =>
    exact continuous_numericalEntry.comp
      ((continuous_apply j).comp (continuous_snd.comp continuous_snd))

lemma receipt_upper_ge {N H : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm)
    (i : Target N H) (hi : i ∈ upperPool N row) : Rm ≤ receipt b q ξ row i := by
  cases i with
  | inl i => exact (inl_not_mem_upperPool row i hi).elim
  | inr j =>
    have hh := (inr_mem_upperPool row j).mp hi
    cases hrow : row j with
    | inl v => simpa only [receipt,numericalEntry,hrow,Set.mem_Ici] using v.2
    | inr v => simp [signal,signalEntry,hrow,isUpper] at hh

lemma receipt_nonupper_le {N H : ℕ} {R Rp Rm U : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm)
    (hξ : 0 ≤ ξ) (hb : ∀ i, b i ∈ Icc (0:ℝ) U) (hq : ∀ i, 0 ≤ q i)
    (hRp : Rp ≤ U) (j : Target N H) (hj : j ∉ upperPool N row) :
    receipt b q ξ row j ≤ U := by
  cases j with
  | inl i =>
    apply (mul_le_of_le_one_right (hb i).1 ?_).trans (hb i).2
    nlinarith [mul_nonneg hξ (hq i)]
  | inr j =>
    cases hrow : row j with
    | inl v => exact (hj (by simp [signal,signalEntry,hrow,isUpper])).elim
    | inr v => simpa only [receipt,numericalEntry,hrow] using v.2.2.trans hRp

lemma receipt_nonneg {N H : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : ∀ i, 0 ≤ b i)
    (hq : ∀ i, q i ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRm : 0 ≤ Rm)
    (i : Target N H) : 0 ≤ receipt b q ξ row i := by
  cases i with
  | inl i =>
    apply mul_nonneg (hb i)
    have hh := mul_le_mul hξ.2 (hq i).2 (hq i).1 (by norm_num : (0:ℝ) ≤ 1)
    nlinarith
  | inr j =>
    cases hrow : row j with
    | inl v => simpa only [receipt,numericalEntry,hrow] using hRm.trans v.2
    | inr v => simpa only [receipt,numericalEntry,hrow] using hR.trans v.2.1

lemma residual_receipt_eq {N H : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) :
    itemReceipt b q ξ (signal row) =
      fun i => if i ∈ upperPool N row then 0 else receipt b q ξ row i := by
  funext i
  cases i with
  | inl i => simp [itemReceipt,receipt]
  | inr j =>
    cases hrow : row j with
    | inl v => simp [itemReceipt,signal,signalEntry,hrow,isUpper,partialBid]
    | inr v => simp [itemReceipt,receipt,signal,signalEntry,hrow,isUpper,partialBid,numericalEntry]

def upperSelection {N H : ℕ} {R Rp Rm : ℝ} (c : ℕ)
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) : Finset (Target N H) :=
  AtypicalUnequal.topSelection (upperPool N row) c (receipt b q ξ row)

def restore {N H c : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) (a : Action N H c) :
    Finset (Target N H) := upperSelection c b q ξ row ∪ selected (signal row) a

lemma upper_residual_disjoint {N H c : ℕ} {R Rp Rm : ℝ}
    (row : Row H R Rp Rm) (a : Action N H c) :
    Disjoint (upperPool N row) (selected (signal row) a) := by
  apply Finset.disjoint_left.mpr
  intro i hi hs
  cases i with
  | inl i => exact inl_not_mem_upperPool row i hi
  | inr j =>
    have hu := (inr_mem_upperPool row j).mp hi
    have hp := (selected_feasible (signal row) a).2 j hs
    have he : (true : Bool)=false := hu.symm.trans hp
    cases he

theorem restore_capacity {N H c : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) (a : Action N H c) :
    (restore b q ξ row a).card ≤ c := by
  have hs := AtypicalUnequal.topSelection_feasible (upperPool N row) c (receipt b q ξ row)
  have hcard := Finset.card_le_card hs.2
  have hr := (selected_feasible (signal row) a).1
  rw [upperPool_card] at hcard
  have hc : (upperSelection c b q ξ row).card ≤ c := hs.1
  have hu : (upperSelection c b q ξ row).card ≤ upperCount (marks (signal row)) := hcard
  unfold restore
  exact (Finset.card_union_le _ _).trans (by omega)

lemma measurable_restore {N H c : ℕ} {R Rp Rm : ℝ} (ξ : ℝ) :
    Measurable (fun z : ((Fin N → ℝ) × (Fin N → ℝ) × Row H R Rp Rm) × Action N H c =>
      restore z.1.1 z.1.2.1 ξ z.1.2.2 z.2) := by
  have hu : Measurable (fun z :
      ((Fin N → ℝ) × (Fin N → ℝ) × Row H R Rp Rm) × Action N H c =>
      upperSelection c z.1.1 z.1.2.1 ξ z.1.2.2) :=
    by
      simpa only [upperSelection,Function.comp_def] using
        AtypicalUnequal.measurable_topSelection c
          (fun z : ((Fin N → ℝ) × (Fin N → ℝ) × Row H R Rp Rm) × Action N H c =>
            upperPool N z.1.2.2)
          (fun z => receipt z.1.1 z.1.2.1 ξ z.1.2.2)
          (by
            simpa only [Function.comp_def] using
              ((continuous_upperPool (N := N) (H := H) (R := R) (Rp := Rp) (Rm := Rm)).measurable.comp
                (measurable_snd.comp (measurable_snd.comp measurable_fst))))
          (fun i => by
            simpa only [Function.comp_def] using
              ((continuous_receipt (N := N) (H := H) (R := R) (Rp := Rp) (Rm := Rm) ξ i).measurable.comp
                measurable_fst))
  have hl : Measurable (fun z :
      ((Fin N → ℝ) × (Fin N → ℝ) × Row H R Rp Rm) × Action N H c =>
      selected (signal z.1.2.2) z.2) := continuous_selected.measurable.comp
    ((continuous_signal.measurable.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  exact (measurable_of_countable (fun z : Finset (Target N H) × Finset (Target N H) =>
    z.1 ∪ z.2)).comp (hu.prodMk hl)

theorem restore_optimal {N H c : ℕ} {R Rp Rm U : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) (a : Action N H c)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) U)
    (hq : ∀ i, q i ∈ Icc (0:ℝ) 1) (hR : 0 ≤ R) (hRp : Rp ≤ U)
    (hU : U < Rm) (hRm : 0 < Rm)
    (hbest : ∀ S, Feasible N H c (marks (signal row)) S →
      revenue b q ξ (signal row) S ≤ revenue b q ξ (signal row) (selected (signal row) a)) :
    Finite.Optimal c (receipt b q ξ row) (restore b q ξ row a) := by
  have hpos := receipt_nonneg b q ξ row hξ (fun i => (hb i).1) hq hR hRm.le
  have hupper : ∀ i ∈ upperPool N row, 0 < receipt b q ξ row i :=
    fun i hi => hRm.trans_le (receipt_upper_ge b q ξ row i hi)
  have hpriority : ∀ i ∈ upperPool N row, ∀ j ∉ upperPool N row,
      receipt b q ξ row j ≤ receipt b q ξ row i := by
    intro i hi j hj
    exact (receipt_nonupper_le b q ξ row hξ.1 hb (fun k => (hq k).1) hRp j hj).trans
      (hU.le.trans (receipt_upper_ge b q ξ row i hi))
  by_cases hfit : (upperPool N row).card ≤ c
  · have he : upperSelection c b q ξ row = upperPool N row := by
      apply Finset.eq_of_subset_of_card_le
        (AtypicalUnequal.topSelection_feasible _ _ _).2
      rw [AtypicalUnequal.topSelection_card _ _ _ hupper,min_eq_right hfit]
    have hr := finiteOptimal_of_residualOptimal b q ξ (signal row) (selected (signal row) a)
      (selected_feasible _ _) hbest
    rw [residual_receipt_eq,← upperPool_card (N := N) row] at hr
    rw [restore,he]
    exact Hybrid.priority_union_optimal c _ _ _ hfit (upper_residual_disjoint row a)
      hpos hpriority hr
  · have hc : c ≤ (upperPool N row).card := le_of_not_ge hfit
    have hz : selected (signal row) a = ∅ := by
      have hh := (selected_feasible (signal row) a).1
      rw [← upperPool_card (N := N) row] at hh
      exact Finset.card_eq_zero.mp (by omega)
    rw [restore,hz,Finset.union_empty]
    exact AtypicalUnequal.topSelection_receipt_optimal (upperPool N row) c
      (receipt b q ξ row) (receipt b q ξ row) hc hupper hpos
      (fun i hi => rfl) hpriority

theorem restore_upper_iff_strict_rank {N H c : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) (a : Action N H c)
    (hRm : 0 < Rm) (j : Fin H) (hj : Sum.inr j ∈ upperPool N row)
    (hno : ∀ i ∈ upperPool N row, i ≠ Sum.inr j →
      receipt b q ξ row i ≠ numericalEntry (row j)) :
    Sum.inr j ∈ restore b q ξ row a ↔
      ((upperPool N row).filter fun i => numericalEntry (row j) < receipt b q ξ row i).card < c := by
  have hs : Sum.inr j ∉ selected (signal row) a :=
    fun hs => (Finset.disjoint_left.mp (upper_residual_disjoint row a)) hj hs
  rw [restore,Finset.mem_union,or_iff_left hs]
  exact AtypicalUnequal.topSelection_iff_strict_rank (upperPool N row) c (receipt b q ξ row)
    (fun i hi => hRm.le.trans (receipt_upper_ge b q ξ row i hi)) (Sum.inr j) hj
    (hRm.trans_le (receipt_upper_ge b q ξ row _ hj)) hno

theorem exists_equal_upper_sampler (N H c : ℕ) (R Rp Rm ξ lo hi : ℝ)
    (hξ : ξ ∈ Icc (0:ℝ) 1) (hlo : 0 < lo) (hR : 0 ≤ R)
    (hRp : Rp ≤ hi) (hhi : hi < Rm) (hRm : 0 < Rm) :
    ∃ g : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) →
        unitInterval → Finset (Target N H),
      Measurable (Function.uncurry g) ∧
      (∀ p row,
        volume.map (g (p,row)) =
          (residualKernel N H c R Rp ξ lo hi (p,signal row)).map
            (fun a => restore (EqualPrivateMeasurable.bids p)
              (policyMean N H c R Rp ξ lo hi p) ξ row a)) ∧
      (∀ p row u, (g (p,row) u).card ≤ c) ∧
      (∀ p row u, Finite.Optimal c
        (receipt (EqualPrivateMeasurable.bids p) (policyMean N H c R Rp ξ lo hi p) ξ row)
        (g (p,row) u)) ∧
      (∀ p row u j, Sum.inr j ∈ upperPool N row →
        (∀ i ∈ upperPool N row, i ≠ Sum.inr j →
          receipt (EqualPrivateMeasurable.bids p) (policyMean N H c R Rp ξ lo hi p) ξ row i ≠
            numericalEntry (row j)) →
        (Sum.inr j ∈ g (p,row) u ↔
          ((upperPool N row).filter fun i => numericalEntry (row j) <
            receipt (EqualPrivateMeasurable.bids p) (policyMean N H c R Rp ξ lo hi p) ξ row i).card < c)) := by
  obtain ⟨f,hf,hlaw,_hselected,_hfeas,_hcap,hbest⟩ :=
    exists_jointly_borel_residual_policy N H c R Rp ξ lo hi
  let g : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) →
      unitInterval → Finset (Target N H) := fun z u =>
    restore (EqualPrivateMeasurable.bids z.1) (policyMean N H c R Rp ξ lo hi z.1) ξ
      z.2 (f (z.1,signal z.2) u)
  have hparam : Measurable
      (fun z : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) × unitInterval => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hrow : Measurable
      (fun z : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) × unitInterval => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hf' : Measurable
      (fun z : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) × unitInterval =>
        f (z.1.1,signal z.1.2) z.2) :=
    by simpa only [Function.comp_def,Function.uncurry] using
      hf.comp ((hparam.prodMk (continuous_signal.measurable.comp hrow)).prodMk measurable_snd)
  have hg : Measurable (Function.uncurry g) := by
    change Measurable (fun z : (PolicyParameters N H R Rp lo hi × Row H R Rp Rm) × unitInterval =>
      restore (EqualPrivateMeasurable.bids z.1.1) (policyMean N H c R Rp ξ lo hi z.1.1) ξ
        z.1.2 (f (z.1.1,signal z.1.2) z.2))
    simpa only [Function.comp_def,policyMean] using (measurable_restore ξ).comp
      (((EqualPrivateMeasurable.continuous_bids.measurable.comp hparam).prodMk
        (((EqualPrivateMeasurable.measurable_q (activeIndicator N H c R Rp)
          (privateReceipt N H c R Rp) ξ lo hi).comp hparam).prodMk hrow)).prodMk hf')
  refine ⟨g,hg,?_,fun p row u => restore_capacity _ _ _ _ _,?_,?_⟩
  · intro p row
    have hr : Measurable (fun a : Action N H c => restore (EqualPrivateMeasurable.bids p)
        (policyMean N H c R Rp ξ lo hi p) ξ row a) :=
      by
        simpa only [Function.comp_def] using ((measurable_restore ξ).comp
          (show Measurable (fun a : Action N H c =>
            ((EqualPrivateMeasurable.bids p, policyMean N H c R Rp ξ lo hi p, row), a)) from
            measurable_const.prodMk measurable_id))
    have hfpr : Measurable (f (p,signal row)) := by
      simpa only [Function.comp_def,Function.uncurry,id_eq] using
        hf.comp (measurable_const.prodMk measurable_id)
    rw [← hlaw p (signal row),Measure.map_map hr hfpr]
    rfl
  · intro p row u
    apply restore_optimal _ _ ξ row _ hξ
      (fun i => ⟨(hlo.trans_le (p.1 i).2.1).le,(p.1 i).2.2⟩)
      (policyMean_bounds N H c R Rp ξ lo hi p) hR hRp hhi hRm
    exact hbest p (signal row) u
  · intro p row u j hj hno
    exact restore_upper_iff_strict_rank _ _ ξ row _ hRm j hj hno

lemma restore_active_iff {N H c : ℕ} {R Rp Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R Rp Rm) (a : Action N H c) (i : Fin N) :
    Sum.inl i ∈ restore b q ξ row a ↔ Sum.inl i ∈ selected (signal row) a := by
  have hi : Sum.inl i ∉ upperSelection c b q ξ row := fun hi =>
    inl_not_mem_upperPool row i ((AtypicalUnequal.topSelection_feasible _ _ _).2 hi)
  simp only [restore,Finset.mem_union,hi,false_or]

def rowKernel {N H c : ℕ} {R Rp Rm ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi) : Kernel (Row H R Rp Rm) (Action N H c) :=
  (EqualPrivateMeasurable.fiber (residualKernel N H c R Rp ξ lo hi) p).comap
    signal continuous_signal.measurable

instance {N H c : ℕ} {R Rp Rm ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi) :
    IsMarkovKernel (rowKernel (c := c) (Rm := Rm) (ξ := ξ) p) := by
  unfold rowKernel
  infer_instance

theorem original_row_jointLaw {N H c : ℕ} {R Rp Rm ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi)
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal = WeakProbability.toMeasure p.2) :
    (θ ⊗ₘ rowKernel (c := c) (ξ := ξ) p).map
      (fun z : Row H R Rp Rm × Action N H c => (signal z.1,z.2)) =
      WeakProbability.toMeasure (policyLaw N H c R Rp ξ lo hi p) := by
  have hh := Existence.PayOnceBounded.map_compProd_comap θ signal continuous_signal.measurable
    (EqualPrivateMeasurable.fiber (residualKernel N H c R Rp ξ lo hi) p)
  rw [hθ,residualKernel_jointLaw N H c R Rp ξ lo hi p] at hh
  exact hh

theorem original_row_active_mean {N H c : ℕ} {R Rp Rm ξ lo hi : ℝ}
    (p : PolicyParameters N H R Rp lo hi)
    (θ : Measure (Row H R Rp Rm)) [IsProbabilityMeasure θ]
    (hθ : θ.map signal = WeakProbability.toMeasure p.2) (i : Fin N) :
    (∫ z : Row H R Rp Rm × Action N H c,
      (if Sum.inl i ∈ restore (EqualPrivateMeasurable.bids p)
        (policyMean N H c R Rp ξ lo hi p) ξ z.1 z.2 then (1:ℝ) else 0)
      ∂(θ ⊗ₘ rowKernel (c := c) (ξ := ξ) p)) = policyMean N H c R Rp ξ lo hi p i := by
  have hm : Measurable (fun z : Row H R Rp Rm × Action N H c => (signal z.1,z.2)) :=
    (continuous_signal.measurable.comp measurable_fst).prodMk measurable_snd
  change _ = ∫ z, activeIndicator N H c R Rp i z
    ∂WeakProbability.toMeasure (policyLaw N H c R Rp ξ lo hi p)
  rw [← original_row_jointLaw p θ hθ,
    integral_map hm.aemeasurable (activeIndicator N H c R Rp i).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    simp only [activeIndicator,ContinuousMap.coe_mk,restore_active_iff]

end FCAppendix.Affine.Tail04.EqualPrivateUpper
