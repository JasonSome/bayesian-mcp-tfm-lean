import FCAppendix.Affine.Uniform06.SharpPureSelector
import FCAppendix.Affine.Uniform06.SourcePivotalRates
import FCAppendix.Affine.Uniform06.ReceiptGap

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpPureIntervals

open MeasureTheory Set Filter LowBody LiteralExperiment
open PureRankSelector PureDuplicateIntervals PureRankCounts PurePivotalSource
open PureUnionUpper SharpPureSelector PivotalCrossing PureRankProbability PureDuplicateRare
open FCAppendix.Affine.Uniform07
open scoped BigOperators

variable {N : ℕ}

theorem right_selected_iff_rank_on_left_full
    (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b)
    (hleft : c ≤ classCount 2 ω) :
    (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).2 ↔
      PiBinomial.count (higherRightAtSet b) Finset.univ ω< c := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hzero : T.residual₀=0 := by
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=0
    omega
  have hopt : Finite.Optimal T.residual₁ (rowBids b ω) (T.selection κ (rowBids b ω)).2 := by
    simpa only [T.selection_empty_left κ (rowBids b ω) hzero,Finset.notMem_empty,if_false] using
      right_revenue_optimal T κ (rowBids b ω) (rowBids_outside c b ω)
  constructor
  · exact right_selected_on_left_full_implies_rank c κ hb.le ω hleft
  · intro hcount
    apply Finite.included_of_few_competitors T.residual₁ (rowBids b ω) _ hopt 0
      (by simpa only [rowBids,Fin.cons_zero] using hb)
    have he : Finset.univ.filter (fun j : Fin (N+1) => j≠0 ∧ rowBids b ω 0 ≤ rowBids b ω j)=
        Finset.univ.filter (fun j => rowBids b ω 0 < rowBids b ω j) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hj,hb'⟩
        exact lt_of_le_of_ne hb' (row_ties_excluded hb ω htie j hj)
      · intro hj
        exact ⟨fun he => (lt_irrefl _ (by simpa only [he] using! hj)),hj.le⟩
    rw [he,row_high_card hb.le ω]
    rw [higherRight_count] at hcount
    have hl := lowAboveCount_le_low b ω
    change lowAboveCount b ω < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)
    omega

def rankIndicator (E : Set RowRival) (c : ℕ) (ω : Fin N → RowRival) : ℝ :=
  if PiBinomial.count E Finset.univ ω< c then 1 else 0

theorem rankIndicator_bounds (E : Set RowRival) (c : ℕ) (ω : Fin N → RowRival) :
    rankIndicator E c ω ∈ Icc (0:ℝ) 1 := by unfold rankIndicator; split_ifs <;> norm_num

theorem integrable_rankIndicator (E : Set RowRival) (hE : MeasurableSet E) (c : ℕ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (rankIndicator E c) P := by
  apply Integrable.of_bound (C := 1)
    (Measurable.ite ((PiBinomial.measurable_count E hE Finset.univ) measurableSet_Iio)
      measurable_const measurable_const).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    change ‖rankIndicator E c ω‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (rankIndicator_bounds E c ω).1]
    exact (rankIndicator_bounds E c ω).2

theorem rankIndicator_mono {E F : Set RowRival} (hEF : E ⊆ F) (c : ℕ)
    (ω : Fin N → RowRival) : rankIndicator F c ω ≤ rankIndicator E c ω := by
  have hh := count_mono_of_subset hEF ω
  unfold rankIndicator
  split_ifs <;> simp_all
  omega

theorem higherRightAt_antitone {x y : ℝ} (hxy : x ≤ y) :
    higherRightAtSet y ⊆ higherRightAtSet x := by
  rintro r (h | h | ⟨h0,hb⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h0,hxy.trans_lt hb⟩)

def rareCross (c : ℕ) (x y : ℝ) : Set (Fin N → RowRival) :=
  {ω | (∃ j, ω j ∈ lowCluster (Ioc x y)) ∧ N+1-2*c ≤ lowBelowCount y ω}

theorem measurableSet_rareCross (c : ℕ) (x y : ℝ) :
    MeasurableSet (rareCross (N := N) c x y) := by
  have hm : MeasurableSet {ω : Fin N → RowRival | ∃ j, ω j ∈ lowCluster (Ioc x y)} := by
    have he : {ω : Fin N → RowRival | ∃ j, ω j ∈ lowCluster (Ioc x y)}=
        ⋃ j : Fin N, {ω | ω j ∈ lowCluster (Ioc x y)} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => (measurable_pi_apply j)
      (measurableSet_lowCluster _ measurableSet_Ioc)
  exact hm.inter ((PiBinomial.measurable_count (lowCluster (Iic y))
    (measurableSet_lowCluster _ measurableSet_Iic) Finset.univ) measurableSet_Ici)

theorem row_first_increment_upper
    (c : ℕ) {κ U x y : ℝ} (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hx : 0 < x) (hxy : x < y) (hcross : κ*U < x)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1≠1)
    (hcap : ∀ j, (ω j).1=0 → (ω j).2 ≤ U)
    (htx : ∀ j, (ω j).1=0 → (ω j).2≠x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2≠y) :
    rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω ≤
      (rankIndicator (higherAtSet y) c ω-rankIndicator (higherAtSet x) c ω)+
      (rankIndicator (higherRightAtSet y) c ω-rankIndicator (higherRightAtSet x) c ω)+
      (rareCross c x y).indicator (fun _ => (1:ℝ)) ω := by
  have hL := rankIndicator_mono (higherAt_antitone hxy.le) c ω
  have hR := rankIndicator_mono (higherRightAt_antitone hxy.le) c ω
  have he0 : 0 ≤ (rareCross c x y).indicator (fun _ => (1:ℝ)) ω :=
    indicator_nonneg (fun _ _ => by norm_num) _
  by_cases hx0 : rowUnequalPureFirst κ c x ω=0
  · by_cases hy1 : rowUnequalPureFirst κ c y ω=1
    · have hne : rowResidual c 0 ω≠rowResidual c 1 ω := by
        intro he
        simp only [rowUnequalPureFirst,if_pos he] at hy1
        norm_num at hy1
      have hxn : (0:Fin (N+1)) ∉ (rowPureSelection κ c x ω).1 ∪ (rowPureSelection κ c x ω).2 := by
        intro hs
        simp only [rowUnequalPureFirst,if_neg hne,first_eq_indicator,if_pos hs] at hx0
        norm_num at hx0
      have hys : (0:Fin (N+1)) ∈ (rowPureSelection κ c y ω).1 ∪ (rowPureSelection κ c y ω).2 := by
        by_contra hn
        simp only [rowUnequalPureFirst,if_neg hne,first_eq_indicator,if_neg hn] at hy1
        norm_num at hy1
      by_cases hleft : c ≤ classCount 2 ω
      · have hzero : (patternTemplate c (fun j => (ω j).1)).residual₀=0 := by
          change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=0
          omega
        have hye : (rowPureSelection κ c y ω).1=∅ :=
          (patternTemplate c (fun j => (ω j).1)).selection_empty_left κ (rowBids y ω) hzero
        have hyR : PiBinomial.count (higherRightAtSet y) Finset.univ ω< c := by
          apply (right_selected_iff_rank_on_left_full c κ (hx.trans hxy) ω hty hleft).mp
          simpa only [hye,Finset.empty_union] using hys
        have hxR : ¬PiBinomial.count (higherRightAtSet x) Finset.univ ω< c := by
          intro hh
          exact hxn (Finset.mem_union_right _
            ((right_selected_iff_rank_on_left_full c κ hx ω htx hleft).mpr hh))
        have hyR1 : rankIndicator (higherRightAtSet y) c ω=1 := by simp only [rankIndicator,if_pos hyR]
        have hxR0 : rankIndicator (higherRightAtSet x) c ω=0 := by simp only [rankIndicator,if_neg hxR]
        rw [hx0,hy1,hyR1,hxR0]
        linarith
      · by_cases hright : c ≤ classCount 3 ω
        · have hzero : (patternTemplate c (fun j => (ω j).1)).residual₁=0 := by
            change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)=0
            omega
          have hye : (rowPureSelection κ c y ω).2=∅ :=
            (patternTemplate c (fun j => (ω j).1)).selection_empty_right κ (rowBids y ω) hzero
          have hyL : PiBinomial.count (higherAtSet y) Finset.univ ω< c := by
            apply (pure_left_on_opposite_full_iff_rank c κ (hx.trans hxy) ω hty
              (by simpa only [otherUpper_count] using hright)).mp
            simpa only [hye,Finset.union_empty] using hys
          have hxL : ¬PiBinomial.count (higherAtSet x) Finset.univ ω< c := by
            intro hh
            exact hxn (Finset.mem_union_left _
              ((pure_left_on_opposite_full_iff_rank c κ hx ω htx
                (by simpa only [otherUpper_count] using hright)).mpr hh))
          have hyL1 : rankIndicator (higherAtSet y) c ω=1 := by simp only [rankIndicator,if_pos hyL]
          have hxL0 : rankIndicator (higherAtSet x) c ω=0 := by simp only [rankIndicator,if_neg hxL]
          rw [hx0,hy1,hyL1,hxL0]
          linarith
        · have he : ω ∈ rareCross c x y := both_under_first_acquisition_event c hκ hκ1
            hx hxy hcross ω hno hcap htx hty (lt_of_not_ge hleft) (lt_of_not_ge hright) hx0 hy1
          rw [indicator_of_mem he,hx0,hy1]
          linarith
    · have hy0 : rowUnequalPureFirst κ c y ω=0 := by
        unfold rowUnequalPureFirst at hy1 ⊢
        split_ifs <;> simp_all [first_eq_indicator]
      rw [hy0,hx0]
      linarith
  · have hx1 : rowUnequalPureFirst κ c x ω=1 := by
      unfold rowUnequalPureFirst at hx0 ⊢
      split_ifs <;> simp_all [first_eq_indicator]
    rw [hx1]
    linarith [(rowUnequalPureFirst_bounds κ c y ω).2]

theorem integral_rankIndicator {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (E : Set RowRival) (hE : MeasurableSet E)
    (c : ℕ) :
    (∫ ω : Fin N → RowRival, rankIndicator E c ω
      ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G))=
        Bayes.binomBelow N ((sourceRivalLaw t G).real E) c := by
  letI := sourceRivalLaw_probability ht G
  have he : rankIndicator (N := N) E c=
      {ω | PiBinomial.count E Finset.univ ω< c}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    simp only [rankIndicator,Set.indicator_apply,mem_setOf_eq]
  have hs : MeasurableSet {ω : Fin N → RowRival | PiBinomial.count E Finset.univ ω<c} :=
    (PiBinomial.measurable_count E hE Finset.univ) measurableSet_Iio
  rw [he,integral_indicator_const (1:ℝ) hs]
  simp only [smul_eq_mul,mul_one]
  simpa only [Finset.card_univ,Fintype.card_fin] using
    iid_count_lt_eq_binomBelow (sourceRivalLaw t G) E hE (Finset.univ : Finset (Fin N)) c

theorem source_shifted_low_count_upper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (hw : μ.real E ≤ (17/20000:ℝ))
    (m c N r : ℕ) (hN : N ≤ m) (hcut : m-2*c-r ≤ N)
    (hcm : 2*c+r ≤ m) (hcap : (c:ℝ) ≤ rho*m) :
    (Measure.pi fun _ : Fin N => μ).real
      {ω | m-2*c-r ≤ PiBinomial.count E Finset.univ ω} ≤
        Real.exp ((r:ℝ)/10-(9/1000000:ℝ)*m) := by
  have hh := RankUpperTail.iid_count_upper_chernoff μ E hE N (m-2*c-r) hcut
    (show (0:ℝ) ≤ 1/10 by norm_num)
  have hlog := RankUpperTail.source_tilt_log_bound measureReal_nonneg hw
  have hmc : 2*c ≤ m := by omega
  have hrc : r ≤ m-2*c := by omega
  have hcast : ((m-2*c-r:ℕ):ℝ)=(m:ℝ)-2*c-r := by
    rw [Nat.cast_sub hrc,Nat.cast_sub hmc]
    push_cast
    ring
  have hNR : (N:ℝ) ≤ m := by exact_mod_cast hN
  have hcutR : (m:ℝ)/1000-r ≤ (m-2*c-r:ℕ) := by
    rw [hcast]
    norm_num only [rho] at hcap
    nlinarith
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg N)
  have hnm := mul_le_mul_of_nonneg_right hNR (by norm_num : (0:ℝ) ≤ 901/10000000)
  nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]

theorem source_rareCross_upper (i : Row) {m : ℕ} (hm : 2000 ≤ m)
    (G : Measure ℝ) [IsProbabilityMeasure G] {x y : ℝ}
    (hM : sourceRank (cutoff i) G y ≤ RankCutoff.Mstar i) :
    (Measure.pi fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) G).real
      (rareCross (capacity m) x y) ≤
        (m-1:ℕ)*(cutoff i*G.real (Ioc x y))*Real.exp (1/10-(9/1000000:ℝ)*m) := by
  let μ := sourceRivalLaw (cutoff i) G
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  have hcapacity := (PhysicalRates.capacity_floor_bounds m).2
  have hmc : 2*capacity m+1 ≤ m := by
    have hmR : (2000:ℝ) ≤ m := by exact_mod_cast hm
    have hh : (2*capacity m+1:ℝ) ≤ m := by
      norm_num only [rho] at hcapacity
      nlinarith
    exact_mod_cast hh
  have hN : m-2*capacity m-1 ≤ m-2 := by
    have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
    omega
  have htail := source_shifted_low_count_upper μ (lowCluster (Iic y))
    (measurableSet_lowCluster _ measurableSet_Iic) (by
      change (rivalLaw (cutoff i) 0 (1-cutoff i) G).real (lowCluster (Iic y)) ≤ _
      rw [lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le G (Iic y) measurableSet_Iic]
      exact hM.trans (RankCutoff.Mstar_bounds i).2.le)
    m (capacity m) (m-2) 1 (Nat.sub_le _ _) hN hmc hcapacity
  have hh := cluster_and_many_probability (N := m-2) μ
    (lowCluster (Ioc x y)) (lowCluster (Iic y))
    (measurableSet_lowCluster _ measurableSet_Ioc) (measurableSet_lowCluster _ measurableSet_Iic)
    (m-2*capacity m-1)
  change (Measure.pi fun _ : Fin (m-2+1) => μ).real
    {ω | (∃ j, ω j ∈ lowCluster (Ioc x y)) ∧
      m-2*capacity m-1+1 ≤ PiBinomial.count (lowCluster (Iic y)) Finset.univ ω} ≤
    (m-2+1:ℕ)*μ.real (lowCluster (Ioc x y))*
      (Measure.pi fun _ : Fin (m-2) => μ).real
        {ω | m-2*capacity m-1 ≤ PiBinomial.count (lowCluster (Iic y)) Finset.univ ω} at hh
  simp only [show m-2+1=m-1 by omega,
    show m-2*capacity m-1+1=m-2*capacity m by omega,
    μ,sourceRivalLaw,
    lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le G (Ioc x y) measurableSet_Ioc] at hh
  have he : rareCross (N := m-1) (capacity m) x y=
      {ω | (∃ j, ω j ∈ lowCluster (Ioc x y)) ∧
        m-2*capacity m ≤ PiBinomial.count (lowCluster (Iic y)) Finset.univ ω} := by
    simp only [rareCross,lowBelowCount,show m-1+1=m by omega]
  rw [he]
  let eventProbability (n : ℕ) : ℝ := (Measure.pi fun _ : Fin n => μ).real
    {ω | (∃ j, ω j ∈ lowCluster (Ioc x y)) ∧
      m-2*capacity m ≤ PiBinomial.count (lowCluster (Iic y)) Finset.univ ω}
  have hbound : eventProbability (m-2+1) ≤
      (m-1:ℕ)*(cutoff i*G.real (Ioc x y))*Real.exp (1/10-(9/1000000:ℝ)*m) := by
    simpa only [eventProbability,μ,sourceRivalLaw,Nat.cast_one] using!
      hh.trans (mul_le_mul_of_nonneg_left htail
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (cutoff_pos i).le measureReal_nonneg)))
  have hevent : eventProbability (m-2+1)=eventProbability (m-1) :=
    congrArg eventProbability (show m-2+1=m-1 by omega)
  change eventProbability (m-1) ≤ _
  rw [← hevent]
  exact hbound

theorem source_sharp_pure_upper_interval (i : Row) {m : ℕ} (hm : 2000 ≤ m)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hcap : ∀ᵐ b ∂G, b ≤ ReceiptGap.cap i)
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hcross : kappa i*ReceiptGap.cap i < x)
    (hatomx : G {x}=0) (hatomy : G {y}=0)
    (hM : sourceRank (cutoff i) G y ≤ RankCutoff.Mstar i) :
    expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G y-
      expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G x ≤
      2*(Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G y)-
        Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G x))+
      (m-1:ℕ)*(cutoff i*G.real (Ioc x y))*Real.exp (1/10-(9/1000000:ℝ)*m) := by
  let μ := sourceRivalLaw (cutoff i) G
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  let P := Measure.pi fun _ : Fin (m-1) => μ
  have hrowcap : ∀ᵐ ω ∂P, ∀ j, (ω j).1=0 → (ω j).2 ≤ ReceiptGap.cap i := by
    have hsingle : ∀ᵐ r ∂μ, r.1=0 → r.2 ≤ ReceiptGap.cap i := by
      have hm : (∀ᵐ r ∂G.map (fun b => ((0:Fin 4),b)), r.1=0 → r.2 ≤ ReceiptGap.cap i) :=
        (ae_map_iff
          (show Measurable (fun b : ℝ => ((0:Fin 4),b)) from
            measurable_const.prodMk measurable_id).aemeasurable
          (show MeasurableSet {r : RowRival | r.1=0 → r.2 ≤ ReceiptGap.cap i} by measurability)).mpr
            (by filter_upwards [hcap] with b hb; exact fun _ => hb)
      simp only [μ,sourceRivalLaw,rivalLaw,ae_add_measure_iff]
      refine ⟨⟨⟨Measure.ae_smul_measure hm _,?_⟩,?_⟩,?_⟩ <;>
        apply Measure.ae_smul_measure <;> rw [ae_dirac_eq] <;> intro htag <;>
          have hv := congrArg Fin.val htag <;> norm_num at hv
    exact ae_all_iff.mpr fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin (m-1) => μ) (i := j)) hsingle
  have hpoint : ∀ᵐ ω ∂P, rowUnequalPureFirst (kappa i) (capacity m) y ω-
      rowUnequalPureFirst (kappa i) (capacity m) x ω ≤
      (rankIndicator (higherAtSet y) (capacity m) ω-rankIndicator (higherAtSet x) (capacity m) ω)+
      (rankIndicator (higherRightAtSet y) (capacity m) ω-rankIndicator (higherRightAtSet x) (capacity m) ω)+
      (rareCross (capacity m) x y).indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [source_iid_row_no_tie (cutoff_mem i) G hatomx,
      source_iid_row_no_tie (cutoff_mem i) G hatomy,hrowcap] with ω hxω hyω hUω
    exact row_first_increment_upper (capacity m)
      (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
      (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) hx hxy hcross ω hxω.1 hUω hxω.2 hyω.2
  have hi := integral_mono_ae
    ((integrable_rowUnequalPureFirst (kappa i) (capacity m) y P).sub
      (integrable_rowUnequalPureFirst (kappa i) (capacity m) x P))
    ((((integrable_rankIndicator (higherAtSet y) (measurableSet_higherAtSet y) (capacity m) P).sub
      (integrable_rankIndicator (higherAtSet x) (measurableSet_higherAtSet x) (capacity m) P)).add
      ((integrable_rankIndicator (higherRightAtSet y) (measurableSet_higherRightAtSet y) (capacity m) P).sub
      (integrable_rankIndicator (higherRightAtSet x) (measurableSet_higherRightAtSet x) (capacity m) P))).add
      ((integrable_const (1:ℝ)).indicator (measurableSet_rareCross (capacity m) x y))) hpoint
  have hLy := integrable_rankIndicator (higherAtSet y) (measurableSet_higherAtSet y) (capacity m) P
  have hLx := integrable_rankIndicator (higherAtSet x) (measurableSet_higherAtSet x) (capacity m) P
  have hRy := integrable_rankIndicator (higherRightAtSet y) (measurableSet_higherRightAtSet y) (capacity m) P
  have hRx := integrable_rankIndicator (higherRightAtSet x) (measurableSet_higherRightAtSet x) (capacity m) P
  have hE := (integrable_const (1:ℝ) (μ := P)).indicator (measurableSet_rareCross (capacity m) x y)
  have hLd : Integrable (fun ω => rankIndicator (higherAtSet y) (capacity m) ω-
      rankIndicator (higherAtSet x) (capacity m) ω) P := hLy.sub hLx
  have hRd : Integrable (fun ω => rankIndicator (higherRightAtSet y) (capacity m) ω-
      rankIndicator (higherRightAtSet x) (capacity m) ω) P := hRy.sub hRx
  have hLR : Integrable (fun ω =>
      (rankIndicator (higherAtSet y) (capacity m) ω-rankIndicator (higherAtSet x) (capacity m) ω)+
      (rankIndicator (higherRightAtSet y) (capacity m) ω-rankIndicator (higherRightAtSet x) (capacity m) ω)) P := hLd.add hRd
  simp only [Pi.sub_apply,Pi.add_apply] at hi
  rw [integral_sub (integrable_rowUnequalPureFirst (kappa i) (capacity m) y P)
    (integrable_rowUnequalPureFirst (kappa i) (capacity m) x P),
    integral_add hLR hE,
    integral_add hLd hRd,integral_sub hLy hLx,integral_sub hRy hRx,
    integral_rankIndicator (cutoff_mem i) G (higherAtSet y) (measurableSet_higherAtSet y),
    integral_rankIndicator (cutoff_mem i) G (higherAtSet x) (measurableSet_higherAtSet x),
    integral_rankIndicator (cutoff_mem i) G (higherRightAtSet y) (measurableSet_higherRightAtSet y),
    integral_rankIndicator (cutoff_mem i) G (higherRightAtSet x) (measurableSet_higherRightAtSet x),
    integral_indicator_const (1:ℝ) (measurableSet_rareCross (capacity m) x y)] at hi
  simp only [smul_eq_mul,mul_one] at hi
  simp only [source_higher_probability (cutoff_pos i).le (cutoff_lt_one i).le G,
    source_higherRight_probability (cutoff_pos i).le (cutoff_lt_one i).le G] at hi
  have hr := source_rareCross_upper i hm G hM (x := x)
  change expectedUnequalPureFirst _ _ _ _ _ _-expectedUnequalPureFirst _ _ _ _ _ _ ≤ _ at hi
  dsimp only [Rank.pureRank]
  linarith

end FCAppendix.Affine.Uniform06.SharpPureIntervals
