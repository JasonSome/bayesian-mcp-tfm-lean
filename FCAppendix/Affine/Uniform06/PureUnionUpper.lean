import FCAppendix.Affine.Uniform06.LiteralKernelDecomposition

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureUnionUpper

open MeasureTheory Set Filter LowBody
open PureRankCounts PureRankSelector PureRankProbability PureDuplicateIntervals
open PurePivotalSource PureDuplicateRare LiteralExperiment LiteralKernelDecomposition
open FCAppendix.Affine.Uniform07
open scoped BigOperators ENNReal

def higherRightAtSet (b : ℝ) : Set RowRival :=
  {r | r.1=1 ∨ r.1=3 ∨ (r.1=0 ∧ b< r.2)}

theorem measurableSet_higherRightAtSet (b : ℝ) : MeasurableSet (higherRightAtSet b) :=
  (measurableSet_eq_fun measurable_fst measurable_const).union
    ((measurableSet_eq_fun measurable_fst measurable_const).union
      ((measurableSet_eq_fun measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const measurable_snd)))

theorem source_higherRight_probability {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    (sourceRivalLaw t G).real (higherRightAtSet b)=(1+t)/2-sourceRank t G b := by
  have hlow : Measurable (fun x : ℝ => ((0:Fin 4),x)) := measurable_const.prodMk measurable_id
  have hp : (fun x : ℝ => ((0:Fin 4),x)) ⁻¹' higherRightAtSet b=Ioi b := by
    ext x
    simp only [higherRightAtSet,mem_preimage,mem_setOf_eq,Fin.ext_iff]
    norm_num

  have h1 : ((1:Fin 4),0) ∈ higherRightAtSet b := Or.inl rfl
  have h3 : ((3:Fin 4),0) ∈ higherRightAtSet b := Or.inr (Or.inl rfl)
  have h2 : ((2:Fin 4),0) ∉ higherRightAtSet b := by
    simp only [higherRightAtSet,mem_setOf_eq,Fin.ext_iff]
    norm_num

  have he : sourceRivalLaw t G (higherRightAtSet b)=
      ENNReal.ofReal t*G (Ioi b)+ENNReal.ofReal ((1-t)/2) := by
    simp only [sourceRivalLaw,rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hlow (measurableSet_higherRightAtSet b),hp]
    simp only [Measure.dirac_apply,Set.indicator_of_mem h1,Set.indicator_of_mem h3,
      Set.indicator_of_notMem h2,Pi.one_apply,ENNReal.ofReal_zero,mul_one,mul_zero,add_zero]
  have hsG : ENNReal.ofReal t*G (Ioi b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top G _)
  have htail : G.real (Ioi b)=1-G.real (Iic b) := by
    simpa only [compl_Iic] using probReal_compl_eq_one_sub (μ := G) (s := Iic b) measurableSet_Iic
  rw [measureReal_def,he,ENNReal.toReal_add hsG ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal ht,ENNReal.toReal_ofReal (by linarith : 0 ≤ (1-t)/2)]
  change t*G.real (Ioi b)+(1-t)/2=(1+t)/2-sourceRank t G b
  rw [htail,sourceRank]
  ring

variable {N : ℕ}

theorem higherRight_count (b : ℝ) (ω : Fin N → RowRival) :
    PiBinomial.count (higherRightAtSet b) Finset.univ ω=
      classCount 1 ω+classCount 3 ω+lowAboveCount b ω := by
  rw [PiBinomial.count_eq_sum,lowAboveCount,PiBinomial.count_eq_sum]
  unfold classCount
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  generalize hk : (ω j).1=k
  fin_cases k <;> simp only [higherRightAtSet,lowAboveSet,mem_setOf_eq,hk,Fin.ext_iff] <;> norm_num

theorem right_selected_on_left_full_implies_rank
    (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0 ≤ b) (ω : Fin N → RowRival)
    (hleft : c ≤ classCount 2 ω)
    (hselected : (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).2) :
    PiBinomial.count (higherRightAtSet b) Finset.univ ω< c := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hzero : T.residual₀=0 := by
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=0
    omega
  have hopt : Finite.Optimal T.residual₁ (rowBids b ω) (T.selection κ (rowBids b ω)).2 := by
    simpa only [T.selection_empty_left κ (rowBids b ω) hzero,
      Finset.notMem_empty,if_false] using right_revenue_optimal T κ (rowBids b ω) (rowBids_outside c b ω)
  have hcount : (Finset.univ.filter (fun j => rowBids b ω 0 < rowBids b ω j)).card < T.residual₁ := by
    by_contra hn
    exact Finite.excluded_of_many_better T.residual₁ (rowBids b ω) _ hopt 0
      (le_of_not_gt hn) hselected
  rw [row_high_card hb ω] at hcount
  change lowAboveCount b ω < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hcount
  rw [higherRight_count]
  omega

theorem right_remaining_requires_low_below
    (c : ℕ) {κ b : ℝ} (hκ1 : κ ≤ 1) (hb : 0 ≤ b)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (hleft : classCount 2 ω< c)
    (hselected : (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).2) :
    N+1-2*c ≤ lowBelowCount b ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  have hhigh := selected_implies_fewer_high_bids_than_total_residual T hκ1 (rowBids b ω)
    (rowBids_outside c b ω) 0 (by simpa only [rowBids,Fin.cons_zero] using hb)
    (Finset.mem_union_right _ hselected)
  rw [row_high_card hb ω] at hhigh
  have hf := T.selection_feasible κ (rowBids b ω)
  have hpos : 0 < T.residual₁ := (Finset.card_pos.mpr ⟨0,hselected⟩).trans_le hf.2.2.1
  have hc1 := no_active_count_zero ω hno
  have hcount := classCounts_sum ω
  have hpart := lower_count_partition b ω
  change lowAboveCount b ω < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)+
    min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hhigh
  change 0 < min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω) at hpos
  rw [hc1,Nat.sub_zero] at hhigh hpos
  rw [hc1] at hcount
  have hright : classCount 3 ω< c := by omega
  have hres0 := min_le_right (1+classCount 0 ω) (c-classCount 2 ω)
  have hres1 := min_le_right (1+classCount 0 ω) (c-classCount 3 ω)
  omega

theorem pure_union_event_inclusion
    (c : ℕ) {κ b : ℝ} (hκ1 : κ ≤ 1) (hb : 0 < b)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b)
    (hselected : (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1 ∪ (rowPureSelection κ c b ω).2) :
    PiBinomial.count (higherAtSet b) Finset.univ ω< c ∨
      PiBinomial.count (higherRightAtSet b) Finset.univ ω< c ∨
        N+1-2*c ≤ lowBelowCount b ω := by
  rcases Finset.mem_union.mp hselected with hL | hR
  · rcases (pure_left_rank_event_sandwich c hκ1 hb ω hno htie).2 hL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · by_cases hleft : c ≤ classCount 2 ω
    · exact Or.inr (Or.inl (right_selected_on_left_full_implies_rank c κ hb.le ω hleft hR))
    · exact Or.inr (Or.inr (right_remaining_requires_low_below c hκ1 hb.le ω hno
        (lt_of_not_ge hleft) hR))

theorem expected_unequal_pure_union_upper
    {t κ b : ℝ} (ht : t ∈ Icc 0 1) (hκ1 : κ ≤ 1) (hb : 0 < b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0) (N c : ℕ) :
    expectedUnequalPureFirst N c κ t G b ≤
      2*Rank.pureRank N c ((1+t)/2) (sourceRank t G b)+
        (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real
          {ω | N+1-2*c ≤ lowBelowCount b ω} := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  let A : Set (Fin N → RowRival) := {ω | PiBinomial.count (higherAtSet b) Finset.univ ω< c}
  let B : Set (Fin N → RowRival) := {ω | PiBinomial.count (higherRightAtSet b) Finset.univ ω< c}
  let E : Set (Fin N → RowRival) := {ω | N+1-2*c ≤ lowBelowCount b ω}
  have hA : MeasurableSet A := (PiBinomial.measurable_count (higherAtSet b)
    (measurableSet_higherAtSet b) Finset.univ) measurableSet_Iio
  have hB : MeasurableSet B := (PiBinomial.measurable_count (higherRightAtSet b)
    (measurableSet_higherRightAtSet b) Finset.univ) measurableSet_Iio
  have hE : MeasurableSet E := (PiBinomial.measurable_count (lowCluster (Iic b))
    (measurableSet_lowCluster _ measurableSet_Iic) Finset.univ) measurableSet_Ici
  have hpoint : ∀ᵐ ω ∂P, rowUnequalPureFirst κ c b ω ≤
      (A ∪ B ∪ E).indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [source_iid_row_no_tie ht G hatom] with ω hω
    by_cases hu : ω ∈ A ∪ B ∪ E
    · rw [indicator_of_mem hu]
      exact (rowUnequalPureFirst_bounds κ c b ω).2
    · rw [indicator_of_notMem hu]
      have hn : (0:Fin (N+1)) ∉ (rowPureSelection κ c b ω).1 ∪ (rowPureSelection κ c b ω).2 := by
        intro hs
        have hh := pure_union_event_inclusion c hκ1 hb ω hω.1 hω.2 hs
        apply hu
        rcases hh with hh | hh | hh
        · exact Or.inl (Or.inl hh)
        · exact Or.inl (Or.inr hh)
        · exact Or.inr hh
      unfold rowUnequalPureFirst
      split_ifs
      · rfl
      · simp only [first_eq_indicator,if_neg hn]
        exact le_rfl
  have hi := integral_mono_ae (integrable_rowUnequalPureFirst κ c b P)
    ((integrable_const (1:ℝ)).indicator ((hA.union hB).union hE)) hpoint
  rw [integral_indicator_const (1:ℝ) ((hA.union hB).union hE)] at hi
  have hAU : P.real A=Rank.pureRank N c ((1+t)/2) (sourceRank t G b) := by
    simpa only [P,A,Finset.card_univ,Fintype.card_fin,source_higher_probability ht.1 ht.2 G b,Rank.pureRank] using
      iid_count_lt_eq_binomBelow (sourceRivalLaw t G) (higherAtSet b) (measurableSet_higherAtSet b)
        (Finset.univ : Finset (Fin N)) c
  have hBU : P.real B=Rank.pureRank N c ((1+t)/2) (sourceRank t G b) := by
    simpa only [P,B,Finset.card_univ,Fintype.card_fin,source_higherRight_probability ht.1 ht.2 G b,Rank.pureRank] using
      iid_count_lt_eq_binomBelow (sourceRivalLaw t G) (higherRightAtSet b) (measurableSet_higherRightAtSet b)
        (Finset.univ : Finset (Fin N)) c
  have hu1 := measureReal_union_le (μ := P) (A ∪ B) E
  have hu2 := measureReal_union_le (μ := P) A B
  rw [hAU,hBU] at hu2
  change expectedUnequalPureFirst N c κ t G b ≤ _ at hi
  simp only [smul_eq_mul,mul_one] at hi
  change expectedUnequalPureFirst N c κ t G b ≤
    2*Rank.pureRank N c ((1+t)/2) (sourceRank t G b)+P.real E
  linarith

theorem source_pure_union_upper (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure ℝ) [IsProbabilityMeasure G] {b : ℝ} (hb : 0 < b)
    (hatom : G {b}=0) (hM : sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i) :
    expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G b ≤
      2*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b)+
        Real.exp (-(9/1000000:ℝ)*m) := by
  let μ := sourceRivalLaw (cutoff i) G
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  have hh := expected_unequal_pure_union_upper (cutoff_mem i)
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) hb G hatom (m-1) (capacity m)
  rw [show m-1+1=m by omega] at hh
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcap := (PhysicalRates.capacity_floor_bounds m).2
  have h2 : 2*capacity m ≤ m := by
    have hR : (2*capacity m:ℝ) ≤ m := by norm_num only [rho] at hcap; nlinarith [show (0:ℝ) ≤ m from Nat.cast_nonneg m]
    exact_mod_cast hR
  have hmass : μ.real (lowCluster (Iic b)) ≤ (17/20000:ℝ) := by
    change (rivalLaw (cutoff i) 0 (1-cutoff i) G).real (lowCluster (Iic b)) ≤ _
    rw [lowCluster_probability (cutoff i) 0 (1-cutoff i) (cutoff_pos i).le G (Iic b) measurableSet_Iic]
    exact hM.trans (RankCutoff.Mstar_bounds i).2.le
  have htail := source_low_count_upper_remaining μ (lowCluster (Iic b))
    (measurableSet_lowCluster _ measurableSet_Iic) hmass m (capacity m) (m-1) h2
    (Nat.sub_le _ _) (by omega) hcap
  apply hh.trans
  simpa only [μ,lowBelowCount] using! add_le_add le_rfl htail

end FCAppendix.Affine.Uniform06.PureUnionUpper
