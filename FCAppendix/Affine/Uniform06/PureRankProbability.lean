import FCAppendix.Affine.Uniform06.PureRankSelector
import FCAppendix.Affine.Uniform06.RankUpperTail
import FCAppendix.Affine.Uniform06.UnilateralRank

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureRankProbability

open MeasureTheory Set Filter
open LowBody PureDuplicateIntervals PureRankSelector PureRankCounts
open scoped BigOperators

variable {N : ℕ}

def unequalPureLeftEvent (κ : ℝ) (c : ℕ) (b : ℝ) : Set (Fin N → RowRival) :=
  {ω | rowResidual c 0 ω ≠ rowResidual c 1 ω ∧
    (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1}

def qPure (N c : ℕ) (κ t : ℝ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real (unequalPureLeftEvent κ c b)

theorem measurableSet_unequalPureLeftEvent (κ : ℝ) (c : ℕ) (b : ℝ) :
    MeasurableSet (unequalPureLeftEvent (N := N) κ c b) := by
  have hkind : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst
  have hres (r : Fin 2) : Measurable (fun ω : Fin N → RowRival => rowResidual c r ω) := by
    have hh := (measurable_of_countable
      (fun k : Fin N → Fin 4 => (patternTemplate c k).residual₀)).comp hkind
    have hh' := (measurable_of_countable
      (fun k : Fin N → Fin 4 => (patternTemplate c k).residual₁)).comp hkind
    fin_cases r
    · exact hh
    · exact hh'
  have hsel : MeasurableSet {ω : Fin N → RowRival |
      (0:Fin (N+1)) ∈ (rowPureSelection κ c b ω).1} :=
    (measurable_rowPureSelection κ c b)
      ((Set.to_countable {p : Finset (Fin (N+1)) × Finset (Fin (N+1)) | 0 ∈ p.1}).measurableSet)
  exact (measurableSet_eq_fun (hres 0) (hres 1)).compl.inter hsel

theorem main_event_in_unequal_pure
    (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0 < b) (ω : Fin N → RowRival)
    (htie : ∀ j, (ω j).1=0 → (ω j).2 ≠ b)
    (hX : PiBinomial.count (higherAtSet b) Finset.univ ω < c)
    (hY : c ≤ PiBinomial.count otherUpper Finset.univ ω) :
    ω ∈ unequalPureLeftEvent κ c b := by
  have hleft := (pure_left_on_opposite_full_iff_rank c κ hb ω htie hY).mpr hX
  have hY' : c ≤ classCount 3 ω := by rwa [otherUpper_count] at hY
  have hzero : rowResidual c 1 ω=0 := by
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)=0
    omega
  have hf := (patternTemplate c (fun j => (ω j).1)).selection_feasible κ (rowBids b ω)
  have hpos : 0 < rowResidual c 0 ω :=
    (Finset.card_pos.mpr ⟨0,hleft⟩).trans_le hf.1
  refine ⟨?_,hleft⟩
  rw [hzero]
  exact hpos.ne'

theorem source_single_row_no_tie
    (t : ℝ) (G : Measure ℝ) {b : ℝ} (hatom : G {b}=0) :
    ∀ᵐ r ∂sourceRivalLaw t G, r.1 ≠ 1 ∧ (r.1=0 → r.2≠b) := by
  have hGb : ∀ᵐ v ∂G, v ≠ b := by
    rw [ae_iff]
    simpa using hatom
  have hinj : Measurable (fun v : ℝ => ((0:Fin 4),v)) :=
    measurable_const.prodMk measurable_id
  have hlow : ∀ᵐ r ∂G.map (fun v : ℝ => ((0:Fin 4),v)),
      r.1 ≠ 1 ∧ (r.1=0 → r.2≠b) := by
    apply (ae_map_iff hinj.aemeasurable (by measurability)).mpr
    filter_upwards [hGb] with v hv
    exact ⟨by decide,fun _ => hv⟩
  simp only [sourceRivalLaw,rivalLaw,ENNReal.ofReal_zero,zero_smul,add_zero,
    ae_add_measure_iff]
  refine ⟨⟨Measure.ae_smul_measure hlow _,?_⟩,?_⟩ <;>
    apply Measure.ae_smul_measure <;> rw [ae_dirac_eq] <;>
      exact ⟨by decide,by intro h; have hn := congrArg Fin.val h; norm_num at hn⟩

theorem source_iid_row_no_tie {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] {b : ℝ} (hatom : G {b}=0) :
    ∀ᵐ ω : Fin N → RowRival ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G),
      (∀ j, (ω j).1 ≠ 1) ∧ (∀ j, (ω j).1=0 → (ω j).2≠b) := by
  letI := sourceRivalLaw_probability ht G
  have hrow : ∀ᵐ ω : Fin N → RowRival ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G),
      ∀ j, (ω j).1 ≠ 1 ∧ ((ω j).1=0 → (ω j).2≠b) := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin N => sourceRivalLaw t G) (i := j))
      (source_single_row_no_tie t G hatom)
  filter_upwards [hrow] with ω hω
  exact ⟨fun j => (hω j).1,fun j => (hω j).2⟩

theorem qPure_lower_finite
    {t κ b θ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hb : 0 < b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0)
    (N c : ℕ) (hθ : 0 ≤ θ) :
    (1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+sourceRank t G b))*(1-Real.exp (-θ))))*
      Rank.pureRank N c ((1+t)/2) (sourceRank t G b) ≤ qPure N c κ t G b := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  apply (source_main_rank_event_relative ht ht1 G b N c hθ).trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [source_iid_row_no_tie ⟨ht,ht1.le⟩ G hatom] with ω hω hm
  exact main_event_in_unequal_pure c κ hb ω hω.2 hm.1 hm.2

theorem qPure_upper_finite
    {t κ b : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hκ1 : κ ≤ 1) (hb : 0 < b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0) (N c : ℕ) :
    qPure N c κ t G b ≤ Rank.pureRank N c ((1+t)/2) (sourceRank t G b)+
      (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real
        {ω | N+1-2*c ≤ lowBelowCount b ω} := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  let A : Set (Fin N → RowRival) := {ω | PiBinomial.count (higherAtSet b) Finset.univ ω < c}
  let R : Set (Fin N → RowRival) := {ω | N+1-2*c ≤ lowBelowCount b ω}
  have hsub : qPure N c κ t G b ≤ P.real (A ∪ R) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [source_iid_row_no_tie ⟨ht,ht1.le⟩ G hatom] with ω hω hp
    exact (pure_left_rank_event_sandwich c hκ1 hb ω hω.1 hω.2).2 hp.2
  have hA : P.real A=Rank.pureRank N c ((1+t)/2) (sourceRank t G b) := by
    have h := iid_count_lt_eq_binomBelow (sourceRivalLaw t G) (higherAtSet b)
      (measurableSet_higherAtSet b) (Finset.univ : Finset (Fin N)) c
    simpa only [P,A,Finset.card_univ,Fintype.card_fin,
      source_higher_probability ht ht1.le G b,Rank.pureRank] using h
  calc
    qPure N c κ t G b ≤ P.real (A ∪ R) := hsub
    _ ≤ P.real A+P.real R := measureReal_union_le _ _
    _ = _ := by rw [hA]

theorem count_mono_of_subset {Ω : Type*} {E F : Set Ω} (hEF : E ⊆ F)
    (ω : Fin N → Ω) :
    PiBinomial.count E Finset.univ ω ≤ PiBinomial.count F Finset.univ ω := by
  classical
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  exact hEF hj

theorem unilateral_le_pureRank
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) (N c : ℕ) :
    Bayes.binomBelow N ((1+t)/2) c ≤
      Rank.pureRank N c ((1+t)/2) (sourceRank t G b) := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  have hE : higherAtSet b ⊆ otherUpperᶜ := by
    intro r hr ho
    exact Set.disjoint_left.mp (disjoint_higher_other b) hr ho
  have hsub : {ω : Fin N → RowRival |
      PiBinomial.count otherUpperᶜ Finset.univ ω < c} ⊆
      {ω | PiBinomial.count (higherAtSet b) Finset.univ ω < c} := by
    intro ω hω
    exact (count_mono_of_subset hE ω).trans_lt hω
  have hp := measureReal_mono (μ := Measure.pi fun _ : Fin N => sourceRivalLaw t G) hsub
  rw [iid_count_lt_eq_binomBelow _ _ measurableSet_otherUpper.compl,
    iid_count_lt_eq_binomBelow _ _ (measurableSet_higherAtSet b)] at hp
  have hc : (sourceRivalLaw t G).real otherUpperᶜ=(1+t)/2 := by
    rw [probReal_compl_eq_one_sub measurableSet_otherUpper,source_other_probability ht1.le G b]
    ring
  simpa only [Finset.card_univ,Fintype.card_fin,hc,
    source_higher_probability ht ht1.le G b,Rank.pureRank] using hp

theorem qPure_relative_finite
    {t κ b θ γ r : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hκ1 : κ ≤ 1) (hb : 0 < b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0)
    (m c : ℕ) (hm : 0 < m) (hc : 0 < c) (hcm : 2*c ≤ m)
    (hcap : (c:ℝ) ≤ (999/2000:ℝ)*m)
    (hM : sourceRank t G b ≤ (17/20000:ℝ))
    (hθ : 0 ≤ θ)
    (hcond : θ*(c-1:ℕ)-((m-1)-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+sourceRank t G b))*(1-Real.exp (-θ)) ≤ -γ*m)
    (hL : Real.exp (-(m:ℝ)*r) ≤ Bayes.binomBelow (m-1) ((1+t)/2) c) :
    |qPure (m-1) c κ t G b/Rank.pureRank (m-1) c ((1+t)/2) (sourceRank t G b)-1| ≤
      Real.exp (-γ*m)+Real.exp (-(m:ℝ)*((9/1000000:ℝ)-r)) := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  let Q := Rank.pureRank (m-1) c ((1+t)/2) (sourceRank t G b)
  have hQL := unilateral_le_pureRank ht ht1 G b (m-1) c
  have hQ : 0 < Q := (Real.exp_pos _).trans_le (hL.trans hQL)
  have hlow := qPure_lower_finite (κ := κ) ht ht1 hb G hatom (m-1) c hθ
  have he := Real.exp_le_exp.mpr hcond
  have hlow' : (1-Real.exp (-γ*m))*Q ≤ qPure (m-1) c κ t G b := by
    have hx := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hQ.le
    exact hx.trans hlow
  have hhigh := qPure_upper_finite ht ht1 hκ1 hb G hatom (m-1) c
  have hN : m-1+1=m := Nat.sub_add_cancel hm
  have hmass : (sourceRivalLaw t G).real (lowCluster (Iic b))=sourceRank t G b :=
    lowCluster_probability t 0 (1-t) ht G (Iic b) measurableSet_Iic
  have htail := RankUpperTail.source_low_below_count_upper
    (sourceRivalLaw t G) (lowCluster (Iic b))
    (measurableSet_lowCluster (Iic b) measurableSet_Iic)
    (by rwa [hmass]) m c hc hcm hcap
  have hhigh' : qPure (m-1) c κ t G b ≤ Q+Real.exp (-(9/1000000:ℝ)*m) := by
    rw [hN] at hhigh
    change (Measure.pi fun _ : Fin (m-1) => sourceRivalLaw t G).real
      {ω | m-2*c ≤ lowBelowCount b ω} ≤ _ at htail
    exact hhigh.trans (by linarith only [htail])
  have hquotlo : -Real.exp (-γ*m) ≤ qPure (m-1) c κ t G b/Q-1 := by
    have hh := (le_div_iff₀ hQ).mpr hlow'
    linarith
  have hquotHi : qPure (m-1) c κ t G b/Q-1 ≤
      Real.exp (-(m:ℝ)*((9/1000000:ℝ)-r)) := by
    have hscale := mul_le_mul_of_nonneg_left (hL.trans hQL)
      (Real.exp_pos (-(m:ℝ)*((9/1000000:ℝ)-r))).le
    have heq : Real.exp (-(m:ℝ)*((9/1000000:ℝ)-r))*Real.exp (-(m:ℝ)*r) =
        Real.exp (-(9/1000000:ℝ)*m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hscale
    have hh : qPure (m-1) c κ t G b ≤
        (1+Real.exp (-(m:ℝ)*((9/1000000:ℝ)-r)))*Q := by
      nlinarith
    have hh' := (div_le_iff₀ hQ).mpr hh
    linarith
  apply abs_le.mpr
  constructor <;> linarith [Real.exp_pos (-γ*m),
    Real.exp_pos (-(m:ℝ)*((9/1000000:ℝ)-r))]

end FCAppendix.Affine.Uniform06.PureRankProbability
