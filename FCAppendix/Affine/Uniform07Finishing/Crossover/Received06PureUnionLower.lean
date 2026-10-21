import FCAppendix.Affine.Uniform06.SharpPurePivotal
import FCAppendix.Affine.Uniform06.SourceRankRates

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open FCAppendix.Affine Uniform07 LowBody
open Uniform06 Uniform06.PureRankCounts Uniform06.PureRankSelector
open Uniform06.PureRankProbability Uniform06.PureDuplicateIntervals
open Uniform06.PurePivotalSource Uniform06.PureUnionUpper
open Uniform06.SharpPureIntervals Uniform06.SharpPurePivotal
open Uniform06.LiteralExperiment Uniform06.SourceRankRates
open scoped BigOperators
variable {N : ℕ}

def leftMain (c : ℕ) (b : ℝ) : Set (Fin N→ RowRival) :=
  {ω | PiBinomial.count (higherAtSet b) Finset.univ ω< c ∧
    c≤ PiBinomial.count otherUpper Finset.univ ω}

def rightMain (c : ℕ) (b : ℝ) : Set (Fin N→ RowRival) :=
  {ω | PiBinomial.count (higherRightAtSet b) Finset.univ ω< c ∧
    c≤ PiBinomial.count ownUpper Finset.univ ω}

theorem measurableSet_leftMain (c : ℕ) (b : ℝ) : MeasurableSet (leftMain (N:=N) c b) :=
  ((PiBinomial.measurable_count (higherAtSet b) (measurableSet_higherAtSet b) Finset.univ)
    measurableSet_Iio).inter
      ((PiBinomial.measurable_count otherUpper measurableSet_otherUpper Finset.univ)
        measurableSet_Ici)

theorem measurableSet_rightMain (c : ℕ) (b : ℝ) : MeasurableSet (rightMain (N:=N) c b) :=
  ((PiBinomial.measurable_count (higherRightAtSet b) (measurableSet_higherRightAtSet b) Finset.univ)
    measurableSet_Iio).inter
      ((PiBinomial.measurable_count ownUpper measurableSet_ownUpper Finset.univ)
        measurableSet_Ici)

theorem main_events_disjoint (c : ℕ) (b : ℝ) :
    Disjoint (leftMain (N:=N) c b) (rightMain c b) := by
  apply Set.disjoint_left.mpr
  intro ω hL hR
  have hLc:=hL.1
  rw [higherAtCount_eq] at hLc
  have hRc:=hR.2
  rw [ownUpper_count] at hRc
  omega

theorem leftMain_first_one (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0< b)
    (ω : Fin N→ RowRival) (htie : ∀j,(ω j).1=0→(ω j).2≠b)
    (h : ω∈leftMain c b) : rowUnequalPureFirst κ c b ω=1 := by
  have hsel:=main_event_in_unequal_pure c κ hb ω htie h.1 h.2
  have hunion : (0 : Fin (N+1))∈(rowPureSelection κ c b ω).1∪
      (rowPureSelection κ c b ω).2 := Finset.mem_union_left _ hsel.2
  simp only [rowUnequalPureFirst,if_neg hsel.1,first_eq_indicator,if_pos hunion]

theorem rightMain_first_one (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0< b)
    (ω : Fin N→ RowRival) (htie : ∀j,(ω j).1=0→(ω j).2≠b)
    (h : ω∈rightMain c b) : rowUnequalPureFirst κ c b ω=1 := by
  have hfull : c≤ classCount 2 ω := by simpa only [ownUpper_count] using h.2
  have hsel := (right_selected_iff_rank_on_left_full c κ hb ω htie hfull).mpr h.1
  let T:=patternTemplate c (fun j=>(ω j).1)
  have hzero : T.residual₀=0 := by
    change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=0
    omega
  have hpos : 0< T.residual₁ :=
    (Finset.card_pos.mpr ⟨0,hsel⟩).trans_le (T.selection_feasible κ (rowBids b ω)).2.2.1
  have hne : rowResidual c 0 ω≠rowResidual c 1 ω := by
    change T.residual₀≠T.residual₁
    omega
  have hunion : (0 : Fin (N+1))∈(rowPureSelection κ c b ω).1∪
      (rowPureSelection κ c b ω).2 := Finset.mem_union_right _ hsel
  simp only [rowUnequalPureFirst,if_neg hne,first_eq_indicator,if_pos hunion]

theorem main_indicators_le_first (c : ℕ) (κ : ℝ) {b : ℝ} (hb : 0< b)
    (ω : Fin N→ RowRival) (htie : ∀j,(ω j).1=0→(ω j).2≠b) :
    (leftMain c b).indicator (fun _=>(1:ℝ)) ω+
      (rightMain c b).indicator (fun _=>(1:ℝ)) ω≤ rowUnequalPureFirst κ c b ω := by
  by_cases hL : ω∈leftMain c b
  · have hR : ω∉rightMain c b := Set.disjoint_left.mp (main_events_disjoint c b) hL
    rw [indicator_of_mem hL,indicator_of_notMem hR,leftMain_first_one c κ hb ω htie hL]
    norm_num
  · rw [indicator_of_notMem hL,zero_add]
    by_cases hR : ω∈rightMain c b
    · rw [indicator_of_mem hR,rightMain_first_one c κ hb ω htie hR]
    · rw [indicator_of_notMem hR]
      exact (rowUnequalPureFirst_bounds κ c b ω).1

theorem main_probabilities_le_expected_first {t κ b : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hb : 0< b) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatom : G {b}=0) (N c : ℕ) :
    (Measure.pi (fun _ : Fin N=>sourceRivalLaw t G)).real (leftMain c b)+
      (Measure.pi (fun _ : Fin N=>sourceRivalLaw t G)).real (rightMain c b)≤
        expectedUnequalPureFirst N c κ t G b := by
  letI:=sourceRivalLaw_probability ht G
  let P:=Measure.pi (fun _ : Fin N=>sourceRivalLaw t G)
  have hiL := (integrable_const (1:ℝ) (μ:=P)).indicator (measurableSet_leftMain c b)
  have hiR := (integrable_const (1:ℝ) (μ:=P)).indicator (measurableSet_rightMain c b)
  have hpoint : ∀ᵐω∂P,
      (leftMain c b).indicator (fun _=>(1:ℝ)) ω+
        (rightMain c b).indicator (fun _=>(1:ℝ)) ω≤ rowUnequalPureFirst κ c b ω := by
    filter_upwards [source_iid_row_no_tie ht G hatom] with ω hω
    exact main_indicators_le_first c κ hb ω hω.2
  have h := integral_mono_ae (hiL.add hiR) (integrable_rowUnequalPureFirst κ c b P) hpoint
  change (∫ ω, (leftMain c b).indicator (fun _ => (1 : ℝ)) ω +
    (rightMain c b).indicator (fun _ => (1 : ℝ)) ω ∂P) ≤ _ at h
  have hIL := integral_indicator_one (μ := P) (measurableSet_leftMain (N := N) c b)
  have hIR := integral_indicator_one (μ := P) (measurableSet_rightMain (N := N) c b)
  change (∫ ω, (leftMain c b).indicator (fun _ => (1 : ℝ)) ω ∂P) = _ at hIL
  change (∫ ω, (rightMain c b).indicator (fun _ => (1 : ℝ)) ω ∂P) = _ at hIR
  rw [integral_add hiL hiR,hIL,hIR] at h
  exact h

theorem source_right_main_rank_event_relative {t : ℝ} (ht : 0≤ t) (ht1 : t<1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ)
    (N c : ℕ) {θ : ℝ} (hθ : 0≤θ) :
    (1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+sourceRank t G b))*(1-Real.exp (-θ))))*
      Rank.pureRank N c ((1+t)/2) (sourceRank t G b)≤
    (Measure.pi (fun _ : Fin N=>sourceRivalLaw t G)).real (rightMain c b) := by
  letI:=sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  have hw : 0≤ sourceRank t G b := mul_nonneg ht measureReal_nonneg
  have hE1 : (sourceRivalLaw t G).real (higherRightAtSet b)<1 := by
    rw [source_higherRight_probability ht ht1.le G b]
    linarith
  have h := main_rank_event_relative (sourceRivalLaw t G)
    (higherRightAtSet b) ownUpper (measurableSet_higherRightAtSet b)
    measurableSet_ownUpper (disjoint_higherRight_own b)
    (Finset.univ : Finset (Fin N)) c hθ hE1
  simpa only [Finset.card_univ,Fintype.card_fin,
    source_higherRight_probability ht ht1.le G b,source_own_probability ht1.le G,
    show 1-((1+t)/2-sourceRank t G b)=(1-t)/2+sourceRank t G b by ring,
    Rank.pureRank,rightMain] using h

theorem expected_unequal_pure_union_lower {t κ b θ : ℝ}
    (ht : 0≤ t) (ht1 : t<1) (hb : 0< b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0)
    (N c : ℕ) (hθ : 0≤θ) :
    2*(1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+sourceRank t G b))*(1-Real.exp (-θ))))*
      Rank.pureRank N c ((1+t)/2) (sourceRank t G b)≤
        expectedUnequalPureFirst N c κ t G b := by
  have hL:=source_main_rank_event_relative ht ht1 G b N c hθ
  have hR:=source_right_main_rank_event_relative ht ht1 G b N c hθ
  have hsum:=main_probabilities_le_expected_first (κ:=κ) ⟨ht,ht1.le⟩ hb G hatom N c
  change _≤(Measure.pi (fun _ : Fin N=>sourceRivalLaw t G)).real (leftMain c b) at hL
  nlinarith

theorem eventually_source_pure_union_relative (i : Row) :
    ∃γ : ℝ,0<γ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure ℝ) (_ : IsProbabilityMeasure G) (b : ℝ),
        0< b→ G {b}=0→ sourceRank (cutoff i) G b≤ RankCutoff.Mstar i→
        |expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G b-
          2*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
            (sourceRank (cutoff i) G b)|≤
          (2*Real.exp (-γ*m)+Real.exp (-(6/1000000:ℝ)*m))*
            Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
              (sourceRank (cutoff i) G b) := by
  obtain ⟨θ,γ,hθ,hγ,hdef⟩:=source_conditional_tilt i
  refine ⟨γ,hγ,?_⟩
  filter_upwards [eventually_Lm_lower i,eventually_ge_atTop (4:ℕ)] with m hL hm
  intro G hG b hb hatom hM
  letI:=hG
  let Q:=Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) G b)
  have hQL : Lm i m≤ Q :=
    unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) G b (m-1) (capacity m)
  have hQ : 0< Q := (Real.exp_pos _).trans_le (hL.trans hQL)
  have hc:=PhysicalRates.capacity_positive (show 3≤ m by omega)
  have htwice:=source_capacity_twice m
  have hcond:=source_relative_exponent hc (show capacity m≤ m by omega)
    (cutoff_lt_one i) (show 0≤ rho by norm_num [rho])
    (show rho≤ 1 by norm_num [rho])
    (show 0≤ sourceRank (cutoff i) G b from mul_nonneg (cutoff_pos i).le measureReal_nonneg)
    hM hθ.le (PhysicalRates.capacity_floor_bounds m).2 hdef
  have he:=Real.exp_le_exp.mpr hcond
  have hlow:=expected_unequal_pure_union_lower (κ:=kappa i)
    (cutoff_pos i).le (cutoff_lt_one i) hb G hatom (m-1) (capacity m) hθ.le
  have hlow' : 2*(1-Real.exp (-γ*m))*Q≤
      expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G b := by
    have hscale:=mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) (by linarith : 0≤ 2*Q)
    nlinarith
  have hhigh:=source_pure_union_upper i hm G hb hatom hM
  have hrare : Real.exp (-(9/1000000:ℝ)*m)≤
      Real.exp (-(6/1000000:ℝ)*m)*Q := by
    have h:=mul_le_mul_of_nonneg_left (hL.trans hQL)
      (Real.exp_pos (-(6/1000000:ℝ)*m)).le
    have hexp : Real.exp (-(6/1000000:ℝ)*m)*Real.exp (-(m:ℝ)*(3/1000000:ℝ))=
        Real.exp (-(9/1000000:ℝ)*m) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hexp] at h
    exact h
  have hmain0:=mul_nonneg (Real.exp_pos (-γ*m)).le hQ.le
  have hrare0:=mul_nonneg (Real.exp_pos (-(6/1000000:ℝ)*m)).le hQ.le
  apply abs_le.mpr
  constructor <;> dsimp only [Q] at * <;> nlinarith

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
