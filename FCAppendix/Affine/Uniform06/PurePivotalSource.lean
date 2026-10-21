import FCAppendix.Affine.Uniform06.PivotalCrossing
import FCAppendix.Affine.Uniform06.GuardPrefix

noncomputable section
namespace FCAppendix.Affine.Uniform06.PurePivotalSource

open MeasureTheory Set Filter LowBody
open PureDuplicateIntervals PureRankCounts PureRankSelector PureRankProbability
open PivotalCrossing LiteralExperiment
open scoped BigOperators

variable {N : ℕ}

def rowUnequalPureFirst (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  if rowResidual c 0 ω=rowResidual c 1 ω then 0 else first 0 (rowPureSelection κ c b ω)

theorem measurable_rowUnequalPureFirst (κ : ℝ) (c : ℕ) (b : ℝ) :
    Measurable (rowUnequalPureFirst (N := N) κ c b) := by
  have hkind : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst
  have hres : MeasurableSet {ω : Fin N → RowRival | rowResidual c 0 ω=rowResidual c 1 ω} := by
    have hh := (measurable_of_countable (fun k : Fin N → Fin 4 =>
      (patternTemplate c k).residual₀=(patternTemplate c k).residual₁)).comp hkind
    exact hh.setOf
  exact Measurable.ite hres measurable_const
    ((measurable_of_countable (first (0:Fin (N+1)))).comp (measurable_rowPureSelection κ c b))

theorem rowUnequalPureFirst_bounds (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) :
    rowUnequalPureFirst κ c b ω ∈ Icc (0:ℝ) 1 := by
  unfold rowUnequalPureFirst
  split_ifs
  · norm_num
  · rw [first_eq_indicator]
    split_ifs <;> norm_num

theorem integrable_rowUnequalPureFirst (κ : ℝ) (c : ℕ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (rowUnequalPureFirst κ c b) P :=
  Integrable.of_bound (C := 1) (measurable_rowUnequalPureFirst κ c b).aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (rowUnequalPureFirst_bounds κ c b ω).1]
      exact (rowUnequalPureFirst_bounds κ c b ω).2)

theorem rowUnequalPureFirst_monotone {κ : ℝ} (hκ : 0 < κ) (c : ℕ)
    (ω : Fin N → RowRival) : Monotone (fun b => rowUnequalPureFirst κ c b ω) := by
  intro x y hxy
  unfold rowUnequalPureFirst
  split_ifs
  · rfl
  · have hh := (GuardPrefix.pure_first_duplicate_monotone hκ
      (patternTemplate c (fun j => (ω j).1)) (rowBids x ω) 0).1 hxy
    simpa only [rowPureSelection,rowBids_update,Function.update_eq_self] using hh

def countCrossing (c : ℕ) (x y : ℝ) : Set (Fin N → RowRival) :=
  {ω | PiBinomial.count (higherAtSet y) Finset.univ ω< c ∧
    c ≤ PiBinomial.count (higherAtSet x) Finset.univ ω ∧
    c ≤ PiBinomial.count otherUpper Finset.univ ω}

theorem measurableSet_countCrossing (c : ℕ) (x y : ℝ) :
    MeasurableSet (countCrossing (N := N) c x y) :=
  ((PiBinomial.measurable_count (higherAtSet y) (measurableSet_higherAtSet y) Finset.univ)
    measurableSet_Iio).inter
      (((PiBinomial.measurable_count (higherAtSet x) (measurableSet_higherAtSet x) Finset.univ)
        measurableSet_Ici).inter
          ((PiBinomial.measurable_count otherUpper measurableSet_otherUpper Finset.univ)
            measurableSet_Ici))

theorem countCrossing_first_gain
    {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x ≤ y) (c : ℕ)
    (ω : Fin N → RowRival)
    (htx : ∀ j, (ω j).1=0 → (ω j).2≠x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2≠y) :
    (countCrossing c x y).indicator (fun _ => (1:ℝ)) ω ≤
      rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω := by
  by_cases he : ω ∈ countCrossing c x y
  · rw [indicator_of_mem he]
    have hy := main_event_in_unequal_pure c κ (hx.trans_le hxy) ω hty he.1 he.2.2
    have hxl : (0:Fin (N+1)) ∉ (rowPureSelection κ c x ω).1 := by
      intro hh
      have hc := (pure_left_on_opposite_full_iff_rank c κ hx ω htx he.2.2).mp hh
      have hcross : c ≤ PiBinomial.count (higherAtSet x) Finset.univ ω := he.2.1
      omega
    have hY : c ≤ classCount 3 ω := by
      have hh := he.2.2
      rwa [otherUpper_count] at hh
    have hzero : (patternTemplate c (fun j => (ω j).1)).residual₁=0 := by
      change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 3 ω)=0
      omega
    have hempty (z : ℝ) : (rowPureSelection κ c z ω).2=∅ :=
      (patternTemplate c (fun j => (ω j).1)).selection_empty_right κ (rowBids z ω) hzero
    simp only [rowUnequalPureFirst,if_neg hy.1,first_eq_indicator,
      hempty x,hempty y,Finset.union_empty,if_neg hxl,if_pos hy.2]
    norm_num
  · rw [indicator_of_notMem he]
    exact sub_nonneg.mpr (rowUnequalPureFirst_monotone hκ c ω hxy)

def expectedUnequalPureFirst (N c : ℕ) (κ t : ℝ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, rowUnequalPureFirst κ c b ω
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

theorem countCrossing_probability_le_success_increment
    {t κ x y : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hκ : 0 < κ)
    (hx : 0 < x) (hxy : x ≤ y) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatomx : G {x}=0) (hatomy : G {y}=0) (N c : ℕ) :
    (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real (countCrossing c x y) ≤
      expectedUnequalPureFirst N c κ t G y-expectedUnequalPureFirst N c κ t G x := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hp : ∀ᵐ ω ∂P, (countCrossing c x y).indicator (fun _ => (1:ℝ)) ω ≤
      rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω := by
    filter_upwards [source_iid_row_no_tie ht G hatomx,source_iid_row_no_tie ht G hatomy]
      with ω hωx hωy
    exact countCrossing_first_gain hκ hx hxy c ω hωx.2 hωy.2
  have hh := integral_mono_ae
    ((integrable_const (1:ℝ)).indicator (measurableSet_countCrossing c x y))
    ((integrable_rowUnequalPureFirst κ c y P).sub (integrable_rowUnequalPureFirst κ c x P)) hp
  simp only [Pi.sub_apply] at hh
  rw [integral_indicator_const 1 (measurableSet_countCrossing c x y),smul_eq_mul,mul_one,
    integral_sub (integrable_rowUnequalPureFirst κ c y P) (integrable_rowUnequalPureFirst κ c x P)] at hh
  exact hh

theorem higherAt_antitone {x y : ℝ} (hxy : x ≤ y) : higherAtSet y ⊆ higherAtSet x := by
  intro r hr
  rcases hr with h1 | h2 | ⟨h0,hb⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨h0,hxy.trans_lt hb⟩)

theorem actual_unequal_pure_pivotal_interval
    {t κ x y : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hκ : 0 < κ)
    (hx : 0 < x) (hxy : x < y) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatomx : G {x}=0) (hatomy : G {y}=0) (N c : ℕ) (hc : 0 < c) :
    ((N:ℝ)+1)*(t*G.real (Ioc x y))*
      ((Measure.pi fun _ : Fin N => sourceRivalLaw t G).real
          (boundarySet (higherAtSet y) otherUpper (c-1) c)-
        (N:ℝ)*(t*G.real (Ioc x y))) ≤
      expectedUnequalPureFirst (N+1) c κ t G y-
        expectedUnequalPureFirst (N+1) c κ t G x := by
  letI := sourceRivalLaw_probability ht G
  have hCsub : lowCluster (Ioc x y) ⊆ higherAtSet x := by
    rintro r ⟨h0,hx',hy'⟩
    exact Or.inr (Or.inr ⟨h0,hx'⟩)
  have hdis : Disjoint (lowCluster (Ioc x y)) (higherAtSet y) := by
    apply Set.disjoint_left.mpr
    rintro ⟨k,b⟩ ⟨hk,hx',hy'⟩ hr
    change k=0 at hk
    subst k
    change (0:Fin 4)=1 ∨ (0:Fin 4)=2 ∨ ((0:Fin 4)=0 ∧ y< b) at hr
    norm_num [Fin.ext_iff] at hr
    linarith
  have hh := count_crossing_lower (N := N) (sourceRivalLaw t G)
    (higherAtSet y) (higherAtSet x) (lowCluster (Ioc x y)) otherUpper
    (measurableSet_higherAtSet y) (measurableSet_higherAtSet x)
    (measurableSet_lowCluster (Ioc x y) measurableSet_Ioc) measurableSet_otherUpper
    (higherAt_antitone hxy.le) hCsub hdis c hc
  have hmass : (sourceRivalLaw t G).real (lowCluster (Ioc x y))=t*G.real (Ioc x y) :=
    lowCluster_probability t 0 (1-t) ht.1 G (Ioc x y) measurableSet_Ioc
  rw [hmass] at hh
  exact hh.trans (countCrossing_probability_le_success_increment ht hκ hx hxy.le
    G hatomx hatomy (N+1) c)

theorem actual_unequal_pure_pivotal_tilted
    {t κ x y θ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hκ : 0 < κ)
    (hx : 0 < x) (hxy : x < y) (hθ : 0 ≤ θ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatomx : G {x}=0) (hatomy : G {y}=0)
    (N c : ℕ) (hc : 0 < c) :
    ((N:ℝ)+1)*(t*G.real (Ioc x y))*
      ((1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
        (((1-t)/2)/((1-t)/2+sourceRank t G y))*(1-Real.exp (-θ))))*
          PiBinomial.pmf N ((1+t)/2-sourceRank t G y) (c-1)-
        (N:ℝ)*(t*G.real (Ioc x y))) ≤
      expectedUnequalPureFirst (N+1) c κ t G y-
        expectedUnequalPureFirst (N+1) c κ t G x := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  have hE1 : (sourceRivalLaw t G).real (higherAtSet y) < 1 := by
    rw [source_higher_probability ht ht1.le G y]
    have hw : 0 ≤ sourceRank t G y := mul_nonneg ht measureReal_nonneg
    linarith
  have hb := PivotalCounts.boundary_good_relative (sourceRivalLaw t G)
    (higherAtSet y) otherUpper (measurableSet_higherAtSet y) measurableSet_otherUpper
    (disjoint_higher_other y) (Finset.univ : Finset (Fin N)) (c-1) c hc hθ hE1
  simp only [Finset.card_univ,Fintype.card_fin,source_higher_probability ht ht1.le G y,
    source_other_probability ht1.le G y,
    show 1-((1+t)/2-sourceRank t G y)=(1-t)/2+sourceRank t G y by ring] at hb
  have hm := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hb ((N:ℝ)*(t*G.real (Ioc x y))))
      (show 0 ≤ ((N:ℝ)+1)*(t*G.real (Ioc x y)) by positivity)
  exact hm.trans (actual_unequal_pure_pivotal_interval ⟨ht,ht1.le⟩ hκ hx hxy
    G hatomx hatomy N c hc)

end FCAppendix.Affine.Uniform06.PurePivotalSource
