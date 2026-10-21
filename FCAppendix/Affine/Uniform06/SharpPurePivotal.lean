import FCAppendix.Affine.Uniform06.SharpPureIntervals

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpPurePivotal

open MeasureTheory Set Filter LowBody
open PureRankCounts PureRankSelector PureRankProbability PurePivotalSource
open PureUnionUpper SharpPureIntervals PivotalCrossing
open scoped BigOperators

variable {N : ℕ}

def ownUpper : Set RowRival := {r | r.1=2}

theorem measurableSet_ownUpper : MeasurableSet ownUpper :=
  measurableSet_eq_fun measurable_fst measurable_const

theorem ownUpper_count (ω : Fin N → RowRival) :
    PiBinomial.count ownUpper Finset.univ ω=classCount 2 ω := by
  simp [PiBinomial.count,ownUpper,classCount]

theorem disjoint_higherRight_own (b : ℝ) : Disjoint (higherRightAtSet b) ownUpper := by
  apply Set.disjoint_left.mpr
  rintro ⟨k,x⟩ hr ho
  change k=2 at ho
  subst k
  simp only [higherRightAtSet,Set.mem_setOf_eq,Fin.ext_iff] at hr
  norm_num at hr

theorem source_own_probability {t : ℝ} (ht1 : t ≤ 1)
    (G : Measure ℝ) : (sourceRivalLaw t G).real ownUpper=(1-t)/2 := by
  have hl : Measurable (fun b : ℝ => ((0:Fin 4),b)) := measurable_const.prodMk measurable_id
  have hp : (fun b : ℝ => ((0:Fin 4),b)) ⁻¹' ownUpper=∅ := by
    ext b
    norm_num [ownUpper,Fin.ext_iff]
  have he : sourceRivalLaw t G ownUpper=ENNReal.ofReal ((1-t)/2) := by
    simp only [sourceRivalLaw,rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hl measurableSet_ownUpper,hp]
    norm_num [Measure.dirac_apply,ownUpper,Set.indicator,Fin.ext_iff]
  rw [measureReal_def,he,ENNReal.toReal_ofReal (by linarith)]

def rightCountCrossing (c : ℕ) (x y : ℝ) : Set (Fin N → RowRival) :=
  {ω | PiBinomial.count (higherRightAtSet y) Finset.univ ω< c ∧
    c ≤ PiBinomial.count (higherRightAtSet x) Finset.univ ω ∧
    c ≤ PiBinomial.count ownUpper Finset.univ ω}

theorem measurableSet_rightCountCrossing (c : ℕ) (x y : ℝ) :
    MeasurableSet (rightCountCrossing (N := N) c x y) :=
  ((PiBinomial.measurable_count (higherRightAtSet y) (measurableSet_higherRightAtSet y) Finset.univ)
    measurableSet_Iio).inter
      (((PiBinomial.measurable_count (higherRightAtSet x) (measurableSet_higherRightAtSet x) Finset.univ)
        measurableSet_Ici).inter
          ((PiBinomial.measurable_count ownUpper measurableSet_ownUpper Finset.univ) measurableSet_Ici))

theorem rightCountCrossing_first_gain
    {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x ≤ y) (c : ℕ)
    (ω : Fin N → RowRival)
    (htx : ∀ j, (ω j).1=0 → (ω j).2≠x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2≠y) :
    (rightCountCrossing c x y).indicator (fun _ => (1:ℝ)) ω ≤
      rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω := by
  by_cases he : ω ∈ rightCountCrossing c x y
  · rw [indicator_of_mem he]
    have hfull : c ≤ classCount 2 ω := by simpa only [ownUpper_count] using he.2.2
    have hyR := (right_selected_iff_rank_on_left_full c κ (hx.trans_le hxy) ω hty hfull).mpr he.1
    have hxR : (0:Fin (N+1)) ∉ (PureDuplicateIntervals.rowPureSelection κ c x ω).2 := by
      intro hs
      have hh := (right_selected_iff_rank_on_left_full c κ hx ω htx hfull).mp hs
      have hxfull := he.2.1
      omega
    let T := patternTemplate c (fun j => (ω j).1)
    have hzero : T.residual₀=0 := by
      change min (1+classCount 0 ω) (c-classCount 1 ω-classCount 2 ω)=0
      omega
    have hpos : 0 < T.residual₁ :=
      (Finset.card_pos.mpr ⟨0,hyR⟩).trans_le (T.selection_feasible κ (rowBids y ω)).2.2.1
    have hne : rowResidual c 0 ω≠rowResidual c 1 ω := by change T.residual₀≠T.residual₁; omega
    have hempty (z : ℝ) : (PureDuplicateIntervals.rowPureSelection κ c z ω).1=∅ :=
      T.selection_empty_left κ (rowBids z ω) hzero
    simp only [rowUnequalPureFirst,if_neg hne,LiteralExperiment.first_eq_indicator,
      hempty x,hempty y,Finset.empty_union,if_neg hxR,if_pos hyR]
    norm_num
  · rw [indicator_of_notMem he]
    exact sub_nonneg.mpr (rowUnequalPureFirst_monotone hκ c ω hxy)

theorem crossings_disjoint (c : ℕ) (x y : ℝ) :
    Disjoint (countCrossing (N := N) c x y) (rightCountCrossing c x y) := by
  apply Set.disjoint_left.mpr
  intro ω hL hR
  have hLc := hL.1
  rw [higherAtCount_eq] at hLc
  have hRc := hR.2.2
  rw [ownUpper_count] at hRc
  omega

theorem two_crossings_first_gain
    {κ x y : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hxy : x ≤ y) (c : ℕ)
    (ω : Fin N → RowRival)
    (htx : ∀ j, (ω j).1=0 → (ω j).2≠x)
    (hty : ∀ j, (ω j).1=0 → (ω j).2≠y) :
    (countCrossing c x y).indicator (fun _ => (1:ℝ)) ω+
      (rightCountCrossing c x y).indicator (fun _ => (1:ℝ)) ω ≤
        rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω := by
  have hL := countCrossing_first_gain hκ hx hxy c ω htx hty
  have hR := rightCountCrossing_first_gain hκ hx hxy c ω htx hty
  by_cases h : ω ∈ countCrossing c x y
  · have hn := Set.disjoint_left.mp (crossings_disjoint c x y) h
    simpa only [indicator_of_notMem hn,add_zero] using hL
  · simpa only [indicator_of_notMem h,zero_add] using hR

theorem two_crossings_probability_le_increment
    {t κ x y : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hκ : 0 < κ)
    (hx : 0 < x) (hxy : x ≤ y) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hatomx : G {x}=0) (hatomy : G {y}=0) (N c : ℕ) :
    (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real (countCrossing c x y)+
      (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real (rightCountCrossing c x y) ≤
      expectedUnequalPureFirst N c κ t G y-expectedUnequalPureFirst N c κ t G x := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hiL := (integrable_const (1:ℝ) (μ := P)).indicator (measurableSet_countCrossing c x y)
  have hiR := (integrable_const (1:ℝ) (μ := P)).indicator (measurableSet_rightCountCrossing c x y)
  have hh := integral_mono_ae (hiL.add hiR)
    ((integrable_rowUnequalPureFirst κ c y P).sub (integrable_rowUnequalPureFirst κ c x P))
    (show ∀ᵐ ω ∂P, _ from by
      filter_upwards [source_iid_row_no_tie ht G hatomx,source_iid_row_no_tie ht G hatomy]
        with ω hxω hyω
      exact two_crossings_first_gain hκ hx hxy c ω hxω.2 hyω.2)
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  rw [integral_add hiL hiR,integral_indicator_const (1:ℝ) (measurableSet_countCrossing c x y),
    integral_indicator_const (1:ℝ) (measurableSet_rightCountCrossing c x y),
    integral_sub (integrable_rowUnequalPureFirst κ c y P) (integrable_rowUnequalPureFirst κ c x P)] at hh
  simpa only [smul_eq_mul,mul_one] using! hh

theorem tilted_crossing_lower
    {t x y θ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (_hxy : x < y) (hθ : 0 ≤ θ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) (hc : 0 < c)
    (Elo Ehi B : Set RowRival) (hElo : MeasurableSet Elo) (hEhi : MeasurableSet Ehi)
    (hB : MeasurableSet B) (hmono : Elo ⊆ Ehi)
    (hCsub : lowCluster (Ioc x y) ⊆ Ehi) (hCE : Disjoint (lowCluster (Ioc x y)) Elo)
    (hEB : Disjoint Elo B)
    (hE : (sourceRivalLaw t G).real Elo=(1+t)/2-sourceRank t G y)
    (hprobB : (sourceRivalLaw t G).real B=(1-t)/2) :
    ((N:ℝ)+1)*(t*G.real (Ioc x y))*
      ((1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
        (((1-t)/2)/((1-t)/2+sourceRank t G y))*(1-Real.exp (-θ))))*
          PiBinomial.pmf N ((1+t)/2-sourceRank t G y) (c-1)-
        (N:ℝ)*(t*G.real (Ioc x y))) ≤
      (Measure.pi fun _ : Fin (N+1) => sourceRivalLaw t G).real
        {ω | PiBinomial.count Elo Finset.univ ω< c ∧
          c ≤ PiBinomial.count Ehi Finset.univ ω ∧ c ≤ PiBinomial.count B Finset.univ ω} := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  have hE1 : (sourceRivalLaw t G).real Elo<1 := by
    rw [hE]
    have hw : 0 ≤ sourceRank t G y := mul_nonneg ht measureReal_nonneg
    linarith
  have hb := PivotalCounts.boundary_good_relative (sourceRivalLaw t G)
    Elo B hElo hB hEB (Finset.univ : Finset (Fin N)) (c-1) c hc hθ hE1
  simp only [Finset.card_univ,Fintype.card_fin,hE,hprobB,
    show 1-((1+t)/2-sourceRank t G y)=(1-t)/2+sourceRank t G y by ring] at hb
  have hh := count_crossing_lower (N := N) (sourceRivalLaw t G) Elo Ehi
    (lowCluster (Ioc x y)) B hElo hEhi (measurableSet_lowCluster _ measurableSet_Ioc) hB
    hmono hCsub hCE c hc
  change ((N:ℝ)+1)*(rivalLaw t 0 (1-t) G).real (lowCluster (Ioc x y))*_ ≤ _ at hh
  simp only [sourceRivalLaw,lowCluster_probability t 0 (1-t) ht G (Ioc x y) measurableSet_Ioc] at hh
  change _ ≤ _ at hb
  simpa only [boundarySet,sourceRivalLaw] using!
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hb _)
      (mul_nonneg (by positivity : (0:ℝ) ≤ N+1) (mul_nonneg ht measureReal_nonneg))).trans hh

theorem actual_two_pivotal_interval
    {t κ x y θ : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (hκ : 0 < κ)
    (hx : 0 < x) (hxy : x < y) (hθ : 0 ≤ θ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatomx : G {x}=0) (hatomy : G {y}=0)
    (N c : ℕ) (hc : 0 < c) :
    2*((N:ℝ)+1)*(t*G.real (Ioc x y))*
      ((1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
        (((1-t)/2)/((1-t)/2+sourceRank t G y))*(1-Real.exp (-θ))))*
          PiBinomial.pmf N ((1+t)/2-sourceRank t G y) (c-1)-
        (N:ℝ)*(t*G.real (Ioc x y))) ≤
      expectedUnequalPureFirst (N+1) c κ t G y-
        expectedUnequalPureFirst (N+1) c κ t G x := by
  have hCL : lowCluster (Ioc x y) ⊆ higherAtSet x := by
    rintro r ⟨h0,hb,_⟩
    exact Or.inr (Or.inr ⟨h0,hb⟩)
  have hCR : lowCluster (Ioc x y) ⊆ higherRightAtSet x := by
    rintro r ⟨h0,hb,_⟩
    exact Or.inr (Or.inr ⟨h0,hb⟩)
  have hdL : Disjoint (lowCluster (Ioc x y)) (higherAtSet y) := by
    apply Set.disjoint_left.mpr
    rintro ⟨k,b⟩ ⟨hk,_,hy⟩ h
    change k=0 at hk
    subst k
    simp only [higherAtSet,Set.mem_setOf_eq,Fin.ext_iff] at h
    norm_num at h
    linarith
  have hdR : Disjoint (lowCluster (Ioc x y)) (higherRightAtSet y) := by
    apply Set.disjoint_left.mpr
    rintro ⟨k,b⟩ ⟨hk,_,hy⟩ h
    change k=0 at hk
    subst k
    simp only [higherRightAtSet,Set.mem_setOf_eq,Fin.ext_iff] at h
    norm_num at h
    linarith
  have hL := tilted_crossing_lower ht ht1 hxy hθ G N c hc
    (higherAtSet y) (higherAtSet x) otherUpper
    (measurableSet_higherAtSet y) (measurableSet_higherAtSet x) measurableSet_otherUpper
    (higherAt_antitone hxy.le) hCL hdL (disjoint_higher_other y)
    (source_higher_probability ht ht1.le G y) (source_other_probability ht1.le G y)
  have hR := tilted_crossing_lower ht ht1 hxy hθ G N c hc
    (higherRightAtSet y) (higherRightAtSet x) ownUpper
    (measurableSet_higherRightAtSet y) (measurableSet_higherRightAtSet x) measurableSet_ownUpper
    (higherRightAt_antitone hxy.le) hCR hdR (disjoint_higherRight_own y)
    (source_higherRight_probability ht ht1.le G y) (source_own_probability ht1.le G)
  have hgain := two_crossings_probability_le_increment ⟨ht,ht1.le⟩ hκ hx hxy.le G
    hatomx hatomy (N+1) c
  change _ ≤ (Measure.pi fun _ : Fin (N+1) => sourceRivalLaw t G).real (countCrossing c x y) at hL
  change _ ≤ (Measure.pi fun _ : Fin (N+1) => sourceRivalLaw t G).real (rightCountCrossing c x y) at hR
  nlinarith

end FCAppendix.Affine.Uniform06.SharpPurePivotal
