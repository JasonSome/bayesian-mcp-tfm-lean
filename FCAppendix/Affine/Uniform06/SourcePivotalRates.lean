import FCAppendix.Affine.Uniform06.PurePivotalSource
import FCAppendix.Affine.Uniform06.SourceRankRates
import FCAppendix.Affine.Uniform06.SupportIntervalDomination

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePivotalRates

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open PureRankCounts PureRankProbability PivotalCrossing PurePivotalSource SourceRankRates

theorem source_cutoff_at_least_milli (i : Row) : (1/1000:ℝ) ≤ cutoff i := by
  have hh := (LowChernoff.sourceTBox_ok i).1
  cases i <;> norm_num [LowChernoff.sourceTBox,Box.Holds] at hh ⊢ <;> linarith

theorem source_prefix_rank_parameter (i : Row) {w : ℝ}
    (hw : 0 ≤ w) (hM : w ≤ RankCutoff.Mstar i) :
    ((1+cutoff i)/2-w) ∈ Ioo (0:ℝ) 1 ∧
      rho+1/10000 ≤ (1+cutoff i)/2-w := by
  have htop := hM.trans (RankCutoff.Mstar_bounds i).2.le
  have hlow := source_cutoff_at_least_milli i
  have ht1 := cutoff_lt_one i
  norm_num only [rho]
  constructor
  · constructor <;> linarith
  · linarith

theorem source_deleted_conditional_exponent (i : Row)
    {m : ℕ} (hm : 4 ≤ m) {w θ γ : ℝ}
    (hw : 0 ≤ w) (hM : w ≤ RankCutoff.Mstar i) (hθ : 0 ≤ θ)
    (hγ : γ=(1-rho)*((1-cutoff i)/2)/((1-cutoff i)/2+RankCutoff.Mstar i)*
      (1-Real.exp (-θ))-rho*θ) :
    θ*(capacity m-1:ℕ)-((m-2)-(capacity m-1):ℕ)*
      (((1-cutoff i)/2)/((1-cutoff i)/2+w))*(1-Real.exp (-θ)) ≤ 1-γ*m := by
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcm := PhysicalRates.capacity_strictly_below_rivals hm
  have hbase := source_relative_exponent hc (show capacity m ≤ m by omega)
    (cutoff_lt_one i) (show 0 ≤ rho by norm_num [rho]) (show rho ≤ 1 by norm_num [rho])
    hw hM hθ (PhysicalRates.capacity_floor_bounds m).2 hγ
  have hn : (m-1)-(capacity m-1)=((m-2)-(capacity m-1))+1 := by omega
  have hd : 0 < (1-cutoff i)/2+w := by linarith [cutoff_lt_one i]
  have hq0 : 0 ≤ ((1-cutoff i)/2)/((1-cutoff i)/2+w) :=
    div_nonneg (by linarith [cutoff_lt_one i]) hd.le
  have hq1 : ((1-cutoff i)/2)/((1-cutoff i)/2+w) ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith
  have he0 : 0 ≤ 1-Real.exp (-θ) := by
    have he := Real.exp_le_one_iff.mpr (show -θ ≤ 0 by linarith)
    linarith
  have he1 : 1-Real.exp (-θ) ≤ 1 := by linarith [Real.exp_pos (-θ)]
  have hprod := mul_le_one₀ hq1 he0 he1
  rw [hn,Nat.cast_add,Nat.cast_one] at hbase
  nlinarith

theorem eventually_boundary_lower (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G) (b : ℝ),
      sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i →
        (1/20000:ℝ)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
          (sourceRank (cutoff i) G b) ≤
          (Measure.pi fun _ : Fin (m-2) => sourceRivalLaw (cutoff i) G).real
            (boundarySet (higherAtSet b) otherUpper (capacity m-1) (capacity m)) := by
  obtain ⟨θ,γ,hθ,hγ,hdef⟩ := source_conditional_tilt i
  have htend : Tendsto (fun m : ℕ => Real.exp (1-γ*m)) atTop (𝓝 0) := by
    have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hm.const_mul_atTop hγ)
    have he : (fun m : ℕ => Real.exp (1-γ*m))=
        (fun m : ℕ => Real.exp 1*Real.exp (-(γ*m))) := by
      funext m
      rw [← Real.exp_add]
      congr 1
    rw [he]
    simpa using hh.const_mul (Real.exp 1)
  filter_upwards [htend.eventually_lt_const (by norm_num : (0:ℝ) < 1/4),
    eventually_ge_atTop (4:ℕ)] with m hexp hm
  intro G hG b hM
  letI := hG
  letI := sourceRivalLaw_probability (cutoff_mem i) G
  let w := sourceRank (cutoff i) G b
  let p := (1+cutoff i)/2-w
  have hw : 0 ≤ w := mul_nonneg (cutoff_pos i).le measureReal_nonneg
  have hp := source_prefix_rank_parameter i hw hM
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hcm := PhysicalRates.capacity_strictly_below_rivals hm
  have hN : m-2+1=m-1 := by omega
  have hk : capacity m-1 ≤ m-2 := by omega
  have hevent := PivotalCounts.boundary_good_relative (sourceRivalLaw (cutoff i) G)
    (higherAtSet b) otherUpper (measurableSet_higherAtSet b) measurableSet_otherUpper
    (disjoint_higher_other b) (Finset.univ : Finset (Fin (m-2)))
    (capacity m-1) (capacity m) hc hθ.le (by
      rw [source_higher_probability (cutoff_pos i).le (cutoff_lt_one i).le G b]
      exact hp.1.2)
  simp only [Finset.card_univ,Fintype.card_fin,
    source_higher_probability (cutoff_pos i).le (cutoff_lt_one i).le G b,
    source_other_probability (cutoff_lt_one i).le G b,
    show 1-((1+cutoff i)/2-sourceRank (cutoff i) G b)=
      (1-cutoff i)/2+sourceRank (cutoff i) G b by ring] at hevent
  have hdeleted := source_deleted_conditional_exponent i hm hw hM hθ.le hdef
  have heps := (Real.exp_le_exp.mpr hdeleted).trans_lt hexp
  have hmass0 := BinomialPivotal.pmf_nonneg (m-2) (capacity m-1) ⟨hp.1.1.le,hp.1.2.le⟩
  have hboundary : (1/2:ℝ)*PiBinomial.pmf (m-2) p (capacity m-1) ≤
      (Measure.pi fun _ : Fin (m-2) => sourceRivalLaw (cutoff i) G).real
        (boundarySet (higherAtSet b) otherUpper (capacity m-1) (capacity m)) := by
    have hhalf : (1/2:ℝ) ≤ 1-Real.exp (θ*(capacity m-1:ℕ)-
      ((m-2)-(capacity m-1):ℕ)*(((1-cutoff i)/2)/((1-cutoff i)/2+w))*(1-Real.exp (-θ))) := by
      linarith only [heps]
    have hmcoef := mul_le_mul_of_nonneg_right hhalf hmass0
    exact hmcoef.trans hevent
  have hmcast : ((m-2:ℕ):ℝ)+1=(m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
    ring
  have hccast : ((capacity m-1:ℕ):ℝ)=(capacity m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ capacity m)]
    norm_num
  have hgap : (1/10000:ℝ)*((((m-2:ℕ):ℝ)+1)) ≤ ((((m-2:ℕ):ℝ)+1))*p-(capacity m-1:ℕ) := by
    rw [hmcast,hccast]
    have hcp := (PhysicalRates.capacity_floor_bounds m).2
    have hmR : (1:ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    have hh := mul_le_mul_of_nonneg_left hp.2 (show 0 ≤ (m:ℝ)-1 by linarith)
    have hr1 : rho ≤ 1 := by norm_num [rho]
    dsimp only [p,w] at *
    nlinarith
  have hpivot := BinomialPivotal.pivotal_mass_lower_of_gap (m-2) (capacity m-1) hk hp.1
    (by norm_num : (0:ℝ) ≤ 1/10000) hgap
  rw [hN,show capacity m-1+1=capacity m by omega] at hpivot
  have hNpos : (0:ℝ) < (((m-2:ℕ):ℝ)+1) := by positivity
  have hcancel : (1/10000:ℝ)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w ≤
      PiBinomial.pmf (m-2) p (capacity m-1) := by
    apply (mul_le_mul_iff_of_pos_left hNpos).mp
    dsimp only [Rank.pureRank,p,w] at *
    nlinarith [hpivot]
  exact (by nlinarith : (1/20000:ℝ)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) w ≤
    (1/2:ℝ)*PiBinomial.pmf (m-2) p (capacity m-1)).trans hboundary

theorem eventually_first_pivotal_short_rank_interval (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      (∀ b : ℝ, G {b}=0) → ∀ x y : ℝ, 0 < x → x < y →
      sourceRank (cutoff i) G y ≤ RankCutoff.Mstar i →
      (m-2:ℕ)*(cutoff i*G.real (Ioc x y)) ≤ (1/40000:ℝ)*Lm i m →
        ((m:ℝ)/80000)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
          (sourceRank (cutoff i) G y)*(cutoff i*G.real (Ioc x y)) ≤
          expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G y-
            expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G x := by
  filter_upwards [eventually_boundary_lower i,eventually_ge_atTop (4:ℕ)] with m hboundary hm
  intro G hG hatom x y hx hxy hM hsmall
  letI := hG
  have hc := PhysicalRates.capacity_positive (show 3 ≤ m by omega)
  have hh := actual_unequal_pure_pivotal_interval (cutoff_mem i)
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) hx hxy G
    (hatom x) (hatom y) (m-2) (capacity m) hc
  rw [show m-2+1=m-1 by omega] at hh
  have hQ := unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) G y (m-1) (capacity m)
  have hb := hboundary G hG y hM
  have hΔ : 0 ≤ cutoff i*G.real (Ioc x y) := mul_nonneg (cutoff_pos i).le measureReal_nonneg
  have hQ0 : 0 ≤ Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
      (sourceRank (cutoff i) G y) := by
    have hp := source_prefix_rank_parameter i
      (show 0 ≤ sourceRank (cutoff i) G y by exact mul_nonneg (cutoff_pos i).le measureReal_nonneg) hM
    exact (Rank.pureRank_pos _ _ hc hp.1).le
  have hmcast : ((m-2:ℕ):ℝ)+1=(m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num
    ring
  have hrest : (1/40000:ℝ)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
      (sourceRank (cutoff i) G y) ≤
      (Measure.pi fun _ : Fin (m-2) => sourceRivalLaw (cutoff i) G).real
        (boundarySet (higherAtSet y) otherUpper (capacity m-1) (capacity m))-
      (m-2:ℕ)*(cutoff i*G.real (Ioc x y)) := by
    change Lm i m ≤ _ at hQ
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hrest
    (show 0 ≤ ((((m-2:ℕ):ℝ)+1))*(cutoff i*G.real (Ioc x y)) by positivity)
  have hm2 : (m:ℝ)/2 ≤ ((m-2:ℕ):ℝ)+1 := by
    rw [hmcast]
    have hmR : (2:ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
    linarith
  have hfactor := mul_le_mul_of_nonneg_right hm2 (mul_nonneg hQ0 hΔ)
  have hbefore : ((m:ℝ)/80000)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
      (sourceRank (cutoff i) G y)*(cutoff i*G.real (Ioc x y)) ≤
      ((((m-2:ℕ):ℝ)+1))*(cutoff i*G.real (Ioc x y))*
      ((1/40000:ℝ)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
        (sourceRank (cutoff i) G y)) := by nlinarith
  exact hbefore.trans (hmul.trans hh)

theorem exists_short_interval_rank_mass
    (G : Measure ℝ) [IsFiniteMeasure G] (hatom : ∀ b : ℝ, G {b}=0)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, x ∈ Icc 0 B → y ∈ Icc 0 B → x ≤ y →
      y-x ≤ δ → t*G.real (Ioc x y) ≤ ε := by
  let F := fun x => t*SupportIntervalDomination.cumulative G x
  have hF : Continuous F := continuous_const.mul
    (SupportIntervalDomination.continuous_cumulative G hatom)
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x y hx hy hxy hstep
  have hd : dist y x ≤ δ := by
    rwa [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hxy)]
  have hh := hmod y hy x hx hd
  have he : F y-F x=t*G.real (Ioc x y) := by
    dsimp only [F]
    rw [← mul_sub,SupportIntervalDomination.cumulative_increment G hxy]
  rw [Real.dist_eq,he,abs_of_nonneg (mul_nonneg ht measureReal_nonneg)] at hh
  exact hh

theorem eventually_first_pivotal_short_bid_interval (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure ℝ) (_hG : IsProbabilityMeasure G),
      (∀ b : ℝ, G {b}=0) → ∀ B : ℝ,
      (∀ b, b ∈ Ioc 0 B → sourceRank (cutoff i) G b ≤ RankCutoff.Mstar i) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, 0 < x → x < y → y ≤ B → y-x ≤ δ →
        ((m:ℝ)/80000)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
          (sourceRank (cutoff i) G y)*(cutoff i*G.real (Ioc x y)) ≤
          expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G y-
            expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) G x := by
  filter_upwards [eventually_first_pivotal_short_rank_interval i,eventually_Lm_lower i,
    eventually_ge_atTop (4:ℕ)] with m hfirst hLm hm
  intro G hG hatom B hB
  letI := hG
  have hL : 0 < Lm i m := (Real.exp_pos _).trans_le hLm
  have hN : (0:ℝ) < (m-2:ℕ) := by exact_mod_cast (by omega : 0 < m-2)
  obtain ⟨δ,hδ,hsmall⟩ := exists_short_interval_rank_mass G hatom (cutoff_pos i).le
    (show 0 < Lm i m/(40000*(m-2:ℕ)) by positivity) B
  refine ⟨δ,hδ,?_⟩
  intro x y hx hxy hyB hxyδ
  have hmass := hsmall x y ⟨hx.le,hxy.le.trans hyB⟩ ⟨(hx.trans hxy).le,hyB⟩ hxy.le hxyδ
  have hcollision : (m-2:ℕ)*(cutoff i*G.real (Ioc x y)) ≤ (1/40000:ℝ)*Lm i m := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 40000) hN)).mp hmass
    nlinarith
  exact hfirst G hG hatom x y hx hxy (hB y ⟨hx.trans hxy,hyB⟩) hcollision

end FCAppendix.Affine.Uniform06.SourcePivotalRates
