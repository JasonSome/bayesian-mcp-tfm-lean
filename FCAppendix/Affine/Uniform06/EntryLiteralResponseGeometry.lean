import FCAppendix.Affine.Uniform06.EntryLiteralCentral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralResponseGeometry

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralKernelIdentity EntryRawCentral EntryProfileMean
open EntryEarlySourceLimits EntrySamplingLaw EntryReciprocalLimit ReciprocalSecantBounds
open ActualEntryGoodGeometry EntryOwnImpact
open scoped BigOperators

structure Inputs (μ : Measure RowRival) (i : Row) (g : GuardData)
    (N C : ℕ) (b A U ε c q lo γ w s : ℝ) : Prop where
  rivals_pos : 0 < N
  epsilon_nonneg : 0 ≤ ε
  lo_pos : 0 < lo
  cap_pos : 0 < U
  strip_pos : 0 < q
  radius_pos : 0 < g.radius
  «prefix» : LiteralPrefixStieltjes.PrefixConditions (xi i) g (g.multiplier+g.radius)
  requiredDemand_eq : g.requiredDemand=PrefixRoot.requiredDemand i
  lower_price : lo ≤ g.multiplier-g.radius
  cap_receipt : (1-xi i)*U ≤ g.multiplier-g.radius
  half_receipt : (1-xi i/2)*U ≤ b
  bid_window : b ∈ Icc (g.multiplier-g.radius) (g.multiplier+g.radius)
  bid_cap : b ≤ U
  strip_above : g.multiplier+g.radius < A
  means : MeanMargins μ (xi i) g A U (cutoff i) ((1-cutoff i)/2)
    rho γ w s q
  floor_error : |(C:ℝ)-(N:ℝ)*rho| ≤ 1
  residual_positive : ε*(N:ℝ)+2 < (N:ℝ)*(rho-(1-cutoff i)/2)
  residual_room : 2*ε*(N:ℝ)+3 ≤ (N:ℝ)*(cutoff i-(rho-(1-cutoff i)/2))
  demand_margin : 2*g.margin*g.population ≤ γ*(N:ℝ)-2*error N ε-1
  weight_margin : 2*g.margin*g.population ≤ w*(N:ℝ)-3*error N ε
  rejection_margin : 2*g.margin*g.population ≤
    (rho-(1-cutoff i)/2)*(N:ℝ)-3*error N ε
  seed_margin : 0 < (s-ε)*(N:ℝ)
  strip_margin : 6*error N ε+2 ≤ q*(N:ℝ)
  count_margin : 2*g.margin*g.population ≤ g.countMargin
  sample_weight_margin : c*(N:ℝ) ≤ w*(N:ℝ)-ε*(N:ℝ)

variable {N C : ℕ}

def profile (i : Row) (g : GuardData) (b : ℝ) :
    (Fin N → RowRival) → Weights (Fin (N+1)) :=
  profileWeights (focalWeight i b g.multiplier) (rawWeight i g.multiplier)
    (focalWeight_bounds i b g.multiplier) (rawWeight_bounds i g.multiplier)

lemma measurable_profile (i : Row) (g : GuardData) (b : ℝ) :
    Measurable (profile (N := N) i g b) :=
  measurable_profileWeights _ _ _ _ (measurable_rawWeight i g.multiplier) N

def sampleSet (i : Row) (g : GuardData) (b : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : Finset (Fin (N+1)) :=
  removed (profile i g b) RawMixedSource.draws x

lemma measurable_sampleSet (i : Row) (g : GuardData) (b : ℝ) :
    Measurable (sampleSet (N := N) i g b) :=
  measurable_removed (measurable_profile i g b) (RawMixedSource.measurable_draws N)

def sampleMass (i : Row) (g : GuardData) (b : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  (pathLaw (profile i g b x.1) (RawMixedSource.draws x.1) ∅).mass
    (sampler (RawMixedSource.draws x.1) (profile i g b x.1) x.2)

lemma measurable_sampleMass (i : Row) (g : GuardData) (b : ℝ) :
    Measurable (sampleMass (N := N) i g b) := by
  have hm (d : ℕ) : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      (pathLaw (profile i g b x.1) d ∅).mass (sampler d (profile i g b x.1) x.2)) := by
    have hmass : Measurable (fun z : Weights (Fin (N+1)) × Path (Fin (N+1)) d =>
        (pathLaw z.1 d ∅).mass z.2) :=
      measurable_from_prod_countable_left (fun p => measurable_pathLaw_mass d ∅ p)
    exact hmass.comp (((measurable_profile i g b).comp measurable_fst).prodMk
      ((measurable_sampler d).comp (((measurable_profile i g b).comp measurable_fst).prodMk measurable_snd)))
  exact (measurable_from_prod_countable_right (f := fun x : ℕ × EntryIIDCentral.Row (Ω := RowRival) N =>
      (pathLaw (profile i g b x.2.1) x.1 ∅).mass (sampler x.1 (profile i g b x.2.1) x.2.2)) hm).comp
    (((RawMixedSource.measurable_draws N).comp measurable_fst).prodMk measurable_id)

def rawConditions (i : Row) (g : GuardData) (b U : ℝ) :
    Set (EntryIIDCentral.Row (Ω := RowRival) N) :=
  {x | (∀ j,(x.1 j).1 ≠ 1) ∧
    (∀ j,(x.1 j).1=0 → (x.1 j).2 ≤ U) ∧ 0 < sampleMass i g b x}

lemma measurable_rawConditions (i : Row) (g : GuardData) (b U : ℝ) :
    MeasurableSet (rawConditions (N := N) i g b U) := by
  have hm := measurable_sampleMass (N := N) i g b
  unfold rawConditions
  measurability

def usable (μ : Measure RowRival) (i : Row) (g : GuardData) (b A U ε : ℝ) :
    Set (EntryIIDCentral.Row (Ω := RowRival) N) :=
  (Prod.fst ⁻¹' RivalGood.good μ (tests (xi i) g A U) N ε) ∩ rawConditions i g b U

lemma measurable_usable (μ : Measure RowRival) (i : Row) (g : GuardData) (b A U ε : ℝ) :
    MeasurableSet (usable (N := N) μ i g b A U ε) :=
  ((RivalGood.measurable_good μ (tests (xi i) g A U)
    (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _) N ε).preimage
      measurable_fst).inter (measurable_rawConditions i g b U)

def complement (i : Row) (C : ℕ) (g : GuardData) (b : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  complementMarginal (xi i) (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1)
    (sampleSet i g b x) 0

attribute [local irreducible] complementMarginal

lemma measurable_complement (i : Row) (C : ℕ) (g : GuardData) (b : ℝ) :
    Measurable (complement (N := N) i C g b) := by
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have ht : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      (fun j => (x.1 j).1,sampleSet i g b x)) :=
    (measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_fst).fst).prodMk
      (measurable_sampleSet i g b)
  have hm : Measurable (fun y : ((Fin N → Fin 4) × Finset (Fin (N+1))) × (Fin (N+1) → ℝ) =>
      complementMarginal (xi i) (patternTemplate C y.1.1) y.2 y.1.2 0) :=
    measurable_from_prod_countable_right fun p =>
      LiteralKernelMeasurable.measurable_complementMarginal (xi_pos i) hξ1 (patternTemplate C p.1) p.2 0
  exact hm.comp (ht.prodMk
    ((EntryDeletedReciprocal.measurable_listBids N b).comp measurable_fst))

lemma complement_bounds (i : Row) (C : ℕ) (g : GuardData) (b : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : complement i C g b x ∈ Icc (0:ℝ) 1 :=
  LiteralPrefixStieltjes.complement_bounds (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) _ _ _ _

def response (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ := by
  classical
  exact if x ∈ usable μ i g b A U ε then complement i C g b x else 0

def price (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  b*(1-xi i*response μ i C g b A U ε x)

def reciprocalAt (i : Row) (g : GuardData) (b z : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  reciprocalSum (EntryDeletedReciprocal.listBids 0 x.1) (sampleSet i g b x) z

def slope (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  if 0 < response μ i C g b A U ε x then
    rightSecant (xi i) (rowBids b x.1) (insert 0 (sampleSet i g b x))
      (price μ i C g b A U ε x) b
  else reciprocalAt i g b b x

lemma measurable_response (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ) :
    Measurable (response (N := N) μ i C g b A U ε) :=
  Measurable.ite (measurable_usable μ i g b A U ε) (measurable_complement i C g b) measurable_const

lemma measurable_price (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ) :
    Measurable (price (N := N) μ i C g b A U ε) :=
  (measurable_const.sub ((measurable_response μ i C g b A U ε).const_mul (xi i))).const_mul b

lemma measurable_slope (μ : Measure RowRival) (i : Row) (C : ℕ) (g : GuardData) (b A U ε : ℝ) :
    Measurable (slope (N := N) μ i C g b A U ε) := by
  have hq := measurable_response (N := N) μ i C g b A U ε
  have hp := measurable_price (N := N) μ i C g b A U ε
  have he := measurable_sampleSet (N := N) i g b
  have hb : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      EntryDeletedReciprocal.listBids b x.1) :=
    (EntryDeletedReciprocal.measurable_listBids N b).comp measurable_fst
  have h0 : Measurable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      EntryDeletedReciprocal.listBids 0 x.1) :=
    (EntryDeletedReciprocal.measurable_listBids N 0).comp measurable_fst
  have hmem (j : Fin (N+1)) : MeasurableSet {x : EntryIIDCentral.Row (Ω := RowRival) N |
      j ∈ insert 0 (sampleSet i g b x)} :=
    (Set.to_countable {E : Finset (Fin (N+1)) | j ∈ insert 0 E}).measurableSet.preimage he
  have hd (z : EntryIIDCentral.Row (Ω := RowRival) N → ℝ) (hz : Measurable z) :
      Measurable (fun x => remainingDemand (xi i) (rowBids b x.1)
        (insert 0 (sampleSet i g b x)) (z x)) := by
    apply Finset.measurable_sum
    intro j _
    apply Measurable.ite (hmem j) measurable_const
    have hh := (measurable_pi_apply j).comp hb
    unfold exposure
    exact measurable_const.min ((measurable_const.max (hh.sub hz)).div
      (measurable_const.mul (hh.max hz)))
  unfold slope rightSecant
  exact Measurable.ite (measurableSet_lt measurable_const hq)
    (Measurable.ite (measurableSet_lt hp measurable_const)
      (((hd _ hp).sub (hd _ measurable_const)).const_mul (xi i) |>.div (measurable_const.sub hp))
      measurable_const)
    (EntryDeletedReciprocal.measurable_reciprocalSum h0 he b)

theorem finite_counts (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (r : Fin N → RowRival) (hno : ∀ j,(r j).1 ≠ 1)
    (hg : r ∈ RivalGood.good μ (tests (xi i) g A U) N ε) :
    classCount 1 r+classCount 2 r ≤ C ∧ classCount 1 r+classCount 3 r ≤ C ∧
      C-classCount 1 r-classCount 2 r ≤ 1+classCount 0 r ∧
      C-classCount 1 r-classCount 3 r ≤ 1+classCount 0 r := by
  have he := empirical_errors μ g h.rivals_pos r hg
  have he0 : |(classCount 0 r:ℝ)-(N:ℝ)*cutoff i| < ε*(N:ℝ) := by
    have hh := he 0
    rw [h.means.lower] at hh
    simpa only [tests,RivalGood.statistics,Matrix.cons_val_zero,RawGoodGeometry.sum_tag_eq_count] using hh
  have he2 : |(classCount 2 r:ℝ)-(N:ℝ)*((1-cutoff i)/2)| < ε*(N:ℝ) := by
    have hh := he 1
    rw [h.means.upper0] at hh
    change |(∑ j, RivalGood.tag 2 (r j))-(N:ℝ)*((1-cutoff i)/2)| < ε*(N:ℝ) at hh
    simpa only [RawGoodGeometry.sum_tag_eq_count] using hh
  have he3 : |(classCount 3 r:ℝ)-(N:ℝ)*((1-cutoff i)/2)| < ε*(N:ℝ) := by
    have hh := he 2
    rw [h.means.upper1] at hh
    change |(∑ j, RivalGood.tag 3 (r j))-(N:ℝ)*((1-cutoff i)/2)| < ε*(N:ℝ) at hh
    simpa only [RawGoodGeometry.sum_tag_eq_count] using hh
  have hl : |((1+classCount 0 r:ℕ):ℝ)-(N:ℝ)*cutoff i| ≤ ε*(N:ℝ)+1 := by
    have hh := abs_add_le ((classCount 0 r:ℝ)-(N:ℝ)*cutoff i) 1
    have hid : ((1+classCount 0 r:ℕ):ℝ)-(N:ℝ)*cutoff i=
        ((classCount 0 r:ℝ)-(N:ℝ)*cutoff i)+1 := by push_cast; ring
    rw [hid]
    norm_num only [abs_one] at hh
    linarith
  have hr0 := RivalGood.residual_of_counts h.floor_error hl
    (he2.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith [h.residual_positive]) (by linarith [h.residual_room])
  have hr1 := RivalGood.residual_of_counts h.floor_error hl
    (he3.le.trans (by linarith : ε*(N:ℝ) ≤ ε*(N:ℝ)+1))
    (by linarith [h.residual_positive]) (by linarith [h.residual_room])
  have hc1 : classCount 1 r=0 := by simp [classCount,hno]
  simpa only [hc1,zero_add,Nat.sub_zero] using
    And.intro hr0.2.1.le (And.intro hr1.2.1.le
      (And.intro (min_eq_right_iff.mp hr0.1) (min_eq_right_iff.mp hr1.1)))

theorem finite_weight (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (r : Fin N → RowRival)
    (hg : r ∈ RivalGood.good μ (tests (xi i) g A U) N ε) :
    c*(N:ℝ) ≤ totalWeight (profile i g b r) := by
  have he := (abs_lt.mp (empirical_errors μ g h.rivals_pos r hg 5)).1
  have hmean := mul_le_mul_of_nonneg_left h.means.weight (Nat.cast_nonneg N)
  have hw0 := (FiniteGuards.eligibility_bounds (xi i) g.multiplier g.requiredDemand b).1
  dsimp only [profile]
  rw [← EntryLiteralCentral.weights_eq_profile i g h.requiredDemand_eq C b r,
    ActualEntryGoodGeometry.totalWeight_eq]
  change -(ε*(N:ℝ)) <
    (∑ j, RivalGood.lowerTest (FiniteGuards.eligibility (xi i) g.multiplier g.requiredDemand) (r j))-
      (N:ℝ)*(∫ r, tests (xi i) g A U 5 r ∂μ) at he
  nlinarith [h.sample_weight_margin]

theorem finite_response (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N)
    (hx : x ∈ usable μ i g b A U ε) :
    let p := complement i C g b x
    let Λ := b*(1-xi i*p)
    let K := focalSlope (xi i) (patternTemplate C (fun j => (x.1 j).1))
      (rowBids b x.1) (sampleSet i g b x) 0
    p=max (deficit i C b g.multiplier c hstar x) 0/(1+b*K) ∧
      (0< p ↔ 0< deficit i C b g.multiplier c hstar x) ∧
      (0< p → Λ ∈ Ioo (g.multiplier-g.radius) (min b (g.multiplier+g.radius)) ∧
        reciprocalAt i g b b x ≤ K ∧ K ≤ reciprocalAt i g b Λ x ∧
        q*(N:ℝ)/(2*U) ≤ K) := by
  rcases hx with ⟨hgood,hno,hcap,hpath⟩
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hc := finite_counts μ i g h x.1 hno hgood
  have hd := RawDeficitGeometry.template_imbalance_eq_draws C x.1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hwEq : weights (xi i) g (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) =
      profile i g b x.1 := EntryLiteralCentral.weights_eq_profile i g h.requiredDemand_eq C b x.1
  have hαs := all_action_guard_and_strip μ g h.rivals_pos (xi_pos i) hξ1 h.epsilon_nonneg
    h.prefix.margin_pos h.prefix.population_pos h.prefix.lower_pos
    (by linarith [h.prefix.lower_pos,h.radius_pos]) h.prefix.rejectionScale_pos
    h.means h.floor_error h.residual_positive h.residual_room h.demand_margin
    h.weight_margin h.rejection_margin h.seed_margin h.strip_margin h.count_margin x.1 hno hgood
  have hα : 0 < guardAlpha (xi i) g (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) := by
    rw [hαs.2.1 b]
    norm_num
  have hBU : ∀ j,rowBids b x.1 j ≤ U := by
    intro j
    refine Fin.cases h.bid_cap (fun j => ?_) j
    by_cases hj : (x.1 j).1=0
    · simpa [rowBids,hj] using hcap j hj
    · simp [rowBids,hj,h.cap_pos.le]
  let path := sampler (RawMixedSource.draws x.1) (profile i g b x.1) x.2
  have hp : 0 < (pathLaw (profile i g b x.1) (RawMixedSource.draws x.1) ∅).mass path := hpath
  have hW := finite_weight μ i g h x.1 hgood
  have hD : deficit i C b g.multiplier c hstar x=EntryLiteralCentral.pathDeficit i C b x.1 path := by
    unfold deficit selected EntryCentralSampling.guardedSample
    have hW' := hW
    dsimp only [profile] at hW'
    rw [if_pos hW']
    rfl
  have hcast : ∀ (d : ℕ) (hd : imbalance (patternTemplate C (fun j => (x.1 j).1))=d)
      (p : Path (Fin (N+1)) d),
      0 < (pathLaw (profile i g b x.1) d ∅).mass p →
      let E := finalSet d ∅ p
      let a := complementMarginal (xi i) (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) E 0
      let K := focalSlope (xi i) (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) E 0
      a=max (EntryLiteralCentral.pathDeficit i C b x.1 p) 0/(1+b*K) ∧
      (0< a ↔ 0< EntryLiteralCentral.pathDeficit i C b x.1 p) ∧
      (0< a → b*(1-xi i*a) ∈ Ioo (g.multiplier-g.radius) (min b (g.multiplier+g.radius)) ∧
        reciprocalSum (rowBids b x.1) (insert 0 E) b ≤ K ∧
        K ≤ reciprocalSum (rowBids b x.1) (insert 0 E) (b*(1-xi i*a)) ∧
        q*(N:ℝ)/(2*U) ≤ K) := by
    intro d hd p hp
    subst d
    rw [← hwEq] at hp
    have hf := all_action_focal_not_sampled (xi_pos i) g h.prefix _ (rowBids b x.1) 0
      h.bid_window.2 hα p hp
    have hh := EntryLiteralCentral.literal_response_from_guards i g hb h.cap_pos
      h.prefix.margin_pos h.prefix.population_pos h.radius_pos h.prefix.lower_pos h.cap_receipt
      x.1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hBU h.half_receipt hα p hp hf
    refine ⟨hh.1,hh.2.1,?_⟩
    intro ha
    have hprice := hh.2.2 ha
    have hB0 : rowBids b x.1 0=b := rfl
    have hpr : b*(1-xi i*complementMarginal (xi i) (patternTemplate C (fun j => (x.1 j).1))
        (rowBids b x.1) (finalSet _ ∅ p) 0)=
      focalPrice (xi i) (patternTemplate C (fun j => (x.1 j).1)) (rowBids b x.1) (finalSet _ ∅ p) 0 := rfl
    have hk := rightSecant_bracket (rowBids b x.1) (insert 0 (finalSet _ ∅ p))
      (xi_pos i) hξ1 (h.prefix.lower_pos.trans hprice.1)
      (hprice.2.trans_le (min_le_left _ _)) hBU (h.cap_receipt.trans hprice.1.le)
    obtain ⟨root,hroot,hr,hstrip⟩ := all_action_roots_and_reciprocals g (xi_pos i) hξ1
      h.cap_pos h.prefix.margin_pos h.prefix.population_pos h.radius_pos h.prefix.lower_pos
      h.cap_receipt h.strip_above x.1 hcap hαs.2.1 hαs.2.2 b h.bid_window h.bid_cap p hp
    exact ⟨hprice,hk.1,hk.2,(hstrip b h.bid_window).trans hk.1⟩
  have hh := hcast _ hd path hp
  rw [hD]
  dsimp only [complement,sampleSet,removed,path] at hh ⊢
  refine ⟨hh.1,hh.2.1,?_⟩
  intro hp'
  have hh' := hh.2.2 hp'
  refine ⟨hh'.1,?_,?_,hh'.2.2.2⟩
  · simpa only [reciprocalAt,sampleSet,removed,path,EntryLiteralCentral.rowBids_eq_listBids,
      EntryDeletedReciprocal.omitted_focal_identity b b hb] using hh'.2.1
  · have hprice0 : 0 < b*(1-xi i*complement i C g b x) := h.prefix.lower_pos.trans hh'.1.1
    change _ ≤ reciprocalSum (EntryDeletedReciprocal.listBids 0 x.1) (sampleSet i g b x)
      (b*(1-xi i*complement i C g b x))
    calc
      _ ≤ reciprocalSum (EntryDeletedReciprocal.listBids b x.1) (insert 0 (sampleSet i g b x))
          (b*(1-xi i*complement i C g b x)) := hh'.2.2.1
      _ = _ := EntryDeletedReciprocal.omitted_focal_identity b _ hprice0 x.1 (sampleSet i g b x)

theorem total_finite_geometry (μ : Measure RowRival) (i : Row) (g : GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    let p := response μ i C g b A U ε x
    let Λ := price μ i C g b A U ε x
    let K := slope μ i C g b A U ε x
    lo ≤ Λ ∧ Λ ≤ b ∧ reciprocalAt i g b b x ≤ K ∧ K ≤ reciprocalAt i g b Λ x ∧
      (x ∈ usable μ i g b A U ε → p=max (deficit i C b g.multiplier c hstar x) 0/(1+b*K)) ∧
      (0< p → q*(N:ℝ)/(2*U) ≤ K) ∧
      (0< p ↔ x ∈ usable μ i g b A U ε ∧ 0< deficit i C b g.multiplier c hstar x) := by
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hblo : lo ≤ b := h.lower_price.trans h.bid_window.1
  by_cases hx : x ∈ usable μ i g b A U ε
  · have hfin := finite_response μ i g h hstar x hx
    have hq0 := (complement_bounds i C g b x).1
    by_cases hp : 0 < complement i C g b x
    · have hs := hfin.2.2 hp
      simp only [response,if_pos hx,price,slope,if_pos hp]
      refine ⟨h.lower_price.trans hs.1.1.le,(hs.1.2.trans_le (min_le_left _ _)).le,
        hs.2.1,hs.2.2.1,fun _ => hfin.1,fun _ => hs.2.2.2,?_⟩
      simpa only [hx,true_and] using hfin.2.1
    · have hz : complement i C g b x=0 := le_antisymm (le_of_not_gt hp) hq0
      have hD : max (deficit i C b g.multiplier c hstar x) 0=0 := by
        have hnot : ¬ 0 < deficit i C b g.multiplier c hstar x :=
          fun hh => hp (hfin.2.1.mpr hh)
        exact max_eq_right (le_of_not_gt hnot)
      have hnot : ¬ 0 < deficit i C b g.multiplier c hstar x :=
        fun hh => hp (hfin.2.1.mpr hh)
      simp [response,hx,price,slope,hz,hD,hblo,hnot]
  · simp [response,hx,price,slope,hblo]

end FCAppendix.Affine.Uniform06.EntryLiteralResponseGeometry
