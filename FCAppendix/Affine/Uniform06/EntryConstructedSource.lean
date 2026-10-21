import FCAppendix.Affine.Uniform06.EntryFiniteConstructor
import FCAppendix.Affine.Uniform06.EntrySourceLower
import FCAppendix.Affine.Uniform06.SourceEarlyFamily

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryConstructedSource

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment SourcePrefixConstructor EntryPopulationMargins
open EntryEarlySourceLimits EntryFiniteConstructor EntryLiteralResponseGeometry
open EntryLiteralCanonicalTransfer

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Row)

structure EarlyArray where
  value : Ω→ℝ
  bid : ℕ→Ω→ℝ
  value_measurable : Measurable value
  bid_measurable : ∀ m,Measurable (bid m)
  value_law : μ.map value=LowChernoff.conditionalValueLaw i
  admissible : ∀ m,∀ᵐ ω ∂μ,bid m ω≤ value ω
  nonnegative : ∀ m,∀ᵐ ω ∂μ,0≤ bid m ω
  bid_cap : ∀ m,∀ᵐ ω ∂μ,bid m ω≤ ReceiptGap.cap i
  active_closed : ∀ a>(0:ℝ),∀ e>(0:ℝ),∀ᶠ m in atTop,∀ᵐ ω ∂μ,
    value ω∈Icc (entry i+a) (cutoff i) →
      |bid m ω-ActiveGraphComponent.activeBid i (value ω)|< e
  guards : ℕ→ GuardData
  literal : ∀ m,LiteralFields i (guards m)
  multiplier_pos : ∀ m,0<(guards m).multiplier
  multiplier_tendsto : Tendsto (fun m => (guards m).multiplier) atTop (𝓝 (entry i))
  root_equation : ∀ m,(∫ ω,exposure (xi i) (guards m).multiplier (bid m ω) ∂μ)=
    PrefixRoot.requiredDemand i
  rejection_equation : ∀ m,(∫ ω,PrefixRoot.sourcePsi i (guards m).rejectionRoot (bid m ω) ∂μ)=
    3*PrefixRoot.requiredDemand i
  population : ℕ→ℕ
  population_tendsto : Tendsto population atTop atTop
  population_eq : ∀ m,(guards m).population=(population m:ℝ)
  margin_small : ∀ m,(guards m).margin≤ epsilon i

namespace EarlyArray
variable {μ i} (s : EarlyArray μ i)

def jointLaw (m : ℕ) : Measure (ℝ×ℝ) := joint μ s.value (s.bid m)
instance jointLaw_probability (m : ℕ) : IsProbabilityMeasure (s.jointLaw m) :=
  Measure.isProbabilityMeasure_map (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable

omit [IsProbabilityMeasure μ] in
theorem value_marginal (m : ℕ) : (s.jointLaw m).map Prod.fst=LowChernoff.conditionalValueLaw i := by
  rw [jointLaw,joint_first μ s.value (s.bid m) s.value_measurable (s.bid_measurable m),s.value_law]

omit [IsProbabilityMeasure μ] in
theorem cap (m : ℕ) : ∀ᵐ p ∂s.jointLaw m,p.2≤ ReceiptGap.cap i :=
  (ae_map_iff (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable
    (measurableSet_le measurable_snd measurable_const)).mpr (s.bid_cap m)

omit [IsProbabilityMeasure μ] in
theorem joint_nonnegative (m : ℕ) : ∀ᵐ p ∂s.jointLaw m,0≤ p.2 :=
  (ae_map_iff (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable
    (measurableSet_le measurable_const measurable_snd)).mpr (s.nonnegative m)

omit [IsProbabilityMeasure μ] in
theorem joint_admissible (m : ℕ) : ∀ᵐ p ∂s.jointLaw m,p.2≤ p.1 :=
  joint_bid_le_value μ s.value (s.bid m) s.value_measurable (s.bid_measurable m) (s.admissible m)

omit [IsProbabilityMeasure μ] in
theorem root (m : ℕ) : (∫ p,exposure (xi i) (s.guards m).multiplier p.2 ∂s.jointLaw m)=
    PrefixRoot.requiredDemand i := by
  have hm : Measurable (fun p : ℝ×ℝ => exposure (xi i) (s.guards m).multiplier p.2) := by
    unfold exposure
    fun_prop
  rw [jointLaw,joint,integral_map (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable
    hm.aestronglyMeasurable]
  exact s.root_equation m

omit [IsProbabilityMeasure μ] in
theorem rejection (m : ℕ) : (∫ p,PrefixRoot.sourcePsi i (s.guards m).rejectionRoot p.2 ∂s.jointLaw m)=
    3*PrefixRoot.requiredDemand i := by
  have hm : Measurable (fun p : ℝ×ℝ => PrefixRoot.sourcePsi i (s.guards m).rejectionRoot p.2) := by
    unfold PrefixRoot.sourcePsi PrefixRoot.psi
    fun_prop
  rw [jointLaw,joint,integral_map (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable hm.aestronglyMeasurable]
  exact s.rejection_equation m

omit [IsProbabilityMeasure μ] in

theorem common_active_limit : ∀ᵐ ω ∂μ,entry i< s.value ω →
    Tendsto (fun m => s.bid m ω) atTop (𝓝 (ActiveGraphComponent.activeBid i (s.value ω))) := by
  have hnk (n k : ℕ) : ∃ M : ℕ,∀ m≥ M,∀ᵐ ω ∂μ,
      s.value ω∈Icc (entry i+1/((k:ℝ)+1)) (cutoff i) →
        |s.bid m ω-ActiveGraphComponent.activeBid i (s.value ω)|<1/((n:ℝ)+1) :=
    eventually_atTop.mp (s.active_closed (1/((k:ℝ)+1)) (by positivity)
      (1/((n:ℝ)+1)) (by positivity))
  choose M hM using hnk
  have hcommon : ∀ᵐ ω ∂μ,∀ n k m : ℕ,M n k≤ m →
      s.value ω∈Icc (entry i+1/((k:ℝ)+1)) (cutoff i) →
        |s.bid m ω-ActiveGraphComponent.activeBid i (s.value ω)|<1/((n:ℝ)+1) := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro m
    by_cases hm : M n k≤ m
    · exact (hM n k m hm).mono fun ω hω _ => hω
    · exact ae_of_all _ fun ω hh => (hm hh).elim
  filter_upwards [hcommon,value_support μ i s.value s.value_measurable s.value_law]
    with ω hω hv
  intro hactive
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt he
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (sub_pos.mpr hactive)
  refine ⟨M n k,?_⟩
  intro m hm
  rw [Real.dist_eq]
  exact (hω n k m hm ⟨by linarith,hv.2⟩).trans hn

theorem weight_tendsto : Tendsto (fun m => weightMean i (s.jointLaw m) (s.guards m).multiplier)
    atTop (𝓝 (eligibleMass μ i s.value)) := by
  have hh := (source_profile_limits μ i s.value s.bid s.value_measurable s.bid_measurable
    s.value_law s.admissible s.common_active_limit (fun _ => entry i)
    (fun m => (s.guards m).multiplier) (fun _ => EarlyMean.entry_pos i) s.multiplier_pos
    tendsto_const_nhds s.multiplier_tendsto).1
  have he (m : ℕ) : weightMean i (s.jointLaw m) (s.guards m).multiplier=
      cutoff i*(∫ ω,FiniteGuards.eligibility (xi i) (s.guards m).multiplier
        (PrefixRoot.requiredDemand i) (s.bid m ω) ∂μ) := by
    have hm : Measurable (fun p : ℝ×ℝ => FiniteGuards.eligibility (xi i)
        (s.guards m).multiplier (PrefixRoot.requiredDemand i) p.2) := by
      unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
      fun_prop
    rw [weightMean,jointLaw,joint,integral_map
      (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable hm.aestronglyMeasurable]
  simpa only [he] using hh

theorem eligibleMass_lower : stripMass i≤ eligibleMass μ i s.value :=
  ge_of_tendsto s.weight_tendsto (Eventually.of_forall fun m =>
    original_weight_lower i (s.jointLaw m) (s.multiplier_pos m) (s.root m))

theorem eventually_weight_margin : ∀ᶠ m in atTop,
    eligibleMass μ i s.value/2+epsilon i≤ weightMean i (s.jointLaw m) (s.guards m).multiplier := by
  have hc := eligibleMass_positive μ i s.value s.value_measurable s.value_law
  have he := (epsilon_bounds i).2.2.2.1.trans s.eligibleMass_lower
  filter_upwards [s.weight_tendsto.eventually_const_lt
    (show 3*eligibleMass μ i s.value/4< eligibleMass μ i s.value by linarith)] with m hm
  linarith

theorem eventually_rejection_above : ∀ᶠ m in atTop,
    entry i+cutoff i/100<(s.guards m).rejectionRoot := by
  have ht := cutoff_pos i
  have he : 0< activeError i := by unfold activeError; positivity
  filter_upwards [s.active_closed (cutoff i/40000) (by positivity) (activeError i) he] with m hm
  have hA : ∀ᵐ p ∂s.jointLaw m,p.1∈Icc (sortEnd i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1|≤ activeError i := by
    apply (ae_map_iff (s.value_measurable.prodMk (s.bid_measurable m)).aemeasurable
      (by unfold ActiveGraphComponent.activeBid; measurability)).mpr
    filter_upwards [hm] with ω hω hv
    exact (hω ⟨by unfold sortEnd at hv; linarith [hv.1],hv.2⟩).le
  exact PrefixRoot.source_root_above_prefix i (s.jointLaw m) (s.value_marginal m)
    (active_tail_lower_of_dimensional_error i (s.jointLaw m) hA) (s.rejection m)

def band (i : Row) : Set ℝ := Icc (entry i-radius i/4) (entry i+radius i/4)

theorem bid_band_geometry (g : GuardData) (hf : LiteralFields i g)
    (hL : |g.multiplier-entry i|< cutoff i/40000) {b : ℝ} (hb : b∈band i) :
    b∈Icc (g.multiplier-g.radius) (g.multiplier+g.radius) ∧
    b< g.multiplier+g.radius ∧ b≤ ReceiptGap.cap i ∧
    ReceiptGap.threshold i≤ b ∧ b≤ cutoff i := by
  have ht := cutoff_pos i
  have hh := abs_lt.mp hL
  have ha : g.radius=cutoff i/10000 := hf.radius_eq
  have hU : x i+1/40000< ReceiptGap.capFactor i := by
    cases i <;> norm_num [x,xQ,ReceiptGap.capFactor,kappa,kappaQ,xi,xiQ,etaQ]
  have hU' := mul_lt_mul_of_pos_left hU ht
  have hx : x i+1/40000<1 := by cases i <;> norm_num [x,xQ]
  have hx' := mul_lt_mul_of_pos_left hx ht
  have hrec := ReceiptGap.receipt_entry_margin i
  dsimp only [band,radius] at hb
  rw [ReceiptGap.cap_scaled]
  unfold entry at *
  simp only [ha] at *
  refine ⟨⟨?_,?_⟩,?_,?_,?_,?_⟩ <;> nlinarith [hb.1,hb.2,hh.1,hh.2]

theorem eventually_inputs : ∀ᶠ m in atTop,4≤ s.population m ∧
    ∀ b∈band i,Inputs (RawMixedSource.source i (s.jointLaw m)) i
      (normalizeCount (s.guards m)) (s.population m-1) (capacity (s.population m))
      b ((s.guards m).multiplier+2*(s.guards m).radius) (ReceiptGap.cap i) (epsilon i)
      (eligibleMass μ i s.value/2) (stripMass i) (lowerPrice i) (gamma i)
      (weightMean i (s.jointLaw m) (s.guards m).multiplier) (cutoff i/2) := by
  have ht := cutoff_pos i
  have hn := PhysicalRates.rivals_tendsto.comp s.population_tendsto
  have hlarge := (tendsto_natCast_atTop_atTop.comp hn).const_mul_atTop (epsilon_bounds i).1
  have hroot : ∀ᶠ m in atTop,|(s.guards m).multiplier-entry i|< cutoff i/40000 := by
    have hh := Metric.tendsto_atTop.mp s.multiplier_tendsto (cutoff i/40000) (by positivity)
    simpa only [Real.dist_eq] using eventually_atTop.mpr hh
  filter_upwards [s.population_tendsto.eventually_ge_atTop 4,
    hlarge.eventually_ge_atTop 100,hroot,s.eventually_rejection_above,s.eventually_weight_margin]
    with m hm hlarge hroot hz hw
  refine ⟨hm,?_⟩
  intro b hb
  have hb' := bid_band_geometry (i := i) (s.guards m) (s.literal m) hroot hb
  exact finite_inputs i (s.jointLaw m) (s.guards m) (s.literal m) hm
    (s.population_eq m) (s.margin_small m) hlarge hroot hz (s.cap m)
    (s.value_marginal m) (s.joint_admissible m) (s.root m) (s.rejection m)
    hb'.1 hb'.2.2.1 hb'.2.2.2.1 hw

theorem band_eventually {b : ℕ→ℝ} (hb : Tendsto b atTop (𝓝 (entry i))) :
    ∀ᶠ m in atTop,b m∈band i := by
  have ht := cutoff_pos i
  have ha : 0< radius i/4 := by unfold radius; positivity
  have hh := hb.eventually (Ioo_mem_nhds (by linarith : entry i-radius i/4< entry i)
    (by linarith : entry i< entry i+radius i/4))
  exact hh.mono fun _ h => ⟨h.1.le,h.2.le⟩

theorem shift_tendsto (M : ℕ) : Tendsto (fun m : ℕ => m+M) atTop atTop :=
  tendsto_atTop_mono' atTop (Eventually.of_forall fun m => Nat.le_add_right m M) tendsto_id

theorem source_on_tail (b : ℕ→ℝ) (hb : Tendsto b atTop (𝓝 (entry i))) :
    ∃ M : ℕ,∃ t : EntrySequence.Source μ i,
      t.value=s.value ∧ t.bid=(fun m => s.bid (m+M)) ∧
      t.population=(fun m => s.population (m+M)) ∧ t.focal=(fun m => b (m+M)) ∧
      t.guards=(fun m => normalizeCount (s.guards (m+M))) ∧
      t.epsilon=epsilon i ∧
      t.stripBid=(fun m => (s.guards (m+M)).multiplier+2*(s.guards (m+M)).radius) := by
  have he := s.eventually_inputs.and (band_eventually (i := i) hb)
  obtain ⟨M,hM⟩ := eventually_atTop.mp he
  have hf (m : ℕ) := hM (m+M) (by omega)
  have hshift := shift_tendsto M
  let t : EntrySequence.Source μ i := {
    value := s.value
    bid := fun m => s.bid (m+M)
    value_measurable := s.value_measurable
    bid_measurable := fun m => s.bid_measurable (m+M)
    value_law := s.value_law
    admissible := fun m => s.admissible (m+M)
    active := s.common_active_limit.mono fun ω hω hv => (hω hv).comp hshift
    focal := fun m => b (m+M)
    focal_le_cutoff := fun m => by
      have hband := (hf m).2.2
      have hx : x i+1/40000<1 := by cases i <;> norm_num [x,xQ]
      have hh := mul_lt_mul_of_pos_left hx (cutoff_pos i)
      dsimp [band,radius,entry] at hband
      nlinarith
    focal_tendsto := hb.comp hshift
    guards := fun m => normalizeCount (s.guards (m+M))
    multiplier_tendsto := s.multiplier_tendsto.comp hshift
    population := fun m => s.population (m+M)
    population_ge_four := fun m => (hf m).1.1
    population_tendsto := s.population_tendsto.comp hshift
    epsilon := epsilon i
    epsilon_pos := (epsilon_bounds i).1
    stripDensity := stripMass i
    lowerPrice := lowerPrice i
    lowerPrice_lt_entry := by unfold lowerPrice; have ht := cutoff_pos i; linarith
    stripBid := fun m => (s.guards (m+M)).multiplier+2*(s.guards (m+M)).radius
    demandMargin := fun _ => gamma i
    weightMargin := fun m => weightMean i (s.jointLaw (m+M)) (s.guards (m+M)).multiplier
    seedMargin := fun _ => cutoff i/2
    cap := fun m => s.cap (m+M)
    finite := fun m => (hf m).1.2 (b (m+M)) (hf m).2 }
  exact ⟨M,t,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end EarlyArray
end FCAppendix.Affine.Uniform06.EntryConstructedSource
