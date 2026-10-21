import FCAppendix.Affine.Uniform06.FixedTiltPhysicalDerivative
import FCAppendix.Affine.Uniform06.SelectedMaximumDerivative
import FCAppendix.Affine.Uniform06.CompactStieltjes
import FCAppendix.Affine.Uniform07.TiltUniqueness

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.OptimizedPhysicalRate

open MeasureTheory ProbabilityTheory Set Filter Topology
open Uniform07 PhysicalExposureLimit FullJointLaw FullBidGeometry
open FullSourceSpecialization FullReciprocalMean RawTiltedSource
attribute [local instance] Classical.propDecidable

def band (i : Row) : Set ℝ := Ico (cutoff i/2) (entry i)

theorem positive_of_mem_band (i : Row) {b : ℝ} (hb : b ∈ band i) : 0 < b :=
  (half_pos (cutoff_pos i)).trans_le hb.1

theorem normalized_mem_band (i : Row) {b : ℝ} (hb : b ∈ band i) :
    b/cutoff i ∈ Ico (1/2:ℝ) (x i) := by
  constructor
  · apply (le_div_iff₀ (cutoff_pos i)).mpr
    nlinarith [hb.1]
  · apply (div_lt_iff₀ (cutoff_pos i)).mpr
    simpa only [entry] using hb.2

theorem physical_scale (i : Row) (b : ℝ) : (b/cutoff i)*cutoff i=b :=
  div_mul_cancel₀ b (cutoff_pos i).ne'

theorem full_graph (i : Row) :
    ∀ᵐ p ∂(law i : Measure (ℝ × ℝ)),p.2=FullJointLaw.bid i p.1 := by
  apply (ae_map_iff (show AEMeasurable (fun v : ℝ => (v,FullJointLaw.bid i v))
      (LowChernoff.conditionalValueLaw i) from
      (measurable_id.prodMk (measurable_bid i)).aemeasurable)
    (measurableSet_eq_fun measurable_snd ((measurable_bid i).comp measurable_fst))).mpr
  exact ae_of_all _ fun _ => rfl

theorem full_box (i : Row) :
    ∀ᵐ p ∂(law i : Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) (cutoff i) := by
  have hz : FullJointLaw.bid i 0=0 := by
    simp only [FullJointLaw.bid,if_pos (EarlyMean.entry_pos i).le]
  filter_upwards [EarlyMean.value_support i (law i : Measure (ℝ × ℝ))
    (full_value_marginal i),full_graph i] with p hp hg
  refine ⟨hp,?_,?_⟩
  · rw [hg,← hz]
    exact (strictMonoOn_bid i).monotoneOn
      ⟨le_rfl,(cutoff_pos i).le⟩ hp hp.1
  · rw [hg]
    exact (bid_below_value i hp.1).trans hp.2

def bidCap (i : Row) : ℝ := ActiveGraphComponent.activeBid i (cutoff i)

theorem full_bid_cap (i : Row) :
    ∀ᵐ p ∂(law i : Measure (ℝ × ℝ)),p.2 ≤ bidCap i := by
  have he : FullJointLaw.bid i (cutoff i)=bidCap i := by
    rw [FullJointLaw.bid,if_neg (not_le_of_gt (EarlyMean.entry_lt_cutoff i)),
      EarlyJointCompactness.extendedActive_eq i (cutoff_pos i).le]
    rfl
  filter_upwards [EarlyMean.value_support i (law i : Measure (ℝ × ℝ))
    (full_value_marginal i),full_graph i] with p hp hg
  rw [hg,← he]
  exact (strictMonoOn_bid i).monotoneOn hp ⟨(cutoff_pos i).le,le_rfl⟩ hp.2

theorem full_saturation_guard (i : Row) :
    (1-xi i)*bidCap i < cutoff i/2 := by
  have ht := cutoff_pos i
  have he : bidCap i=cutoff i*(x i/(kappa i+xi i*x i)) := by
    have hd : 0 < kappa i+xi i*x i := by
      cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ,x,xQ]
    unfold bidCap ActiveGraphComponent.activeBid entry
    field_simp [ht.ne',hd.ne']
  have hn : (1-xi i)*(x i/(kappa i+xi i*x i)) < (1/2:ℝ) := by
    cases i <;> norm_num [x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
  rw [he]
  nlinarith [mul_lt_mul_of_pos_left hn ht]

theorem exists_matching_tilt (i : Row) {b : ℝ} (hb : b ∈ band i) :
    ∃ θ ∈ Ioo (0:ℝ) (2/(rho*b)),
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
        (law i : Measure (ℝ × ℝ)))) Prod.fst θ=rho := by
  have hz := normalized_mem_band i hb
  have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
  have hgap : rho < rho+(1-x i)*(entry i-(b/cutoff i)*cutoff i) := by
    rw [physical_scale]
    linarith [mul_pos hx (sub_pos.mpr hb.2)]
  have he := EarlyMean.exists_matching_tilt_early_law i
    (law i : Measure (ℝ × ℝ)) (full_value_marginal i)
    (full_below_value i) (full_active_graph i) hz
    (by norm_num [rho] : 0 < rho) hgap
  simpa only [physical_scale] using he

def theta (i : Row) (b : ℝ) : ℝ :=
  if hb : b ∈ band i then Classical.choose (exists_matching_tilt i hb) else 0

theorem theta_spec (i : Row) {b : ℝ} (hb : b ∈ band i) :
    theta i b ∈ Ioo (0:ℝ) (2/(rho*b)) ∧
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
        (law i : Measure (ℝ × ℝ)))) Prod.fst (theta i b)=rho := by
  rw [theta,dif_pos hb]
  exact Classical.choose_spec (exists_matching_tilt i hb)

theorem theta_pos (i : Row) {b : ℝ} (hb : b ∈ band i) : 0 < theta i b :=
  (theta_spec i hb).1.1

theorem actual_demand_preserving (i : Row) {b : ℝ} (hb : b ∈ band i) :
    MeasurePreserving Prod.fst
      (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
        (law i : Measure (ℝ × ℝ)))) (sourceLaw i (b/cutoff i)) := by
  refine ⟨measurable_fst,?_⟩
  have hz := normalized_mem_band i hb
  simpa only [physical_scale] using full_mixed_demand_law i ⟨hz.1,hz.2.le⟩

theorem theta_score (i : Row) {b : ℝ} (hb : b ∈ band i) :
    tiltScore i (theta i b) (b/cutoff i)=0 := by
  have hz := normalized_mem_band i hb
  have hp := tilted_preserving (actual_demand_preserving i hb)
    (measurable_id.const_mul (-(theta i b)))
  have he : SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
    (law i : Measure (ℝ × ℝ)))) Prod.fst (theta i b)=
      SubentryTilt.mean (sourceLaw i (b/cutoff i)) id (theta i b) := by
    unfold SubentryTilt.mean
    rw [← hp.map_eq]
    exact (integral_map hp.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
  apply FullRateLimit.mean_eq_rho_implies_score_zero i ⟨hz.1,hz.2.le⟩
  rw [← he]
  exact (theta_spec i hb).2

theorem theta_unique (i : Row) {b s : ℝ} (hb : b ∈ band i)
    (hs : tiltScore i s (b/cutoff i)=0) : s=theta i b := by
  have hz := normalized_mem_band i hb
  exact source_tilt_unique i ⟨hz.1,hz.2.le⟩ hs (theta_score i hb)

theorem objective_eq_checked (i : Row) {b : ℝ} (hb : b ∈ band i) (s : ℝ) :
    FixedTiltPhysicalDerivative.objective i (law i : Measure (ℝ × ℝ)) rho s b=
      Uniform07.objective i s (b/cutoff i) := by
  have hz := normalized_mem_band i hb
  rw [FixedTiltPhysicalDerivative.objective_eq_cgf i _ (positive_of_mem_band i hb),
    source_objective_eq_cgf i ⟨hz.1,hz.2.le⟩]
  congr 1
  calc
    _ = cgf Prod.fst (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
        (law i : Measure (ℝ × ℝ)))) (-s) :=
      cgf_comp_of_preserving (RawMixedSource.point_preserving i _
        (positive_of_mem_band i hb)) measurable_fst (-s)
    _ = cgf id (sourceLaw i (b/cutoff i)) (-s) :=
      cgf_comp_of_preserving (actual_demand_preserving i hb) measurable_id (-s)

theorem physical_rate_attained (i : Row) {b : ℝ} (hb : b ∈ band i) :
    canonicalRate i (b/cutoff i)=
      FixedTiltPhysicalDerivative.objective i (law i : Measure (ℝ × ℝ))
        rho (theta i b) b := by
  have hz := normalized_mem_band i hb
  rw [objective_eq_checked i hb]
  exact source_tilt_rate i ⟨hz.1,hz.2.le⟩ (theta_pos i hb).le (theta_score i hb)

theorem physical_objective_le_rate (i : Row) {b : ℝ} (hb : b ∈ band i) (s : ℝ) :
    FixedTiltPhysicalDerivative.objective i (law i : Measure (ℝ × ℝ)) rho s b ≤
      canonicalRate i (b/cutoff i) := by
  have hz := normalized_mem_band i hb
  rw [physical_rate_attained i hb,objective_eq_checked i hb,objective_eq_checked i hb]
  exact source_tilt_global_max i ⟨hz.1,hz.2.le⟩ (theta_score i hb) s

theorem theta_tendsto (i : Row) (b : ℕ → ℝ) {b0 : ℝ}
    (hb : ∀ n,b n ∈ band i) (hb0 : b0 ∈ band i)
    (hblim : Tendsto b atTop (𝓝 b0)) :
    Tendsto (fun n => theta i (b n)) atTop (𝓝 (theta i b0)) := by
  let ν := fun n => lowerProbability i (law i) (b n) (positive_of_mem_band i (hb n))
  let ν0 := lowerProbability i (law i) b0 (positive_of_mem_band i hb0)
  have hν := fun n => MixedLaw.physicalLowerLaw_bounds i
    (positive_of_mem_band i (hb n)) (law i : Measure (ℝ × ℝ))
  have hν0 := MixedLaw.physicalLowerLaw_bounds i
    (positive_of_mem_band i hb0) (law i : Measure (ℝ × ℝ))
  have hw : Tendsto ν atTop (𝓝 ν0) := lowerProbability_tendsto i
    (fun _ => law i) (law i) tendsto_const_nhds b
    (fun n => positive_of_mem_band i (hb n)) (positive_of_mem_band i hb0) hblim
  have hz := normalized_mem_band i hb0
  have hc := ActiveGraphComponent.original_active_graph_continuous_component i
    (law i : Measure (ℝ × ℝ)) (full_value_marginal i) (full_active_graph i)
    (b0/cutoff i) ⟨hz.1,hz.2.le⟩
  have hc' : volume.restrict
      (Ioo (ActiveGraphComponent.activeDemand i (b0/cutoff i) (ActiveGraphComponent.activeLeft i))
        (ActiveGraphComponent.activeDemand i (b0/cutoff i) (ActiveGraphComponent.activeRight i))) ≪
      (ν0:Measure ℝ) := by
    simpa only [ActiveGraphComponent.originalLowerStatisticLaw,physical_scale,ν0,
      lowerProbability,MixedLaw.physicalLowerLaw] using! hc.2
  exact mixed_matching_tilts_tendsto i ν ν0 hν hν0 hw hc.1 hc'
    (fun n => theta i (b n)) (fun _ => rho) tendsto_const_nhds
    (Eventually.of_forall fun n => (theta_spec i (hb n)).2) (theta_spec i hb0).2

theorem continuousOn_theta (i : Row) : ContinuousOn (theta i) (band i) := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_iff_continuousAt.mpr
  intro b0
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro b hb
  exact theta_tendsto i (fun n => (b n : ℝ)) (fun n => (b n).2) b0.2
    (continuous_subtype_val.continuousAt.tendsto.comp hb)

theorem continuous_nu_rectangle (i : Row) {lo hi Θ : ℝ} (hlo : 0 < lo) :
    Continuous (fun p : Icc lo hi × Icc (-Θ) Θ => nu i p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p0
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro p hp
  have hb : Tendsto (fun n => ((p n).1 : ℝ)) atTop (𝓝 (p0.1 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.comp hp
  have hθ : Tendsto (fun n => ((p n).2 : ℝ)) atTop (𝓝 (p0.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hp
  exact (original_tilted_reciprocal_and_window i (fun _ => law i)
    tendsto_const_nhds hlo (cutoff_pos i).le (fun _ => full_box i)
    (fun n => ((p n).1 : ℝ)) (fun n => ((p n).1 : ℝ))
    (fun n => ((p n).2 : ℝ)) (fun n => (p n).1.2)
    (fun n => (p n).1.2) (fun n => (p n).2.2) hb hb hθ).1

theorem continuousAt_nu (i : Row) {b θ : ℝ} (hb : 0 < b) :
    ContinuousAt (fun p : ℝ × ℝ => nu i p.1 p.2) (b,θ) := by
  let lo := b/2
  let hi := 2*b
  let Θ := |θ|+1
  have hbox : lo ≤ hi := by dsimp [lo,hi]; linarith
  have hΘ : 0 < Θ := by dsimp [Θ]; positivity
  let P : ℝ × ℝ → Icc lo hi × Icc (-Θ) Θ := fun p =>
    (⟨CompactStieltjes.clip lo hi p.1,CompactStieltjes.clip_mem hbox p.1⟩,
     ⟨CompactStieltjes.clip (-Θ) Θ p.2,CompactStieltjes.clip_mem (by linarith) p.2⟩)
  have hP : Continuous P :=
    (((CompactStieltjes.clip_continuous lo hi).comp continuous_fst).subtype_mk _).prodMk
      (((CompactStieltjes.clip_continuous (-Θ) Θ).comp continuous_snd).subtype_mk _)
  have hcont := (continuous_nu_rectangle i (show 0 < lo by dsimp [lo]; positivity)).comp hP
  have hblo : lo < b := by dsimp [lo]; linarith
  have hbhi : b < hi := by dsimp [hi]; linarith
  have hθlo : -Θ < θ := by dsimp [Θ]; linarith [neg_abs_le θ]
  have hθhi : θ < Θ := by dsimp [Θ]; linarith [le_abs_self θ]
  have he : (fun p : ℝ × ℝ => nu i (P p).1 (P p).2)=ᶠ[𝓝 (b,θ)]
      (fun p => nu i p.1 p.2) := by
    filter_upwards [(continuous_fst.continuousAt.tendsto).eventually_const_lt hblo,
      (continuous_fst.continuousAt.tendsto).eventually_lt_const hbhi,
      (continuous_snd.continuousAt.tendsto).eventually_const_lt hθlo,
      (continuous_snd.continuousAt.tendsto).eventually_lt_const hθhi]
      with p hp0 hp1 hp2 hp3
    simp only [P,CompactStieltjes.clip_eq ⟨hp0.le,hp1.le⟩,
      CompactStieltjes.clip_eq ⟨hp2.le,hp3.le⟩]
  exact hcont.continuousAt.congr_of_eventuallyEq he.symm

def A (i : Row) (b : ℝ) : ℝ := theta i b/(xi i)*nu i b (theta i b)

theorem A_eq_theta_nu_div_xi (i : Row) (b : ℝ) :
    A i b=theta i b*nu i b (theta i b)/(xi i) := by unfold A; ring

theorem A_pos (i : Row) {b : ℝ} (hb : b ∈ band i) : 0 < A i b :=
  mul_pos (div_pos (theta_pos i hb) (xi_pos i))
    (nu_pos i (positive_of_mem_band i hb) hb.2 (theta i b))

section CoefficientContinuity
attribute [local irreducible] theta nu

theorem continuousOn_A (i : Row) : ContinuousOn (A i) (band i) := by
  intro b hb
  have ht := continuousOn_theta i b hb
  have hp : Tendsto (fun y : ℝ => (y,theta i y)) (𝓝[band i] b) (𝓝 (b,theta i b)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds ht
  have hn : Tendsto (fun y : ℝ => nu i y (theta i y)) (𝓝[band i] b)
      (𝓝 (nu i b (theta i b))) :=
    (continuousAt_nu i (positive_of_mem_band i hb) (θ := theta i b)).tendsto.comp hp
  change Tendsto (fun y : ℝ => theta i y/(xi i)*nu i y (theta i y)) (𝓝[band i] b)
    (𝓝 (theta i b/(xi i)*nu i b (theta i b)))
  exact (ht.div_const (xi i)).mul hn

end CoefficientContinuity

theorem actual_fixed_parameter_derivative (i : Row) {b s : ℝ}
    (hb : b ∈ band i) (hs : 0 ≤ s) :
    HasDerivAt (FixedTiltPhysicalDerivative.objective i (law i : Measure (ℝ × ℝ)) rho s)
      (-s/(xi i)*nu i b s) b := by
  exact FixedTiltPhysicalDerivative.objective_hasDerivAt i
    (law i : Measure (ℝ × ℝ)) (positive_of_mem_band i hb) hs rho
    (full_bid_cap i) ((full_saturation_guard i).trans_le hb.1)
    (full_bid_singleton_null i b)

theorem canonicalRate_hasDerivWithinAt_physical (i : Row) {b : ℝ} (hb : b ∈ band i) :
    HasDerivWithinAt (fun a => canonicalRate i (a/cutoff i)) (-A i b) (band i) b := by
  have hD : ContinuousAt
      (fun p : ℝ × ℝ => -p.1/(xi i)*nu i p.2 p.1) (theta i b,b) := by
    have hswap : Tendsto (fun p : ℝ × ℝ => (p.2,p.1)) (𝓝 (theta i b,b))
        (𝓝 (b,theta i b)) := (continuous_snd.prodMk continuous_fst).tendsto _
    have hn : ContinuousAt (fun p : ℝ × ℝ => nu i p.2 p.1) (theta i b,b) := by
      simpa only [Function.comp_def] using!
        (continuousAt_nu i (positive_of_mem_band i hb) (θ := theta i b)).tendsto.comp hswap
    exact (continuous_fst.continuousAt.neg.div_const (xi i)).mul hn
  have hh := SelectedMaximumDerivative.hasDerivWithinAt_selected_max
    (FixedTiltPhysicalDerivative.objective i (law i : Measure (ℝ × ℝ)) rho)
    (fun s a => -s/(xi i)*nu i a s)
    (fun a => canonicalRate i (a/cutoff i)) (theta i) hb
    (continuousOn_theta i b hb) (fun a ha => (theta_pos i ha).le)
    (fun a ha => physical_rate_attained i ha)
    (fun a ha s _ => physical_objective_le_rate i ha s)
    (fun a ha s hs => actual_fixed_parameter_derivative i ha hs) hD
  simpa only [A,neg_div,neg_mul,band] using! hh

theorem canonicalRate_hasDerivAt_physical (i : Row) {b : ℝ}
    (hb : b ∈ Ioo (cutoff i/2) (entry i)) :
    HasDerivAt (fun a => canonicalRate i (a/cutoff i)) (-A i b) b := by
  apply (canonicalRate_hasDerivWithinAt_physical i ⟨hb.1.le,hb.2⟩).hasDerivAt
  exact mem_of_superset (isOpen_Ioo.mem_nhds hb) (fun a ha => ⟨ha.1.le,ha.2⟩)

theorem A_eq_negative_physical_deriv (i : Row) {b : ℝ}
    (hb : b ∈ Ioo (cutoff i/2) (entry i)) :
    A i b= -deriv (fun a => canonicalRate i (a/cutoff i)) b := by
  rw [(canonicalRate_hasDerivAt_physical i hb).deriv,neg_neg]

theorem canonicalRate_hasDerivAt_normalized (i : Row) {z : ℝ}
    (hz : z ∈ Ioo (1/2:ℝ) (x i)) :
    HasDerivAt (canonicalRate i) (-(cutoff i)*A i (z*cutoff i)) z := by
  have hb : z*cutoff i ∈ Ioo (cutoff i/2) (entry i) := by
    constructor
    · nlinarith [mul_lt_mul_of_pos_right hz.1 (cutoff_pos i)]
    · simpa only [entry] using mul_lt_mul_of_pos_right hz.2 (cutoff_pos i)
  have hh := (canonicalRate_hasDerivAt_physical i hb).comp z
    ((hasDerivAt_id z).mul_const (cutoff i))
  have he : (fun a : ℝ => canonicalRate i ((a*cutoff i)/cutoff i))=canonicalRate i := by
    funext a
    rw [mul_div_cancel_right₀ a (cutoff_pos i).ne']
  change HasDerivAt (fun a : ℝ => canonicalRate i ((a*cutoff i)/cutoff i))
    (-A i (z*cutoff i)*(1*cutoff i)) z at hh
  rw [he] at hh
  convert! hh using 1
  ring

theorem original_matching_gradient_tendsto (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (law i)))
    {lo hi U : ℝ} (hlo : 0 < lo) (hU : 0 ≤ U)
    (hbox : ∀ n,∀ᵐ p ∂(G n : Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) U)
    (b s : ℕ → ℝ) {b0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hb0 : b0 ∈ band i)
    (hblim : Tendsto b atTop (𝓝 b0))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n)
        (G n : Measure (ℝ × ℝ)))) Prod.fst (s n)=
          (capacity (m n) : ℝ)/((m n-1 : ℕ) : ℝ)) :
    Tendsto (fun n => s n/(xi i)*(∫ q,FullReciprocalMean.reciprocal (b n) q
      ∂tiltedSource i (G n : Measure (ℝ × ℝ)) (b n) (s n))) atTop (𝓝 (A i b0)) := by
  have hp := fun n => hlo.trans_le (hb n).1
  have hz := normalized_mem_band i hb0
  obtain ⟨s0,hs0,hslim,hscore,_hrate,_hcost⟩ :=
    FullRateLimit.original_triangular_cost_limit i G hG b s hp hz
      (by simpa only [physical_scale] using hblim) m hm hmatch
  have heq : s0=theta i b0 := theta_unique i hb0 hscore
  subst s0
  let Θ := |theta i b0|+1
  have hΘ : 0 < Θ := by dsimp [Θ]; positivity
  let sclip := fun n => CompactStieltjes.clip (-Θ) Θ (s n)
  have hbθ : theta i b0 ∈ Icc (-Θ) Θ := by
    dsimp [Θ]
    constructor <;> linarith [neg_abs_le (theta i b0),le_abs_self (theta i b0)]
  have hc : Tendsto sclip atTop (𝓝 (theta i b0)) := by
    have hh := (CompactStieltjes.clip_continuous (-Θ) Θ).continuousAt.tendsto.comp hslim
    simpa only [sclip,Function.comp_def,CompactStieltjes.clip_eq hbθ] using! hh
  have ht := FixedTiltPhysicalDerivative.actual_triangular_gradient_limit i G hG hlo hU hbox
    b sclip hb (fun n => CompactStieltjes.clip_mem (by linarith) (s n)) hblim hc
  change Tendsto _ atTop (𝓝 (A i b0)) at ht
  apply ht.congr'
  have hleft : -Θ < theta i b0 := by dsimp [Θ]; linarith [neg_abs_le (theta i b0)]
  have hright : theta i b0 < Θ := by dsimp [Θ]; linarith [le_abs_self (theta i b0)]
  filter_upwards [hslim.eventually_const_lt hleft,hslim.eventually_lt_const hright]
    with n hn0 hn1
  simp only [sclip,CompactStieltjes.clip_eq ⟨hn0.le,hn1.le⟩]

end FCAppendix.Affine.Uniform06.OptimizedPhysicalRate
