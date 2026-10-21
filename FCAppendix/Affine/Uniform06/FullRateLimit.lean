import FCAppendix.Affine.Uniform06.FullBidGeometry
import FCAppendix.Affine.Uniform06.PhysicalExposureLimit
import FCAppendix.Affine.Uniform06.RawTiltedSource
import FCAppendix.Affine.Uniform07.TiltCertificate

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FullRateLimit

open MeasureTheory ProbabilityTheory Set Filter Topology
open Uniform07 FullJointLaw FullBidGeometry FullSourceSpecialization
open PhysicalExposureLimit MixedWeakLimits RawTiltedSource

theorem mean_eq_rho_implies_score_zero (i : Row) {z θ : ℝ}
    (hz : z ∈ Icc (1/2:ℝ) (x i))
    (hm : SubentryTilt.mean (sourceLaw i z) id θ=rho) : tiltScore i θ z=0 := by
  have hZ := mgf_pos (sourceLaw_exp_integrable i hz (-θ))
  rw [SubentryTilt.mean_eq_ratio (sourceLaw i z) measurable_id (sourceLaw_bounds i hz) θ] at hm
  have he := (div_eq_iff hZ.ne').mp hm
  dsimp only [id] at he
  rw [sourceLaw_score_moment i hz θ]
  linarith

theorem original_triangular_cost_limit (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (law i)))
    (b θ : ℕ → ℝ) (hb : ∀ n,0 < b n)
    {z : ℝ} (hz : z ∈ Ico (1/2:ℝ) (x i))
    (hblim : Tendsto b atTop (𝓝 (z*cutoff i)))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (hmatch : ∀ᶠ n in atTop,
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n)
        (G n:Measure (ℝ × ℝ)))) Prod.fst (θ n)=
          (capacity (m n):ℝ)/((m n-1:ℕ):ℝ)) :
    ∃ θ0 > (0:ℝ),Tendsto θ atTop (𝓝 θ0) ∧ tiltScore i θ0 z=0 ∧
      canonicalRate i z=objective i θ0 z ∧
      Tendsto (fun n => ExactUntilting.cost (RawMixedSource.source i (G n:Measure (ℝ × ℝ)))
        (RawMixedSource.demand (xi i) (b n)) (θ n) (capacity (m n)) (m n-1)/((m n-1:ℕ):ℝ))
        atTop (𝓝 (canonicalRate i z)) := by
  have hb0 : 0 < z*cutoff i := mul_pos (by linarith [hz.1]) (cutoff_pos i)
  let ν := fun n => lowerProbability i (G n) (b n) (hb n)
  let ν0 := lowerProbability i (law i) (z*cutoff i) hb0
  letI (n : ℕ) : IsProbabilityMeasure (MixedLaw.physicalLowerLaw i (b n) (G n:Measure (ℝ × ℝ))) :=
    MixedLaw.physicalLowerLaw_probability i (hb n) (G n:Measure (ℝ × ℝ))
  letI : IsProbabilityMeasure (MixedLaw.physicalLowerLaw i (z*cutoff i) (law i:Measure (ℝ × ℝ))) :=
    MixedLaw.physicalLowerLaw_probability i hb0 (law i:Measure (ℝ × ℝ))
  have hν := fun n => MixedLaw.physicalLowerLaw_bounds i (hb n) (G n:Measure (ℝ × ℝ))
  have hν0 := MixedLaw.physicalLowerLaw_bounds i hb0 (law i:Measure (ℝ × ℝ))
  have hw : Tendsto ν atTop (𝓝 ν0) := lowerProbability_tendsto i G (law i) hG b hb hb0 hblim
  have hc := ActiveGraphComponent.original_active_graph_continuous_component i
    (law i:Measure (ℝ × ℝ)) (full_value_marginal i) (full_active_graph i) z ⟨hz.1,hz.2.le⟩
  have hgap : rho < rho+(1-x i)*(entry i-z*cutoff i) := by
    have hx : 0 < 1-x i := by cases i <;> norm_num [x,xQ]
    have he : 0 < entry i-z*cutoff i := by unfold entry; nlinarith [cutoff_pos i,hz.2]
    linarith [mul_pos hx he]
  obtain ⟨θ0,hθ0,hm0⟩ := EarlyMean.exists_matching_tilt_early_law i (law i:Measure (ℝ × ℝ))
    (full_value_marginal i) (full_below_value i) (full_active_graph i) hz
    (by norm_num [rho] : 0 < rho) hgap
  have ht : Tendsto θ atTop (𝓝 θ0) := mixed_matching_tilts_tendsto i ν ν0 hν hν0 hw
    hc.1 hc.2 θ (fun n => (capacity (m n):ℝ)/((m n-1:ℕ):ℝ))
    (PhysicalRates.rival_capacity_density_tendsto.comp hm) hmatch hm0
  have hp : MeasurePreserving Prod.fst (MixedLaw.law i (ν0:Measure ℝ)) (sourceLaw i z) :=
    ⟨measurable_fst,full_mixed_demand_law i ⟨hz.1,hz.2.le⟩⟩
  have hpt := RawTiltedSource.tilted_preserving hp (measurable_id.const_mul (-θ0))
  have hm0' : SubentryTilt.mean (sourceLaw i z) id θ0=rho := by
    have hh : SubentryTilt.mean (MixedLaw.law i (ν0:Measure ℝ)) Prod.fst θ0=
        SubentryTilt.mean (sourceLaw i z) id θ0 := by
      unfold SubentryTilt.mean
      rw [←hpt.map_eq]
      exact (integral_map hpt.measurable.aemeasurable measurable_id.aestronglyMeasurable).symm
    rw [← hh]
    exact hm0
  have hs := mean_eq_rho_implies_score_zero i ⟨hz.1,hz.2.le⟩ hm0'
  have hrate := source_tilt_rate i ⟨hz.1,hz.2.le⟩ hθ0.1.le hs
  have hZ := normalizer_tendsto i ν ν0 hν hν0 hw (fun n => -θ n) ht.neg
  have hlog := hZ.log (normalizer_pos i (ν0:Measure ℝ) hν0 (-θ0)).ne'
  have hcg : Tendsto (fun n => cgf Prod.fst (MixedLaw.law i (ν n:Measure ℝ)) (-θ n))
      atTop (𝓝 (cgf id (sourceLaw i z) (-θ0))) := by
    have he (n : ℕ) : cgf Prod.fst (MixedLaw.law i (ν n:Measure ℝ)) (-θ n)=
        Real.log (normalizer i (ν n:Measure ℝ) (-θ n)) := by
      rw [cgf,← normalizer_eq_mgf i (ν n:Measure ℝ) (hν n)]
    have he0 : Real.log (normalizer i (ν0:Measure ℝ) (-θ0))=cgf id (sourceLaw i z) (-θ0) := by
      rw [normalizer_eq_mgf i (ν0:Measure ℝ) hν0]
      exact cgf_comp_of_preserving hp measurable_id (-θ0)
    simpa only [he,he0] using hlog
  have hlimit := (ht.neg.mul (PhysicalRates.rival_capacity_density_tendsto.comp hm)).sub hcg
  have hobj : -θ0*rho-cgf id (sourceLaw i z) (-θ0)=canonicalRate i z := by
    calc
      _=objective i θ0 z := by
        convert! (source_objective_eq_cgf i ⟨hz.1,hz.2.le⟩ θ0).symm using 1
      _=canonicalRate i z := hrate.symm
  rw [hobj] at hlimit
  refine ⟨θ0,hθ0.1,ht,hs,hrate,?_⟩
  apply hlimit.congr'
  filter_upwards [hm.eventually_ge_atTop 2] with n hn
  have hN : (0:ℝ)<((m n-1:ℕ):ℝ) := by exact_mod_cast (show 0 < m n-1 by omega)
  rw [source_cost_eq_mixed_cost i (G n:Measure (ℝ × ℝ)) (hb n)]
  change -θ n*((capacity (m n):ℝ)/((m n-1:ℕ):ℝ))-
    cgf Prod.fst (MixedLaw.law i (MixedLaw.physicalLowerLaw i (b n) (G n:Measure (ℝ × ℝ)))) (-θ n)=_
  dsimp only [ExactUntilting.cost]
  field_simp [hN.ne']

end FCAppendix.Affine.Uniform06.FullRateLimit
