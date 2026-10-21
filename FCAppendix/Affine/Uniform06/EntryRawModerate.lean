import FCAppendix.Affine.Uniform06.EntryRawTiltedFiber
import FCAppendix.Affine.Uniform06.EntryRawCentral
import FCAppendix.Affine.Uniform06.EntryTilts
import FCAppendix.Affine.Uniform06.EntryWeightedLaplace
import FCAppendix.Affine.Uniform06.EntryProfileConcentration

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawModerate

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.ExponentialTilt
open EntryEarlySourceLimits EntryRawTiltedFiber EntryRawCentral
open scoped BigOperators

section SmallTilt
variable {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]

theorem small_tilt_mean_tendsto
    (X f : (m : ℕ) → Ω m → ℝ) (hX : ∀ m, Measurable (X m))
    (hf : ∀ m, Measurable (f m))
    (hXb : ∀ m, ∀ᵐ x ∂μ m,X m x ∈ Icc (0:ℝ) 1)
    (hfb : ∀ m, ∀ᵐ x ∂μ m,f m x ∈ Icc (0:ℝ) 1)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) {a : ℝ}
    (ha : Tendsto (fun m => ∫ x, f m x ∂μ m) atTop (𝓝 a)) :
    Tendsto (fun m => ∫ x, f m x ∂(μ m).tilted (fun x => u m*X m x)) atTop (𝓝 a) := by
  have hb (m) := integral_tilted_bounds (μ m) (hX m) (hXb m)
    (le_refl |u m|) (Integrable.of_mem_Icc 0 1 (hf m).aemeasurable (hfb m))
    ((hfb m).mono fun _ hx => hx.1)
  have hl : Tendsto (fun m => Real.exp (-2*|u m|)*(∫ x, f m x ∂μ m)) atTop (𝓝 a) := by
    have he := (Real.continuous_exp.tendsto (-2*|(0:ℝ)|)).comp (hu.abs.const_mul (-2))
    simpa using! he.mul ha
  have hr : Tendsto (fun m => Real.exp (2*|u m|)*(∫ x, f m x ∂μ m)) atTop (𝓝 a) := by
    have he := (Real.continuous_exp.tendsto (2*|(0:ℝ)|)).comp (hu.abs.const_mul 2)
    simpa using! he.mul ha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr
    (Eventually.of_forall fun m => (hb m).1) (Eventually.of_forall fun m => (hb m).2)

end SmallTilt

section Original
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem raw_mean_formula (i : Row) (V B : Ω → ℝ) (hV : Measurable V)
    (hB : Measurable B) {b : ℝ} (hb : 0 < b) :
    RawMixedSource.mean i (joint μ V B) b=
      (1-cutoff i)/2+cutoff i*(∫ ω, exposure (xi i) b (B ω) ∂μ) := by
  let G := joint μ V B
  letI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map (hV.prodMk hB).aemeasurable
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  have he := RawMixedSource.integral_source_test i G hb Prod.fst measurable_fst
  change RawMixedSource.mean i G b=_ at he
  rw [he,EarlyMean.physical_mean_formula i hb G]
  dsimp only [G,joint]
  rw [integral_map (f := fun p : ℝ × ℝ => exposure (xi i) b p.2) (hV.prodMk hB).aemeasurable
      ((continuous_exposure (xi_pos i) hb).measurable.comp measurable_snd).aestronglyMeasurable]

theorem raw_mean_tendsto (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hb : Tendsto b atTop (𝓝 (entry i))) :
    Tendsto (fun m => RawMixedSource.mean i (joint μ V (B m)) (b m)) atTop (𝓝 rho) := by
  have hlim := EntryActiveLimit.entry_exposure_tendsto_ae μ V B
    (ActiveGraphComponent.activeBid i) (xi_pos i) (EarlyMean.entry_pos i) b hb
    hadmissible (fixed_value_null μ i V hV hvalue (entry i)) hactive
  have hi := EntryActiveMoments.bounded_power_integral_tendsto μ
    (fun m ω => exposure (xi i) (b m) (B m ω)) (entryExposure i V)
    (fun m => (continuous_exposure (xi_pos i) (hbp m)).measurable.comp (hB m))
    (fun m => ae_of_all _ fun ω =>
      ⟨exposure_nonneg (xi_pos i) (hbp m),exposure_le_one _ _ _⟩) hlim 1
  simp only [pow_one,entryExposure_mean μ i V hV hvalue] at hi
  have hμ : Tendsto (fun m => (1-cutoff i)/2+cutoff i*
      (∫ ω, exposure (xi i) (b m) (B m ω) ∂μ)) atTop
      (𝓝 ((1-cutoff i)/2+cutoff i*PrefixRoot.requiredDemand i)) :=
    tendsto_const_nhds.add (hi.const_mul (cutoff i))
  have he : (1-cutoff i)/2+cutoff i*PrefixRoot.requiredDemand i=rho := by
    unfold PrefixRoot.requiredDemand
    field_simp [(cutoff_pos i).ne']
    norm_num [rho,delta]
  rw [he] at hμ
  simpa only [raw_mean_formula μ i V _ hV (hB _) (hbp _)] using hμ

def theta (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (b : ℕ → ℝ) (n : ℕ → ℕ) : ℕ → ℝ :=
  EntryTilts.moderateTilt
    (fun m => RawMixedSource.source i (joint μ V (B m)))
    (fun m => RawMixedSource.demand (xi i) (b m))
    (fun m => (capacity (n m):ℝ)/((n m-1:ℕ):ℝ))

lemma gap_sqrt_eq_negative_center (i : Row) (G : Measure (ℝ × ℝ))
    {N C : ℕ} (hN : 0 < N) (b : ℝ) :
    (RawMixedSource.mean i G b-(C:ℝ)/(N:ℝ))*Real.sqrt (N:ℝ)=
      -EntryRawCentral.center i G N C b := by
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  have hs : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hNr).ne'
  have hsq := Real.sq_sqrt hNr.le
  unfold EntryRawCentral.center
  field_simp [hNr.ne',hs]
  nlinarith [congrArg (fun z : ℝ => ((N:ℝ)*RawMixedSource.mean i G b-(C:ℝ))*z) hsq]

theorem original_moderate_tilt
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hbt : ∀ m,b m ≤ cutoff i)
    (hb : Tendsto b atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    (hmoderate : Tendsto (fun m => -center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop) :
    let ν := fun m => RawMixedSource.source i (joint μ V (B m))
    let X := fun m => RawMixedSource.demand (xi i) (b m)
    let r := fun m => (capacity (n m):ℝ)/((n m-1:ℕ):ℝ)
    let θ := theta μ i V B b n
    (∀ᶠ m in atTop,EntryTilts.Matches ν X r m (θ m)) ∧
    Tendsto θ atTop (𝓝 0) ∧
    Tendsto (fun m => θ m*Real.sqrt ((n m-1:ℕ):ℝ)) atTop atTop ∧
    Tendsto (fun m => variance (X m) (rawTilt i (joint μ V (B m)) (b m) (-θ m)))
      atTop (𝓝 (limitingVariance μ i V)) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let ν := fun m => RawMixedSource.source i (G m)
  let X := fun m => RawMixedSource.demand (xi i) (b m)
  let r := fun m => (capacity (n m):ℝ)/((n m-1:ℕ):ℝ)
  have hX := fun m => RawMixedSource.measurable_demand (xi i) (b m)
  have hXb : ∀ m, ∀ᵐ x ∂ν m,X m x ∈ Icc (0:ℝ) 1 :=
    fun m => ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (hbp m))
  have hv := limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb
  have hvar := raw_variance_tendsto μ i V B hV hB hvalue hadmissible hactive b hbp hb
  have hgap : Tendsto (fun m => (∫ x, X m x ∂ν m)-r m) atTop (𝓝 0) := by
    have h := (raw_mean_tendsto μ i V B hV hB hvalue hadmissible hactive b hbp hb).sub
      (PhysicalRates.rival_capacity_density_tendsto.comp hn)
    simpa only [sub_self,G,ν,X,r,RawMixedSource.mean,Function.comp_def] using! h
  have hmod : Tendsto (fun m => ((∫ x, X m x ∂ν m)-r m)*
      Real.sqrt ((n m-1:ℕ):ℝ)) atTop atTop := by
    apply hmoderate.congr
    intro m
    exact (gap_sqrt_eq_negative_center i (G m) (by have := hnp m; omega) (b m)).symm
  have hpos : ∀ᶠ m in atTop,0 < (∫ x, X m x ∂ν m)-r m := by
    filter_upwards [hmod.eventually_gt_atTop 0] with m hm
    rcases mul_pos_iff.mp hm with hp | hn
    · exact hp.1
    · exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hn.2)
  refine ⟨EntryTilts.eventually_matches ν X r hX hXb hv hvar hgap hpos,
    EntryTilts.moderateTilt_tendsto_zero ν X r hX hXb hv hvar hgap hpos,
    EntryTilts.moderateTilt_mul_sqrt_tendsto_atTop ν X r (fun m => n m-1)
      hX hXb hv hvar hgap hpos hmod,
    EntryTilts.tilted_variance_tendsto ν X r hX hXb hv hvar hgap hpos⟩

theorem original_scalar_factorial_moments
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hbt : ∀ m,b m ≤ cutoff i)
    (hb : Tendsto b atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    (hmoderate : Tendsto (fun m => -center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop)
    {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : k ≤ 3) :
    let θ := theta μ i V B b n
    let _ν := fun m => RawMixedSource.source i (joint μ V (B m))
    let X := fun m => RawMixedSource.demand (xi i) (b m)
    let σ := fun m => Real.sqrt (((n m-1:ℕ):ℝ)*
      variance (X m) (rawTilt i (joint μ V (B m)) (b m) (-θ m)))
    Tendsto (fun m => σ m*(a*θ m)^(k+1)*
      (∫ r : Fin (n m-1) → RowRival,
        EntryLaplace.weightedMonomial (a*θ m) k
          ((capacity (n m):ℝ)-iidSum (X m) (n m-1) r)
        ∂Measure.pi (fun _ => rawTilt i (joint μ V (B m)) (b m) (-θ m))))
      atTop (𝓝 ((gaussianPDFReal 0 1 0)*(k.factorial:ℝ))) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let ν := fun m => RawMixedSource.source i (G m)
  let X := fun m => RawMixedSource.demand (xi i) (b m)
  let θ := theta μ i V B b n
  have hs := original_moderate_tilt μ i V B hV hB hvalue hadmissible hactive
    b hbp hbt hb n hnp hn hmoderate
  have hv := limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb
  have hvroot : Tendsto (fun m => Real.sqrt (variance (X m) (rawTilt i (G m) (b m) (-θ m))))
      atTop (𝓝 (Real.sqrt (limitingVariance μ i V))) := hs.2.2.2.sqrt
  have hw : Tendsto (fun m => (a*θ m)*Real.sqrt (((n m-1:ℕ):ℝ)*
      variance (X m) (rawTilt i (G m) (b m) (-θ m)))) atTop atTop := by
    have hh := (hs.2.2.1.const_mul_atTop ha).atTop_mul_pos (Real.sqrt_pos.mpr hv) hvroot
    simpa only [Real.sqrt_mul (Nat.cast_nonneg _),mul_assoc] using hh
  have hlim := EntryWeightedLaplace.actual_centered_tilt_weighted_moments ν X
    (fun m => -θ m) (fun m => a*θ m) (fun m => n m-1)
    (fun m => RawMixedSource.measurable_demand _ _)
    (fun m => ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (hbp m)))
    (PhysicalRates.rivals_tendsto.comp hn) hv hs.2.2.2 (by simpa using hs.2.1.const_mul a) hw hk
  apply hlim.congr'
  filter_upwards [hs.1] with m hm
  have hN : (0:ℝ)<((n m-1:ℕ):ℝ) := by exact_mod_cast (show 0 < n m-1 by have := hnp m; omega)
  have hcenter : ((n m-1:ℕ):ℝ)*(∫ x, X m x ∂(ν m).tilted (fun x => -θ m*X m x))=
      (capacity (n m):ℝ) := by
    have hmmean : (∫ x, X m x ∂(ν m).tilted (fun x => -θ m*X m x))=
        (capacity (n m):ℝ)/((n m-1:ℕ):ℝ) := hm.2.2.1
    rw [hmmean]
    field_simp [hN.ne']
  rw [← pi_tilted_eq_tilted_iidSum,hcenter]
  rfl

theorem original_tilted_profile_limits
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l u : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hlp : ∀ m,0 < l m)
    (hb : Tendsto b atTop (𝓝 (entry i))) (hl : Tendsto l atTop (𝓝 (entry i)))
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun m => ∫ r, rawWeight i (l m) r ∂rawTilt i (joint μ V (B m)) (b m) (u m))
      atTop (𝓝 (eligibleMass μ i V)) ∧
    Tendsto (fun m => ∫ r, rawWeight i (l m) r*rawH i (b m) r
      ∂rawTilt i (joint μ V (B m)) (b m) (u m)) atTop (𝓝 (eligibleHMass μ i V)) := by
  let ν := fun m => RawMixedSource.source i (joint μ V (B m))
  letI (m : ℕ) : IsProbabilityMeasure (joint μ V (B m)) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  have hp := raw_profile_limits μ i V B hV hB hvalue hadmissible hactive b l hbp hlp hb hl
  have hX := fun m => RawMixedSource.measurable_demand (xi i) (b m)
  have hXb := fun m => ae_of_all (ν m) (RawMixedSource.demand_bounds (xi_pos i) (hbp m))
  constructor
  · exact small_tilt_mean_tendsto ν (fun m => RawMixedSource.demand (xi i) (b m))
      (fun m => rawWeight i (l m)) hX (fun m => measurable_rawWeight i (l m)) hXb
      (fun m => ae_of_all _ (rawWeight_bounds i (l m))) u hu hp.1
  · apply small_tilt_mean_tendsto ν (fun m => RawMixedSource.demand (xi i) (b m))
      (fun m r => rawWeight i (l m) r*rawH i (b m) r) hX
      (fun m => (measurable_rawWeight i (l m)).mul (measurable_rawH i (b m))) hXb
      (fun m => ae_of_all _ fun r => ?_) u hu hp.2
    have hw := rawWeight_bounds i (l m) r
    have hh := rawH_bounds i (hbp m) r
    exact ⟨mul_nonneg hw.1 hh.1,by nlinarith [hw.1,hw.2,hh.1,hh.2]⟩

end Original
end FCAppendix.Affine.Uniform06.EntryRawModerate
