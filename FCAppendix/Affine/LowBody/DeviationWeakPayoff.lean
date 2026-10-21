import FCAppendix.Affine.LowBody.DeviationNoiseBox

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory
open Existence.Distributional

variable {N : ℕ}
abbrev DeviationSample (d : ℝ) (N : ℕ) :=
  NoiseBox×(((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval)

def deviationPatternInput (d B : ℝ) (t : DeviationSample d N) : ℝ×ℝ×(Fin N→LowValue d) :=
  (t.2.1.1.1.1,(deviationPhysicalBid d B t.1 t.2.1.1.1 t.2.2).1,t.2.1.2)

@[fun_prop] theorem continuous_deviationPatternInput (d B : ℝ) :
    Continuous (deviationPatternInput (N:=N) d B) := by
  unfold deviationPatternInput
  have hc:= (continuous_deviationPhysicalBid d B).comp
    (show Continuous (fun t : DeviationSample d N=>(t.1,t.2.1.1.1,t.2.2)) by fun_prop)
  exact continuous_snd.fst.fst.fst.subtype_val.prodMk
    (hc.subtype_val.prodMk continuous_snd.fst.snd)

def deviationSampleLaw {d : ℝ} (e : NoiseBox)
    (M : ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d))) :
    ProbabilityMeasure (DeviationSample d N) :=
  productLaw (diracProba e) (productLaw M (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval))

theorem continuous_deviationSampleLaw (d : ℝ) :
    Continuous (fun p : NoiseBox×ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d))=>
      deviationSampleLaw p.1 p.2) :=
  continuous_productLaw.comp ((continuous_diracProba.comp continuous_fst).prodMk
    (continuous_productLaw.comp (continuous_snd.prodMk continuous_const)))

theorem deviationPatternInput_zero (d B : ℝ) (hB : 0<B)
    (s : (LowValue d×LowValue d)×(Fin N→LowValue d)) (z : unitInterval) :
    deviationPatternInput d B (zeroNoiseBox,s,z)=(s.1.1.1,min s.1.1.1 B,s.2) := by
  simp only [deviationPatternInput,deviationPhysicalBid_zero d B hB]

theorem deviationPattern_bad_null {d κ B : ℝ} (hκ : 0<κ) (hB : 0<B)
    (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G0 : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G0 : Measure (LowValue d))]
    (hvalue : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.1.1)
    (kind : Fin N→Fin 4) :
    (deviationSampleLaw (d:=d) (N:=N) zeroNoiseBox (productLaw pi0 (rowLaw N G0)) : Measure _)
      (deviationPatternInput d B ⁻¹' patternBadSet d κ kind)=0 := by
  have hm : MeasurableSet {t : DeviationSample d N |
      deviationPatternInput d B t∉patternBadSet d κ kind} :=
    ((isClosed_patternBadSet d κ kind).preimage (continuous_deviationPatternInput d B)).measurableSet.compl
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐt ∂(Measure.dirac zeroNoiseBox).prod
    (((productLaw pi0 (rowLaw N G0)) : Measure ((LowValue d×LowValue d)×(Fin N→LowValue d))).prod (volume : Measure unitInterval)),_
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  simp only [ae_dirac_eq,Filter.eventually_pure]
  have hm0 : MeasurableSet {t : ((LowValue d×LowValue d)×(Fin N→LowValue d))×unitInterval |
      deviationPatternInput d B (zeroNoiseBox,t)∉patternBadSet d κ kind} :=
    hm.preimage (measurable_const.prodMk measurable_id)
  apply (Measure.ae_prod_iff_ae_ae hm0).mpr
  simp_rw [deviationPatternInput_zero d B hB]
  simp only [Filter.eventually_const]
  change ∀ᵐs ∂((pi0 : Measure (LowValue d×LowValue d)).prod
    (rowLaw N G0 : Measure (Fin N→LowValue d))),_
  rw [rowLaw_eq_measure_pi]
  have hmc : MeasurableSet {s : (LowValue d×LowValue d)×(Fin N→LowValue d) |
      (s.1.1.1,min s.1.1.1 B,s.2)∉patternBadSet d κ kind} :=
    ((isClosed_patternBadSet d κ kind).preimage (by fun_prop)).measurableSet.compl
  apply (Measure.ae_prod_iff_ae_ae hmc).mpr
  filter_upwards [hvalue] with x hx
  have hpos : 0 < min x.1.1 B := lt_min hx hB
  filter_upwards [ae_pattern_ties_same_focalCopy hκ hpos.ne' (G0 : Measure (LowValue d)) kind] with r hr
  rintro (hn|⟨P,Q,hne,he⟩)
  · exact not_le_of_gt hpos hn
  · exact hne (hr P Q he)

theorem tendsto_integral_deviationPatternTest {d ξ B : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (hB : 0<B)
    (c : ℕ) (kind : Fin N→Fin 4) (a : C(LowValue d×LowValue d,ℝ))
    (pi0 : ProbabilityMeasure (LowValue d×LowValue d))
    (G0 : ProbabilityMeasure (LowValue d)) [NullSingletonClass (G0 : Measure (LowValue d))]
    (hvalue : ∀ᵐx ∂(pi0 : Measure (LowValue d×LowValue d)),0<x.1.1)
    (eps : ℕ→NoiseBox) (heps : Tendsto eps atTop (𝓝 zeroNoiseBox))
    (M : ℕ→ProbabilityMeasure ((LowValue d×LowValue d)×(Fin N→LowValue d)))
    (hM : Tendsto M atTop (𝓝 (productLaw pi0 (rowLaw N G0)))) :
    Tendsto (fun j=>∫t : DeviationSample d N,
      a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
        ∂(deviationSampleLaw (d:=d) (N:=N) (eps j) (M j) : Measure _)) atTop
      (𝓝 (∫t : DeviationSample d N,
        a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
          ∂(deviationSampleLaw (d:=d) (N:=N) zeroNoiseBox (productLaw pi0 (rowLaw N G0)) : Measure _))) := by
  let f : DeviationSample d N→ℝ:=fun t=>
    a t.2.1.1*patternActualPayoff d ξ c kind (deviationPatternInput d B t)
  let S : Set (DeviationSample d N):=deviationPatternInput d B ⁻¹' patternBadSet d (1-ξ) kind
  have hs : IsClosed S := (isClosed_patternBadSet d (1-ξ) kind).preimage
    (continuous_deviationPatternInput d B)
  have ha : Continuous (fun t : DeviationSample d N=>a t.2.1.1) :=
    a.continuous.comp (show Continuous (fun t : DeviationSample d N=>t.2.1.1) by fun_prop)
  have hm : Measurable f := ha.measurable.mul
    ((measurable_patternActualPayoff hξ hξ1 c kind).comp
      (continuous_deviationPatternInput (N:=N) d B).measurable)
  have hb (t : DeviationSample d N) : |f t|≤‖a‖*((4+2*|1-ξ|)*|d|) := by
    let v : (LowValue d×LowValue d)×(Fin N→LowValue d):=
      ((t.2.1.1.1,deviationPhysicalBid d B t.1 t.2.1.1.1 t.2.2),t.2.1.2)
    change |a t.2.1.1*physicalPatternPayoff d ξ c kind v|≤_
    rw [abs_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm t.2.1.1)
      (abs_physicalPatternPayoff_le hξ hξ1 c kind v) (abs_nonneg _) (norm_nonneg _)
  have hc : ∀t∉S,ContinuousAt f t := by
    intro t ht
    exact ha.continuousAt.mul
      ((continuousAt_patternActualPayoff_of_not_mem_bad hξ hξ1 c kind _ ht).comp
        (continuous_deviationPatternInput d B).continuousAt)
  have hseq : Tendsto (fun j=>deviationSampleLaw (d:=d) (N:=N) (eps j) (M j)) atTop
      (𝓝 (deviationSampleLaw (d:=d) (N:=N) zeroNoiseBox (productLaw pi0 (rowLaw N G0)))) := by
    have hp : Tendsto (fun j=>(eps j,M j)) atTop
        (𝓝 (zeroNoiseBox,productLaw pi0 (rowLaw N G0))) := heps.prodMk_nhds hM
    have hh:=((continuous_deviationSampleLaw (N:=N) d).tendsto
      (zeroNoiseBox,productLaw pi0 (rowLaw N G0))).comp hp
    simpa only [Function.comp_def] using hh
  have hnull : (deviationSampleLaw (d:=d) (N:=N) zeroNoiseBox (productLaw pi0 (rowLaw N G0)) :
      Measure (DeviationSample d N)) S=0 :=
    deviationPattern_bad_null (N:=N) (sub_pos.mpr hξ1) hB pi0 G0 hvalue kind
  exact tendsto_integral_of_closed_null_discontinuities f hm S hs hc
    (show 0≤‖a‖*((4+2*|1-ξ|)*|d|) by positivity) hb
    (fun j=>deviationSampleLaw (d:=d) (N:=N) (eps j) (M j))
    (deviationSampleLaw (d:=d) (N:=N) zeroNoiseBox (productLaw pi0 (rowLaw N G0))) hseq hnull

end FCAppendix.Affine.LowBody
