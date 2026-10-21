import FCAppendix.Affine.LowBody.FiniteCopyContinuity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology
open scoped BigOperators

abbrev uniformNoise : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)

instance uniformNoise_probability : IsProbabilityMeasure uniformNoise := by
  constructor
  simp [uniformNoise,Real.volume_Icc]

theorem uniformNoise_support : ∀ᵐz ∂uniformNoise,z∈Icc (0:ℝ) 1 :=
  ae_restrict_mem measurableSet_Icc

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [Nonempty A]

def parameterBids (i : ι) (t : ℝ×ℝ×(ι→ℝ)) : ℝ×(ι→ℝ) :=
  (t.1,Function.update t.2.2 i (t.1*t.2.1))

omit [Fintype ι] in
theorem continuous_parameterBids (i : ι) : Continuous (parameterBids i) := by
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro j
  by_cases hji : j=i
  · subst j
    simp only [Function.update_self]
    fun_prop
  · simp only [Function.update_of_ne hji]
    fun_prop

def parameterPurePayoff (pair : A→Finset ι × Finset ι) (κ ε : ℝ) (i : ι)
    (t : ℝ×ℝ×(ι→ℝ)) : ℝ :=
  pureSmoothedPayoff pair uniformNoise κ ε i (parameterBids i t)

omit [Fintype ι] in
theorem parameterPurePayoff_at_zero (pair : A→Finset ι × Finset ι) (κ ε : ℝ)
    (i : ι) (t : ℝ×ℝ×(ι→ℝ)) (ht : t.1=0) :
    parameterPurePayoff pair κ ε i t=0 := by
  unfold parameterPurePayoff pureSmoothedPayoff pureNoisyPayoff purePayoff
  simp [parameterBids,noisyFocal,ht]

omit [Fintype ι] in

theorem continuousAt_parameterPurePayoff_zero (pair : A→Finset ι × Finset ι)
    (κ ε : ℝ) (i : ι) (t₀ : ℝ×ℝ×(ι→ℝ)) (ht : t₀.1=0) :
    ContinuousAt (parameterPurePayoff pair κ ε i) t₀ := by
  apply Metric.tendsto_nhds.mpr
  intro e he
  rw [parameterPurePayoff_at_zero pair κ ε i t₀ ht]
  let C : ℝ:=1+(1+2*|κ|)*((|t₀.2.1|+1)*(1+|ε|))
  have hC : 0<C := by dsimp [C]; positivity
  have hq : ∀ᶠt : ℝ×ℝ×(ι→ℝ) in 𝓝 t₀,|t.2.1| < |t₀.2.1|+1 :=
    (show ContinuousAt (fun t : ℝ×ℝ×(ι→ℝ)=>|t.2.1|) t₀ from by fun_prop)
      (Iio_mem_nhds (by linarith))
  have hw : ∀ᶠt : ℝ×ℝ×(ι→ℝ) in 𝓝 t₀,|t.1|<e/C := by
    have hc : ContinuousAt (fun t : ℝ×ℝ×(ι→ℝ)=>|t.1|) t₀ := by fun_prop
    exact hc (Iio_mem_nhds (by simpa only [ht,abs_zero] using div_pos he hC))
  filter_upwards [hq,hw] with t hqt hwt
  have hbound : ∀ᵐz ∂uniformNoise,
      ‖pureNoisyPayoff pair κ ε i (parameterBids i t) z‖≤C*|t.1| := by
    filter_upwards [uniformNoise_support] with z hz
    let b:=(parameterBids i t).2
    let bids:=noisyFocal i ε b z
    let P:=pair (FiniteSelector.select (fun a=>CompleteInformation.potential κ bids (pair a).1 (pair a).2))
    change |purePayoff κ t.1 bids P i|≤C*|t.1|
    have hb : |b i|=|t.1| *|t.2.1| := by simp [b,parameterBids,abs_mul]
    have hn:=abs_noisyFocal_le i ε b z hz
    change |bids i|≤_ at hn
    rw [hb] at hn
    have hnon : 0≤1+2*|κ| := by positivity
    calc
      _≤|t.1|+(1+2*|κ|)*|bids i|:=abs_purePayoff_le κ t.1 bids P i
      _≤|t.1|+(1+2*|κ|)*((|t.1| *|t.2.1|)*(1+|ε|)):=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hn hnon)
      _≤|t.1|+(1+2*|κ|)*((|t.1| *(|t₀.2.1|+1))*(1+|ε|)):=by
        gcongr
      _=C*|t.1|:=by dsimp [C]; ring
  have hi : |parameterPurePayoff pair κ ε i t|≤C*|t.1| := by
    simpa only [parameterPurePayoff,pureSmoothedPayoff,Real.norm_eq_abs,
      probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hbound
  rw [dist_zero_right,Real.norm_eq_abs]
  have hsmall : C*|t.1|<e := by nlinarith [(lt_div_iff₀ hC).mp hwt]
  exact hi.trans_lt hsmall

theorem continuousAt_parameterPurePayoff (pair : A→Finset ι × Finset ι)
    {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0) (i : ι)
    (t₀ : ℝ×ℝ×(ι→ℝ)) (hq : t₀.2.1≠0) :
    ContinuousAt (parameterPurePayoff pair κ ε i) t₀ := by
  by_cases hw : t₀.1=0
  · exact continuousAt_parameterPurePayoff_zero pair κ ε i t₀ hw
  · have hb : (parameterBids i t₀).2 i≠0 := by
      simpa only [parameterBids,Function.update_self] using mul_ne_zero hw hq
    exact (continuousAt_pureSmoothedPayoff pair uniformNoise uniformNoise_support
      hκ hε i (parameterBids i t₀) hb).comp
      (f:=parameterBids i) (x:=t₀) (continuous_parameterBids i).continuousAt

theorem continuous_parameterPurePayoff_positive (pair : A→Finset ι × Finset ι)
    {κ ε : ℝ} (hκ : 0<κ) (hε : ε≠0) (i : ι) :
    Continuous (fun t : ℝ×Ioi (0:ℝ)×(ι→ℝ)=>
      parameterPurePayoff pair κ ε i (t.1,t.2.1.1,t.2.2)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hmap : Continuous (fun t : ℝ×Ioi (0:ℝ)×(ι→ℝ)=>(t.1,t.2.1.1,t.2.2)) := by
    fun_prop
  exact (continuousAt_parameterPurePayoff pair hκ hε i (t.1,t.2.1.1,t.2.2) t.2.1.2.ne').comp
    (f:=fun t : ℝ×Ioi (0:ℝ)×(ι→ℝ)=>(t.1,t.2.1.1,t.2.2)) (x:=t) hmap.continuousAt

end FCAppendix.Affine.LowBody
