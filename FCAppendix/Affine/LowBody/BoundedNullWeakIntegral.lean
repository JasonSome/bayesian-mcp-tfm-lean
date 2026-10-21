import FCAppendix.Affine.LowBody.NoisyRow
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory Metric

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def nullCutoff (f : X→ℝ) (s : Set X) (r : ℝ) (x : X) : ℝ :=
  min 1 (infDist x s/r)*f x

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem continuous_nullCutoff (f : X→ℝ) (s : Set X) {r C : ℝ} (hr : 0<r) (_hC : 0≤C)
    (hbound : ∀x,|f x|≤C) (hcont : ∀x∉s,ContinuousAt f x) :
    Continuous (nullCutoff f s r) := by
  have hc : Continuous (fun x : X=>min 1 (infDist x s/r)) :=
    continuous_const.min ((continuous_infDist_pt s).div_const r)
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x∈s
  · have hx0 : nullCutoff f s r x=0 := by simp [nullCutoff,infDist_zero_of_mem hx]
    change Tendsto _ (𝓝 x) (𝓝 (nullCutoff f s r x))
    rw [hx0]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun y : X=>C*(infDist y s/r)) (𝓝 x) (𝓝 0) := by
      have hc' : Continuous (fun y : X=>C*(infDist y s/r)) :=
        continuous_const.mul ((continuous_infDist_pt s).div_const r)
      simpa only [infDist_zero_of_mem hx,zero_div,mul_zero] using hc'.continuousAt.tendsto (x:=x)
    apply squeeze_zero (fun _=>norm_nonneg _) (fun y=>?_) ht
    change |min 1 (infDist y s/r)*f y|≤C*(infDist y s/r)
    have hd : 0 ≤ infDist y s/r := div_nonneg infDist_nonneg hr.le
    rw [abs_mul,abs_of_nonneg (le_min zero_le_one hd)]
    exact (mul_le_mul (min_le_right _ _) (hbound y) (abs_nonneg _) hd).trans_eq (mul_comm _ _)
  · exact hc.continuousAt.mul (hcont x hx)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
theorem nullCutoff_abs_le (f : X→ℝ) (s : Set X) {r C : ℝ} (hr : 0<r) (_hC : 0≤C)
    (hbound : ∀x,|f x|≤C) (x : X) : |nullCutoff f s r x|≤C := by
  have hd : 0 ≤ infDist x s/r := div_nonneg infDist_nonneg hr.le
  rw [nullCutoff,abs_mul,abs_of_nonneg (le_min zero_le_one hd)]
  exact (mul_le_mul (min_le_left _ _) (hbound x) (abs_nonneg _) zero_le_one).trans_eq (one_mul C)

theorem nullCutoff_integral_error (f : X→ℝ) (hf : Measurable f) (s : Set X) (hs : s.Nonempty)
    {r C : ℝ} (hr : 0<r) (hC : 0≤C) (hbound : ∀x,|f x|≤C)
    (hcont : ∀x∉s,ContinuousAt f x) (mu : ProbabilityMeasure X) :
    |(∫x,f x ∂(mu : Measure X))-(∫x,nullCutoff f s r x ∂(mu : Measure X))|≤
      2*C*(mu : Measure X).real (cthickening r s) := by
  have hfi : Integrable f (mu : Measure X) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ (fun x=>by simpa only [Real.norm_eq_abs] using hbound x))
  have hgi : Integrable (nullCutoff f s r) (mu : Measure X) :=
    (ContinuousMap.equivBoundedOfCompact _ _ ⟨_,continuous_nullCutoff f s hr hC hbound hcont⟩).integrable _
  have hE : MeasurableSet (cthickening r s) := isClosed_cthickening.measurableSet
  have hb (x : X) : ‖f x-nullCutoff f s r x‖≤(cthickening r s).indicator (fun _=>2*C) x := by
    by_cases hx : x∈cthickening r s
    · rw [Set.indicator_of_mem hx,Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith [hbound x,nullCutoff_abs_le f s hr hC hbound x])
    · rw [Set.indicator_of_notMem hx]
      have hd : r < infDist x s := by
        apply lt_of_not_ge
        intro h
        apply hx
        exact (ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hs) hr.le).mpr h
      have hratio : 1 ≤ infDist x s/r := (le_div_iff₀ hr).mpr (by linarith)
      simp only [nullCutoff,min_eq_left hratio,one_mul,sub_self,norm_zero,le_refl]
  rw [←integral_sub hfi hgi,←Real.norm_eq_abs]
  have hh := norm_integral_le_of_norm_le
    ((integrable_const (μ:=(mu : Measure X)) (2*C)).indicator hE)
    (ae_of_all (mu : Measure X) hb)
  rw [integral_indicator_const (2*C) hE,smul_eq_mul] at hh
  exact hh.trans_eq (mul_comm _ _)

theorem tendsto_integral_of_closed_null_discontinuities (f : X→ℝ) (hf : Measurable f)
    (s : Set X) (hs : IsClosed s) (hcont : ∀x∉s,ContinuousAt f x)
    {C : ℝ} (hC : 0≤C) (hbound : ∀x,|f x|≤C)
    (mu : ℕ→ProbabilityMeasure X) (mu0 : ProbabilityMeasure X)
    (ht : Tendsto mu atTop (𝓝 mu0)) (hnull : (mu0 : Measure X) s=0) :
    Tendsto (fun j=>∫x,f x ∂(mu j : Measure X)) atTop (𝓝 (∫x,f x ∂(mu0 : Measure X))) := by
  by_cases hsne : s.Nonempty
  · apply Metric.tendsto_nhds.mpr
    intro e he
    let eta := e/(8*(C+1))
    have heta : 0<eta := by dsimp [eta]; positivity
    have hetaEq : eta*(8*(C+1))=e := by dsimp [eta]; field_simp
    have hct := tendsto_measure_cthickening_of_isClosed (μ:=(mu0 : Measure X))
      (s:=s) ⟨1,zero_lt_one,measure_ne_top _ _⟩ hs
    rw [hnull] at hct
    have hsmall : ∀ᶠr in 𝓝[>] (0:ℝ),(mu0 : Measure X) (cthickening r s)<ENNReal.ofReal eta :=
      (hct.mono_left nhdsWithin_le_nhds) (Iio_mem_nhds (ENNReal.ofReal_pos.mpr heta))
    obtain ⟨r,hrsmall,hr⟩ := (hsmall.and self_mem_nhdsWithin).exists
    let g : C(X,ℝ):=⟨nullCutoff f s r,continuous_nullCutoff f s hr hC hbound hcont⟩
    have hg := (ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp ht
    have hgnear : ∀ᶠj in atTop,|(∫x,g x ∂(mu j : Measure X))-(∫x,g x ∂(mu0 : Measure X))|<e/2 := by
      simpa only [Real.dist_eq,Function.comp_def] using (Metric.tendsto_nhds.mp hg (e/2) (half_pos he))
    have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto ht (isClosed_cthickening : IsClosed (cthickening r s))
    have hmass : ∀ᶠj in atTop,(mu j : Measure X) (cthickening r s)<ENNReal.ofReal eta :=
      eventually_lt_of_limsup_lt (hlimsup.trans_lt hrsmall)
    filter_upwards [hgnear,hmass] with j hj hmassj
    have herrj := nullCutoff_integral_error f hf s hsne hr hC hbound hcont (mu j)
    have herr0 := nullCutoff_integral_error f hf s hsne hr hC hbound hcont mu0
    have hmj : (mu j : Measure X).real (cthickening r s)≤eta := (ENNReal.toReal_lt_of_lt_ofReal hmassj).le
    have hm0 : (mu0 : Measure X).real (cthickening r s)≤eta := (ENNReal.toReal_lt_of_lt_ofReal hrsmall).le
    have hEj := herrj.trans (mul_le_mul_of_nonneg_left hmj (mul_nonneg (by norm_num) hC))
    have hE0 := herr0.trans (mul_le_mul_of_nonneg_left hm0 (mul_nonneg (by norm_num) hC))
    rw [Real.dist_eq]
    have htri := (abs_sub_le (∫x,f x ∂(mu j : Measure X)) (∫x,g x ∂(mu j : Measure X))
      (∫x,f x ∂(mu0 : Measure X))).trans (add_le_add le_rfl
        (abs_sub_le (∫x,g x ∂(mu j : Measure X)) (∫x,g x ∂(mu0 : Measure X))
          (∫x,f x ∂(mu0 : Measure X))))
    have hE0' : |(∫x,g x ∂(mu0 : Measure X))-(∫x,f x ∂(mu0 : Measure X))|≤2*C*eta := by
      change |(∫x,nullCutoff f s r x ∂(mu0 : Measure X))-(∫x,f x ∂(mu0 : Measure X))|≤2*C*eta
      rw [abs_sub_comm]
      exact hE0
    change |(∫x,f x ∂(mu j : Measure X))-(∫x,f x ∂(mu0 : Measure X))|<e
    change |(∫x,f x ∂(mu j : Measure X))-(∫x,g x ∂(mu j : Measure X))|≤2*C*eta at hEj
    nlinarith [hetaEq]
  · have hempty : s=∅ := Set.not_nonempty_iff_eq_empty.mp hsne
    have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x=>hcont x (by simp [hempty]))
    let g : C(X,ℝ) := ⟨f,hc⟩
    exact (ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp ht

end FCAppendix.Affine.LowBody
