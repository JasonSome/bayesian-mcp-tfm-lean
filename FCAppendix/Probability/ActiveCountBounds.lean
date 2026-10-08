import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi
import FCAppendix.Probability.EmpiricalMean

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators ProbabilityTheory
variable {α : Type*} [MeasurableSpace α]

noncomputable def sampleCount (E : Set α) {N : ℕ} (r : Fin N → α) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => r i ∈ E).card

theorem measurable_sampleCount (E : Set α) (hE : MeasurableSet E) (N : ℕ) :
    Measurable (sampleCount (N := N) E) := by
  classical
  have he : sampleCount (N := N) E = fun r => ∑ i, if r i ∈ E then (1:ℕ) else 0 := by
    funext r
    simp [sampleCount]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hE.preimage (measurable_pi_apply i)) measurable_const measurable_const

theorem iid_indicator_lower_tail_le (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | (sampleCount E r:ℝ) ≤
        (N:ℝ)*(μ.real E-δ)} ≤ Real.exp (-2*(N:ℝ)*δ^2) := by
  classical
  let P := Measure.pi (fun _ : Fin N => μ)
  let f := E.indicator (fun _ : α => (1:ℝ))
  let X : Fin N → (Fin N → α) → ℝ := fun i r => μ.real E-f (r i)
  have hf : Measurable f := measurable_const.indicator hE
  have hfb (a : α) : f a ∈ Icc (0:ℝ) 1 := by
    dsimp only [f,indicator]
    split_ifs <;> norm_num
  have hfi : Integrable f μ := Integrable.of_mem_Icc 0 1 hf.aemeasurable (Eventually.of_forall hfb)
  have hmean : ∫ a, f a ∂μ = μ.real E := integral_indicator_one hE
  have hXmeas i : Measurable (X i) := measurable_const.sub (hf.comp (measurable_pi_apply i))
  have hind : iIndepFun X P := by
    exact iIndepFun_pi (fun _ : Fin N => (measurable_const.sub hf).aemeasurable)
  have hsub i : HasSubgaussianMGF (X i) (1/4:NNReal) P := by
    have hb : ∀ᵐ r ∂P, X i r ∈ Icc (μ.real E-1) (μ.real E) :=
      Eventually.of_forall fun r => ⟨by dsimp only [X]; linarith [(hfb (r i)).2],
        by dsimp only [X]; linarith [(hfb (r i)).1]⟩
    have hm : ∫ r, X i r ∂P = 0 := by
      rw [show X i = fun r => μ.real E-f (r i) from rfl]
      rw [integral_sub (integrable_const _) (integrable_comp_eval hfi)]
      rw [integral_comp_eval hf.aestronglyMeasurable,hmean]
      simp
    have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hXmeas i).aemeasurable hb hm
    convert hh using 1
    norm_num
  have he (r : Fin N → α) : ∑ i, X i r =
      (N:ℝ)*μ.real E-(sampleCount E r:ℝ) := by
    simp [X,f,indicator_apply,Finset.sum_sub_distrib,sampleCount]
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i) (show 0 ≤ (N:ℝ)*δ by positivity)
  have hsets : {r | (N:ℝ)*δ ≤ ∑ i, X i r} =
      {r | (sampleCount E r:ℝ) ≤ (N:ℝ)*(μ.real E-δ)} := by
    ext r
    dsimp only [mem_setOf_eq]
    rw [he]
    constructor <;> intro hh <;> nlinarith
  rw [hsets] at h
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,NNReal.coe_mul,
    NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at h
  have hexp : -((N:ℝ)*δ)^2 / (2*((N:ℝ)*(1/4))) = -2*(N:ℝ)*δ^2 := by
    field_simp [Nat.cast_ne_zero.mpr hN.ne']
    ring
  rwa [hexp] at h

theorem iid_sampleCount_underfill_exponential (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    (hgap : ρ < μ.real E) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (Measure.pi (fun _ : Fin (N t) => μ)).real {r | sampleCount E r ≤ C t} ≤
        Real.exp (-q*(N t:ℝ)) := by
  let δ := (μ.real E-ρ)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hev := hρ.eventually_lt_const (show ρ < μ.real E-δ by dsimp only [δ]; linarith)
  refine ⟨2*δ^2,by positivity,?_⟩
  filter_upwards [hev,hN.eventually_ge_atTop 1] with t ht hNt
  have hNR : (0:ℝ) < N t := Nat.cast_pos.mpr (by omega)
  have hcap : (C t:ℝ) ≤ (N t:ℝ)*(μ.real E-δ) := by
    have hh := (div_lt_iff₀ hNR).mp ht
    nlinarith
  have hs : {r : Fin (N t) → α | sampleCount E r ≤ C t} ⊆
      {r | (sampleCount E r:ℝ) ≤ (N t:ℝ)*(μ.real E-δ)} := by
    intro r hr
    have hh : (sampleCount E r:ℝ) ≤ C t := by exact_mod_cast hr
    exact hh.trans hcap
  have hh := (measureReal_mono hs).trans (iid_indicator_lower_tail_le μ E hE (N t) (by omega) hδ.le)
  have he : -2*(N t:ℝ)*δ^2 = -(2*δ^2)*(N t:ℝ) := by ring
  simpa only [he] using hh

theorem iid_sampleCount_underfill_tendsto_zero (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    (hgap : ρ < μ.real E) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (N t) => μ)).real
      {r | sampleCount E r ≤ C t}) atTop (𝓝 0) := by
  obtain ⟨q,hq,hb⟩ := iid_sampleCount_underfill_exponential μ E hE N C hN hρ hgap
  have he : Tendsto (fun t => Real.exp (-q*(N t:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hq)
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hb he

theorem iid_sampleCount_fraction_L1 (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun t => ∫ r : Fin (N t) → α,
      |(sampleCount E r:ℝ)/(N t:ℝ)-μ.real E| ∂Measure.pi (fun _ : Fin (N t) => μ))
      atTop (𝓝 0) := by
  classical
  let f := E.indicator (fun _ : α => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator hE
  have hb (a : α) : |f a| ≤ 1 := by
    dsimp only [f,indicator]
    split_ifs <;> norm_num
  have hm : ∫ a, f a ∂μ = μ.real E := integral_indicator_one hE
  have hs t (r : Fin (N t) → α) : (∑ i, f (r i)) = (sampleCount E r:ℝ) := by
    simp [f,indicator_apply,sampleCount]
  have ht := iid_empiricalMean_L1_tendsto_zero (fun _ => μ) (fun _ => f)
    (fun _ => hf.aestronglyMeasurable) 1 zero_le_one (fun _ => Eventually.of_forall hb) N hN
  simpa only [hm,hs] using ht

end FCAppendix.Probability
