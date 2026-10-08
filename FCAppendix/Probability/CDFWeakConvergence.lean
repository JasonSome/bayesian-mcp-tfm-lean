import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem real_Ioc_eq_cdf_sub (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) : μ.real (Ioc a b) = cdf μ b-cdf μ a := by
  have hh := (cdf μ).measure_Ioc a b
  rw [measure_cdf] at hh
  rw [Measure.real,hh,ENNReal.toReal_ofReal (sub_nonneg.mpr (monotone_cdf μ hab))]

theorem probabilityMeasure_tendsto_of_cdf
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ι → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (h : ∀ x : ℝ, Tendsto (fun i => cdf (μ i : Measure ℝ) x) l
      (𝓝 (cdf (ν : Measure ℝ) x))) : Tendsto μ l (𝓝 ν) := by
  apply (isPiSystem_Ioc (id : ℝ → ℝ) id).tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a,b,_,rfl⟩
    exact measurableSet_Ioc
  · intro U hU x hx
    obtain ⟨a,b,haxb,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hx)
    obtain ⟨b',hxb',hb'b⟩ := exists_between haxb.2
    refine ⟨Ioc a b',⟨a,b',haxb.1.trans hxb',rfl⟩,Ioc_mem_nhds haxb.1 hxb',?_⟩
    intro y hy
    exact hsub ⟨hy.1,hy.2.trans_lt hb'b⟩
  · rintro s ⟨a,b,hab,rfl⟩
    change a < b at hab
    apply NNReal.tendsto_coe.mp
    change Tendsto (fun i => (μ i : Measure ℝ).real (Ioc a b)) l
      (𝓝 ((ν : Measure ℝ).real (Ioc a b)))
    simp_rw [real_Ioc_eq_cdf_sub _ hab.le]
    exact (h b).sub (h a)

end FCAppendix.Probability
