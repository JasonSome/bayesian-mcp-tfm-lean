import FCAppendix.PayOnce.RivalDemandLimit

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList
open CompactifiedBidLaws
open scoped BigOperators

theorem eventually_window_mass_pos (G : ℕ → ProbabilityMeasure ℝ)
    {G₀ : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => scaledLaw (G t) 1) atTop (𝓝 G₀))
    {a z : ℝ} (ha : 0 < a) (haz : a < z)
    (hwin : 0 < (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z))) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop, q ≤ (G t : Measure ℝ).real (Ioo a z) := by
  let e := (G₀ : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z))
  have he : 0 < e.toReal := ENNReal.toReal_pos hwin.ne' (measure_ne_top _ _)
  let q := e.toReal/2
  have hq : 0 < q := half_pos he
  have hqe : ENNReal.ofReal q < e := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hq.le (measure_ne_top _ _)]
    dsimp only [q]
    linarith
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
    (isOpen_Ioo (a := ENNReal.ofReal a) (b := ENNReal.ofReal z))
  have ht := eventually_lt_of_lt_liminf (hqe.trans_le hp)
  refine ⟨q,hq,?_⟩
  filter_upwards [ht] with t hmass
  have hm : (scaledLaw (G t) 1 : Measure ENNReal) (Ioo (ENNReal.ofReal a) (ENNReal.ofReal z)) =
      (G t : Measure ℝ) (Ioo a z) := by
    change (Measure.map (fun b : ℝ => ENNReal.ofReal (b/1)) (G t : Measure ℝ)) _ = _
    simp only [div_one]
    rw [Measure.map_apply ENNReal.measurable_ofReal measurableSet_Ioo]
    congr 1
    ext b
    simp only [mem_preimage, mem_Ioo,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le, ENNReal.ofReal_lt_ofReal_iff (ha.trans haz)]
  rw [hm, ENNReal.ofReal_lt_iff_lt_toReal hq.le (measure_ne_top _ _)] at hmass
  exact hmass.le

theorem tendsto_rival_window_error
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (G : ℕ → ProbabilityMeasure ℝ)
    (a z : ℝ) :
    Tendsto (fun t => ∫ r : Fin (N t) → ℝ,
      |((Finset.univ.filter fun j => r j ∈ Ioo a z).card:ℝ)/(N t:ℝ)-
        (G t : Measure ℝ).real (Ioo a z)|
          ∂Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))) atTop (𝓝 0) := by
  classical
  let f := (Ioo a z).indicator (fun _ : ℝ => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioo
  have hb (b : ℝ) : |f b| ≤ 1 := by
    dsimp only [f, indicator]
    split_ifs <;> norm_num
  have he (t) : (∫ b, f b ∂(G t : Measure ℝ)) = (G t : Measure ℝ).real (Ioo a z) :=
    integral_indicator_one measurableSet_Ioo
  have hs (t) (r : Fin (N t) → ℝ) : (∑ j, f (r j)) =
      ((Finset.univ.filter fun j => r j ∈ Ioo a z).card:ℝ) := by
    simp only [f, indicator_apply]
    simp
  have ht := Probability.iid_empiricalMean_L1_tendsto_zero (fun t => (G t : Measure ℝ))
    (fun _ => f) (fun _ => hf.aestronglyMeasurable) 1 zero_le_one
    (fun _ => Eventually.of_forall hb) N hN
  simp only [he,hs] at ht
  exact ht

theorem integrable_rival_window_error (G : Measure ℝ) [IsProbabilityMeasure G]
    (N : ℕ) (a z m : ℝ) :
    Integrable (fun r : Fin N → ℝ =>
      |((Finset.univ.filter fun j => r j ∈ Ioo a z).card:ℝ)/(N:ℝ)-m|)
        (Measure.pi (fun _ : Fin N => G)) := by
  classical
  let f := (Ioo a z).indicator (fun _ : ℝ => (1:ℝ))
  have hf : Measurable f := measurable_const.indicator measurableSet_Ioo
  have hb (b : ℝ) : |f b| ≤ 1 := by
    dsimp only [f, indicator]
    split_ifs <;> norm_num
  have hi (j : Fin N) : Integrable (fun r : Fin N → ℝ => f (r j))
      (Measure.pi (fun _ : Fin N => G)) :=
    Integrable.of_bound (hf.comp (measurable_pi_apply j)).aestronglyMeasurable 1
      (Eventually.of_forall fun r => by simpa only [Real.norm_eq_abs] using hb (r j))
  have ht := (((integrable_finsetSum Finset.univ (fun j _ => hi j)).div_const (N:ℝ)).sub
    (integrable_const m)).abs
  simpa only [f, indicator_apply, Finset.sum_boole, Pi.sub_apply] using ht

end FCAppendix.PayOnce.AnalyticalKernel
