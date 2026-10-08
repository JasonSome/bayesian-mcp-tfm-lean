import FCAppendix.PayOnce.NullClipping
import FCAppendix.PayOnce.WeightedDerivative

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Filter Topology Set CommonList OwnImpact RareSuccessSlope
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem measurable_allocation_joint {n c : ℕ} (hn : 2 ≤ n)
    (hc : c ≤ Fintype.card ι + 1) :
    Measurable (fun z : ℝ × (ι → ℝ) => allocation n c hn hc z.2 z.1) := by
  classical
  apply measurable_of_Ici
  intro s
  by_cases hs0 : s ≤ 0
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn hc z.2 z.1) ⁻¹' Ici s = univ := by
      ext z
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact hs0.trans (allocation_bounds hn hc z.2 z.1).1
    rw [he]
    exact MeasurableSet.univ
  have hs : 0 < s := lt_of_not_ge hs0
  by_cases hs1 : s ≤ 1
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn hc z.2 z.1) ⁻¹' Ici s =
        {z | 0 < z.1 ∧ ∀ j, 0 < z.2 j} ∩
        {z | ∑ j, NullClipping.positiveKernel n hn (z.2 j) (z.1 * H n s) ≤ (c : ℝ) - s} := by
      ext z
      simp only [mem_preimage, mem_Ici, mem_inter_iff, mem_setOf_eq]
      by_cases hz : 0 < z.1 ∧ ∀ j, 0 < z.2 j
      · have hL := mul_pos hz.1 (H_pos n (by omega) s hs.le hs1)
        have hsum : ∑ j, NullClipping.positiveKernel n hn (z.2 j) (z.1 * H n s) =
            ∑ j, kernel n (z.2 j) (z.1 * H n s) :=
          Finset.sum_congr rfl fun j _ => NullClipping.positiveKernel_eq hn (hz.2 j) hL
        rw [hsum]
        exact ⟨fun h => ⟨hz, (le_allocation_iff hn hc z.2 hz.2 hz.1 hs hs1).mp h⟩,
          fun h => (le_allocation_iff hn hc z.2 hz.2 hz.1 hs hs1).mpr h.2⟩
      · have ha : allocation n c hn hc z.2 z.1 = 0 := by
          unfold allocation
          rw [dif_neg hz]
        simp only [ha, hz, false_and, iff_false]
        exact not_le_of_gt hs
    rw [he]
    have hp : MeasurableSet {z : ℝ × (ι → ℝ) | 0 < z.1 ∧ ∀ j, 0 < z.2 j} := by
      refine (measurableSet_lt measurable_const measurable_fst).inter ?_
      have he : {z : ℝ × (ι → ℝ) | ∀ j, 0 < z.2 j} = ⋂ j, {z | 0 < z.2 j} := by
        ext z
        simp only [mem_setOf_eq, mem_iInter]
      change MeasurableSet {z : ℝ × (ι → ℝ) | ∀ j, 0 < z.2 j}
      rw [he]
      exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const
        ((measurable_pi_apply j).comp measurable_snd)
    refine hp.inter (measurableSet_le ?_ measurable_const)
    apply Finset.measurable_sum
    intro j _
    exact (scalarDemand_continuous n hn 1 (by norm_num)).measurable.comp
      ((measurable_fst.mul_const (H n s)).div ((measurable_pi_apply j).comp measurable_snd))
  · have he : (fun z : ℝ × (ι → ℝ) => allocation n c hn hc z.2 z.1) ⁻¹' Ici s = ∅ := by
      ext z
      simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
      exact not_le_of_gt ((allocation_bounds hn hc z.2 z.1).2.trans_lt (lt_of_not_ge hs1))
    rw [he]
    exact MeasurableSet.empty

theorem ae_regularClearing_prod [DecidableEq ι] (G : Measure ℝ)
    [IsProbabilityMeasure G] [NullSingletonClass G]
    {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)), 0 < z.1 ∧ RegularClearing n c z.2 z.1 := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)
  have hfull := NullClipping.ae_positive_regularRoot (ι := Option ι) G hn (by simpa using hc) hpos
  rw [← Measure.pi_map_piOptionEquivProd (fun _ : Option ι => G)] at hfull
  have hp := ae_of_ae_map e.symm.measurable.aemeasurable hfull
  have hreg : ∀ᵐ z ∂(Measure.pi (fun _ : ι => G)).prod G,
      0 < z.2 ∧ RegularClearing n c z.1 z.2 := by
    filter_upwards [hp] with z hz
    obtain ⟨hpositive, L, hL, hcap, hz0, hz1⟩ := hz
    refine ⟨hpositive none, fun j => hpositive (some j), L, hL, ?_, hz0 none, hz1 none,
      fun j => hz0 (some j), fun j => hz1 (some j)⟩
    change kernel n (e.symm z none) L + ∑ j, kernel n (e.symm z (some j)) L = (c : ℝ)
    simpa only [Fintype.sum_option, add_comm] using hcap
  rw [← Measure.prod_swap] at hreg
  exact ae_of_ae_map measurable_swap.aemeasurable hreg

theorem aestronglyMeasurable_success_deriv_joint [DecidableEq ι] (G : Measure ℝ)
    [IsProbabilityMeasure G] [NullSingletonClass G]
    {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    AEStronglyMeasurable (fun z : ℝ × (ι → ℝ) =>
      deriv (fun x => success n (allocation n c hn hc z.2 x)) z.1)
      (G.prod (Measure.pi (fun _ : ι => G))) := by
  let F := fun z : ℝ × (ι → ℝ) => success n (allocation n c hn hc z.2 z.1)
  have hF : Measurable F := (continuous_success n).measurable.comp (measurable_allocation_joint hn hc)
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : 0 < δ j := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall fun j => (hδ j).ne'⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j z => (F (z.1 + δ j, z.2) - F z) / δ j)
  · intro j
    exact (((hF.comp ((measurable_fst.add_const (δ j)).prodMk measurable_snd)).sub hF).div_const
      (δ j)).aestronglyMeasurable
  · filter_upwards [ae_regularClearing_prod (ι := ι) G hn hc hpos] with z hz
    have hp := differentiableAt_allocation_of_regular hn hc z.2 hz.1 hz.2
    have hs : DifferentiableAt ℝ (fun x => F (x, z.2)) z.1 :=
      (differentiableAt_const (1 : ℝ)).sub (((differentiableAt_const (1 : ℝ)).sub hp).pow n)
    have hh := hs.hasDerivAt.tendsto_slope_zero.comp hδlim
    simpa only [Function.comp_def, F, smul_eq_mul, div_eq_mul_inv, mul_comm] using hh

theorem exists_joint_measurable_weight [DecidableEq ι] (G : Measure ℝ)
    [IsProbabilityMeasure G] [NullSingletonClass G]
    {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι + 1)
    (hpos : ∀ᵐ b ∂G, 0 < b) :
    ∃ weight : ℝ × (ι → ℝ) → ℝ, Measurable weight ∧
      (∀ z, weight z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z, 1 / ((n : ℝ)^3+1) ≤ 1-weight z) ∧
      (∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)),
        z.1 * deriv (fun x => success n (allocation n c hn hc z.2 x)) z.1 =
          weightedSlope n (allocation n c hn hc z.2 z.1) (weight z)) ∧
      (∀ᵐ b ∂G, HasDerivAt (coverage n c hn hc (Measure.pi (fun _ : ι => G)))
        ((∫ rivals, weightedSlope n (allocation n c hn hc rivals b) (weight (b, rivals))
          ∂Measure.pi (fun _ : ι => G)) / b) b) := by
  let p := fun z : ℝ × (ι → ℝ) => allocation n c hn hc z.2 z.1
  let d := fun z : ℝ × (ι → ℝ) => deriv (fun x => success n (allocation n c hn hc z.2 x)) z.1
  have hd := aestronglyMeasurable_success_deriv_joint (ι := ι) G hn hc hpos
  let dm := hd.mk d
  let κ : ℝ := 1 / ((n : ℝ)^3+1)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hκ1 : κ ≤ 1 := by
    dsimp only [κ]
    apply (div_le_one (by positivity : 0 < (n : ℝ)^3+1)).mpr
    linarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3]
  let weight := fun z : ℝ × (ι → ℝ) => max 0 (min (1-κ) (1-z.1*dm z/phi n (p z)))
  have hw : Measurable weight :=
    measurable_const.max (measurable_const.min
      (measurable_const.sub ((measurable_fst.mul hd.measurable_mk).div
        ((measurable_phi n).comp (measurable_allocation_joint hn hc)))))
  have hw0 (z : ℝ × (ι → ℝ)) : 0 ≤ weight z := le_max_left _ _
  have hwcap (z : ℝ × (ι → ℝ)) : weight z ≤ 1-κ :=
    max_le (sub_nonneg.mpr hκ1) (min_le_left _ _)
  have hw1 (z : ℝ × (ι → ℝ)) : weight z ≤ 1 := (hwcap z).trans (by linarith)
  have he : ∀ᵐ z ∂G.prod (Measure.pi (fun _ : ι => G)),
      z.1*d z = weightedSlope n (p z) (weight z) := by
    filter_upwards [ae_regularClearing_prod (ι := ι) G hn hc hpos, hd.ae_eq_mk] with z hz hdm
    obtain ⟨w, hwbound, hwgap, hderiv⟩ := exists_weight_success_derivative_of_regular hn hc z.2 hz.1 hz.2
    change z.1*d z = weightedSlope n (p z) w at hderiv
    by_cases hi : 0 < p z ∧ p z < 1
    · have hφ := phi_pos_interior hn hi
      have hsolve : 1-z.1*dm z/phi n (p z) = w := by
        change d z = dm z at hdm
        rw [← hdm, hderiv, weightedSlope, if_pos hi]
        field_simp
        ring
      have hweight : weight z = w := by
        change max 0 (min (1-κ) (1-z.1*dm z/phi n (p z))) = w
        rw [hsolve, min_eq_right (by linarith [hwgap hi]), max_eq_right hwbound.1]
      rw [hweight]
      exact hderiv
    · simpa only [weightedSlope, if_neg hi] using hderiv
  refine ⟨weight, hw, fun z => ⟨hw0 z, hw1 z⟩, fun z => by linarith [hwcap z], he, ?_⟩
  filter_upwards [hpos, NullClipping.ae_regularClearing (ι := ι) G hn hc hpos,
    Measure.ae_ae_of_ae_prod he] with b hb hreg heq
  have hderiv := hasDerivAt_coverage_of_regular hn hc (Measure.pi (fun _ : ι => G)) hb hreg
  have hint : (∫ rivals, weightedSlope n (p (b, rivals)) (weight (b, rivals))
      ∂Measure.pi (fun _ : ι => G)) =
      b * ∫ rivals, d (b, rivals) ∂Measure.pi (fun _ : ι => G) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (heq.mono fun _ hh => hh.symm)
  change HasDerivAt _ ((∫ rivals, weightedSlope n (p (b, rivals)) (weight (b, rivals))
    ∂Measure.pi (fun _ : ι => G)) / b) b
  rw [hint, mul_div_cancel_left₀ _ hb.ne']
  exact hderiv.2

end FCAppendix.PayOnce.AnalyticalKernel
