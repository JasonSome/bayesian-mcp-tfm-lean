import FCAppendix.PayOnce.InactiveEventualPopulation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem tendsto_capacity_div_rivals {N C : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/((N t:ℝ)+1)) atTop (𝓝 ρ)) :
    Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ) := by
  have hratio : Tendsto (fun t => ((N t:ℝ)+1)/N t) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN))
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hN.eventually_gt_atTop 0] with t ht
    have hne : (N t:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
    dsimp only [Function.comp_def]
    field_simp
  have hh := hρ.mul hratio
  simp only [mul_one] at hh
  apply hh.congr
  intro t
  have hne : (N t:ℝ)+1 ≠ 0 := by positivity
  field_simp

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem active_card_eq_sampleCount {N : ℕ} (r : Fin N → ℝ) :
    Fintype.card (Active r) = Probability.sampleCount (Ioi (0:ℝ)) r := by
  classical
  simp only [Active,Fintype.card_subtype,Probability.sampleCount,mem_Ioi]

theorem triangular_underfill_exponential
    (G : ℕ → ProbabilityMeasure ℝ) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {ρ π : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    (hπ : ∀ᶠ t in atTop, (G t : Measure ℝ).real (Ioi 0) = π) (hgap : ρ < π) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))).real
        {r | Fintype.card (Active r) < C t} ≤ Real.exp (-q*(N t:ℝ)) := by
  let δ := (π-ρ)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hev := hρ.eventually_lt_const (show ρ < π-δ by dsimp only [δ]; linarith)
  refine ⟨2*δ^2,by positivity,?_⟩
  filter_upwards [hev,hN.eventually_gt_atTop 0,hπ] with t ht hNt hπt
  have hNR : (0:ℝ) < N t := Nat.cast_pos.mpr hNt
  have hcap : (C t:ℝ) ≤ (N t:ℝ)*(π-δ) := by
    have hh := (div_lt_iff₀ hNR).mp ht
    nlinarith
  have hs : {r : Fin (N t) → ℝ | Fintype.card (Active r) < C t} ⊆
      {r | (Probability.sampleCount (Ioi (0:ℝ)) r:ℝ) ≤ (N t:ℝ)*(π-δ)} := by
    intro r hr
    change Fintype.card (Active r) < C t at hr
    have hh : Fintype.card (Active r) ≤ C t := by omega
    rw [active_card_eq_sampleCount] at hh
    exact (show (Probability.sampleCount (Ioi (0:ℝ)) r:ℝ) ≤ C t by exact_mod_cast hh).trans hcap
  have hh := Probability.iid_indicator_lower_tail_le (G t : Measure ℝ)
    (Ioi (0:ℝ)) measurableSet_Ioi (N t) hNt hδ.le
  rw [hπt] at hh
  have hb := (measureReal_mono hs).trans hh
  have he : -2*(N t:ℝ)*δ^2 = -(2*δ^2)*(N t:ℝ) := by ring
  simpa only [he] using hb

theorem triangular_rival_underfill_exponential
    (G : ℕ → ProbabilityMeasure ℝ) (N C : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    {ρ π : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(N t:ℝ)) atTop (𝓝 ρ))
    (hπ : ∀ᶠ t in atTop, (G t : Measure ℝ).real (Ioi 0) = π) (hgap : ρ < π) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (Measure.pi (fun _ : Fin (N t) => (G t : Measure ℝ))).real
        {r | Fintype.card (Active r)+1 < C t} ≤ Real.exp (-q*(N t:ℝ)) := by
  obtain ⟨q,hq,hbound⟩ := triangular_underfill_exponential G N C hN hρ hπ hgap
  refine ⟨q,hq,?_⟩
  filter_upwards [hbound] with t ht
  apply (measureReal_mono (show {r : Fin (N t) → ℝ | Fintype.card (Active r)+1 < C t} ⊆
    {r | Fintype.card (Active r) < C t} from ?_)).trans ht
  intro r hr
  change Fintype.card (Active r)+1 < C t at hr
  change Fintype.card (Active r) < C t
  omega

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce PayOnce.CompactifiedBidLaws
variable {N C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_rival_underfill_exponential
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (Measure.pi (fun _ : Fin (N t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Fintype.card (DummyKernel.Active r)+1 < C t} ≤ Real.exp (-q*(N t:ℝ)) := by
  have hN : Tendsto N atTop atTop := by
    simpa only [Function.comp_def,Nat.add_sub_cancel] using (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hratio := tendsto_capacity_div_rivals hN (by
    simpa only [Nat.cast_add,Nat.cast_one] using h.capacity_ratio)
  apply DummyKernel.triangular_rival_underfill_exponential
    (fun t => BidScaling.realBidLaw (Γ t)) N C hN hratio _ h.capacity_bounds.2
  filter_upwards [h.eventually_scarce] with t ht
  have he := realEffectiveBidLaw_positive_mass (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t)
  rw [h.common_values t,h.common_fee t] at he
  exact congrArg ENNReal.toReal he

theorem payOnce_inactive_rival_underfill_tendsto_zero
    (Γ : ∀ t, FiniteGame (N t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => N t+1) C Γ B F g ρ) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (N t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Fintype.card (DummyKernel.Active r)+1 < C t}) atTop (𝓝 0) := by
  obtain ⟨q,hq,hbound⟩ := payOnce_inactive_rival_underfill_exponential Γ B F g ρ h
  have hN : Tendsto N atTop atTop := by
    simpa only [Function.comp_def,Nat.add_sub_cancel] using (tendsto_sub_atTop_nat 1).comp h.population_grows
  have he : Tendsto (fun t => Real.exp (-q*(N t:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hq)
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hbound he

variable {M : ℕ → ℕ}

theorem payOnce_inactive_profile_underfill_exponential
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (Measure.pi (fun _ : Fin (M t) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Fintype.card (DummyKernel.Active r) < C t} ≤ Real.exp (-q*(M t:ℝ)) := by
  apply DummyKernel.triangular_underfill_exponential
    (fun t => BidScaling.realBidLaw (Γ t)) M C h.population_grows h.capacity_ratio _ h.capacity_bounds.2
  filter_upwards [h.eventually_scarce] with t ht
  have he := realEffectiveBidLaw_positive_mass (Γ t) ht.1 ht.2 (h.action_schedule t)
    (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
    (h.positive_values_atomless t)
  rw [h.common_values t,h.common_fee t] at he
  exact congrArg ENNReal.toReal he

theorem payOnce_inactive_profile_underfill_tendsto_zero
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    Tendsto (fun t => (Measure.pi (fun _ : Fin (M t) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | Fintype.card (DummyKernel.Active r) < C t}) atTop (𝓝 0) := by
  obtain ⟨q,hq,hbound⟩ := payOnce_inactive_profile_underfill_exponential Γ B F g ρ h
  have he : Tendsto (fun t => Real.exp (-q*(M t:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp h.population_grows).const_mul_atTop hq)
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hbound he

end FCAppendix.Bayes
