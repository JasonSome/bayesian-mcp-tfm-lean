import FCAppendix.Finite.PPITailWindow
import FCAppendix.Finite.PPIBidProfile

noncomputable section
namespace FCAppendix.Bayes.NearPPIAssumptions
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem ppi_utility_window
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (hzero : ∀ k j, visibleBidMeasure (Γ k) j {0} = 0)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R) :
    let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
      (f vstar * Real.sqrt (N k + 1 : ℕ))
    TendstoUniformlyOn
      (fun k x => (problem (Γ k) (i k)).envelope (vstar + scale k * x) / scale k)
      gaussianSuccessPrimitive atTop (Icc (-R) R) := by
  let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
    (f vstar * Real.sqrt (N k + 1 : ℕ))
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have hh := h.proposers_two; omega)
  have hσ : 0 < Real.sqrt (ρ * (1 - ρ)) :=
    Real.sqrt_pos.mpr (mul_pos h.ratio_pos (sub_pos.mpr h.ratio_lt_one))
  have hscale_pos (k : ℕ) : 0 < scale k :=
    div_pos (mul_pos hn hσ) (mul_pos hpos (Real.sqrt_pos.mpr (by positivity)))
  have hscale : Tendsto scale atTop (𝓝 0) := by
    have hh : Tendsto (fun k => ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) / f vstar) /
        Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
    simpa only [div_div, mul_comm (Real.sqrt _) (f vstar)] using hh
  obtain ⟨d, hd, sel, hsel⟩ := exists_local_ae_bestResponse_selections
    (fun k => N k + 1) C Γ i F h.common_values (fun k => (h.equilibria k).users)
    f hf vstar U hUn hF hc hpos
  apply envelope_profile_of_left_anchor (fun k => problem (Γ k) (i k)) vstar scale
    hscale hscale_pos d hd sel hsel ?_
    (h.ppi_tail_anchor i hA hzero f hf U hUn hF hc hpos hC) R hR
  intro T hT ε hε
  filter_upwards [h.ppi_central_window i hA hV hsupp f hf U hUn hF hc hpos hC T hT ε hε]
    with k hk
  intro x hx act ha
  exact (hk x hx act ha).2

theorem ppi_cutoff_expansion
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    (hzero : ∀ k j, visibleBidMeasure (Γ k) j {0} = 0)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R) :
    let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
      (f vstar * Real.sqrt (N k + 1 : ℕ))
    TendstoUniformlyOn
      (fun k x => (problem (Γ k) (i k)).envelope (vstar + scale k * x) / scale k)
      gaussianSuccessPrimitive atTop (Icc (-R) R) ∧
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act,
      (problem (Γ k) (i k)).BestResponse (vstar + scale k * x) act →
      act.routeCount = 1 ∧
        |(act.bid - (vstar - g)) / scale k +
          gaussianPDFReal 0 1 x / cdf (gaussianReal 0 1) x| < ε := by
  dsimp only
  have hu := h.ppi_utility_window i hA hzero hV hsupp f hf U hUn hF hc hpos hC R hR
  refine ⟨hu, ?_⟩
  have hn : 0 < n := by have hh := h.proposers_two; omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hσ : 0 < Real.sqrt (ρ * (1 - ρ)) :=
    Real.sqrt_pos.mpr (mul_pos h.ratio_pos (sub_pos.mpr h.ratio_lt_one))
  exact bid_profile_of_uniform_envelope (fun k => N k + 1) C Γ hn i g vstar h.common_fee
    (fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) / (f vstar * Real.sqrt (N k + 1 : ℕ)))
    (fun _ => div_pos (mul_pos hnR hσ) (mul_pos hpos (Real.sqrt_pos.mpr (by positivity))))
    R hR hu (h.ppi_central_window i hA hV hsupp f hf U hUn hF hc hpos hC R hR)

end FCAppendix.Bayes.NearPPIAssumptions

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem ppi_gaussian
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (g ρ vstar : ℝ) (h : CongestedAssumptions M C Γ F g ρ vstar)
    (i : ∀ k, Fin (M k)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (M k : ℝ) * ρ) /
      Real.sqrt (M k)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R) :
    (∀ δ > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act,
      (problem (Γ k) (i k)).BestResponse
        (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
          (f vstar * Real.sqrt (M k))) * x) act →
      act.routeCount = 1 ∧
        |((problem (Γ k) (i k)).outcome act).success - cdf (gaussianReal 0 1) x| < δ) ∧
    (∀ v > vstar, ∀ᶠ k in atTop, ∀ act,
      (problem (Γ k) (i k)).BestResponse v act → act.routeCount = 1) := by
  generalize hN : (fun k => M k - 1) = N
  have he : M = (fun k => N k + 1) := by
    funext k
    have hk := congrFun hN k
    have hpos := h.capacity_lt_population k
    omega
  subst M
  let hh := h.nearPPI_of_ppi hA
  exact ⟨hh.ppi_central_window i hA hV hsupp f hf U hUn hF hc hpos hC R hR,
    fun v hv => hh.ppi_above_cutoff_one_route i hA v hv⟩

theorem ppi_cutoff_prices
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (g ρ vstar : ℝ) (h : CongestedAssumptions M C Γ F g ρ vstar)
    (i : ∀ k, Fin (M k)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (M k : ℝ) * ρ) /
      Real.sqrt (M k)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ k j, visibleBidMeasure (Γ k) j {0} = 0) :
    let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
      (f vstar * Real.sqrt (M k))
    TendstoUniformlyOn
      (fun k x => (problem (Γ k) (i k)).envelope (vstar + scale k * x) / scale k)
      gaussianSuccessPrimitive atTop (Icc (-R) R) ∧
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act,
      (problem (Γ k) (i k)).BestResponse (vstar + scale k * x) act →
      act.routeCount = 1 ∧
        |(act.bid - (vstar - g)) / scale k +
          gaussianPDFReal 0 1 x / cdf (gaussianReal 0 1) x| < ε := by
  generalize hN : (fun k => M k - 1) = N
  have he : M = (fun k => N k + 1) := by
    funext k
    have hk := congrFun hN k
    have hpos := h.capacity_lt_population k
    omega
  subst M
  let hh := h.nearPPI_of_ppi hA
  exact hh.ppi_cutoff_expansion i hA hzero hV hsupp f hf U hUn hF hc hpos hC R hR

end FCAppendix.Bayes
