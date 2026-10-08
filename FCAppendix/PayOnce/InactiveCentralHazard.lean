import FCAppendix.PayOnce.InactiveCentralEntry
import FCAppendix.PayOnce.InactiveLowerAllocation

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.EntryDerivativeLower
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_central_hazard
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (R : ℝ) :
    let hn : 2 ≤ k+1 := by have hk := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
      ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t in atTop, ∀ b ∈ Icc (bar t-R/Real.sqrt (M t)) (bar t),
      (∀ᵐ r ∂μ t, RegularClearing (k+1) (C t) r b) →
      HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b ∧
        Q t b/deriv (Q t) b ≤ D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have hk := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
    ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  obtain ⟨A,hA,halloc⟩ := payOnce_inactive_lower_allocation_bounds Γ B F g ρ h
  obtain ⟨cR,hcR,hentry⟩ := payOnce_inactive_central_entry_lower Γ B F g ρ h hlocal R
  obtain ⟨η,hη,_,hC,hcut⟩ := exists_entry_deriv_cutoff (n := k+1) hn
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hbar : ∀ᶠ t in atTop, bar t ≤ L+1 :=
    (payOnce_inactive_population_price Γ B F g ρ h).2.eventually_le_const (show L < L+1 by linarith)
  have hδ : Tendsto (fun t => (M t:ℝ)^(-(1:ℝ)/2)) atTop (𝓝 0) := by
    simpa only [neg_div,Function.comp_def] using
      (tendsto_rpow_neg_atTop (y := (1:ℝ)/2) (by norm_num)).comp
        (tendsto_natCast_atTop_atTop.comp h.population_grows)
  have htail : ∀ᶠ t in atTop, A*(M t:ℝ)^(-(1:ℝ)/2)/η ≤ cR/2 := by
    have hh : Tendsto (fun t => A*(M t:ℝ)^(-(1:ℝ)/2)/η) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_div] using (hδ.const_mul A).div_const η
    exact hh.eventually_le_const (by positivity)
  let d₀ := (entrySlopeConstant (k+1)/(2*(L+1)))*cR
  have hc : 0 < entrySlopeConstant (k+1)/(2*(L+1)) := div_pos hC (by positivity)
  have hd₀ : 0 < d₀ := mul_pos hc hcR
  have hnR : (0:ℝ) < (k+1:ℕ) := Nat.cast_pos.mpr (by omega)
  refine ⟨((k+1:ℕ):ℝ)*A/d₀,div_pos (mul_pos hnR hA) hd₀,?_⟩
  filter_upwards [halloc,hentry,hbar,htail] with t ha he hbbar hsmall b hb hreg
  have hbe := he b hb.1
  have hba := ha b hbe.1 hb.2
  have hsmall' : (μ t).real {r | η ≤ allocation (k+1) (C t) hn r b} ≤
      (μ t).real {r | 0 < allocation (k+1) (C t) hn r b}/2 := by
    calc
      _ ≤ A*(M t:ℝ)^(-(1:ℝ)/2)/η := hba.2.2 η hη
      _ ≤ cR/2 := hsmall
      _ ≤ _ := div_le_div_of_nonneg_right hbe.2 (by norm_num)
  have hderiv := hcut (μ t) (C t) b hbe.1 hreg η ⟨hη,le_rfl⟩
  have hD := absorb_bad_mass hC hbe.1 (hb.2.trans hbbar) measureReal_nonneg hsmall' hderiv.2
  have hfloor : d₀ ≤ deriv (Q t) b := by
    exact (mul_le_mul_of_nonneg_left hbe.2 hc.le).trans hD
  refine ⟨hderiv.1,hd₀.trans_le hfloor,?_⟩
  calc
    Q t b/deriv (Q t) b ≤ (((k+1:ℕ):ℝ)*A*(M t:ℝ)^(-(1:ℝ)/2))/d₀ :=
      div_le_div₀ (by positivity) hba.2.1 hd₀ hfloor
    _ = (((k+1:ℕ):ℝ)*A/d₀)*(M t:ℝ)^(-(1:ℝ)/2) := by ring

end FCAppendix.Bayes
