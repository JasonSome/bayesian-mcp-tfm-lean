import FCAppendix.PayOnce.InactiveCentralHazard
import FCAppendix.PayOnce.InactiveRareEntryHazard
import FCAppendix.PayOnce.HazardRateComparison
import FCAppendix.PayOnce.DummyFixedFocalRegularity

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel PayOnce.EntryDerivativeLower
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_entry_hazard_of_regular
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    ∃ η A : ℝ, 0 < η ∧ 0 < A ∧ ∀ᶠ t in atTop,
      ∀ b ∈ Icc (bar t-η) (bar t),
        (∀ᵐ r ∂μ t, RegularClearing (k+1) (C t) r b) →
        HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b ∧
          Q t b/deriv (Q t) b ≤ A/(sqrt (M t:ℝ)+(M t:ℝ)*(bar t-b)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  obtain ⟨η,H,D,hη,_,_,hD,hrare⟩ :=
    payOnce_inactive_rare_entry_hazard_of_regular Γ B F g ρ h hlocal
  obtain ⟨A,hA,hcentral⟩ := payOnce_inactive_central_hazard Γ B F g ρ h hlocal 1
  have hroot : Tendsto (fun t => sqrt (M t:ℝ)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows)
  refine ⟨η,max (2*A) (4*D),hη,(by positivity : (0:ℝ) < 2*A).trans_le (le_max_left _ _),?_⟩
  filter_upwards [hrare,hcentral,hroot.eventually_ge_atTop (2*H)] with t ht hct hlarge
  intro b hb hreg
  have hM : 0 < M t := by omega
  have hN : 0 < M t-1 := by omega
  have hMN : M t ≤ 2*(M t-1) := by omega
  have hMR : (0:ℝ) < M t := Nat.cast_pos.mpr hM
  have hNR : (0:ℝ) < (M t-1:ℕ) := Nat.cast_pos.mpr hN
  have hs := sqrt_pos.mpr hMR
  have hsq := sq_sqrt hMR.le
  have hMNr : (M t:ℝ) ≤ 2*((M t-1:ℕ):ℝ) := by exact_mod_cast hMN
  have hHdiv : H/((M t-1:ℕ):ℝ) ≤ 1/sqrt (M t:ℝ) := by
    apply (div_le_div_iff₀ hNR hs).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge hs.le]
  have hcen (hd : bar t-b ≤ 1/sqrt (M t:ℝ)) :
      HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b ∧
        Q t b/deriv (Q t) b ≤ A/sqrt (M t:ℝ) := by
    have hh := hct b ⟨by change bar t-1/sqrt (M t:ℝ) ≤ b; linarith,hb.2⟩ hreg
    refine ⟨hh.1,hh.2.1,?_⟩
    convert hh.2.2 using 1
    rw [neg_div,rpow_neg hMR.le,← sqrt_eq_rpow,div_eq_mul_inv]
  have hrar (hd : H/((M t-1:ℕ):ℝ) ≤ bar t-b) :
      HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b ∧
        Q t b/deriv (Q t) b ≤ D/(((M t-1:ℕ):ℝ)*(bar t-b)) :=
    ht.2 b hb.1 hb.2 hd hreg
  have hder : HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b := by
    by_cases hc : bar t-b ≤ 1/sqrt (M t:ℝ)
    · exact ⟨(hcen hc).1,(hcen hc).2.1⟩
    · have hh := hrar (hHdiv.trans (le_of_not_ge hc))
      exact ⟨hh.1,hh.2.1⟩
  refine ⟨hder.1,hder.2,?_⟩
  exact combine_central_rare_hazard hM hN hMN (sub_nonneg.mpr hb.2) hA hD hlarge
    (fun hd => (hcen hd).2.2) (fun hd => (hrar hd).2.2)

theorem payOnce_inactive_entry_hazard
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    let bar := fun t => KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
    let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
      (BidScaling.realBidLaw (Γ t) : Measure ℝ))
    let Q := fun t => coverage (k+1) (C t) hn (μ t)
    ∃ η A : ℝ, 0 < η ∧ 0 < A ∧ ∀ᶠ t in atTop,
      ∀ b ∈ Icc (bar t-η) (bar t),
        0 < b ∧ HasDerivAt (Q t) (deriv (Q t) b) b ∧ 0 < deriv (Q t) b ∧
          Q t b/deriv (Q t) b ≤ A/(sqrt (M t:ℝ)+(M t:ℝ)*(bar t-b)) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  obtain ⟨η₁,A,hη₁,hA,he⟩ := payOnce_inactive_entry_hazard_of_regular Γ B F g ρ h hlocal
  let η := min η₁ (L/4)
  have hη : 0 < η := lt_min hη₁ (by positivity)
  have hη₁' : η ≤ η₁ := min_le_left _ _
  have hηL : η ≤ L/4 := min_le_right _ _
  have hbar : ∀ᶠ t in atTop, L/2 < bar t :=
    (payOnce_inactive_population_price Γ B F g ρ h).2.eventually
      (eventually_gt_nhds (by linarith : L/2 < L))
  refine ⟨η,A,hη,hA,?_⟩
  filter_upwards [he,hbar,h.eventually_scarce] with t ht hbbar hscarce
  intro b hb
  have hbp : 0 < b := by linarith [hb.1]
  have ha (x : ℝ) (hx : 0 < x) : (BidScaling.realBidLaw (Γ t) : Measure ℝ) {x} = 0 :=
    realEffectiveBidLaw_positive_atomless (Γ t) hscarce.1 hscarce.2 (h.action_schedule t)
      (h.base_schedule t) (h.users t) (B t) (h.proposers t) (h.symmetry t)
      (h.positive_values_atomless t) (h.visible_atomless t) hx
  have hreg := ae_regularClearing_fixed_bid (ι := Fin (M t-1)) (c := C t)
    (BidScaling.realBidLaw (Γ t) : Measure ℝ) ha hn hbp
  exact ⟨hbp,ht b ⟨by linarith [hb.1],hb.2⟩ hreg⟩

end FCAppendix.Bayes
