import FCAppendix.PayOnce.InactiveEntryHazard
import FCAppendix.PayOnce.InactiveLowerAllocation

namespace FCAppendix.PayOnce.Limit
open Set Real

theorem pStar_le_positive_surplus {n : ℕ} (hn : 2 ≤ n) {L w : ℝ} (hL : 0 < L) :
    pStar n L w ≤ max (w-L) 0/L := by
  by_cases hw : w ≤ L
  · rw [pStar_eq_zero_of_le hn hL.le hw,max_eq_right (sub_nonpos.mpr hw),zero_div]
  · have hLw : L < w := lt_of_not_ge hw
    have hwp : 0 < w := hL.trans hLw
    have ha : 1/((n:ℝ)-1) ≤ 1 := by
      have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
      apply (div_le_one (by linarith : (0:ℝ) < (n:ℝ)-1)).mpr
      linarith
    have hr := self_le_rpow_of_le_one (div_nonneg hL.le hwp.le)
      ((div_le_one hwp).mpr hLw.le) ha
    rw [pStar_of_lt hn hL.le hLw,max_eq_left (sub_pos.mpr hLw).le]
    have he : 1-L/w=(w-L)/w := by field_simp
    calc
      1-(L/w)^(1/((n:ℝ)-1)) ≤ 1-L/w := by linarith
      _ = (w-L)/w := he
      _ ≤ (w-L)/L := div_le_div_of_nonneg_left (sub_pos.mpr hLw).le hL hLw.le

theorem pStar_le_bid_surplus {n : ℕ} (hn : 2 ≤ n) {L w b S : ℝ}
    (hL : 0 < L) (hb : b ≤ L) (hS : 0 ≤ S) (hs : w-b ≤ S) :
    pStar n L w ≤ S/L := by
  apply (pStar_le_positive_surplus hn hL).trans
  apply div_le_div_of_nonneg_right _ hL.le
  exact max_le (by linarith) hS

end FCAppendix.PayOnce.Limit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList Real
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_lower_entry_response_error
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
    ∃ η D : ℝ, 0 < η ∧ 0 < D ∧ ∀ᶠ t in atTop,
      ∀ w b : ℝ, b ∈ Icc (bar t-η) (bar t) →
        Q t b=(w-b)*deriv (Q t) b →
        |(∫ r, allocation (k+1) (C t) hn r b ∂μ t)-Limit.pStar (k+1) (bar t) w| ≤
          D*(M t:ℝ)^(-(1:ℝ)/2) := by
  dsimp only
  have hn : 2 ≤ k+1 := by have := h.proposers_two; omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  let μ := fun t => Measure.pi (fun _ : Fin (M t-1) =>
    (BidScaling.realBidLaw (Γ t) : Measure ℝ))
  let Q := fun t => coverage (k+1) (C t) hn (μ t)
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  obtain ⟨η,A,hη,hA,hhazard⟩ := payOnce_inactive_entry_hazard Γ B F g ρ h hlocal
  obtain ⟨K,hK,halloc⟩ := payOnce_inactive_lower_allocation_bounds Γ B F g ρ h
  have hbar : ∀ᶠ t in atTop, L/2 < bar t :=
    (payOnce_inactive_population_price Γ B F g ρ h).2.eventually
      (eventually_gt_nhds (by linarith : L/2 < L))
  refine ⟨η,K+2*A/L,hη,by positivity,?_⟩
  filter_upwards [hhazard,halloc,hbar,h.population_grows.eventually_ge_atTop 1]
    with t ht ha hbt hM
  intro w b hb hFOC
  change Q t b=(w-b)*deriv (Q t) b at hFOC
  have hh := ht b hb
  have hMpos : (0:ℝ) < M t := Nat.cast_pos.mpr (by omega)
  have hroot := sqrt_pos.mpr hMpos
  have hbarpos : 0 < bar t := (by positivity : (0:ℝ) < L/2).trans hbt
  have hsur : w-b ≤ A/sqrt (M t:ℝ) := by
    have he : (w-b)=Q t b/deriv (Q t) b := by rw [hFOC,mul_div_cancel_right₀ _ hh.2.2.1.ne']
    rw [he]
    exact hh.2.2.2.trans (div_le_div_of_nonneg_left hA.le hroot
      (le_add_of_nonneg_right (mul_nonneg hMpos.le (sub_nonneg.mpr hb.2))))
  have hstar := Limit.pStar_le_bid_surplus hn hbarpos hb.2 (by positivity : 0 ≤ A/sqrt (M t:ℝ)) hsur
  have hstar' : Limit.pStar (k+1) (bar t) w ≤ (2*A/L)*(M t:ℝ)^(-(1:ℝ)/2) := by
    apply hstar.trans
    have h₁ := div_le_div_of_nonneg_left (by positivity : 0 ≤ A/sqrt (M t:ℝ))
      (by positivity : (0:ℝ) < L/2) hbt.le
    apply h₁.trans_eq
    rw [neg_div,rpow_neg hMpos.le,← sqrt_eq_rpow]
    field_simp
  have hmean := (ha b hh.1 hb.2).1
  have hnonneg : 0 ≤ ∫ r, allocation (k+1) (C t) hn r b ∂μ t :=
    integral_nonneg fun r => (allocation_bounds hn r b).1
  apply le_trans (abs_sub _ _)
  rw [abs_of_nonneg hnonneg,abs_of_nonneg Limit.pStar_nonneg]
  nlinarith

end FCAppendix.Bayes
