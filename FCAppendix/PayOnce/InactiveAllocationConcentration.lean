import FCAppendix.PayOnce.InactivePriceConcentration
import FCAppendix.PayOnce.DummyInterimKernel

namespace FCAppendix.PayOnce.KernelLawConvergence
open Set CommonList KernelTailEvent

theorem kernel_price_difference_of_reference {n : ℕ} (hn : 2 ≤ n)
    {R T ℓ : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R) (hT : 2*ℓ ≤ T) (b : ℝ) :
    |kernel n b R-kernel n b T| ≤ ((n:ℝ)/ℓ)*|R-T| := by
  have hTpos : 0 < T := by linarith
  by_cases hRlo : ℓ ≤ R
  · exact kernel_price_difference hn hℓ hRlo (by linarith) b
  · have hbR := kernel_bounds hn hR b
    have hbT := kernel_bounds hn hTpos b
    have hunit : |kernel n b R-kernel n b T| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hbR.1,hbT.2],by linarith [hbR.2,hbT.1]⟩
    have hgap : ℓ ≤ |R-T| := by
      rw [abs_of_nonpos (by linarith : R-T ≤ 0)]
      linarith
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hcoeff : 0 ≤ (n:ℝ)/ℓ := by positivity
    apply hunit.trans
    calc
      (1:ℝ) ≤ n := hnR
      _ = ((n:ℝ)/ℓ)*ℓ := by field_simp
      _ ≤ ((n:ℝ)/ℓ)*|R-T| := mul_le_mul_of_nonneg_left hgap hcoeff

end FCAppendix.PayOnce.KernelLawConvergence

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList KernelTailEvent
variable {N n c : ℕ}

theorem measurable_allocation_error (hn : 2 ≤ n) (b T : ℝ) :
    Measurable (fun r : Fin N → ℝ => |allocation n c hn r b-kernel n b T|) :=
  ((measurable_allocation_fixed_bid hn b).sub_const _).abs

theorem allocation_error_le_one (hn : 2 ≤ n) {T : ℝ} (hT : 0 < T)
    (b : ℝ) (r : Fin N → ℝ) : |allocation n c hn r b-kernel n b T| ≤ 1 := by
  have ha := allocation_bounds (c := c) hn r b
  have hb := kernel_bounds hn hT b
  exact abs_le.mpr ⟨by linarith [ha.1,hb.2],by linarith [ha.2,hb.1]⟩

theorem allocation_error_le_price_error (hn : 2 ≤ n) {T ℓ : ℝ}
    (hℓ : 0 < ℓ) (hT : 2*ℓ ≤ T) (b : ℝ) (hb : 0 < b) (r : Fin N → ℝ) :
    |allocation n c hn r b-kernel n b T| ≤
      ((n:ℝ)/ℓ)*|focalPrice n c hn b r-T| := by
  obtain ⟨hp,_,ha⟩ := focalPrice_spec (c := c) hn b r hb
  rw [ha]
  exact KernelLawConvergence.kernel_price_difference_of_reference hn hℓ hp hT b

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_allocation_concentration
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      ∀ ε : ℝ, 0 ≤ ε →
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | ε ≤ |allocation (k+1) (C t) (by have := h.proposers_two; omega) r b-
          kernel (k+1) b (KernelDemand.populationPrice (k+1)
            (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|} ≤
        3*Real.exp (-d*((M t-1:ℕ):ℝ))+
          (2*Real.exp 8)*Real.exp (-((M t-1:ℕ):ℝ)*ε^2/(2*K^2)) := by
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
  let ℓ := L/4
  let a : ℝ := ((k+1:ℕ):ℝ)/ℓ
  have hL : 0 < L := (payOnce_inactive_eventual_pure_bid_limit Γ B F g ρ h).1
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; positivity
  have ha : 0 < a := by dsimp only [a]; positivity
  have hbar := (payOnce_inactive_population_price Γ B F g ρ h).2
  have hbarlo : ∀ᶠ t in atTop, 2*ℓ ≤ KernelDemand.populationPrice (k+1)
      (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)) :=
    hbar.eventually_const_le (by dsimp only [ℓ]; linarith)
  obtain ⟨K,d,hK,hd,hconc⟩ := payOnce_inactive_focal_price_concentration Γ B F g ρ h
  refine ⟨a*K,d,mul_pos ha hK,hd,?_⟩
  filter_upwards [hconc,hbarlo] with t ht hT
  intro b hb ε hε
  have hs := ht b hb (ε/a) (div_nonneg hε ha.le)
  have hsub : {r : Fin (M t-1) → ℝ | ε ≤ |allocation (k+1) (C t) hn r b-
      kernel (k+1) b (KernelDemand.populationPrice (k+1)
        (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t)))|} ⊆
      {r | ε/a ≤ |focalPrice (k+1) (C t) hn b r-
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|} := by
    intro r hr
    apply (div_le_iff₀ ha).mpr
    have he := allocation_error_le_price_error (c := C t) hn hℓ hT b hb r
    change ε ≤ _ at hr
    change ε ≤ _
    simpa only [a,mul_comm] using hr.trans he
  have hexp : -((M t-1:ℕ):ℝ)*(ε/a)^2/(2*K^2) =
      -((M t-1:ℕ):ℝ)*ε^2/(2*(a*K)^2) := by field_simp
  rw [hexp] at hs
  exact (measureReal_mono hsub).trans hs

end FCAppendix.Bayes
