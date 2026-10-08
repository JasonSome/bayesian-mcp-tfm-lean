import FCAppendix.PayOnce.PriceConcentrationLimit
import FCAppendix.PayOnce.InactiveKernelCLT
import FCAppendix.PayOnce.InactiveRivalUnderfill
import FCAppendix.PayOnce.FocalPrice

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.PriceConcentration
open scoped BigOperators
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_inactive_focal_price_concentration
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ t in atTop, ∀ b : ℝ, 0 < b →
      ∀ ε : ℝ, 0 ≤ ε →
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        {r | ε ≤ |DummyKernel.focalPrice (k+1) (C t) (by have := h.proposers_two; omega) b r-
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))|} ≤
        3*Real.exp (-d*((M t-1:ℕ):ℝ))+
          (2*Real.exp 8)*Real.exp (-((M t-1:ℕ):ℝ)*ε^2/(2*K^2)) := by
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let N := fun t => M t-1
  let G := fun t => BidScaling.realBidLaw (Γ t)
  let bar := fun t => KernelDemand.populationPrice (k+1)
    (bidLaw (Γ t) : Measure ENNReal) ((C t:ℝ)/(M t))
  have hN : Tendsto N atTop atTop := (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hcapSucc : Tendsto (fun t => (C t:ℝ)/((N t:ℝ)+1)) atTop (𝓝 ρ) := by
    apply h.capacity_ratio.congr'
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    have he : (N t:ℝ)+1 = (M t:ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel ht : M t-1+1=M t)
    rw [he]
  have hcap := tendsto_capacity_div_rivals hN hcapSucc
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop
      (𝓝 (inactiveLimitBidLaw F (k+1) g
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) := by
    simpa only [G,BidScaling.scaled_realBidLaw_one] using hweak
  obtain ⟨hL,hroot,huniq,a,z,ha,haz,hz,hwin⟩ :=
    payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  obtain ⟨ℓ,u,q,d,hℓ,hℓL,hLu,hua,hzℓ,hq,hd,he⟩ :=
    exists_eventually_price_concentration N hN hn G
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hL hroot huniq hcap ha haz hz hwin
  have hbar : Tendsto bar atTop
      (𝓝 (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) :=
    (payOnce_inactive_population_price Γ B F g ρ h).2
  have hbarlo := hbar.eventually_const_lt hℓL
  have hbarhi := hbar.eventually_lt_const hLu
  have hzpos : 0 < z := ((hL.trans hLu).trans hua).trans haz
  refine ⟨((k+1:ℕ):ℝ)*z/q,d,by positivity,hd,?_⟩
  filter_upwards [he,hbarlo,hbarhi,payOnce_inactive_population_kernel_mean Γ B F g ρ h,
    h.eventually_scarce,h.population_grows.eventually_gt_atTop 1] with t ht htlo hthi htmean hts htM
  intro b hb ε hε
  have htN : 0 < N t := by dsimp only [N]; omega
  have hcN : C t ≤ N t+1 := by dsimp only [N]; omega
  have hm : (∫ b, kernel (k+1) b (bar t) ∂(G t : Measure ℝ)) = (C t:ℝ)/((N t:ℝ)+1) := by
    have heR : (N t:ℝ)+1 = (M t:ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ M t) : M t-1+1=M t)
    rw [heR]
    exact htmean
  have hbias := fullPopulation_reference_bias_le htN hcN hm
  exact ht.2 (bar t) ε ⟨htlo.le,hthi.le⟩ hbias hε
    (fun _ => b) (DummyKernel.focalPrice (k+1) (C t) hn b)
    (fun r => (DummyKernel.focalPrice_spec hn b r hb).1)
    (fun r => (DummyKernel.focalPrice_spec hn b r hb).2.1)

theorem payOnce_inactive_price_good_event
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let L := Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ
    let hn : 2 ≤ k+1 := by have := h.proposers_two; omega
    ∃ ℓ u a z q d : ℝ, 0 < ℓ ∧ ℓ < L ∧ L < u ∧ u < a ∧ a < z ∧
      z < ((k+1:ℕ):ℝ)*ℓ ∧ 0 < q ∧ 0 < d ∧ ∀ᶠ t in atTop,
      0 < M t-1 ∧ MeasurableSet (goodEvent (k+1) (M t-1) (C t) ℓ u a z q) ∧
      (Measure.pi (fun _ : Fin (M t-1) => (BidScaling.realBidLaw (Γ t) : Measure ℝ))).real
        (goodEvent (k+1) (M t-1) (C t) ℓ u a z q)ᶜ ≤ 3*Real.exp (-d*((M t-1:ℕ):ℝ)) ∧
      ∀ r ∈ goodEvent (k+1) (M t-1) (C t) ℓ u a z q,
        q*((M t-1:ℕ):ℝ) ≤ (Probability.sampleCount (Ioo a z) r:ℝ) ∧
        (∀ b : ℝ, 0 < b →
          DummyKernel.focalPrice (k+1) (C t) hn b r ∈ Icc ℓ u ∧
          ∀ j : Fin (M t-1), r j ∈ Ioo a z →
            kernel (k+1) (r j) (DummyKernel.focalPrice (k+1) (C t) hn b r) ∈ Ioo (0:ℝ) 1) ∧
        ∀ b b' : ℝ, 0 < b → 0 < b' →
          |DummyKernel.focalPrice (k+1) (C t) hn b r-
            DummyKernel.focalPrice (k+1) (C t) hn b' r| ≤
              ((k+1:ℕ):ℝ)*z/(q*((M t-1:ℕ):ℝ)) := by
  dsimp only
  have hk := h.proposers_two
  have hn : 2 ≤ k+1 := by omega
  let N := fun t => M t-1
  let G := fun t => BidScaling.realBidLaw (Γ t)
  have hN : Tendsto N atTop atTop := (tendsto_sub_atTop_nat 1).comp h.population_grows
  have hcapSucc : Tendsto (fun t => (C t:ℝ)/((N t:ℝ)+1)) atTop (𝓝 ρ) := by
    apply h.capacity_ratio.congr'
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with t ht
    have he : (N t:ℝ)+1 = (M t:ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel ht : M t-1+1=M t)
    rw [he]
  have hcap := tendsto_capacity_div_rivals hN hcapSucc
  have hweak := payOnce_inactive_bidLaw_tendsto Γ B F g ρ h
  have hweakRaw : Tendsto (fun t => scaledLaw (G t) 1) atTop
      (𝓝 (inactiveLimitBidLaw F (k+1) g
        (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ))) := by
    simpa only [G,BidScaling.scaled_realBidLaw_one] using hweak
  obtain ⟨hL,hroot,huniq,a,z,ha,haz,hz,hwin⟩ :=
    payOnce_inactive_limit_root_window Γ B F g ρ h hweak
  obtain ⟨ℓ,u,q,d,hℓ,hℓL,hLu,hua,hzℓ,hq,hd,he⟩ :=
    exists_eventually_price_concentration N hN hn G
      (fun t => ae_realEffectiveBidLaw_nonneg (Γ t)) hweakRaw hL hroot huniq hcap ha haz hz hwin
  refine ⟨ℓ,u,a,z,q,d,hℓ,hℓL,hLu,hua,haz,hzℓ,hq,hd,?_⟩
  filter_upwards [he,hN.eventually_gt_atTop 0] with t ht htN
  refine ⟨htN,measurableSet_goodEvent hn hℓ (hL.trans hLu),ht.1,?_⟩
  intro r hr
  have hbracket (b : ℝ) (hb : 0 < b) :
      DummyKernel.focalPrice (k+1) (C t) hn b r ∈ Icc ℓ u := by
    have hp := DummyKernel.focalPrice_spec (c := C t) hn b r hb
    have hc := goodEvent_capacity_le_active hn hℓ hr
    have hh := hp.2.1
    rw [Nat.min_eq_left (hc.trans (Nat.le_succ _))] at hh
    exact goodEvent_root_mem_Icc hn hℓ (hL.trans hLu) hr hp.1 hh
  refine ⟨hr.2.2,?_,?_⟩
  · intro b hb
    refine ⟨hbracket b hb,?_⟩
    intro j hj
    exact PriceInteriorBounds.kernel_interior_on_window hn hℓ (hbracket b hb) hua hzℓ hj
  · intro b b' hb hb'
    exact goodEvent_focal_price_gap_le hn htN hℓ (hL.trans hLu) hua haz hzℓ hq hr
      (DummyKernel.focalPrice_spec hn b r hb).1
      (DummyKernel.focalPrice_spec hn b' r hb').1
      (DummyKernel.focalPrice_spec hn b r hb).2.1
      (DummyKernel.focalPrice_spec hn b' r hb').2.1

end FCAppendix.Bayes
