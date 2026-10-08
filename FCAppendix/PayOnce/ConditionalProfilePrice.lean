import FCAppendix.PayOnce.InactivePriceCLT
import FCAppendix.PayOnce.DummyInterimKernel

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Set CommonList Bayes
open scoped BigOperators
variable {m n c : ℕ}

theorem profileMarginal_comp_equiv (e : Fin m ≃ Fin m) (hn : 2 ≤ n)
    (b : Fin m → ℝ) (i : Fin m) :
    profileMarginal n c hn (fun j => b (e j)) i = profileMarginal n c hn b (e i) := by
  have hcard : Fintype.card (Active (fun j => b (e j))) = Fintype.card (Active b) :=
    Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  obtain ⟨L,hL,hp,hcap⟩ := profileMarginal_root (c := c) hn b
  rw [hp]
  apply profileMarginal_eq_kernel hn _ hL
  rw [e.sum_comp (fun j => kernel n (b j) L),hcard]
  exact hcap

theorem profilePrice_comp_equiv (e : Fin m ≃ Fin m) (hn : 2 ≤ n) (hm : 0 < m)
    (b : Fin m → ℝ) : profilePrice n c hn hm (fun j => b (e j)) = profilePrice n c hn hm b := by
  have hp := profileMarginal_comp_equiv (c := c) e hn b
  have hi : (∃ i, 0 < profileMarginal n c hn (fun j => b (e j)) i ∧
      profileMarginal n c hn (fun j => b (e j)) i < 1) ↔
      ∃ i, 0 < profileMarginal n c hn b i ∧ profileMarginal n c hn b i < 1 := by
    simp only [hp]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨e.symm i,by simpa only [e.apply_symm_apply] using hi⟩
  have hs : priceSentinel hm (fun j => b (e j)) = priceSentinel hm b := by
    unfold priceSentinel
    congr 2
    apply le_antisymm
    · apply (Finset.sup'_le_iff _ _).mpr
      intro j _
      exact Finset.le_sup' b (Finset.mem_univ (e j))
    · apply (Finset.sup'_le_iff _ _).mpr
      intro j _
      simpa only [e.apply_symm_apply] using
        Finset.le_sup' (fun j => b (e j)) (Finset.mem_univ (e.symm j))
  have hint : interiorPrice n c hn (fun j => b (e j)) = interiorPrice n c hn b := by
    unfold interiorPrice interiorCount
    simp only [hp]
    congr 1
    · exact e.sum_comp (fun i => if 0 < profileMarginal n c hn b i ∧
        profileMarginal n c hn b i < 1 then b i * H n (profileMarginal n c hn b i) else 0)
    · exact e.sum_comp (fun i => if 0 < profileMarginal n c hn b i ∧
        profileMarginal n c hn b i < 1 then (1:ℝ) else 0)
  have hend : endpointPrice n c hn hm (fun j => b (e j)) = endpointPrice n c hn hm b := by
    unfold endpointPrice
    simp only [hp,hs]
    apply le_antisymm
    · apply (Finset.le_inf'_iff _ _).mpr
      intro j _
      simpa only [e.apply_symm_apply] using Finset.inf'_le
        (fun j => if profileMarginal n c hn b (e j) = 1 then b (e j)/(n:ℝ) else priceSentinel hm b)
        (Finset.mem_univ (e.symm j))
    · apply (Finset.le_inf'_iff _ _).mpr
      intro j _
      exact Finset.inf'_le _ (Finset.mem_univ (e j))
  simp only [profilePrice,hi,hint,hend]

theorem profilePrice_eq_focalPrice_succAbove {N : ℕ} (hn : 2 ≤ n)
    (i : Fin (N+1)) (b : Fin (N+1) → ℝ) :
    profilePrice n c hn (Nat.succ_pos N) b =
      focalPrice n c hn (b i) (fun j => b (i.succAbove j)) := by
  let e : Fin (N+1) ≃ Fin (N+1) := (finSuccEquiv N).trans (finSuccEquiv' i).symm
  have he : (fun j => b (e j)) = Fin.cons (b i) (fun j => b (i.succAbove j)) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [e]
  have hh := profilePrice_comp_equiv (c := c) e hn (Nat.succ_pos N) b
  rw [he] at hh
  exact hh.symm

end FCAppendix.PayOnce.DummyKernel

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology CommonList
open PayOnce PayOnce.CompactifiedBidLaws PayOnce.DummyKernel
variable {N c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def conditionalProfilePrice (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1))
    (d : UserProfile (N+1) (k+1)) : ℝ :=
  actualSampleProfilePrice Γ hk (Function.update d i u)

theorem conditionalProfilePrice_eq_focalPrice (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1))
    (d : UserProfile (N+1) (k+1)) :
    conditionalProfilePrice Γ hk i u d = focalPrice (k+1) c (by omega)
      (effectiveBid u.1.2) (fun j => effectiveBid (d (i.succAbove j)).1.2) := by
  unfold conditionalProfilePrice
  rw [actualSampleProfilePrice_eq Γ hk (Nat.succ_pos N)]
  unfold actualProfilePrice
  rw [profilePrice_eq_focalPrice_succAbove (by omega) i]
  simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne _ _)]

theorem effectiveRivals_succAbove_measurePreserving (Γ : FiniteGame (N+1) (k+1) c Seed)
    (i : Fin (N+1)) :
    MeasurePreserving (fun d : UserProfile (N+1) (k+1) =>
      fun j => effectiveBid (d (i.succAbove j)).1.2) (userProfileLaw Γ)
      (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))) := by
  have hdrop := (measurePreserving_snd (μ := userLaw Γ)
    (ν := Measure.pi (fun _ : Fin N => userLaw Γ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => userLaw Γ) i)
  have hm : Measurable (fun u : UserDraw (k+1) => effectiveBid u.1.2) :=
    (measurable_effectiveBid (k+1)).comp (measurable_snd.comp measurable_fst)
  have hb := measurePreserving_pi (fun _ : Fin N => userLaw Γ)
    (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))
    (fun _ => show MeasurePreserving (fun u : UserDraw (k+1) => effectiveBid u.1.2)
      (userLaw Γ) (BidScaling.realBidLaw Γ : Measure ℝ) from ⟨hm,rfl⟩)
  exact hb.comp hdrop

theorem measurable_conditionalProfilePrice (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1)) :
    Measurable (conditionalProfilePrice Γ hk i u) := by
  have he : conditionalProfilePrice Γ hk i u = fun d => focalPrice (k+1) c (by omega)
      (effectiveBid u.1.2) (fun j => effectiveBid (d (i.succAbove j)).1.2) :=
    funext (conditionalProfilePrice_eq_focalPrice Γ hk i u)
  rw [he]
  exact (measurable_focalPrice (by omega) _).comp
    (effectiveRivals_succAbove_measurePreserving Γ i).measurable

theorem conditionalProfilePrice_map_eq (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1)) :
    (userProfileLaw Γ).map (conditionalProfilePrice Γ hk i u) =
      (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (focalPrice (k+1) c (by omega) (effectiveBid u.1.2)) := by
  rw [← (effectiveRivals_succAbove_measurePreserving Γ i).map_eq,
    Measure.map_map (measurable_focalPrice (by omega) _)
      (effectiveRivals_succAbove_measurePreserving Γ i).measurable]
  congr 1
  exact funext (conditionalProfilePrice_eq_focalPrice Γ hk i u)

theorem conditionalProfilePrice_standardized_map_eq (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1)) (center scale : ℝ) :
    (userProfileLaw Γ).map (fun d => (conditionalProfilePrice Γ hk i u d-center)/scale) =
      (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))).map
        (fun r => (focalPrice (k+1) c (by omega) (effectiveBid u.1.2) r-center)/scale) := by
  rw [← (effectiveRivals_succAbove_measurePreserving Γ i).map_eq,
    Measure.map_map (((measurable_focalPrice (by omega) _).sub_const center).div_const scale)
      (effectiveRivals_succAbove_measurePreserving Γ i).measurable]
  congr 1
  funext d
  simp only [Function.comp_apply,conditionalProfilePrice_eq_focalPrice]

theorem conditionalProfilePrice_pos (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (i : Fin (N+1)) (u : UserDraw (k+1))
    (d : UserProfile (N+1) (k+1)) : 0 < conditionalProfilePrice Γ hk i u d := by
  unfold conditionalProfilePrice
  rw [actualSampleProfilePrice_eq Γ hk (Nat.succ_pos N)]
  exact (profilePrice_spec (c := c) (by omega) (Nat.succ_pos N) _).1

theorem ae_conditionalProfilePrice_countLaw (Γ : FiniteGame (N+1) (k+1) c Seed)
    (hk : 1 ≤ k) (hA : Γ.A = Schedule.once (k+1)) (B : PosteriorSystem Γ)
    (hB : PosteriorProposerOptimalAE Γ B) (hsym : SymmetricProposersOnPath Γ)
    (hroute : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      x.2.routeCount = 0 ∨ (0 < x.2.bid ∧ x.2.routeCount = k+1)) :
    ∀ᵐ u ∂userLaw Γ, ∀ i : Fin (N+1), ∀ᵐ d ∂userProfileLaw Γ,
      profileCountLaw Γ (Function.update d i u) i = IndependentCounts.binomial (k+1)
        (kernel (k+1) (effectiveBid u.1.2) (conditionalProfilePrice Γ hk i u d))
        (KernelTailEvent.kernel_bounds (by omega) (conditionalProfilePrice_pos Γ hk i u d) _).1
        (KernelTailEvent.kernel_bounds (by omega) (conditionalProfilePrice_pos Γ hk i u d) _).2 := by
  have hp := ae_profileCountLaw_eq_actualPrice_binomial Γ hk (Nat.succ_pos N) hA B hB hsym hroute
  have hi (i : Fin (N+1)) : ∀ᵐ u ∂userLaw Γ, ∀ᵐ d ∂userProfileLaw Γ,
      profileCountLaw Γ (Function.update d i u) i = IndependentCounts.binomial (k+1)
        (kernel (k+1) (effectiveBid u.1.2) (conditionalProfilePrice Γ hk i u d))
        (KernelTailEvent.kernel_bounds (by omega) (conditionalProfilePrice_pos Γ hk i u d) _).1
        (KernelTailEvent.kernel_bounds (by omega) (conditionalProfilePrice_pos Γ hk i u d) _).2 := by
    have hpres : MeasurePreserving (fun z : UserDraw (k+1) × UserProfile (N+1) (k+1) =>
        Function.update z.2 i z.1) ((userLaw Γ).prod (userProfileLaw Γ)) (userProfileLaw Γ) :=
      ⟨Resample.measurable_update_pair i,Resample.map_update_eq (userLaw Γ) i⟩
    have hh := Measure.ae_ae_of_ae_prod (hpres.quasiMeasurePreserving.ae hp)
    filter_upwards [hh] with u hu
    filter_upwards [hu] with d hd
    simpa only [conditionalProfilePrice,actualSampleProfilePrice_eq Γ hk (Nat.succ_pos N),
      Function.update_self] using hd i
  exact ae_all_iff.mpr hi

theorem conditionalProfilePrice_standardized_probability_eq
    (Γ : FiniteGame (N+1) (k+1) c Seed) (hk : 1 ≤ k) (i : Fin (N+1))
    (u : UserDraw (k+1)) (center scale x : ℝ) :
    (userProfileLaw Γ).real {d | (conditionalProfilePrice Γ hk i u d-center)/scale ≤ x} =
      (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))).real
        {r | (focalPrice (k+1) c (by omega) (effectiveBid u.1.2) r-center)/scale ≤ x} := by
  have he := congrArg (fun μ : Measure ℝ => μ.real (Iic x))
    (conditionalProfilePrice_standardized_map_eq Γ hk i u center scale)
  rw [map_measureReal_apply (((measurable_conditionalProfilePrice Γ hk i u).sub_const center).div_const scale)
      measurableSet_Iic,
    map_measureReal_apply (((measurable_focalPrice (by omega) _).sub_const center).div_const scale)
      measurableSet_Iic] at he
  exact he

theorem cdf_conditionalProfilePrice_standardized_eq
    (Γ : FiniteGame (N+1) (k+1) c Seed) (hk : 1 ≤ k) (i : Fin (N+1))
    (u : UserDraw (k+1)) (center scale x : ℝ) :
    cdf ((userProfileLaw Γ).map (fun d => (conditionalProfilePrice Γ hk i u d-center)/scale)) x =
      (Measure.pi (fun _ : Fin N => (BidScaling.realBidLaw Γ : Measure ℝ))).real
        {r | (focalPrice (k+1) c (by omega) (effectiveBid u.1.2) r-center)/scale ≤ x} := by
  have hm := ((measurable_conditionalProfilePrice Γ hk i u).sub_const center).div_const scale
  haveI := Measure.isProbabilityMeasure_map (μ := userProfileLaw Γ) hm.aemeasurable
  rw [cdf_eq_real,map_measureReal_apply hm measurableSet_Iic]
  exact conditionalProfilePrice_standardized_probability_eq Γ hk i u center scale x

variable {R C : ℕ → ℕ}

theorem payOnce_inactive_conditional_price_gaussian_uniform
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop, ∀ i : Fin (R t+1), ∀ u : UserDraw (k+1),
      0 < effectiveBid u.1.2 →
      |cdf ((userProfileLaw (Γ t)).map (fun d =>
        (conditionalProfilePrice (Γ t) h.proposers_two i u d -
          KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
            ((C t:ℝ)/(R t+1:ℕ)))/
          inactiveGaussianScale (fun t => R t+1) F (k+1) g ρ t)) x -
        cdf (gaussianReal 0 1) x| < ε := by
  intro ε hε
  filter_upwards [payOnce_inactive_focal_price_gaussian_uniform Γ B F g ρ h hlocal x ε hε]
    with t ht
  intro i u hu
  rw [cdf_conditionalProfilePrice_standardized_eq]
  exact ht (effectiveBid u.1.2) hu

theorem payOnce_inactive_conditional_price_gaussian_cdf
    (Γ : ∀ t, FiniteGame (R t+1) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions (fun t => R t+1) C Γ B F g ρ)
    (hlocal : GaussianParameters.LocalFullSupport (F.map (fun v => max (v-g) 0))
      (Limit.capRoot (F.map (fun v => max (v-g) 0)) (k+1) ρ)) (x : ℝ)
    (i : ∀ t, Fin (R t+1)) (u : ℕ → UserDraw (k+1))
    (hu : ∀ᶠ t in atTop, 0 < effectiveBid (u t).1.2) :
    Tendsto (fun t => cdf ((userProfileLaw (Γ t)).map (fun d =>
      (conditionalProfilePrice (Γ t) h.proposers_two (i t) (u t) d -
        KernelDemand.populationPrice (k+1) (bidLaw (Γ t) : Measure ENNReal)
          ((C t:ℝ)/(R t+1:ℕ)))/
        inactiveGaussianScale (fun t => R t+1) F (k+1) g ρ t)) x)
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [payOnce_inactive_conditional_price_gaussian_uniform Γ B F g ρ h hlocal x ε hε,hu]
    with t ht hut
  simpa only [Real.dist_eq] using ht (i t) (u t) hut

end FCAppendix.Bayes
