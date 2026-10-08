import FCAppendix.PayOnce.SaturatedLimit

namespace FCAppendix.PayOnce.KernelDemand
open MeasureTheory ProbabilityTheory Set Filter Topology CommonList KernelLawConvergence

theorem demand_le_positive_mass {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {L : ℝ} (hL : 0 < L) : demand n (G : Measure ENNReal) L ≤ (G : Measure ENNReal).real ({0}ᶜ) := by
  have hE : MeasurableSet ({0}ᶜ : Set ENNReal) := (measurableSet_singleton 0).compl
  have hh := integral_mono (CompactKernelRareSuccess.integrable_compactKernel hn (G : Measure ENNReal) hL)
    ((integrable_const (1:ℝ)).indicator hE) (fun b => by
      by_cases hb : b = 0
      · subst b
        simp only [compactKernel, ENNReal.zero_ne_top, if_false, ENNReal.toReal_zero,
          kernel_of_le n hL.le, mem_compl_iff, mem_singleton_iff, not_true_eq_false,
          indicator_of_notMem, not_false_eq_true, le_refl]
      · rw [indicator_of_mem (show b ∈ ({0}ᶜ : Set ENNReal) from hb)]
        exact (compactKernel_bounds hn hL b).2)
  simpa only [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one, demand] using hh

theorem eq_zero_law_of_no_positive_tails (G : ProbabilityMeasure ENNReal) {n : ℕ}
    (h : ∀ L : ℝ, 0 < L → (G : Measure ENNReal) (Ioi (ENNReal.ofReal ((n:ℝ)*L))) = 0) :
    G = (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal) := by
  let L := fun m : ℕ => 1/((m:ℝ)+1)
  have hL : ∀ m, 0 < L m := fun m => by dsimp [L]; positivity
  have hr : Tendsto (fun m => (n:ℝ)*L m) atTop (𝓝 0) := by
    simpa only [L, mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (n:ℝ)
  have hz : Tendsto (fun m => ENNReal.ofReal ((n:ℝ)*L m)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto (0:ℝ) |>.comp hr
  have hae : ∀ᵐ b ∂(G : Measure ENNReal), b = 0 := by
    have hh := ae_all_iff.mpr (fun m => measure_eq_zero_iff_ae_notMem.mp (h (L m) (hL m)))
    filter_upwards [hh] with b hb
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hz (Eventually.of_forall fun m => le_of_not_gt (hb m))
  apply Subtype.ext
  change (G : Measure ENNReal) = Measure.dirac 0
  calc
    _ = (G : Measure ENNReal).map id := Measure.map_id.symm
    _ = (G : Measure ENNReal).map (fun _ => 0) := Measure.map_congr hae
    _ = _ := by simp

theorem no_two_roots_of_no_high_tail {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {ρ L T : ℝ} (hρ : 0 < ρ) (hL : 0 < L) (hLT : L < T)
    (hrootL : demand n (G : Measure ENNReal) L = ρ)
    (hrootT : demand n (G : Measure ENNReal) T = ρ)
    (htail : (G : Measure ENNReal) (Ioi (ENNReal.ofReal ((n:ℝ)*L))) = 0) : False := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have heq := ae_compactKernel_eq_of_demand_eq hn (G : Measure ENNReal) hL (hL.trans hLT) hLT.le
    (hrootL.trans hrootT.symm)
  have he := ae_endpoints_of_two_roots hn (G : Measure ENNReal) hL hLT hrootL hrootT
  have hle := measure_eq_zero_iff_ae_notMem.mp htail
  have hz : ∀ᵐ b ∂(G : Measure ENNReal), compactKernel n b L = 0 := by
    filter_upwards [he,heq,hle] with b hb heq hle
    rcases hb with hb | hb
    · exact hb
    · have hbE : b ≤ ENNReal.ofReal ((n:ℝ)*L) := le_of_not_gt hle
      have hbtop : b ≠ ⊤ := ne_of_lt (hbE.trans_lt ENNReal.ofReal_lt_top)
      have hbR : b.toReal ≤ (n:ℝ)*L := by
        simpa only [ENNReal.toReal_ofReal (mul_pos hnR hL).le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hbE
      have hone : kernel n b.toReal T = 1 := by simpa only [compactKernel, if_neg hbtop] using heq.symm.trans hb
      have hbp : 0 < b.toReal := by
        by_contra hnot
        rw [kernel_of_le n ((le_of_not_gt hnot).trans (hL.trans hLT).le)] at hone
        norm_num at hone
      have hh := (kernel_eq_one_iff n hn hbp (hL.trans hLT)).mp hone
      have hh' := (le_div_iff₀ hnR).mp hh
      nlinarith
  have hd0 : demand n (G : Measure ENNReal) L = 0 := by
    rw [demand, integral_congr_ae hz, integral_zero]
  exact hρ.ne' (hrootL.symm.trans hd0)

theorem exists_root_of_no_saturated_tails {n : ℕ} (hn : 2 ≤ n) (G : ProbabilityMeasure ENNReal)
    {ρ : ℝ} (hρ : 0 < ρ) (hinfty : (G : Measure ENNReal) {⊤} = 0)
    (hne : G ≠ (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal))
    (htail : ∀ L : ℝ, 0 < L → demand n (G : Measure ENNReal) L ≤ ρ →
      (G : Measure ENNReal) (Ioi (ENNReal.ofReal ((n:ℝ)*L))) = 0) :
    ρ < (G : Measure ENNReal).real ({0}ᶜ) ∧ ∃! L, 0 < L ∧ demand n (G : Measure ENNReal) L = ρ := by
  have hpos : ρ < (G : Measure ENNReal).real ({0}ᶜ) := by
    by_contra hnot
    apply hne
    exact eq_zero_law_of_no_positive_tails G (fun L hL =>
      htail L hL ((demand_le_positive_mass hn G hL).trans (le_of_not_gt hnot)))
  obtain ⟨L,hL,hroot⟩ := exists_capacity_root hn G (by simpa only [measureReal_def, hinfty, ENNReal.toReal_zero] using hρ) hpos
  refine ⟨hpos,L,⟨hL,hroot⟩,?_⟩
  intro T hT
  rcases lt_trichotomy L T with h | h | h
  · exact (no_two_roots_of_no_high_tail hn G hρ hL h hroot hT.2 (htail L hL hroot.le)).elim
  · exact h.symm
  · exact (no_two_roots_of_no_high_tail hn G hρ hT.1 h hT.2 hroot (htail T hT.1 hT.2.le)).elim

end FCAppendix.PayOnce.KernelDemand

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce
open scoped ProbabilityTheory

theorem payOnce_positive_capacity_root
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hactive : ∀ᵐ v ∂F, g < v)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    (hρb : ρ ∈ Ioo (0:ℝ) 1) {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G)) :
    ρ < (G : Measure ENNReal).real ({0}ᶜ) ∧
      ∃! L, 0 < L ∧ KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ := by
  have hm t := (hc t).trans (hcm t)
  have hv t : PositiveValueAtomless (Γ t) := by
    intro v _
    rw [hF t]
    exact measure_singleton v
  have hfull t := ae_full_routes_positive_bids_of_active (Γ t) (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hv t) (by simpa only [hF t, hg t] using hactive)
  have hinfty := CompactifiedBidLaws.equilibrium_limit_no_infinity Γ hm hc
    (fun t => posterior_isAEEquilibrium (Γ t) (hu t) (B t) (hB t)) F hF hweak
  have hne : G ≠ (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ENNReal) := by
    intro he
    exact payOnce_not_weak_zero Γ hk hc hcm hM hA hG hu B hB hsym hatom F hF hg hactive hρ hρb (he ▸ hweak)
  apply KernelDemand.exists_root_of_no_saturated_tails (by omega) G hρb.1 hinfty hne
  intro L hL hD
  exact actual_limit_saturated_tail_zero Γ hk hm (fun t => (hcm t).le) hM hA hG hu B hB hsym hatom
    (fun t => (hfull t).mono fun _ hx => hx.2) (fun t => (hfull t).mono fun _ hx => hx.1)
    F hF hweak hρ hL hD

end FCAppendix.Bayes
