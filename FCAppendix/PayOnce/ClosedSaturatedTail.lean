import FCAppendix.PayOnce.DeficitLimit
import FCAppendix.PayOnce.SaturatedLimit

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game CommonList
open PayOnce PayOnce.KernelLawConvergence PayOnce.CovarianceConcentration
open scoped BigOperators

theorem actual_limit_saturated_tail_bound
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hm : ∀ t, 0 < M t) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {T R : ℝ} (hT : 0 < T) (hR : 0 ≤ R) :
    (G : Measure ENNReal) (Ioi (ENNReal.ofReal (((k+1:ℕ):ℝ)*T))) ≤
      ENNReal.ofReal (max (KernelDemand.demand (k+1) (G : Measure ENNReal) T-ρ) 0 /
        ((((k+1:ℕ):ℝ)*T) / (((k+1:ℕ):ℝ)*T+R*((k+1:ℕ):ℝ)^2))) + F (Ioi R) := by
  let ε := ((k+1:ℕ):ℝ)*T
  let γ := ε / (ε+R*((k+1:ℕ):ℝ)^2)
  have hε : 0 < ε := mul_pos (Nat.cast_pos.mpr (by omega)) hT
  have hγ : 0 < γ := RareSuccessSlope.saturation_gap_pos hε hR
  let A := fun t => ∫ d, populationMean (fun i => max (kernel (k+1) (d i).1.2.bid T-
    analyticalProfileMarginal (Γ t) (by omega) (hcm t) d i) 0) ∂userProfileLaw (Γ t)
  have hlim := tendsto_actual_kernel_deficit Γ (by omega) hcm hM hroute hbid hweak hρ hT
  have hbound t : ((Γ t).F ⊗ₘ (Γ t).σ)
      {x : ℝ × JointAction (k+1) | ε ≤ x.2.bid ∧ x.1-(Γ t).g ≤ R} ≤ ENNReal.ofReal (A t/γ) := by
    have hh := actual_group_average_deficit_lower (Γ t) hk (hm t) (hcm t) (hA t) (hG t)
      (hu t) (B t) (hB t) (hsym t) (hatom t) (hroute t) (hbid t) hT hε hR (le_refl ε)
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hγ).mpr
    simpa only [γ, A, measureReal_def, mul_comm] using hh
  have hle t := (actual_bid_tail_le_bounded_group (Γ t) (by omega) (hroute t) (R := R) (ε := ε)).trans
    (add_le_add (hbound t) le_rfl)
  simp only [hF] at hle
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak
    (isOpen_Ioi (a := ENNReal.ofReal ε))
  have hl := Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall hle)
  have ht := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.div_const γ)).add_const (F (Ioi R))
  exact hp.trans (hl.trans_eq ht.liminf_eq)

theorem actual_limit_closed_saturated_tail_zero
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hm : ∀ t, 0 < M t) (hcm : ∀ t, C t ≤ M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hroute : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), x.2.routeCount = k+1)
    (hbid : ∀ t, ∀ᵐ x ∂((Γ t).F ⊗ₘ (Γ t).σ), 0 < x.2.bid)
    (F : Measure ℝ) [IsProbabilityMeasure F] (hF : ∀ t, (Γ t).F = F)
    {G : ProbabilityMeasure ENNReal}
    (hweak : Tendsto (fun t => CompactifiedBidLaws.bidLaw (Γ t)) atTop (𝓝 G))
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t : ℝ)/(M t)) atTop (𝓝 ρ))
    {L : ℝ} (hL : 0 < L) (hD : KernelDemand.demand (k+1) (G : Measure ENNReal) L = ρ) :
    (G : Measure ENNReal) (Ici (ENNReal.ofReal (((k+1:ℕ):ℝ)*L))) = 0 := by
  let n : ℝ := ((k+1:ℕ):ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr (by omega)
  let T : ℕ → ℝ := fun j => L-L/((j:ℝ)+2)
  have hT j : 0 < T j := by
    dsimp only [T]
    have hd : (1:ℝ) < (j:ℝ)+2 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hh : L/((j:ℝ)+2) < L := (div_lt_self hL hd)
    linarith
  have hTL j : T j < L := by
    dsimp only [T]
    have hh : 0 < L/((j:ℝ)+2) := by positivity
    linarith
  have ht : Tendsto T atTop (𝓝 L) := by
    have hden : Tendsto (fun j : ℕ => (j:ℝ)+2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hh := (tendsto_const_nhds (x := L)).sub
      ((tendsto_const_nhds (x := L)).mul (tendsto_inv_atTop_zero.comp hden))
    simpa only [mul_zero, sub_zero, Function.comp_def, ← div_eq_mul_inv, T] using hh
  have hd := KernelDemand.tendsto_demand (by omega : 2 ≤ k+1) (tendsto_const_nhds (x := G)) hT hL ht
  rw [hD] at hd
  have hbound (R : ℝ) (hR : 0 ≤ R) :
      (G : Measure ENNReal) (Ici (ENNReal.ofReal (n*L))) ≤ F (Ioi R) := by
    have hγ : 0 < n*L/(n*L+R*n^2) := div_pos (mul_pos hn hL) (by positivity)
    have hγt := (ht.const_mul n).div ((ht.const_mul n).add_const (R*n^2)) (by positivity : n*L+R*n^2 ≠ 0)
    have hnum : Tendsto (fun j => max (KernelDemand.demand (k+1) (G : Measure ENNReal) (T j)-ρ) 0)
        atTop (𝓝 0) := by
      simpa only [sub_self, max_self] using (hd.sub_const ρ).max (tendsto_const_nhds (x := (0:ℝ)))
    have hlim := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hnum.div hγt hγ.ne')).add_const (F (Ioi R))
    simp only [zero_div, ENNReal.ofReal_zero, zero_add] at hlim
    apply ge_of_tendsto hlim
    apply Eventually.of_forall
    intro j
    have hsub : Ici (ENNReal.ofReal (n*L)) ⊆ Ioi (ENNReal.ofReal (n*T j)) := by
      intro b hb
      exact ((ENNReal.ofReal_lt_ofReal_iff (mul_pos hn hL)).mpr
        (mul_lt_mul_of_pos_left (hTL j) hn)).trans_le hb
    exact (measure_mono hsub).trans (actual_limit_saturated_tail_bound Γ hk hm hcm hM hA hG hu B hB
      hsym hatom hroute hbid F hF hweak hρ (hT j) hR)
  have hreal : (G : Measure ENNReal).real (Ici (ENNReal.ofReal (n*L))) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (TailQuantile.tail_tendsto_zero F)
      ((eventually_ge_atTop (0:ℝ)).mono fun R hR => ENNReal.toReal_mono (measure_ne_top F _) (hbound R hR))
  by_contra hne
  exact (ENNReal.toReal_pos hne (measure_ne_top _ _)).not_ge hreal

end FCAppendix.Bayes
