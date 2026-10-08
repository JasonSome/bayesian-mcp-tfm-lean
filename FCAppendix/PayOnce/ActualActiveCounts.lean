import FCAppendix.PayOnce.EffectiveParticipation
import FCAppendix.PayOnce.VisibleDummyKernel
import FCAppendix.Probability.ActiveCountBounds

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open PayOnce.CompactifiedBidLaws
open scoped ProbabilityTheory BigOperators
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def activeUserCount (Γ : FiniteGame m n c Seed) (d : UserProfile m n) : ℕ :=
  Probability.sampleCount {a : UserDraw n | Γ.g < a.1.1} d

noncomputable def activeBidCount (d : UserProfile m n) : ℕ :=
  Probability.sampleCount {a : UserDraw n | 0 < effectiveBid a.1.2} d

theorem measurable_activeUserCount (Γ : FiniteGame m n c Seed) : Measurable (activeUserCount Γ) :=
  Probability.measurable_sampleCount _ (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst)) m

theorem activeBidCount_eq_card (d : UserProfile m n) :
    activeBidCount d = Fintype.card (PayOnce.DummyKernel.Active (fun i => effectiveBid (d i).1.2)) := by
  classical
  simp only [activeBidCount,Probability.sampleCount,PayOnce.DummyKernel.Active,Fintype.card_subtype,mem_setOf_eq]

theorem userLaw_active_mass (Γ : FiniteGame m n c Seed) :
    (userLaw Γ).real {a : UserDraw n | Γ.g < a.1.1} = Γ.F.real (Ioi Γ.g) := by
  have he : userLaw Γ {a : UserDraw n | Γ.g < a.1.1} = Γ.F (Ioi Γ.g) := by
    rw [← userLaw_value_map Γ,Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  exact congrArg ENNReal.toReal he

theorem ae_activeBidCount_eq_activeUserCount (Γ : FiniteGame m (k+1) c Seed)
    (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ) :
    ∀ᵐ d ∂userProfileLaw Γ, activeBidCount d = activeUserCount Γ d := by
  classical
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae
    (ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hatom)
  have hdraw : ∀ᵐ d ∂userProfileLaw Γ, ∀ i, 0 < effectiveBid (d i).1.2 ↔ Γ.g < (d i).1.1 :=
    ae_all_iff.mpr fun i => ((measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser).mono
      fun _ hx => hx.1
  filter_upwards [hdraw] with d hd
  unfold activeBidCount activeUserCount Probability.sampleCount
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_setOf_eq,hd i]

theorem ae_profileLoad_eq_activeCapacity (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) :
    ∀ᵐ d ∂userProfileLaw Γ, profileLoad Γ d =
      (k+1:ℕ)*(min c (activeUserCount Γ d):ℕ)/(m:ℝ) := by
  have hr := ae_positive_broadcast_or_abstain Γ hc hcm hA hG hu B hB hsym hatom hinactive
  filter_upwards [ae_dummy_kernel_representation Γ hk hA B hB hsym hr,
    ae_activeBidCount_eq_activeUserCount Γ hc hcm hA hG hu B hB hsym hatom] with d hd hcount
  obtain ⟨L,hL,hlaw,hcap⟩ := hd
  unfold profileLoad
  simp_rw [hlaw,IndependentCounts.binomial_load]
  rw [← Finset.mul_sum,hcap,← activeBidCount_eq_card d,hcount]

theorem activeUserCount_underfill_exponential
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : Tendsto M atTop atTop) (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F)
    {g ρ : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hρ : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 ρ))
    (hgap : ρ < F.real (Ioi g)) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ t in atTop,
      (userProfileLaw (Γ t)).real {d | activeUserCount (Γ t) d ≤ C t} ≤ Real.exp (-q*(M t:ℝ)) := by
  let δ := (F.real (Ioi g)-ρ)/2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hev := hρ.eventually_lt_const (show ρ < F.real (Ioi g)-δ by dsimp only [δ]; linarith)
  refine ⟨2*δ^2,by positivity,?_⟩
  filter_upwards [hev,hM.eventually_ge_atTop 1] with t ht hMt
  have hMR : (0:ℝ) < M t := Nat.cast_pos.mpr (by omega)
  have hmass : (userLaw (Γ t)).real {a : UserDraw n | (Γ t).g < a.1.1} = F.real (Ioi g) := by
    rw [userLaw_active_mass,hF t,hg t]
  have hcap : (C t:ℝ) ≤ (M t:ℝ)*(F.real (Ioi g)-δ) := by
    have hh := (div_lt_iff₀ hMR).mp ht
    nlinarith
  have hs : {d : UserProfile (M t) n | activeUserCount (Γ t) d ≤ C t} ⊆
      {d | (activeUserCount (Γ t) d:ℝ) ≤ (M t:ℝ)*(F.real (Ioi g)-δ)} := by
    intro d hd
    exact (show (activeUserCount (Γ t) d:ℝ) ≤ C t by exact_mod_cast hd).trans hcap
  have hh := Probability.iid_indicator_lower_tail_le (userLaw (Γ t))
    {a : UserDraw n | (Γ t).g < a.1.1}
    (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst)) (M t) (by omega) hδ.le
  rw [hmass] at hh
  have hh' := (measureReal_mono hs).trans hh
  have he : -2*(M t:ℝ)*δ^2 = -(2*δ^2)*(M t:ℝ) := by ring
  simpa only [he,userProfileLaw] using hh'

theorem activeUserCount_underfill_tendsto_zero
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hM : Tendsto M atTop atTop) (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F)
    {g ρ : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hρ : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 ρ))
    (hgap : ρ < F.real (Ioi g)) :
    Tendsto (fun t => (userProfileLaw (Γ t)).real {d | activeUserCount (Γ t) d ≤ C t})
      atTop (𝓝 0) := by
  obtain ⟨q,hq,hb⟩ := activeUserCount_underfill_exponential Γ hM F hF hg hρ hgap
  have he : Tendsto (fun t => Real.exp (-q*(M t:ℝ))) atTop (𝓝 0) := by
    simpa only [neg_mul,Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop.comp hM).const_mul_atTop hq)
  exact squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) hb he

end FCAppendix.Bayes
