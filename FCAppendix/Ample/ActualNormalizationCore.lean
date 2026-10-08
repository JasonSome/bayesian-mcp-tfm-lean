import FCAppendix.Ample.ActualNormalizationFinite
import FCAppendix.Ample.ActualRouteCompactness
import FCAppendix.Ample.RankProbabilitySubsequence
import FCAppendix.Ample.SlackAsymptotics

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure ActualNormalizationConclusion {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (g ell z : ℝ) : Prop where
  pointwise : ∀ w, ell < w →
    Tendsto (fun t => actualDeficit (Γ t) w / actualDeficit (Γ t) z) atTop (𝓝 1)
  compact : ∀ lo hi, ell < lo → lo ≤ hi → ∀ eps > 0,
    ∀ᶠ t in atTop, ∀ w ∈ Icc lo hi,
      |actualDeficit (Γ t) w / actualDeficit (Γ t) z - 1| < eps
  random_deficit : ProbZero (fun t => activeDrawLaw (Γ t))
    (fun t x => actualDeficit (Γ t) (x.1-g) / actualDeficit (Γ t) z - 1)
  bid_tiers : ProbZero (fun t => activeDrawLaw (Γ t))
    (fun t x => (x.2.routeCount : ℝ) * x.2.bid / actualDeficit (Γ t) z - 1)

namespace ActualNormalizationConclusion
variable {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}
  {g ell z : ℝ}

theorem along (h : ActualNormalizationConclusion Γ g ell z)
    (phi : ℕ → ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualNormalizationConclusion (fun t => Γ (phi t)) g ell z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (h.pointwise w hw).comp hphi
  · intro lo hi hlo hhi eps heps
    exact hphi.eventually (h.compact lo hi hlo hhi eps heps)
  · exact probZero_along h.random_deficit phi hphi
  · exact probZero_along h.bid_tiers phi hphi

theorem of_shift (T : ℕ)
    (h : ActualNormalizationConclusion (fun t => Γ (T + t)) g ell z) :
    ActualNormalizationConclusion Γ g ell z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (tendsto_shift_iff
      (fun t => actualDeficit (Γ t) w / actualDeficit (Γ t) z) T (𝓝 1)).mp
      (h.pointwise w hw)
  · intro lo hi hlo hhi eps heps
    exact (eventually_shift_iff T _).mp (h.compact lo hi hlo hhi eps heps)
  · exact (probZero_shift_iff (fun t => activeDrawLaw (Γ t))
      (fun t x => actualDeficit (Γ t) (x.1-g) / actualDeficit (Γ t) z - 1) T).mp
      h.random_deficit
  · exact (probZero_shift_iff (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ) * x.2.bid / actualDeficit (Γ t) z - 1) T).mp
      h.bid_tiers

end ActualNormalizationConclusion

theorem actual_normalization_on_tail {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (F : Measure ℝ) (g ell z : ℝ)
    (hM : ∀ t, 0 < M t)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hf : ∀ t, FreeDuplicateBase (Γ t)) (hu : ∀ t, UsersOptimal (Γ t))
    (he : IsActiveEndpoint F g ell) (hz : ell < z)
    (hC : ∀ t, 0 < actualDeficit (Γ t) z)
    (hCsmall : Tendsto (fun t => actualDeficit (Γ t) z) atTop (𝓝 0))
    (hUsed : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / actualDeficit (Γ t) z))
    (hAcc : ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
      0 < x.2.routeCount →
        |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps) :
    ActualNormalizationConclusion Γ g ell z := by
  letI : IsProbabilityMeasure F := by
    rw [← hF 0]
    infer_instance
  let mu := fun t => activeDrawLaw (Γ t)
  let menu := fun t => actualMenu (Γ t)
  let f := fun t => actualDeficit (Γ t)
  let V := fun (_ : ℕ) (x : ℝ × JointAction n) => x.1-g
  let chosen := fun (_ : ℕ) (x : ℝ × JointAction n) => x.2
  let K := fun (_ : ℕ) (x : ℝ × JointAction n) => (x.2.routeCount : ℝ)
  let bids := fun (_ : ℕ) (x : ℝ × JointAction n) => x.2.bid
  let S := fun t (x : ℝ × JointAction n) => actualMeanLoad (Γ t) x.2
  let nu := activeSurplusLaw F g
  letI : IsFiniteMeasure nu := activeSurplusLaw_finite F g
  have hLaw := activeEndpointLaw_actual Γ hF hg he
  have hE : ∀ t, IsEnvelope (menu t) (f t) :=
    fun t => actualMenu_isEnvelope (Γ t) (hM t) (hA t) (hf t)
  have hBest : ∀ t, ∀ᵐ x ∂mu t, 0 ≤ V t x ∧
      IsBestReply (menu t) (V t x) (chosen t x) := by
    intro t
    simpa only [V, chosen, menu, mu, hg t] using
      activeDrawLaw_bestReply (Γ t) (hM t) (hA t) (hf t) (hu t)
  have hUp : Request02NormalizationInput mu menu f chosen K S z := by
    refine ⟨⟨hC, hUsed⟩, hCsmall, ?_⟩
    intro eps heps
    filter_upwards [hAcc eps heps] with t ht
    filter_upwards [ht] with x hx
    intro hk
    change 0 < (x.2.routeCount : ℝ) at hk
    exact hx (Nat.cast_pos.mp hk)
  have hPoint : ∀ w, ell < w → Tendsto (fun t => f t w / f t z) atTop (𝓝 1) :=
    fun w hw => pointwise_deficit_normalization mu menu f V chosen
      he.1 hz hE hBest hLaw.positiveLowerBands hUp.toRequest02UsedFailure hw
  refine ⟨hPoint, ?_, ?_, ?_⟩
  · intro lo hi hlo hhi eps heps
    exact compact_uniform_normalization f he.1 hlo hhi
      (fun t => envelope_monotone (hE t)) hC hPoint heps
  · exact random_deficit_normalization_fixedLaw mu menu f V chosen nu
      he.1 hz hLaw hE hBest hUp.toRequest02UsedFailure
  · apply normalized_charge_fixedLaw_of_upstream mu menu f V chosen K bids S nu
      he.1 hz hLaw hE hBest hUp
    · intro t
      filter_upwards [] with x hk
      change (x.2.routeCount : ℝ) = 0 at hk
      exact (actualMenu_semantics (Γ t) (hM t)).1 x.2 (by exact_mod_cast hk)
    · intro t
      filter_upwards [] with x
      exact (actualMenu_semantics (Γ t) (hM t)).2 x.2

theorem actual_normalization_from_used_failure {M C : ℕ → ℕ}
    (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (F : Measure ℝ) (g ell z : ℝ)
    (hM : ∀ᶠ t in atTop, 0 < M t)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hf : ∀ t, FreeDuplicateBase (Γ t)) (hu : ∀ t, UsersOptimal (Γ t))
    (he : IsActiveEndpoint F g ell) (hz : ell < z)
    (hC : ∀ᶠ t in atTop, 0 < actualDeficit (Γ t) z)
    (hCsmall : Tendsto (fun t => actualDeficit (Γ t) z) atTop (𝓝 0))
    (hUsed : ProbZero (fun t => activeDrawLaw (Γ t))
      (fun t x => actualFailure (Γ t) x.2 / actualDeficit (Γ t) z))
    (hAcc : ∀ eps > 0, ∀ᶠ t in atTop, ∀ᵐ x ∂activeDrawLaw (Γ t),
      0 < x.2.routeCount →
        |actualMeanLoad (Γ t) x.2 / (x.2.routeCount : ℝ) - 1| ≤ eps) :
    ActualNormalizationConclusion Γ g ell z := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hM.and hC)
  have hs : Tendsto (fun t : ℕ => T + t) atTop atTop := shift_tendsto_atTop T
  have hh := actual_normalization_on_tail (fun t => Γ (T + t)) F g ell z
    (fun t => (hT (T + t) (by omega)).1)
    (fun t => hF (T + t)) (fun t => hg (T + t))
    (fun t => hA (T + t)) (fun t => hf (T + t)) (fun t => hu (T + t))
    he hz (fun t => (hT (T + t) (by omega)).2)
    (hCsmall.comp hs) (probZero_along hUsed (fun t => T + t) hs)
    (fun eps heps => hs.eventually (hAcc eps heps))
  exact ActualNormalizationConclusion.of_shift T hh

theorem positive_rate_scale_zero {M : ℕ → ℕ} {p : ℕ → ℝ} {J : ℝ}
    (hM : Tendsto M atTop atTop) (hJ : 0 < J) (hRate : HasPopulationRate M p J) :
    Tendsto p atTop (𝓝 0) := by
  have hhalf : 0 < J / 2 := half_pos hJ
  have hhalfJ : J / 2 < J := by linarith
  have hupper : ∀ᶠ t in atTop, |p t - 0| ≤ exp (-(J / 2) * M t) := by
    filter_upwards [hRate.1, hRate.2.eventually_const_lt hhalfJ,
      hM.eventually_ge_atTop 1] with t hpt hrt hmt
    have hmpos : (0 : ℝ) < (M t : ℝ) := by exact_mod_cast (show 0 < M t by omega)
    have hlog : log (p t) ≤ -(J / 2) * (M t : ℝ) := by
      have hmul := (lt_div_iff₀ hmpos).mp hrt
      linarith
    have hexp := Real.exp_le_exp.mpr hlog
    simpa only [sub_zero, abs_of_pos hpt, Real.exp_log hpt] using hexp
  exact squeeze_count_error tendsto_const_nhds
    (exp_neg_population_tendsto_zero hM hhalf) hupper

theorem actualNormalization_subsequence_principle
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (g ell z : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi →
      ∃ psi : ℕ → ℕ, StrictMono psi ∧
        ActualNormalizationConclusion (fun t => Γ (phi (psi t))) g ell z) :
    ActualNormalizationConclusion Γ g ell z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    apply coordinate_subsequence_principle _ 1
    intro phi hphi
    obtain ⟨psi, hpsi, hs⟩ := h phi hphi
    exact ⟨psi, hpsi, hs.pointwise w hw⟩
  · intro lo hi hlo hhi
    apply uniform_subsequence_principle
      (fun t w => actualDeficit (Γ t) w / actualDeficit (Γ t) z)
      (fun _ => 1) (Icc lo hi)
    intro phi hphi
    obtain ⟨psi, hpsi, hs⟩ := h phi hphi
    exact ⟨psi, hpsi, hs.compact lo hi hlo hhi⟩
  · apply probZero_subsequence_principle
      (fun t => activeDrawLaw (Γ t))
      (fun t x => actualDeficit (Γ t) (x.1-g) / actualDeficit (Γ t) z - 1)
    intro phi hphi
    obtain ⟨psi, hpsi, hs⟩ := h phi hphi
    exact ⟨psi, hpsi, hs.random_deficit⟩
  · apply probZero_subsequence_principle
      (fun t => activeDrawLaw (Γ t))
      (fun t x => (x.2.routeCount : ℝ) * x.2.bid / actualDeficit (Γ t) z - 1)
    intro phi hphi
    obtain ⟨psi, hpsi, hs⟩ := h phi hphi
    exact ⟨psi, hpsi, hs.bid_tiers⟩

theorem actualNormalization_of_route_limits
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed) (g ell z : ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi →
        ActualNormalizationConclusion (fun t => Γ (phi t)) g ell z) :
    ActualNormalizationConclusion Γ g ell z := by
  apply actualNormalization_subsequence_principle Γ g ell z
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  exact ⟨psi, hpsi, h (phi ∘ psi) (hphi.comp hpsi) pi hp⟩

theorem actual_probZero_of_route_limits
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (X : ℕ → (ℝ × JointAction n) → ℝ)
    (h : ∀ phi : ℕ → ℕ, StrictMono phi → ∀ pi : ℕ → ℝ,
      RouteLimit (fun t => Γ (phi t)) pi →
        ProbZero (fun t => activeDrawLaw (Γ (phi t))) (fun t => X (phi t))) :
    ProbZero (fun t => activeDrawLaw (Γ t)) X := by
  apply probZero_subsequence_principle
  intro phi hphi
  obtain ⟨psi, hpsi, pi, hp⟩ := finite_route_compactness Γ phi hphi
  exact ⟨psi, hpsi, h (phi ∘ psi) (hphi.comp hpsi) pi hp⟩

end FCAppendix.Bayes
