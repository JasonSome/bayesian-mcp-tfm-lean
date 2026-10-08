import FCAppendix.PayOnce.ActualActiveCounts

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology
open scoped ProbabilityTheory BigOperators
variable {m c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem payOnce_load_shortfall_bound (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hatom : PositiveValueAtomless Γ)
    (hinactive : InactiveAbstain Γ) :
    0 ≤ ((k+1:ℕ):ℝ)*(c:ℝ)/m-finiteLoad Γ ∧
      ((k+1:ℕ):ℝ)*(c:ℝ)/m-finiteLoad Γ ≤
        ((k+1:ℕ):ℝ)*(userProfileLaw Γ).real {d | activeUserCount Γ d ≤ c} := by
  let E := {d : UserProfile m (k+1) | activeUserCount Γ d ≤ c}
  have hE : MeasurableSet E := measurableSet_le (measurable_activeUserCount Γ) measurable_const
  let target : ℝ := ((k+1:ℕ):ℝ)*(c:ℝ)/m
  have hm : 0 < m := by omega
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hn : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _
  have hcR : (c:ℝ) ≤ m := Nat.cast_le.mpr hcm.le
  have htarget : target ≤ ((k+1:ℕ):ℝ) := by
    apply (div_le_iff₀ hmR).mpr
    exact mul_le_mul_of_nonneg_left hcR hn
  have hpoint : ∀ᵐ d ∂userProfileLaw Γ,
      0 ≤ target-profileLoad Γ d ∧
      target-profileLoad Γ d ≤ E.indicator (fun _ => ((k+1:ℕ):ℝ)) d := by
    filter_upwards [ae_profileLoad_eq_activeCapacity Γ hk hc hcm hA hG hu B hB hsym hatom hinactive] with d hd
    have hload : 0 ≤ profileLoad Γ d ∧ profileLoad Γ d ≤ target := by
      rw [hd]
      constructor
      · positivity
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.min_le_left c (activeUserCount Γ d))) hn) hmR.le
    refine ⟨sub_nonneg.mpr hload.2,?_⟩
    by_cases hmem : d ∈ E
    · rw [indicator_of_mem hmem]
      linarith [hload.1]
    · rw [indicator_of_notMem hmem]
      have hm0 : c ≤ activeUserCount Γ d := by
        dsimp only [E,mem_setOf_eq] at hmem
        omega
      rw [hd,min_eq_left hm0]
      exact sub_self target ▸ le_rfl
  have hleft : Integrable (fun d => target-profileLoad Γ d) (userProfileLaw Γ) :=
    (integrable_const target).sub (integrable_profileLoad Γ hm)
  have hright : Integrable (E.indicator (fun _ => ((k+1:ℕ):ℝ))) (userProfileLaw Γ) :=
    (integrable_const _).indicator hE
  have hnonneg := integral_nonneg_of_ae (hpoint.mono fun _ hd => hd.1)
  have hupper := integral_mono_ae hleft hright (hpoint.mono fun _ hd => hd.2)
  have he : (∫ d, target-profileLoad Γ d ∂userProfileLaw Γ) = target-finiteLoad Γ := by
    rw [integral_sub (integrable_const _) (integrable_profileLoad Γ hm)]
    simp only [integral_const,probReal_univ,one_smul,finiteLoad]
  rw [he] at hnonneg hupper
  rw [integral_indicator hE,setIntegral_const,smul_eq_mul] at hupper
  exact ⟨hnonneg,by simpa only [target,E,mul_comm] using hupper⟩

theorem payOnce_inactive_load_limit
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1)) (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hatom : ∀ t, PositiveValueAtomless (Γ t))
    (hinactive : ∀ t, InactiveAbstain (Γ t))
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) {g ρ : ℝ} (hg : ∀ t, (Γ t).g = g)
    (hρ : Tendsto (fun t => (C t:ℝ)/(M t:ℝ)) atTop (𝓝 ρ))
    (hgap : ρ < F.real (Ioi g)) :
    Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k+1:ℕ):ℝ)*ρ)) := by
  have he := activeUserCount_underfill_tendsto_zero Γ hM F hF hg hρ hgap
  have hb t := payOnce_load_shortfall_bound (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hatom t) (hinactive t)
  have hdiff : Tendsto (fun t => ((k+1:ℕ):ℝ)*(C t:ℝ)/(M t:ℝ)-finiteLoad (Γ t)) atTop (𝓝 0) :=
    squeeze_zero (fun t => (hb t).1) (fun t => (hb t).2)
      (by simpa only [mul_zero] using he.const_mul (((k+1:ℕ):ℝ)))
  have htarget : Tendsto (fun t => ((k+1:ℕ):ℝ)*(C t:ℝ)/(M t:ℝ)) atTop
      (𝓝 (((k+1:ℕ):ℝ)*ρ)) := by
    simpa only [mul_div_assoc] using hρ.const_mul (((k+1:ℕ):ℝ))
  simpa only [sub_sub_cancel,sub_zero] using htarget.sub hdiff

end FCAppendix.Bayes
