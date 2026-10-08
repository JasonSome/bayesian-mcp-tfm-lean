import FCAppendix.PayOnce.ActiveEmpiricalCovariance
import FCAppendix.PayOnce.ProfileConcentration
import FCAppendix.PayOnce.InactiveProfileWeights
import FCAppendix.PayOnce.ActualActiveCounts

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration PayOnce.CompactifiedBidLaws
open scoped BigOperators ProbabilityTheory
variable {m n c k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem populationMean_active_eq_count (Γ : FiniteGame m n c Seed) (d : UserProfile m n) :
    populationMean (fun i => if Γ.g < (d i).1.1 then (1:ℝ) else 0) = activeUserCount Γ d/m := by
  classical
  simp [populationMean,activeUserCount,Probability.sampleCount]

theorem ae_dummy_marginal_active_capacity (Γ : FiniteGame m (k+1) c Seed)
    (hk : 1 ≤ k) (hc : 0 < c) (hcm : c < m)
    (hA : Γ.A = Schedule.once (k+1)) (hG : Γ.G = Schedule.once (k+1))
    (hu : UsersOptimal Γ) (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hsym : SymmetricProposersOnPath Γ) (hvalue : PositiveValueAtomless Γ) :
    ∀ᵐ d ∂userProfileLaw Γ,
      (∀ i, (if Γ.g < (d i).1.1 then (1:ℝ) else 0)*dummyProfileMarginal Γ (by omega) d i =
        dummyProfileMarginal Γ (by omega) d i) ∧
      (∑ i, dummyProfileMarginal Γ (by omega) d i) = min c (activeUserCount Γ d) := by
  let hn : 2 ≤ k+1 := by omega
  have huser := (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw (k+1))).quasiMeasurePreserving.ae
    (ae_effectiveBid_participation Γ hc hcm hA hG hu B hB hsym hvalue)
  have hprof := ae_all_iff.mpr fun i : Fin m =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae huser
  filter_upwards [hprof,ae_activeBidCount_eq_activeUserCount Γ hc hcm hA hG hu B hB hsym hvalue]
    with d hd hcount
  constructor
  · intro i
    by_cases hv : Γ.g < (d i).1.1
    · rw [if_pos hv,one_mul]
    · rw [if_neg hv,zero_mul]
      have hbid : effectiveBid (d i).1.2 ≤ 0 := le_of_not_gt fun hb => hv ((hd i).1.mp hb)
      symm
      exact DummyKernel.allocation_eq_zero_of_nonpos hn _ hbid
  · obtain ⟨L,_,hp,hcap⟩ := DummyKernel.profileMarginal_root (c := c) hn (fun i => effectiveBid (d i).1.2)
    change (∑ i, DummyKernel.profileMarginal (k+1) c hn (fun j => effectiveBid (d j).1.2) i) = _
    simp_rw [hp]
    rw [hcap,← activeBidCount_eq_card d,hcount]

theorem active_profile_fraction_L1
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hm : ∀ t, 0 < M t) (hM : Tendsto M atTop atTop)
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) (g : ℝ) :
    Tendsto (fun t => ∫ d, |populationMean (fun i => if g < (d i).1.1 then (1:ℝ) else 0)-
      F.real (Ioi g)| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  let s : ℝ → ℝ := (Ioi g).indicator (fun _ => 1)
  have hs : Measurable s := measurable_const.indicator measurableSet_Ioi
  have hb v : s v ∈ Icc (0:ℝ) 1 := by by_cases hv : v ∈ Ioi g <;> simp [s,hv]
  have hR : Tendsto (fun t => (1:ℝ)/Real.sqrt (M t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hM))
  apply squeeze_zero (fun t => integral_nonneg fun d => abs_nonneg _) _ hR
  intro t
  have hh := integral_profileMeanType_error_le (Γ t) (hm t) s hs hb
  have he : (∫ v, s v ∂(Γ t).F) = F.real (Ioi g) := by
    rw [hF t]
    exact integral_indicator_one measurableSet_Ioi
  rw [he] at hh
  simpa only [s,profileMeanType,populationMean,Fintype.card_fin,indicator,mem_Ioi] using hh

end FCAppendix.Bayes

namespace FCAppendix.PayOnce.CovarianceConcentration
open MeasureTheory Filter Topology Set

theorem abs_min_sub_le {a c π ρ : ℝ} (hρ : ρ ≤ π) :
    |min c a-ρ| ≤ |c-ρ|+|a-π| := by
  apply abs_le.mpr
  constructor
  · apply (le_sub_iff_add_le).mpr
    apply le_min <;> linarith [neg_abs_le (c-ρ),neg_abs_le (a-π),abs_nonneg (c-ρ),abs_nonneg (a-π)]
  · have hm := min_le_left c a
    linarith [le_abs_self (c-ρ),abs_nonneg (a-π)]

theorem integral_min_mean_tendsto
    {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
    (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
    (a : ∀ t, Ω t → ℝ) (ha : ∀ t, Integrable (a t) (P t))
    (c : ℕ → ℝ) {π ρ : ℝ} (hρπ : ρ ≤ π) (hc : Tendsto c atTop (𝓝 ρ))
    (hactive : Tendsto (fun t => ∫ ω, |a t ω-π| ∂P t) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ ω, |min (c t) (a t ω)-ρ| ∂P t) atTop (𝓝 0) := by
  have hu : Tendsto (fun t => |c t-ρ|+(∫ ω, |a t ω-π| ∂P t)) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_add] using ((hc.sub_const ρ).abs).add hactive
  apply squeeze_zero (fun t => integral_nonneg fun _ => abs_nonneg _) _ hu
  intro t
  have hh := integral_mono (((integrable_const (c t)).inf (ha t)).sub (integrable_const ρ)).abs
    ((integrable_const |c t-ρ|).add ((ha t).sub (integrable_const π)).abs)
    (fun ω => abs_min_sub_le hρπ)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const |c t-ρ|) ((ha t).sub (integrable_const π)).abs,
    integral_const,probReal_univ,one_smul] at hh
  exact hh

end FCAppendix.PayOnce.CovarianceConcentration

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Filter Topology Set Game
open PayOnce PayOnce.CovarianceConcentration
open scoped BigOperators ProbabilityTheory

theorem dummy_profile_mean_L1
    {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (hk : 1 ≤ k) (hc : ∀ t, 0 < C t) (hcm : ∀ t, C t < M t)
    (hM : Tendsto M atTop atTop)
    (hA : ∀ t, (Γ t).A = Schedule.once (k+1))
    (hG : ∀ t, (Γ t).G = Schedule.once (k+1))
    (hu : ∀ t, UsersOptimal (Γ t)) (B : ∀ t, PosteriorSystem (Γ t))
    (hB : ∀ t, PosteriorProposerOptimalAE (Γ t) (B t))
    (hsym : ∀ t, SymmetricProposersOnPath (Γ t)) (hvalue : ∀ t, PositiveValueAtomless (Γ t))
    (F : Measure ℝ) (hF : ∀ t, (Γ t).F = F) {g : ℝ} (hg : ∀ t, (Γ t).g = g)
    {ρ : ℝ} (hρ : Tendsto (fun t => (C t:ℝ)/(M t)) atTop (𝓝 ρ))
    (hρπ : ρ ≤ F.real (Ioi g)) :
    Tendsto (fun t => ∫ d, |populationMean (fun i =>
      (if g < (d i).1.1 then (1:ℝ) else 0)*dummyProfileMarginal (Γ t) (by omega) d i)-ρ|
      ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
  have hm t := (hc t).trans (hcm t)
  let s : ℝ → ℝ := (Ioi g).indicator (fun _ => 1)
  have hs : Measurable s := measurable_const.indicator measurableSet_Ioi
  have hb v : s v ∈ Icc (0:ℝ) 1 := by by_cases hv : v ∈ Ioi g <;> simp [s,hv]
  let a := fun t (d : UserProfile (M t) (k+1)) => profileMeanType s d
  have ha t : Integrable (a t) (userProfileLaw (Γ t)) := UnitInterval.integrable _ _
    (measurable_profileMeanType hs) (fun d => (profileMeanType_bounds (hm t) hb d).1)
    (fun d => (profileMeanType_bounds (hm t) hb d).2)
  have hfrac := active_profile_fraction_L1 Γ hm hM F hF g
  have hfrac' : Tendsto (fun t => ∫ d, |a t d-F.real (Ioi g)| ∂userProfileLaw (Γ t)) atTop (𝓝 0) := by
    simpa only [a,profileMeanType,populationMean,Fintype.card_fin,s,indicator,mem_Ioi] using hfrac
  have ht := integral_min_mean_tendsto (fun t => userProfileLaw (Γ t)) a ha
    (fun t => (C t:ℝ)/(M t)) hρπ hρ hfrac'
  apply ht.congr
  intro t
  apply integral_congr_ae
  filter_upwards [ae_dummy_marginal_active_capacity (Γ t) hk (hc t) (hcm t) (hA t) (hG t)
    (hu t) (B t) (hB t) (hsym t) (hvalue t)] with d hd
  have hmR : (0:ℝ) < M t := Nat.cast_pos.mpr (hm t)
  have he : populationMean (fun i => (if g < (d i).1.1 then (1:ℝ) else 0)*
      dummyProfileMarginal (Γ t) (by omega) d i) = min ((C t:ℝ)/(M t)) (a t d) := by
    have hpoint := hd.1
    rw [hg t] at hpoint
    simp only [populationMean,Fintype.card_fin,hpoint,hd.2,Nat.cast_min]
    rw [← min_div_div_right hmR.le]
    congr 1
    have hcount := populationMean_active_eq_count (Γ t) d
    simpa only [populationMean,Fintype.card_fin,hg t,a,profileMeanType,s,indicator,mem_Ioi] using hcount.symm
  rw [he]

end FCAppendix.Bayes
