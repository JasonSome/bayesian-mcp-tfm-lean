import FCAppendix.Ample.RankSupportSelection

noncomputable section
namespace FCAppendix.Bayes.RankLimit
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.RankMeasureTools

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed] {M C : ℕ → ℕ}
    {Γ : ∀ t, FiniteGame (M t) n (C t) Seed} {pi : ℕ → ℝ} {h : ℝ}
    {nu : ℕ → Measure ℝ} (hr : RankLimit Γ pi h nu)

include hr

theorem used_rate_ge_actual
    (F : Measure ℝ) [IsProbabilityMeasure F] (g : ℝ)
    (hF : ∀ t, (Γ t).F = F) (hg : ∀ t, (Γ t).g = g)
    (hu : ∀ t, UsersOptimal (Γ t)) (hact : ∀ t, NonpositiveAbstention (Γ t))
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hfree : ∀ t, FreeDuplicateBase (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hpolicy : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j)
    (hM : Tendsto M atTop atTop) {ρ J : ℝ}
    (hC : Tendsto (fun t => (C t : ℝ)/M t) atTop (𝓝 ρ))
    (hpart : ∀ᶠ t in atTop, positiveRouteMass (Γ t) (fun _ => True) = h)
    (hh : h ≤ 1) (hρ : ρ < 1)
    (hmean : (∑ j ∈ Finset.Icc 1 n, (j : ℝ)*pi j) < n*ρ)
    (hfull : HasPopulationRate M (fun t => actualAllFailure (Γ t)) J)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ᵐ u ∂nu k, J ≤ rivalRate n ρ k (rankTail nu h u) := by
  letI := hr.finite hk
  have hn : 0 < n := by
    have := Finset.mem_Icc.mp hk
    omega
  filter_upwards [hr.used_tail_positive hk, (nu k).support_mem_ae] with u huRank huSupport
  obtain ⟨phi, hphi, x, hx, hxr⟩ := hr.supported_approximation F g hF hg hu hact
    (fun t => 0 < M t) (hM.eventually_gt_atTop 0) hk
    huRank.1 huRank.2.1 huSupport
  let p : ℕ → ℕ → ℝ := fun q => visibleClassMass (Γ (phi q)) (x q).2.bid
  have hp (q : ℕ) : ValidLaw n (p q) := visibleClassMass_valid _ _
  have hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun q => p q j) atTop (𝓝 (rankTail nu h u j)) :=
    (hr.along phi hphi.tendsto_atTop).visible_weights_tendsto
      (fun q => hatom (phi q)) (fun q => (x q).2.bid)
      (Eventually.of_forall (fun q => (hx q).2.2.2.1.le))
      (hphi.tendsto_atTop.eventually hpart) hxr
  have hslack := hr.mean_tail_lt hn hmean u
  have htop := hr.own_tail_support_guard hρ hk huRank.2.2
  have hrate := ample_event_rate (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
    hp (hr.valid_tail hh u) hconv (hM.comp hphi.tendsto_atTop)
    (hC.comp hphi.tendsto_atTop) hslack htop
  have he (q : ℕ) : actualFailure (Γ (phi q)) (x q).2 =
      congestProb n (M (phi q)-1) (C (phi q)) k (p q) := by
    rw [actualFailure_eq_congestProb _ (hx q).1 (hA _) (hatom _) (hpolicy _)
      _ (hx q).2.2.2.1, (hx q).2.2.2.2]
  have hrate' : Tendsto
      (fun q => populationLogRate (M (phi q)) (actualFailure (Γ (phi q)) (x q).2))
      atTop (𝓝 (rivalRate n ρ k (rankTail nu h u))) := by
    simpa only [populationLogRate, he, Function.comp_def] using hrate.2
  have hfull' := hfull.2.comp hphi.tendsto_atTop
  apply le_of_tendsto_of_tendsto hfull' hrate'
  filter_upwards [hrate.1] with q hpos
  have hpos' : 0 < actualFailure (Γ (phi q)) (x q).2 := by rwa [he]
  have hBR := (hx q).2.1 (hx q).1
  have hw : 0 < (x q).1-g := sub_pos.mpr (hx q).2.2.1
  have hAM := actual_AM1 (Γ (phi q)) (hx q).1 (hA _) (hfree _)
    (hatom _) (hpolicy _) hn hw (x q).2 hBR
  have hlog := Real.log_le_log hpos' hAM.2.1
  unfold populationLogRate
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) (Nat.cast_nonneg _)

end FCAppendix.Bayes.RankLimit
