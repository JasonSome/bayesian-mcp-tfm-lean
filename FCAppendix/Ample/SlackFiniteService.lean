import FCAppendix.Ample.SlackConsequences
import FCAppendix.Ample.SlackAsymptotics

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem ppi_slack_finite_consequences {m c : ℕ}
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ((m - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c)
    (hsmall : exp (-2 * (m - 1 : ℕ) * δ ^ 2) ≤ 1 / 2) (i : Fin m) :
    (∀ a : JointAction n, 0 < a.bid →
      ((problem Γ i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
        n * exp (-2 * (m - 1 : ℕ) * δ ^ 2)) ∧
    (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
      (problem Γ i).BestResponse (w + Γ.g) a →
        a.bid ≤ 2 * w * exp (-2 * (m - 1 : ℕ) * δ ^ 2)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_sub_one] at hc hsmall ⊢
  constructor
  · intro a hb
    exact ppi_missing_copy_le_exp_of_arrival_gap Γ hn hA hatom hj i a hb hδ hc
  · intro w hw a ha
    exact ppi_free_bestResponse_bid_le_exp_of_arrival_gap Γ hn hA hfree hatom hj
      i hw a ha hδ hc hsmall

theorem ppi_slack_finite_service {m c : ℕ}
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : ((m - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c)
    (i : Fin m) :
    (∀ b : ℝ, 0 < b → 1 - meanAcceptProb Γ i b ≤
      exp (-2 * (m - 1 : ℕ) * δ ^ 2)) ∧
    (∀ w : ℝ, 0 ≤ w → Ample.deficit (problem Γ i) w ≤
      w * exp (-2 * (m - 1 : ℕ) * δ ^ 2)) ∧
    (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
      (problem Γ i).BestResponse (w + Γ.g) a →
      1 - ((problem Γ i).outcome a).success ≤
        exp (-2 * (m - 1 : ℕ) * δ ^ 2)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  simp only [Nat.succ_sub_one] at hc ⊢
  have hR := allPositiveCongestion_le_exp Γ hn i hδ hc
  refine ⟨?_, ?_, ?_⟩
  · intro b hb
    have hq := ppi_meanAcceptProb_ge_of_arrival_gap Γ hn hA hatom hj i b hb hδ hc
    linarith
  · intro w hw
    have hU := envelope_ge_allPositive_outside Γ hA hfree hatom hj i hw
    have hr := mul_le_mul_of_nonneg_left hR hw
    change w - (problem Γ i).envelope (w + Γ.g) ≤ _
    linarith
  · intro w hw a ha
    exact (ppi_free_AM1 Γ hA hfree hatom hj hn i hw a ha).2.1.trans hR

theorem ppi_source_exponential_of_margin
    {M C : ℕ → ℕ} (Γ : ∀ t, FiniteGame (M t) n (C t) Seed)
    (hn : 0 < n) (hM : Tendsto M atTop atTop)
    {ρ η : ℝ} (hcap : Tendsto (fun t => (C t : ℝ) / M t) atTop (𝓝 ρ))
    (hη : 0 < η)
    (hmargin : ∀ᶠ t in atTop, submittedMarginal (Γ t) ≤ ρ - η)
    (hA : ∀ t, (Γ t).A = Schedule.ppi n)
    (hfree : ∀ t, FreeDuplicateBase (Γ t))
    (hatom : ∀ t, PositiveVisibleAtomless (Γ t))
    (hj : ∀ t j, ProposerRationalAtFeasibleLists (Γ t) j) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ t in atTop, ∀ i : Fin (M t),
      (∀ b : ℝ, 0 < b →
        1 - meanAcceptProb (Γ t) i b ≤ exp (-κ * M t)) ∧
      (∀ w : ℝ, 0 ≤ w → Ample.deficit (problem (Γ t) i) w ≤
        w * exp (-κ * M t)) ∧
      (∀ a : JointAction n, 0 < a.bid →
        ((problem (Γ t) i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
          n * exp (-κ * M t)) ∧
      (∀ w : ℝ, 0 < w → ∀ a : JointAction n,
        (problem (Γ t) i).BestResponse (w + (Γ t).g) a →
          1 - ((problem (Γ t) i).outcome a).success ≤ exp (-κ * M t) ∧
          a.bid ≤ 2 * w * exp (-κ * M t)) := by
  let δ : ℝ := η / 2
  have hδ : 0 < δ := half_pos hη
  let κ : ℝ := δ ^ 2
  have hκ : 0 < κ := sq_pos_of_pos hδ
  have hratio := SimultaneousCongestion.capacity_per_rival hM hcap
  have hcapLower : ∀ᶠ t in atTop,
      ((M t - 1 : ℕ) : ℝ) * (ρ - δ) ≤ C t := by
    filter_upwards [hM.eventually_ge_atTop 2,
      hratio.eventually_const_lt (show ρ - δ < ρ by linarith)] with t ht hc
    have hN : (0 : ℝ) < (M t - 1 : ℕ) := by
      exact_mod_cast (show 0 < M t - 1 by omega)
    have hh := (lt_div_iff₀ hN).mp hc
    nlinarith
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hM.eventually_ge_atTop 2, hmargin, hcapLower,
    (Ample.exp_neg_population_tendsto_zero hM hκ).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with t ht hmarg hcl hsmall
  have hm : 0 < M t := by omega
  have he := Ample.rival_hoeffding_le_full ht δ
  have hc : ((M t - 1 : ℕ) : ℝ) *
      (Ample.contactMarginal n (visibleClassMass (Γ t) 0) + δ) ≤ C t := by
    have harr := arrivalMean_le_submitted (Γ t) 0
    have hs : Ample.contactMarginal n (visibleClassMass (Γ t) 0) + δ ≤ ρ - δ := by
      dsimp [δ]
      linarith
    exact (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)).trans hcl
  intro i
  have hs := ppi_slack_finite_service (Γ t) hm hn (hA t) (hfree t)
    (hatom t) (hj t) hδ.le hc i
  have hf := ppi_slack_finite_consequences (Γ t) hm hn (hA t) (hfree t)
    (hatom t) (hj t) hδ.le hc (he.trans hsmall.le) i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    exact (hs.1 b hb).trans he
  · intro w hw
    exact (hs.2.1 w hw).trans (mul_le_mul_of_nonneg_left he hw)
  · intro a hb
    exact (hf.1 a hb).trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n))
  · intro w hw a ha
    exact ⟨(hs.2.2 w hw a ha).trans he,
      (hf.2 w hw a ha).trans (mul_le_mul_of_nonneg_left he (by positivity))⟩

theorem coverage_ge_positiveParticipation_sub_error {m c : ℕ}
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hn : 0 < n)
    {e : ℝ} (he : 0 ≤ e)
    (hq : ∀ i : Fin m, ∀ b : ℝ, 0 < b → 1 - meanAcceptProb Γ i b ≤ e) :
    positiveRouteMass Γ (fun _ => True) - e ≤ finiteCoverage Γ := by
  classical
  let f : ℝ × JointAction n → ℝ := fun x =>
    if 0 < cutRouteCount 0 x ∧ True then 1 else 0
  have hf : Integrable f (Γ.F ⊗ₘ Γ.σ) := by
    simpa only [f, and_true] using integrable_cutRouteIndicator Γ 0 (fun _ => True)
  have hfint : (∫ x, f x ∂(Γ.F ⊗ₘ Γ.σ)) = positiveRouteMass Γ (fun _ => True) := by
    simpa only [f, and_true] using (positiveRouteMass_eq_integral Γ (fun _ => True)).symm
  have hrow (i : Fin m) : positiveRouteMass Γ (fun _ => True) - e ≤
      ∫ x, ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ) := by
    have hpoint : ∀ x : ℝ × JointAction n,
        f x - e ≤ ((problem Γ i).outcome x.2).success := by
      intro x
      by_cases hb : 0 < x.2.bid
      · by_cases hk : 0 < x.2.routeCount
        · have hkR : (0 : ℝ) < x.2.routeCount := Nat.cast_pos.mpr hk
          have hload := load_le_routeCount_mul_success Γ i x.2
          rw [load_eq_mean Γ hn i x.2] at hload
          have hqs : meanAcceptProb Γ i x.2.bid ≤ ((problem Γ i).outcome x.2).success :=
            (mul_le_mul_iff_right₀ hkR).mp (by simpa only [mul_comm] using hload)
          have hh := hq i x.2.bid hb
          simp only [f, cutRouteCount, if_pos hb, hk, and_self, if_true]
          linarith
        · simpa [f, cutRouteCount, hb, hk] using
            (show -e ≤ ((problem Γ i).outcome x.2).success from
              (neg_nonpos.mpr he).trans ((problem Γ i).outcome x.2).success_nonneg)
      · simpa [f, cutRouteCount, hb] using
          (show -e ≤ ((problem Γ i).outcome x.2).success from
            (neg_nonpos.mpr he).trans ((problem Γ i).outcome x.2).success_nonneg)
    have hh := integral_mono (hf.sub (integrable_const e))
      (integrable_joint_success Γ i) hpoint
    simp only [Pi.sub_apply] at hh
    rw [integral_sub hf (integrable_const e), hfint, integral_const,
      probReal_univ, one_smul] at hh
    exact hh
  rw [finiteCoverage_eq_average_success Γ hm]
  calc
    positiveRouteMass Γ (fun _ => True) - e =
        (∑ _i : Fin m, (positiveRouteMass Γ (fun _ => True) - e)) / m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact (mul_div_cancel_left₀ _ (show (m : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hm.ne')).symm
    _ ≤ _ := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ => hrow i)) (Nat.cast_nonneg m)

end FCAppendix.Bayes
