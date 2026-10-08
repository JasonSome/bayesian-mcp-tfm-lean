import FCAppendix.Ample.FreeBaseIncentives
import FCAppendix.Probability.ContactHoeffding

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology Real Finset
open scoped BigOperators

variable {n N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem visibleContactMarginal_antitone (Γ : FiniteGame (N + 1) n c Seed)
    (hn : 0 < n) {b d : ℝ} (hbd : b ≤ d) :
    Ample.contactMarginal n (visibleClassMass Γ d) ≤
      Ample.contactMarginal n (visibleClassMass Γ b) := by
  let s : Fin n := ⟨0, hn⟩
  rw [visibleClassMass_marginal Γ d s, visibleClassMass_marginal Γ b s]
  unfold alphaGt
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  exact ⟨hx.1, lt_of_le_of_lt hbd hx.2⟩

theorem positive_arrivalMarginal_le_submitted (Γ : FiniteGame (N + 1) n c Seed)
    (hn : 0 < n) :
    Ample.contactMarginal n (visibleClassMass Γ 0) ≤ submittedMarginal Γ := by
  rw [submittedMarginal_eq_contactMarginal]
  exact visibleContactMarginal_antitone Γ hn (by norm_num)

theorem allPositiveCongestion_le_exp (Γ : FiniteGame (N + 1) n c Seed)
    (hn : 0 < n) (i : Fin (N + 1)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c) :
    allPositiveCongestion Γ i ≤ exp (-2 * N * δ ^ 2) := by
  let s : Fin n := ⟨0, hn⟩
  have hh := SimultaneousCongestion.congestionProb_le_exp_of_coordinate
    (visibleLaw Γ 0) (univ : Finset (Fin n)) (mem_univ s) N c hδ
    (by simpa only [visibleLaw_eq_contactLaw, Ample.contactLaw_marginal] using hc)
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    ← joint_rank_congestion_eq Γ i 0] at hh
  simpa [allPositiveCongestion] using hh

theorem ppi_meanAcceptProb_ge_of_arrival_gap (Γ : FiniteGame (N + 1) n c Seed)
    (hn : 0 < n) (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (b : ℝ) (hb : 0 < b) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c) :
    1 - exp (-2 * N * δ ^ 2) ≤ meanAcceptProb Γ i b := by
  let a : JointAction n := ⟨b, hb.le, 1, hn⟩
  have hK : (Ample.selected n 1).Nonempty := by
    rw [← card_pos, Ample.card_selected hn]
    decide
  obtain ⟨s, hs⟩ := hK
  have hcap : (N : ℝ) * (Proposer.marginal (visibleLaw Γ b) s + δ) ≤ c := by
    rw [visibleLaw_eq_contactLaw, Ample.contactLaw_marginal]
    have hm := visibleContactMarginal_antitone Γ hn hb.le
    have hg : Ample.contactMarginal n (visibleClassMass Γ b) + δ ≤
        Ample.contactMarginal n (visibleClassMass Γ 0) + δ := by linarith
    exact (mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg N)).trans hc
  have hh := SimultaneousCongestion.congestionProb_le_exp_of_coordinate
    (visibleLaw Γ b) (Ample.selected n 1) hs N c hδ hcap
  rw [visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb,
    Ample.congestProbAt_eq_congestProb, Ample.card_selected hn] at hh
  have he := ppi_failure_eq_congestProb Γ hA hatom hj i a hb
  rw [singleton_success Γ hn i a rfl] at he
  change 1 - meanAcceptProb Γ i b = Ample.congestProb n N c 1 (visibleClassMass Γ b) at he
  rw [← he] at hh
  linarith

theorem prob_missing_copy_le_routeCount_sub_load
    (Γ : FiniteGame (N + 1) n c Seed) (i : Fin (N + 1)) (a : JointAction n) :
    ((problem Γ i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
      (a.routeCount : ℝ) - ((problem Γ i).outcome a).load := by
  classical
  have he : (a.routeCount : ℝ) - ((problem Γ i).outcome a).load =
      ((problem Γ i).outcome a).expect (fun r => (a.routeCount : ℝ) - r.val) := by
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
    rfl
  rw [he, FiniteLaw.prob_eq_expect, problem_outcome, CountLaw.expect_ofMeasure,
    CountLaw.expect_ofMeasure]
  apply integral_mono
    (CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => if r.val ≠ a.routeCount then 1 else 0))
    (CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => (a.routeCount : ℝ) - r.val))
  intro ω
  dsimp only
  have hk := focalCount_le Γ i a ω
  by_cases he : (focalCount Γ i a ω).val = a.routeCount
  · simp [he]
  · rw [if_pos he]
    have hh : (focalCount Γ i a ω).val + 1 ≤ a.routeCount := by omega
    have hhR : ((focalCount Γ i a ω).val : ℝ) + 1 ≤ a.routeCount := by exact_mod_cast hh
    linarith

theorem ppi_missing_copy_le_exp_of_arrival_gap (Γ : FiniteGame (N + 1) n c Seed)
    (hn : 0 < n) (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c) :
    ((problem Γ i).outcome a).prob (fun r => r.val ≠ a.routeCount) ≤
      n * exp (-2 * N * δ ^ 2) := by
  have hq := ppi_meanAcceptProb_ge_of_arrival_gap Γ hn hA hatom hj i a.bid hb hδ hc
  have hp := prob_missing_copy_le_routeCount_sub_load Γ i a
  rw [load_eq_mean Γ hn i a] at hp
  have hk : (a.routeCount : ℝ) ≤ n := by exact_mod_cast a.routeCount_le
  have h1 := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg a.routeCount)
  have h2 := mul_le_mul_of_nonneg_right hk (exp_pos (-2 * N * δ ^ 2)).le
  nlinarith

theorem ppi_free_bestResponse_bid_le_exp_of_arrival_gap
    (Γ : FiniteGame (N + 1) n c Seed) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) {w : ℝ} (hw : 0 < w)
    (a : JointAction n) (ha : (problem Γ i).BestResponse (w + Γ.g) a)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hc : (N : ℝ) * (Ample.contactMarginal n (visibleClassMass Γ 0) + δ) ≤ c)
    (hsmall : exp (-2 * N * δ ^ 2) ≤ 1 / 2) :
    a.bid ≤ 2 * w * exp (-2 * N * δ ^ 2) := by
  by_cases hb : a.bid = 0
  · rw [hb]
    positivity
  have hb' : 0 < a.bid := lt_of_le_of_ne a.bid_nonneg (Ne.symm hb)
  have hq := ppi_meanAcceptProb_ge_of_arrival_gap Γ hn hA hatom hj i a.bid hb' hδ hc
  have hAM := ppi_free_AM1 Γ hA hfree hatom hj hn i hw a ha
  have hR := allPositiveCongestion_le_exp Γ hn i hδ hc
  have hS : 0 < ((problem Γ i).outcome a).success := by linarith [hAM.2.1]
  have hk : 1 ≤ a.routeCount := by
    by_contra hn0
    have hz : a.routeCount = 0 := by omega
    have hload := ((problem Γ i).outcome a).success_le_load
    rw [load_eq_mean Γ hn i a, hz, Nat.cast_zero, zero_mul] at hload
    linarith
  have hkR : (1 : ℝ) ≤ a.routeCount := by exact_mod_cast hk
  have hq0 : 0 ≤ meanAcceptProb Γ i a.bid := by linarith
  have hl : (1 / 2 : ℝ) ≤ (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid := by
    have hh := mul_le_mul_of_nonneg_right hkR hq0
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hl a.bid_nonneg
  have h2 := mul_le_mul_of_nonneg_left hR hw.le
  nlinarith [hAM.2.2]

theorem eventual_arrival_gap_and_source_exponential
    {N C : ℕ → ℕ} {p : ℕ → ℝ} {ρ η : ℝ} (hη : 0 < η)
    (hN : Tendsto (fun a => N a + 1) atTop atTop)
    (hc : Tendsto (fun a => (C a : ℝ) / (N a + 1)) atTop (𝓝 ρ))
    (hp : ∀ᶠ a in atTop, p a ≤ ρ - η) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ a in atTop,
      (N a : ℝ) * (p a + η / 2) ≤ C a ∧
      exp (-2 * N a * (η / 2) ^ 2) ≤ exp (-κ * (N a + 1)) ∧
      exp (-2 * N a * (η / 2) ^ 2) ≤ 1 / 2 := by
  have hNr : Tendsto N atTop atTop := by
    simpa only [Nat.add_sub_cancel] using
      (SimultaneousCongestion.rival_population_scaling hN).1
  have hcap : Tendsto (fun a => (C a : ℝ) / N a) atTop (𝓝 ρ) := by
    have hh := SimultaneousCongestion.capacity_per_rival hN (by simpa only [Nat.cast_add, Nat.cast_one] using hc)
    simpa only [Nat.add_sub_cancel] using hh
  let κ : ℝ := (η / 2) ^ 2
  have hκ : 0 < κ := sq_pos_of_pos (by positivity)
  have he : Tendsto (fun a => exp (-2 * N a * (η / 2) ^ 2)) atTop (𝓝 0) := by
    have hNrR : Tendsto (fun a => (N a : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hNr
    have ht := tendsto_exp_neg_atTop_nhds_zero.comp
      (hNrR.const_mul_atTop (show 0 < 2 * (η / 2) ^ 2 by positivity))
    convert ht using 1
    ext a
    congr 1
    ring
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hp, hcap.eventually_const_lt (show ρ - η / 2 < ρ by linarith),
    hNr.eventually_ge_atTop 1, he.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with a hpa hca hNa hsmall
  have hNR : (0 : ℝ) < N a := by exact_mod_cast hNa
  have hca' : (N a : ℝ) * (ρ - η / 2) < C a := by
    have hh := (lt_div_iff₀ hNR).mp hca
    nlinarith
  refine ⟨?_, ?_, hsmall.le⟩
  · have hh := mul_le_mul_of_nonneg_left (show p a + η / 2 ≤ ρ - η / 2 by linarith) hNR.le
    linarith
  · apply exp_le_exp.mpr
    have hN1 : (1 : ℝ) ≤ N a := by exact_mod_cast hNa
    have hh := mul_nonneg (sub_nonneg.mpr hN1) hκ.le
    dsimp [κ] at *
    nlinarith

theorem ppi_free_uniform_exponential_of_arrival_margin
    {N C : ℕ → ℕ} {Seed : ℕ → Type*} [∀ a, MeasurableSpace (Seed a)]
    (Γ : ∀ a, FiniteGame (N a + 1) n (C a) (Seed a)) (hn : 0 < n)
    (hA : ∀ a, (Γ a).A = Schedule.ppi n)
    (hfree : ∀ a, FreeDuplicateBase (Γ a))
    (hatom : ∀ a, PositiveVisibleAtomless (Γ a))
    (hj : ∀ a j, ProposerRationalAtFeasibleLists (Γ a) j)
    {ρ η : ℝ} (hη : 0 < η)
    (hN : Tendsto (fun a => N a + 1) atTop atTop)
    (hc : Tendsto (fun a => (C a : ℝ) / (N a + 1)) atTop (𝓝 ρ))
    (hmargin : ∀ᶠ a in atTop, Ample.contactMarginal n (visibleClassMass (Γ a) 0) ≤ ρ - η) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ a in atTop, ∀ i : Fin (N a + 1),
      (∀ act : JointAction n, 0 < act.bid →
        ((problem (Γ a) i).outcome act).prob (fun r => r.val ≠ act.routeCount) ≤
          n * exp (-κ * (N a + 1))) ∧
      (∀ w : ℝ, 0 < w → ∀ act : JointAction n,
        (problem (Γ a) i).BestResponse (w + (Γ a).g) act →
          act.bid ≤ 2 * w * exp (-κ * (N a + 1))) := by
  obtain ⟨κ, hκ, hrow⟩ := eventual_arrival_gap_and_source_exponential hη hN hc hmargin
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hrow] with a ha
  intro i
  constructor
  · intro act hb
    exact (ppi_missing_copy_le_exp_of_arrival_gap (Γ a) hn (hA a) (hatom a) (hj a)
      i act hb (by positivity) ha.1).trans
      (mul_le_mul_of_nonneg_left ha.2.1 (Nat.cast_nonneg n))
  · intro w hw act hbr
    exact (ppi_free_bestResponse_bid_le_exp_of_arrival_gap (Γ a) hn (hA a) (hfree a)
      (hatom a) (hj a) i hw act hbr (by positivity) ha.1 ha.2.2).trans
      (mul_le_mul_of_nonneg_left ha.2.1 (by positivity))

theorem ppi_free_uniform_exponential_of_submitted_margin
    {N C : ℕ → ℕ} {Seed : ℕ → Type*} [∀ a, MeasurableSpace (Seed a)]
    (Γ : ∀ a, FiniteGame (N a + 1) n (C a) (Seed a)) (hn : 0 < n)
    (hA : ∀ a, (Γ a).A = Schedule.ppi n)
    (hfree : ∀ a, FreeDuplicateBase (Γ a))
    (hatom : ∀ a, PositiveVisibleAtomless (Γ a))
    (hj : ∀ a j, ProposerRationalAtFeasibleLists (Γ a) j)
    {ρ η : ℝ} (hη : 0 < η)
    (hN : Tendsto (fun a => N a + 1) atTop atTop)
    (hc : Tendsto (fun a => (C a : ℝ) / (N a + 1)) atTop (𝓝 ρ))
    (hmargin : ∀ᶠ a in atTop, submittedMarginal (Γ a) ≤ ρ - η) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ a in atTop, ∀ i : Fin (N a + 1),
      (∀ act : JointAction n, 0 < act.bid →
        ((problem (Γ a) i).outcome act).prob (fun r => r.val ≠ act.routeCount) ≤
          n * exp (-κ * (N a + 1))) ∧
      (∀ w : ℝ, 0 < w → ∀ act : JointAction n,
        (problem (Γ a) i).BestResponse (w + (Γ a).g) act →
          act.bid ≤ 2 * w * exp (-κ * (N a + 1))) := by
  apply ppi_free_uniform_exponential_of_arrival_margin Γ hn hA hfree hatom hj hη hN hc
  filter_upwards [hmargin] with a ha
  exact (positive_arrivalMarginal_le_submitted (Γ a) hn).trans ha

end FCAppendix.Bayes
