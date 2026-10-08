import FCAppendix.Ample.ActualEventRate
import FCAppendix.Ample.ServiceBounds
import FCAppendix.Finite.PPIRankTypes

namespace FCAppendix.CountLaw

variable {n : ℕ}

theorem excess_base_eq_zero_of_free (μ : CountLaw n) (G : Schedule n) (g : ℝ)
    (hfree : ∀ r, 1 ≤ r → r ≤ n → g * (G.charge r - 1) = 0) :
    g * (μ.charge G - μ.success) = 0 := by
  have he : g * (μ.charge G - μ.success) =
      μ.expect (fun r => g * (G.charge r.val - successIndicator r.val)) := by
    rw [μ.expect_const_mul, μ.expect_sub]
    rfl
  rw [he]
  calc
    _ = μ.expect (fun _ => 0) := by
      apply μ.expect_congr
      intro r
      by_cases hr : r.val = 0
      · simp [hr, G.zero, successIndicator]
      · simpa [successIndicator, hr] using hfree r.val (by omega) (by omega)
    _ = 0 := μ.expect_zero

end FCAppendix.CountLaw

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology Real
open scoped BigOperators

variable {m n N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def FreeDuplicateBase (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ r, 1 ≤ r → r ≤ n → Γ.g * (Γ.G.charge r - 1) = 0

theorem ppi_free_payoff (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (i : Fin m) (w : ℝ) (a : JointAction n) :
    (problem Γ i).payoff (w + Γ.g) a =
      w * ((problem Γ i).outcome a).success - a.bid * ((problem Γ i).outcome a).load := by
  have hz := ((problem Γ i).outcome a).excess_base_eq_zero_of_free Γ.G Γ.g hfree
  change ((problem Γ i).outcome a).utility _ _ _ _ _ = _
  rw [CountLaw.utility_eq]
  change (w + Γ.g) * _ - a.bid * ((problem Γ i).outcome a).charge Γ.A -
    Γ.g * ((problem Γ i).outcome a).charge Γ.G = _
  rw [hA, CountLaw.charge_ppi]
  nlinarith

theorem ppi_free_deficit_identity (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hn : 0 < n) (i : Fin m) (w : ℝ) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (w + Γ.g) a) :
    Ample.deficit (problem Γ i) w =
      w * (1 - ((problem Γ i).outcome a).success) +
        a.bid * (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid := by
  have h := Ample.deficit_identity (problem Γ i) w a ha
  have hz := ((problem Γ i).outcome a).excess_base_eq_zero_of_free Γ.G Γ.g hfree
  change _ = w * (1 - _) + a.bid * ((problem Γ i).outcome a).charge Γ.A +
    Γ.g * (((problem Γ i).outcome a).charge Γ.G - _) at h
  rw [hz, add_zero, hA, CountLaw.charge_ppi, load_eq_mean Γ hn i a] at h
  simpa only [mul_assoc] using h

noncomputable def allPositiveCongestion (Γ : FiniteGame m n c Seed) (i : Fin m) : ℝ :=
  (backgroundLaw Γ).real {ω | ∀ j : Fin n, c ≤ rivals i (aboveAt j 0) ω}

omit [MeasurableSpace Seed] in
theorem rivals_mono_threshold (i : Fin m) {b d : ℝ} (hbd : b ≤ d)
    (j : Fin n) (ω : Background m n Seed) :
    rivals i (aboveAt j d) ω ≤ rivals i (aboveAt j b) ω := by
  classical
  unfold rivals PiBinomial.count
  apply Finset.card_le_card
  intro l hl
  rcases Finset.mem_filter.mp hl with ⟨hl, hdraw⟩
  refine Finset.mem_filter.mpr ⟨hl, ?_⟩
  exact ⟨hdraw.1, lt_of_le_of_lt hbd hdraw.2⟩

theorem joint_rank_congestion_antitone_bid (Γ : FiniteGame m n c Seed)
    (i : Fin m) (K : Finset (Fin n)) {b d : ℝ} (hbd : b ≤ d) :
    (backgroundLaw Γ).real {ω | ∀ j ∈ K, c ≤ rivals i (aboveAt j d) ω} ≤
      (backgroundLaw Γ).real {ω | ∀ j ∈ K, c ≤ rivals i (aboveAt j b) ω} := by
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω j hj
  exact (hω j hj).trans (rivals_mono_threshold i hbd j ω)

theorem broadcast_failure_le_allPositive (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid)
    (hk : a.routeCount = n) :
    1 - ((problem Γ i).outcome a).success ≤ allPositiveCongestion Γ i := by
  classical
  rw [ppi_failure_eq_congestProb Γ hA hatom hj i a hb, hk]
  have he := joint_rank_congestion_eq Γ i a.bid (Finset.univ : Finset (Fin n))
  rw [Ample.congestProbAt_eq_congestProb, Finset.card_univ, Fintype.card_fin] at he
  rw [← he]
  simpa [allPositiveCongestion] using
    joint_rank_congestion_antitone_bid Γ i Finset.univ hb.le

theorem envelope_ge_allPositive_outside (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) {w : ℝ} (hw : 0 ≤ w) :
    w * (1 - allPositiveCongestion Γ i) ≤ (problem Γ i).envelope (w + Γ.g) := by
  let e : ℕ → ℝ := fun t => 1 / ((t : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun t => w * (1 - allPositiveCongestion Γ i) -
      e t * (n : ℝ)) atTop (𝓝 (w * (1 - allPositiveCongestion Γ i))) := by
    simpa using tendsto_const_nhds.sub (he.mul_const (n : ℝ))
  apply le_of_tendsto hlim
  filter_upwards [] with t
  have het : 0 < e t := by dsimp [e]; positivity
  let a : JointAction n := ⟨e t, het.le, n, le_rfl⟩
  have hd := broadcast_failure_le_allPositive Γ hA hatom hj i a het rfl
  have hp := (problem Γ i).action_le_envelope (w + Γ.g) a
  rw [ppi_free_payoff Γ hA hfree] at hp
  have hload := ((problem Γ i).outcome a).load_le_n
  have h1 := mul_le_mul_of_nonneg_left hload het.le
  have h2 := mul_le_mul_of_nonneg_left (show 1 - allPositiveCongestion Γ i ≤
      ((problem Γ i).outcome a).success by linarith) hw
  change _ ≤ (problem Γ i).envelope (w + Γ.g)
  change w * _ - e t * _ ≤ _ at hp
  linarith

theorem ppi_free_AM1 (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hn : 0 < n) (i : Fin (N + 1)) {w : ℝ} (hw : 0 < w)
    (a : JointAction n) (ha : (problem Γ i).BestResponse (w + Γ.g) a) :
    Ample.deficit (problem Γ i) w ≤ w * allPositiveCongestion Γ i ∧
    1 - ((problem Γ i).outcome a).success ≤ allPositiveCongestion Γ i ∧
    a.bid * (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid ≤
      w * allPositiveCongestion Γ i := by
  have hU := envelope_ge_allPositive_outside Γ hA hfree hatom hj i hw.le
  have hf : Ample.deficit (problem Γ i) w ≤ w * allPositiveCongestion Γ i := by
    change w - (problem Γ i).envelope (w + Γ.g) ≤ _
    linarith
  have hd := ppi_free_deficit_identity Γ hA hfree hn i w a ha
  have hpay : 0 ≤ a.bid * (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid := by
    rw [mul_assoc, ← load_eq_mean Γ hn i a]
    exact mul_nonneg a.bid_nonneg ((problem Γ i).outcome a).load_nonneg
  have hfail := sub_nonneg.mpr ((problem Γ i).outcome a).success_le_one
  refine ⟨hf, ?_, ?_⟩
  · nlinarith
  · nlinarith

def sameBidSingleton (hn : 0 < n) (a : JointAction n) : JointAction n :=
  ⟨a.bid, a.bid_nonneg, 1, hn⟩

theorem ppi_free_sameBid_singleton_comparison (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hn : 0 < n) (i : Fin m) (w : ℝ) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (w + Γ.g) a) :
    a.bid * ((a.routeCount : ℝ) - 1) * meanAcceptProb Γ i a.bid ≤
      w * (((problem Γ i).outcome a).success - meanAcceptProb Γ i a.bid) := by
  have h := ha (sameBidSingleton hn a)
  rw [ppi_free_payoff Γ hA hfree, ppi_free_payoff Γ hA hfree,
    load_eq_mean Γ hn i a, load_eq_mean Γ hn i (sameBidSingleton hn a),
    singleton_success Γ hn i (sameBidSingleton hn a) rfl] at h
  simp only [sameBidSingleton, Nat.cast_one] at h
  change w * meanAcceptProb Γ i a.bid - a.bid * ((1 : ℝ) * meanAcceptProb Γ i a.bid) ≤
    w * ((problem Γ i).outcome a).success - a.bid * ((a.routeCount : ℝ) *
      meanAcceptProb Γ i a.bid) at h
  nlinarith

theorem ppi_free_multiroute_bid_bound (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hn : 0 < n) (i : Fin m) {w H r : ℝ} (hw : 0 ≤ w) (hwH : w ≤ H)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (a : JointAction n)
    (ha : (problem Γ i).BestResponse (w + Γ.g) a)
    (hk : 2 ≤ a.routeCount) (hq : 1 - r ≤ meanAcceptProb Γ i a.bid) :
    a.bid ≤ H * r / (1 - r) := by
  have hc := ppi_free_sameBid_singleton_comparison Γ hA hfree hn i w a ha
  have hS := ((problem Γ i).outcome a).success_le_one
  have hk' : (2 : ℝ) ≤ a.routeCount := by exact_mod_cast hk
  have hq0 : 0 ≤ meanAcceptProb Γ i a.bid := by linarith
  have hbk : a.bid * meanAcceptProb Γ i a.bid ≤
      a.bid * ((a.routeCount : ℝ) - 1) * meanAcceptProb Γ i a.bid := by
    have hh := mul_nonneg (mul_nonneg a.bid_nonneg hq0) (show 0 ≤ (a.routeCount : ℝ)-2 by linarith)
    nlinarith
  have hwS : w * (((problem Γ i).outcome a).success - meanAcceptProb Γ i a.bid) ≤ w * r := by
    exact mul_le_mul_of_nonneg_left (by linarith) hw
  have hwHr := mul_le_mul_of_nonneg_right hwH hr0
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  have hbq := mul_le_mul_of_nonneg_left hq a.bid_nonneg
  nlinarith

theorem ppi_free_no_low_bestReply_of_gain (Γ : FiniteGame m n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hn : 0 < n) (i : Fin m) {ε w H s r B : ℝ}
    (hε : 0 < ε) (hεw : ε ≤ w) (hwH : w ≤ H)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (_hB : 0 ≤ B)
    (lo hi : JointAction n) (hhi : hi.routeCount = 1)
    (hfail : s ≤ 1 - ((problem Γ i).outcome lo).success)
    (hq : 1 - r ≤ meanAcceptProb Γ i hi.bid) (hbid : hi.bid ≤ B)
    (hgain : H * r + B < ε * s) :
    ¬ (problem Γ i).BestResponse (w + Γ.g) lo := by
  intro hbr
  have hw : 0 ≤ w := (hε.trans_le hεw).le
  have hq0 : 0 ≤ meanAcceptProb Γ i hi.bid := by
    rw [← singleton_success Γ hn i hi hhi]
    exact ((problem Γ i).outcome hi).success_nonneg
  have hq1 : meanAcceptProb Γ i hi.bid ≤ 1 := by
    rw [← singleton_success Γ hn i hi hhi]
    exact ((problem Γ i).outcome hi).success_le_one
  have h := hbr hi
  rw [ppi_free_payoff Γ hA hfree, ppi_free_payoff Γ hA hfree,
    load_eq_mean Γ hn i hi, hhi, Nat.cast_one, one_mul,
    singleton_success Γ hn i hi hhi] at h
  have hp0 := mul_nonneg lo.bid_nonneg ((problem Γ i).outcome lo).load_nonneg
  have hpayment : hi.bid * meanAcceptProb Γ i hi.bid ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left hq1 hi.bid_nonneg
    nlinarith
  have hws := mul_le_mul_of_nonneg_left hfail hw
  have hwr := mul_le_mul_of_nonneg_left hq hw
  have hεs := mul_le_mul_of_nonneg_right hεw hs
  have hHr := mul_le_mul_of_nonneg_right hwH hr
  nlinarith

end FCAppendix.Bayes
