import FCAppendix.Ample.ActualEventRate
import FCAppendix.Ample.SlackParticipation

noncomputable section
namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Filter Set
open scoped BigOperators
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in

theorem rivals_le_predecessor (i : Fin (N + 1)) (E : Set (UserDraw n))
    (ω : Background (N + 1) n Seed) : rivals i E ω ≤ N := by
  classical
  unfold rivals PiBinomial.count
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem ae_accepts_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) {b : ℝ} (hb : 0 < b) :
    ∀ᵐ ω ∂backgroundLaw Γ, ∀ j : Fin n, Accepts Γ i b j ω := by
  have hr := ae_all_iff.mpr fun j =>
    ae_ppi_accepts_iff_rank Γ hA hatom j (hpolicy j) i b hb
  filter_upwards [hr] with ω hω
  intro j
  exact (hω j).mpr (lt_of_le_of_lt (rivals_le_predecessor i (aboveAt j b) ω)
    (by omega))

theorem ae_count_eq_chosen_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) :
    ∀ᵐ ω ∂sampleLaw Γ, (focalCount Γ i a ω).val = a.routeCount := by
  classical
  have hacc := ae_accepts_of_no_shortage Γ hc hA hatom hpolicy i hb
  have hprod : ∀ᵐ ω ∂sampleLaw Γ, ∀ j, Accepts Γ i a.bid j ω.1 :=
    Measure.quasiMeasurePreserving_fst.ae hacc
  filter_upwards [hprod] with ω hω
  have he := focalCount_val_eq Γ i a ω
  simp only [hω, if_true, mul_one] at he
  have hcard : (∑ j : Fin n, if j ∈ firstK ω.2 a.routeCount then (1 : ℝ) else 0) =
      (a.routeCount : ℝ) := by
    rw [sum_membership_real, card_firstK ω.2 a.routeCount a.routeCount_le]
  rw [hcard] at he
  exact_mod_cast he

theorem outcome_test_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) (f : ℕ → ℝ) :
    ((problem Γ i).outcome a).expect (fun r => f r.val) = f a.routeCount := by
  rw [problem_outcome, CountLaw.expect_ofMeasure]
  calc
    (∫ ω, f (focalCount Γ i a ω).val ∂sampleLaw Γ) =
        ∫ _ : Sample (N + 1) n Seed, f a.routeCount ∂sampleLaw Γ := by
      apply integral_congr_ae
      filter_upwards [ae_count_eq_chosen_of_no_shortage Γ hc hA hatom hpolicy i a hb]
        with ω hω
      rw [hω]
    _ = _ := by simp

def halfBid (a : JointAction n) : JointAction n :=
  { a with bid := a.bid / 2, bid_nonneg := div_nonneg a.bid_nonneg (by norm_num) }

theorem positive_routed_not_bestResponse_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (v : ℝ) (a : JointAction n)
    (hb : 0 < a.bid) (hk : 0 < a.routeCount) :
    ¬ (problem Γ i).BestResponse v a := by
  have hbhalf : 0 < (halfBid a).bid := half_pos hb
  have hpay (b : JointAction n) (hbp : 0 < b.bid) :
      (problem Γ i).payoff v b =
        userPayoff v b.bid Γ.g Γ.A.charge Γ.G.charge b.routeCount := by
    change ((problem Γ i).outcome b).expect
      (fun r => userPayoff v b.bid Γ.g Γ.A.charge Γ.G.charge r.val) = _
    exact outcome_test_of_no_shortage Γ hc hA hatom hpolicy i b hbp
      (userPayoff v b.bid Γ.g Γ.A.charge Γ.G.charge)
  intro hbr
  have hle := hbr (halfBid a)
  rw [hpay a hb, hpay (halfBid a) hbhalf] at hle
  simp only [halfBid, userPayoff, hA, Schedule.ppi] at hle
  have hgain : 0 < (a.bid / 2) * (a.routeCount : ℝ) :=
    mul_pos (half_pos hb) (Nat.cast_pos.mpr hk)
  nlinarith

theorem ae_no_positive_routed_draw_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j) (hu : UsersOptimal Γ) :
    ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount = 0 ∨ x.2.bid = 0 := by
  let i : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
  filter_upwards [ae_bestResponse_compProd Γ hu i] with x hx
  by_cases hk : x.2.routeCount = 0
  · exact Or.inl hk
  · right
    by_contra hb
    exact positive_routed_not_bestResponse_of_no_shortage Γ hc hA hatom hpolicy
      i x.1 x.2 (lt_of_le_of_ne x.2.bid_nonneg (Ne.symm hb))
      (Nat.pos_of_ne_zero hk) hx

theorem no_bestResponse_above_fee_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hz : RejectsZeroBids Γ) (i : Fin (N + 1)) (v : ℝ) (hv : Γ.g < v)
    (a : JointAction n) : ¬ (problem Γ i).BestResponse v a := by
  have hw : 0 < v - Γ.g := sub_pos.mpr hv
  let s : JointAction n := ⟨(v - Γ.g) / 2, (half_pos hw).le, 1, hn⟩
  have hsb : 0 < s.bid := half_pos hw
  have hpay : (problem Γ i).payoff v s = (v - Γ.g) / 2 := by
    calc
      (problem Γ i).payoff v s =
          userPayoff v s.bid Γ.g Γ.A.charge Γ.G.charge s.routeCount :=
        outcome_test_of_no_shortage Γ hc hA hatom hpolicy i s hsb
          (userPayoff v s.bid Γ.g Γ.A.charge Γ.G.charge)
      _ = (v - Γ.g) / 2 := by
        simp only [s, userPayoff, successIndicator, Nat.one_ne_zero, if_false,
          mul_one, Γ.A.one hn, Γ.G.one hn]
        ring
  have hgood : 0 < (problem Γ i).payoff v s := by rw [hpay]; exact half_pos hw
  intro ha
  have hzero : ((problem Γ i).outcome a).success = 0 := by
    by_cases hk : 0 < a.routeCount
    · by_cases hb : 0 < a.bid
      · exact False.elim (positive_routed_not_bestResponse_of_no_shortage Γ hc hA
          hatom hpolicy i v a hb hk ha)
      · have hb0 : a.bid = 0 := le_antisymm (le_of_not_gt hb) a.bid_nonneg
        exact success_zero_of_bid_zero Γ hn hz i a hb0
    · exact success_zero_of_route_zero Γ i a (by omega)
  have hupper := ((problem Γ i).outcome a).utility_le_net_success
    v a.bid Γ.g Γ.A Γ.G a.bid_nonneg Γ.g_nonneg
  change (problem Γ i).payoff v a ≤ (v - Γ.g) * _ at hupper
  rw [hzero, mul_zero] at hupper
  exact (not_le_of_gt (hgood.trans_le (ha s))) hupper

theorem not_usersOptimal_of_no_shortage
    (Γ : FiniteGame (N + 1) n c Seed) (hc : N + 1 ≤ c) (hn : 0 < n)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hz : RejectsZeroBids Γ) (hactive : 0 < Γ.F.real (Ioi Γ.g)) :
    ¬ UsersOptimal Γ := by
  intro hu
  let i : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
  have hae : ∀ᵐ v ∂Γ.F, v ∉ Ioi Γ.g := by
    filter_upwards [hu i] with v hv
    intro hvg
    obtain ⟨a, ha⟩ := hv.exists
    exact no_bestResponse_above_fee_of_no_shortage Γ hc hn hA hatom hpolicy hz
      i v hvg a ha
  have hzF : Γ.F (Ioi Γ.g) = 0 := measure_eq_zero_iff_ae_notMem.mpr hae
  have hreal : Γ.F.real (Ioi Γ.g) = 0 := by simp [Measure.real, hzF]
  rw [hreal] at hactive
  exact (lt_irrefl 0) hactive

end FCAppendix.Bayes.CompletionDraft
