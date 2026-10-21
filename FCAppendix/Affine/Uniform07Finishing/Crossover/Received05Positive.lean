import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Family
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Positive
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Capped

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment Physical

section OneMarket
variable {row : Uniform07.Row} {m : ℕ} [Nonempty (Fin m)]

theorem native_positive_payoff (E : ReadyLaw row m)
    (hc : 1≤ Uniform07.capacity m) (i : Fin m) (v b : ℝ)
    (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
    (problem (Concrete05.nativeGame E.1 hc (sourceLowerPriceCeiling row)) i).payoff v (two b)=
      Rank.payoff (Uniform07.eta row) v b
        (sourceSuccess row m (G row m E) (g row m E) (cm row m E) b)
        (sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b) := by
  cases m with
  | zero => exact (Nat.not_succ_le_zero 1 E.1.cluster.market_two_le).elim
  | succ N =>
    let a : Uniform05.Bid row:=⟨b,⟨hb.1.le,by rw [cap_eq]; exact hb.2⟩⟩
    have ha : Hybrid.lowBroadcast a=two b := by
      simpa only [Hybrid.lowBroadcast,a] using raw_two_eq (Hybrid.lowBroadcast a) rfl
    rw [←ha]
    exact (Concrete05.native_capped_payoff_eq_raw E.1 hc
      (source_auxiliary_floor_guards row).1
      (source_auxiliary_floor_guards row).2.1
      (source_auxiliary_floor_guards row).2.2.1
      (Concrete05.auxiliary_receipt_gap E.1) i v a hb.1).trans
        (rawUtility_eq_source row (N+1) E v b ⟨hb.1.le,hb.2⟩)

theorem native_positive_counts (E : ReadyLaw row m)
    (hc : 1≤ Uniform07.capacity m) (i : Fin m) :
    Received06.PositiveCountTransport row (G row m E) (g row m E) (cm row m E)
      (Concrete05.nativeGame E.1 hc (sourceLowerPriceCeiling row)) i := by
  let Γ:=Concrete05.nativeGame E.1 hc (sourceLowerPriceCeiling row)
  have hpay (v b : ℝ) (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
      (v-b)*success Γ i b-Uniform07.eta row*b*duplicate Γ i b=
        (v-b)*sourceSuccess row m (G row m E) (g row m E) (cm row m E) b-
          Uniform07.eta row*b*sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b := by
    have h:=native_positive_payoff E hc i v b hb
    rw [LowBody.native_affine_zero_fee_payoff Γ
      (Uniform07.eta_pos row).le (source_eta_lt_one row).le rfl rfl] at h
    simpa only [Rank.payoff,Physical.success,Physical.duplicate,two_bid hb.1.le] using h
  have hS (b : ℝ) (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
      success Γ i b=sourceSuccess row m (G row m E) (g row m E) (cm row m E) b := by
    have h₀:=hpay 0 b hb
    have h₁:=hpay 1 b hb
    linarith
  refine ⟨hS,?_⟩
  intro b hb
  have h:=hpay 0 b hb
  rw [hS b hb] at h
  have he : Uniform07.eta row*b≠0:=(mul_pos (Uniform07.eta_pos row) hb.1).ne'
  exact (mul_left_cancel₀ he (by linarith :
    (Uniform07.eta row*b)*duplicate Γ i b=
      (Uniform07.eta row*b)*sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b))

end OneMarket

theorem ReadyLowerFamily.positive_counts (F : ReadyLowerFamily)
    (row : Uniform07.Row) (k : ℕ) (i : Fin (F.start+k)) :
    Received06.PositiveCountTransport row (G row (F.start+k) (F.law row k))
      (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k))
      (F.market row k).native i := by
  letI : Nonempty (Fin (F.start+k)) := (F.market row k).fin_nonempty
  exact native_positive_counts (F.law row k) (F.market row k).capacity_positive i

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
