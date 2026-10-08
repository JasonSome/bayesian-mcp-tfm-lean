import FCAppendix.Finite.TruncatedActualPayments
import FCAppendix.Game.JointMeasurability
import FCAppendix.Affine.FixedBounds
import FCAppendix.Game.RealizedIntegrals

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem truncatedBid_le_bid (R b : ℝ) (hb : 0 ≤ b) : truncatedBid R b ≤ b := by
  unfold truncatedBid
  split
  · simp only [max_eq_left hb, le_refl]
  · exact hb

noncomputable def truncatedPaymentStatistic (Γ : FiniteGame m n c Seed)
    (R : ℝ) (x : (ℝ × JointAction n) × Fin (n + 1)) : ℝ :=
  truncatedBid R x.1.2.bid * Γ.A.charge x.2.val

theorem measurable_truncatedPaymentStatistic (Γ : FiniteGame m n c Seed) (R : ℝ) :
    Measurable (truncatedPaymentStatistic Γ R) :=
  ((measurable_truncatedBid R).comp ((measurable_bid n).comp
    (measurable_snd.comp measurable_fst))).mul
    ((measurable_of_countable (fun r : Fin (n + 1) => Γ.A.charge r.val)).comp measurable_snd)

theorem truncatedPaymentStatistic_bounds (Γ : FiniteGame m n c Seed)
    (R : ℝ) (hR : 0 ≤ R) (x : (ℝ × JointAction n) × Fin (n + 1)) :
    0 ≤ truncatedPaymentStatistic Γ R x ∧ truncatedPaymentStatistic Γ R x ≤ n * R := by
  have hb := truncatedBid_bounds R x.1.2.bid hR
  have hc0 := Γ.A.nonneg x.2.val (by omega)
  have hcn : Γ.A.charge x.2.val ≤ n :=
    (Γ.A.upper x.2.val (by omega)).trans (Nat.cast_le.mpr (by omega))
  exact ⟨mul_nonneg hb.1 hc0, (mul_le_mul hb.2 hcn hc0 hR).trans_eq (mul_comm R n)⟩

noncomputable def interimTruncatedPayment (Γ : FiniteGame m n c Seed)
    (i : Fin m) (R : ℝ) (x : ℝ × JointAction n) : ℝ :=
  truncatedBid R x.2.bid * ((problem Γ i).outcome x.2).charge Γ.A

theorem interimTruncatedPayment_eq_expect (Γ : FiniteGame m n c Seed)
    (i : Fin m) (R : ℝ) (x : ℝ × JointAction n) :
    interimTruncatedPayment Γ i R x =
      ((problem Γ i).outcome x.2).expect (fun r => truncatedPaymentStatistic Γ R (x, r)) := by
  unfold interimTruncatedPayment truncatedPaymentStatistic CountLaw.charge
  exact (((problem Γ i).outcome x.2).expect_const_mul _ _).symm

theorem integrable_interimTruncatedPayment (Γ : FiniteGame m n c Seed)
    (i : Fin m) (R : ℝ) (hR : 0 ≤ R) :
    Integrable (interimTruncatedPayment Γ i R) (Γ.F ⊗ₘ Γ.σ) := by
  have h := integrable_interim_expect Γ i (truncatedPaymentStatistic Γ R)
    (measurable_truncatedPaymentStatistic Γ R) (n * R) (fun x => by
      have hx := truncatedPaymentStatistic_bounds Γ R hR x
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  simpa only [← interimTruncatedPayment_eq_expect] using h

theorem finiteTruncatedPayment_eq_interim (Γ : FiniteGame m n c Seed)
    (R : ℝ) (hR : 0 ≤ R) :
    finiteTruncatedPayment Γ R =
      (∑ i, ∫ x, interimTruncatedPayment Γ i R x ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
  rw [finiteTruncatedPayment_eq_user_integrals Γ R hR]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := integral_realized_eq_interim Γ i (truncatedPaymentStatistic Γ R)
    (measurable_truncatedPaymentStatistic Γ R) (n * R) (fun x => by
      have hx := truncatedPaymentStatistic_bounds Γ R hR x
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)
  rw [show (fun x : ℝ × JointAction n =>
      ((problem Γ i).outcome x.2).expect (fun r => truncatedPaymentStatistic Γ R (x, r))) =
      interimTruncatedPayment Γ i R from
    funext (fun x => (interimTruncatedPayment_eq_expect Γ i R x).symm)] at h
  exact h

theorem bestResponse_bid_payment_le_envelope_error
    (Γ : FiniteGame m n c Seed) (i : Fin m) (v P δ : ℝ) (act : JointAction n)
    (hbr : (problem Γ i).BestResponse v act)
    (henv : max (v - Γ.g - P) 0 - δ ≤ (problem Γ i).envelope v) :
    act.bid * ((problem Γ i).outcome act).charge Γ.A ≤
      P * ((problem Γ i).outcome act).success + δ := by
  let μ := (problem Γ i).outcome act
  have he : 0 ≤ Γ.g * (μ.charge Γ.G - μ.success) :=
    mul_nonneg Γ.g_nonneg (sub_nonneg.mpr (μ.success_le_charge Γ.G))
  have hid : (problem Γ i).envelope v =
      (v - Γ.g) * μ.success - act.bid * μ.charge Γ.A -
        Γ.g * (μ.charge Γ.G - μ.success) := by
    have hatt := ((problem Γ i).bestResponse_iff_attains v act).mp hbr
    rw [← hatt]
    change μ.utility v act.bid Γ.g Γ.A Γ.G = _
    rw [CountLaw.utility_eq]
    ring
  exact Affine.transfer_le_of_envelope_error (v - Γ.g) P μ.success
    (act.bid * μ.charge Γ.A) ((problem Γ i).envelope v)
    (Γ.g * (μ.charge Γ.G - μ.success)) δ μ.success_nonneg μ.success_le_one he hid henv

theorem finiteTruncatedPayment_upper_value_cutoff
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hu : UsersOptimal Γ)
    (P R H δ : ℝ) (hP : 0 ≤ P) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (henv : ∀ (i : Fin m) v, v ≤ H →
      max (v - Γ.g - P) 0 - δ ≤ (problem Γ i).envelope v) :
    finiteTruncatedPayment Γ R ≤ P * finiteCoverage Γ + δ +
      (n * R) * Γ.F.real (Ioi H) := by
  classical
  let s : Set (ℝ × JointAction n) := Ioi H ×ˢ univ
  have hs : MeasurableSet s := measurableSet_Ioi.prod MeasurableSet.univ
  have hmeasure : (Γ.F ⊗ₘ Γ.σ) s = Γ.F (Ioi H) := by
    simp [s, Measure.compProd_apply_prod measurableSet_Ioi MeasurableSet.univ]
  have hi (i : Fin m) :
      (∫ x, interimTruncatedPayment Γ i R x ∂(Γ.F ⊗ₘ Γ.σ)) ≤
        P * (∫ x, ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ)) + δ +
          (n * R) * Γ.F.real (Ioi H) := by
    have hms := (measurable_outcome_expect Γ i (fun r => successIndicator r.val)).comp
      (show Measurable (fun x : ℝ × JointAction n => x.2) from measurable_snd)
    change Measurable (fun x : ℝ × JointAction n => ((problem Γ i).outcome x.2).success) at hms
    have his := UnitInterval.integrable (Γ.F ⊗ₘ Γ.σ) _ hms
      (fun _ => CountLaw.success_nonneg _) (fun _ => CountLaw.success_le_one _)
    have hic : Integrable (s.indicator (fun _ => n * R)) (Γ.F ⊗ₘ Γ.σ) :=
      (integrable_const (n * R)).indicator hs
    have hupp := ((his.const_mul P).add (integrable_const δ)).add hic
    have h := integral_mono_ae (integrable_interimTruncatedPayment Γ i R hR) hupp
      (show interimTruncatedPayment Γ i R ≤ᵐ[Γ.F ⊗ₘ Γ.σ]
        (fun x => P * ((problem Γ i).outcome x.2).success + δ +
          s.indicator (fun _ => n * R) x) from by
        filter_upwards [ae_bestResponse_compProd Γ hu i] with x hx
        have hS := CountLaw.success_nonneg ((problem Γ i).outcome x.2)
        by_cases hv : x.1 ≤ H
        · have hnot : x ∉ s := by
            simpa only [s, mem_prod, mem_Ioi, mem_univ, and_true] using not_lt.mpr hv
          rw [indicator_of_notMem hnot, add_zero]
          exact (mul_le_mul_of_nonneg_right (truncatedBid_le_bid R x.2.bid x.2.bid_nonneg)
            (CountLaw.charge_nonneg _ Γ.A)).trans
              (bestResponse_bid_payment_le_envelope_error Γ i x.1 P δ x.2 hx (henv i x.1 hv))
        · have hmem : x ∈ s := ⟨lt_of_not_ge hv, mem_univ _⟩
          rw [indicator_of_mem hmem]
          have hb := truncatedBid_bounds R x.2.bid hR
          have hc := (CountLaw.charge_le_load ((problem Γ i).outcome x.2) Γ.A).trans
            (CountLaw.load_le_n _)
          have hh := mul_le_mul hb.2 hc (CountLaw.charge_nonneg _ Γ.A) hR
          dsimp only [interimTruncatedPayment]
          nlinarith [mul_nonneg hP hS])
    dsimp only [Pi.add_apply] at h
    rw [integral_add (f := fun x : ℝ × JointAction n => P * ((problem Γ i).outcome x.2).success + δ)
      ((his.const_mul P).add (integrable_const δ)) hic,
      integral_add (his.const_mul P) (integrable_const δ), integral_const_mul,
      integral_const, probReal_univ, one_smul, integral_indicator_const _ hs] at h
    simpa only [smul_eq_mul, measureReal_def, hmeasure, mul_comm] using h
  rw [finiteTruncatedPayment_eq_interim Γ R hR, finiteCoverage_eq_actual]
  simp_rw [integral_realized_success_eq_interim]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hi i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply (div_le_iff₀ (Nat.cast_pos.mpr hm : (0 : ℝ) < m)).mpr
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  convert hsum using 1
  field_simp [hmR]

end FCAppendix.Bayes
