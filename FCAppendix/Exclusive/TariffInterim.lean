import FCAppendix.Exclusive.BayesianKernel
import FCAppendix.PayOnce.Reliability
import FCAppendix.Finite.GameEnvelope

namespace FCAppendix.Exclusive
open MeasureTheory Filter Topology Game
open scoped BigOperators

inductive UserTariff where
  | unique
  | affine (eta : ℝ)

namespace UserTariff

noncomputable def charge : UserTariff → ℕ → ℝ
  | .unique, r => if r = 1 then 1 else 0
  | .affine eta, r => (1 - eta) * successIndicator r + eta * (r : ℝ)

def Allowed : UserTariff → Prop
  | .unique => True
  | .affine eta => 0 ≤ eta ∧ eta ≤ 1

@[simp] theorem charge_zero (a : UserTariff) : a.charge 0 = 0 := by
  cases a <;> simp [charge, successIndicator]

theorem charge_nonneg (a : UserTariff) (ha : a.Allowed) (r : ℕ) : 0 ≤ a.charge r := by
  cases a with
  | unique => simp only [charge]; split_ifs <;> norm_num
  | affine eta =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (successIndicator_nonneg r))
      (mul_nonneg ha.1 (Nat.cast_nonneg r))

theorem charge_affine_eq_schedule (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (n r : ℕ) :
    (UserTariff.affine eta).charge r = (Schedule.affine n eta h0 h1).charge r := by
  simp only [charge, Schedule.affine]
  ring

noncomputable def expected {n : ℕ} (a : UserTariff) (mu : CountLaw n) : ℝ :=
  mu.expect (fun r => a.charge r.val)

theorem expected_unique_binomial (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    UserTariff.unique.expected (IndependentCounts.binomial n p hp0 hp1) =
      n * p * (1 - p) ^ (n - 1) := by
  change (IndependentCounts.binomial n p hp0 hp1).expect
    (fun r => if r.val = 1 then (1 : ℝ) else 0) = _
  rw [← FiniteLaw.prob_eq_expect]
  exact PayOnce.Limit.binomial_single n p hp0 hp1

theorem expected_affine {n : ℕ} (eta : ℝ) (mu : CountLaw n) :
    (UserTariff.affine eta).expected mu = (1 - eta) * mu.success + eta * mu.load := by
  unfold expected charge
  rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul]
  rfl

theorem expected_affine_binomial (n : ℕ) (eta p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (UserTariff.affine eta).expected (IndependentCounts.binomial n p hp0 hp1) =
      (1 - eta) * PayOnce.success n p + eta * ((n : ℝ) * p) := by
  rw [expected_affine, IndependentCounts.binomial_success, IndependentCounts.binomial_load]
  rfl

end UserTariff
end FCAppendix.Exclusive

namespace FCAppendix.Bayes
open MeasureTheory Filter Topology Game Exclusive
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def exclusiveTariffPayoff (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) (a : JointAction n) : ℝ :=
  let mu := (problem Γ i).outcome a
  v * mu.success - a.bid * tariff.expected mu - Γ.g * mu.charge Γ.G

def ExclusiveTariffBestResponse (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) (a : JointAction n) : Prop :=
  ∀ a', exclusiveTariffPayoff Γ tariff i v a' ≤ exclusiveTariffPayoff Γ tariff i v a

def ExclusiveTariffUsersOptimal (Γ : FiniteGame m n c Seed) (tariff : UserTariff) : Prop :=
  ∀ i, ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, ExclusiveTariffBestResponse Γ tariff i v a

theorem exclusiveTariffPayoff_affine (Γ : FiniteGame m n c Seed)
    (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hA : Γ.A = Schedule.affine n eta h0 h1) (i : Fin m) (v : ℝ) (a : JointAction n) :
    exclusiveTariffPayoff Γ (.affine eta) i v a = (problem Γ i).payoff v a := by
  have he : (UserTariff.affine eta).expected ((problem Γ i).outcome a) =
      ((problem Γ i).outcome a).charge Γ.A := by
    rw [hA]
    unfold UserTariff.expected CountLaw.charge
    apply FiniteLaw.expect_congr
    intro r
    exact UserTariff.charge_affine_eq_schedule eta h0 h1 n r.val
  dsimp only [exclusiveTariffPayoff]
  rw [he]
  exact (CountLaw.utility_eq ((problem Γ i).outcome a) v a.bid Γ.g Γ.A Γ.G).symm

theorem exclusiveTariffUsersOptimal_affine_iff (Γ : FiniteGame m n c Seed)
    (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hA : Γ.A = Schedule.affine n eta h0 h1) :
    ExclusiveTariffUsersOptimal Γ (.affine eta) ↔ UsersOptimal Γ := by
  simp only [ExclusiveTariffUsersOptimal, UsersOptimal, ExclusiveTariffBestResponse,
    Interim.Problem.BestResponse, exclusiveTariffPayoff_affine Γ eta h0 h1 hA]

@[simp] theorem exclusiveTariffPayoff_abstain (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) (v : ℝ) :
    exclusiveTariffPayoff Γ tariff i v (Interim.abstain n) = 0 := by
  unfold exclusiveTariffPayoff
  rw [(problem Γ i).abstention]
  simp [UserTariff.expected, CountLaw.success, CountLaw.charge, FiniteLaw.expect_dirac,
    Interim.abstain, successIndicator, Γ.G.zero]

theorem exclusiveTariff_bestResponse_nonneg (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) {v : ℝ} {a : JointAction n}
    (ha : ExclusiveTariffBestResponse Γ tariff i v a) :
    0 ≤ exclusiveTariffPayoff Γ tariff i v a := by
  simpa only [exclusiveTariffPayoff_abstain] using ha (Interim.abstain n)

theorem exclusiveTariff_success_order (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (i : Fin m) {v w : ℝ} (hvw : v < w)
    {a b : JointAction n} (ha : ExclusiveTariffBestResponse Γ tariff i v a)
    (hb : ExclusiveTariffBestResponse Γ tariff i w b) :
    ((problem Γ i).outcome a).success ≤ ((problem Γ i).outcome b).success := by
  have h1 := ha b
  have h2 := hb a
  dsimp only [exclusiveTariffPayoff] at h1 h2
  by_contra hnot
  have hlt := lt_of_not_ge hnot
  have hp := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr hlt)
  nlinarith

theorem exclusiveTariff_mixed_success_order (Γ : FiniteGame m n c Seed)
    (tariff : UserTariff) (hu : ExclusiveTariffUsersOptimal Γ tariff) (i : Fin m) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ w ∂Γ.F, v < w → ∀ᵐ a ∂Γ.σ v, ∀ᵐ b ∂Γ.σ w,
      ((problem Γ i).outcome a).success ≤ ((problem Γ i).outcome b).success := by
  filter_upwards [hu i] with v hv
  filter_upwards [hu i] with w hw hvw
  filter_upwards [hv] with a ha
  filter_upwards [hw] with b hb
  exact exclusiveTariff_success_order Γ tariff i hvw ha hb

end FCAppendix.Bayes
