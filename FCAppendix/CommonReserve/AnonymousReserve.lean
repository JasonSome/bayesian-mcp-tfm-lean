import FCAppendix.CommonReserve.UniformTies
import FCAppendix.Finite.IdentitySymmetry
import FCAppendix.Finite.MixedBestResponseCounts
import FCAppendix.CommonReserve.Interim

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem anonymous_seed_count_zero (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) (ha : a.bid < r)
    (d : Fin m → Bayes.UserDraw n) (τ : Equiv.Perm (Fin n)) :
    ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw),
      Bayes.focalCount Γ i a ((d, s), τ) = 0 := by
  classical
  let L : Fin n → LocalList m := fun j =>
    Game.observe (Game.deviate (Bayes.drawsRealization d) i a.bid a.bid_nonneg
      (firstK τ a.routeCount)) j
  have hall : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => Γ.seedLaw), ∀ j,
      (Γ.policy j (L j) (s j)).val ⊆ eligible (L j) r := by
    apply ae_all_iff.mpr
    intro j
    exact (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
      ((hT j).eligible (L j))
  filter_upwards [hall] with s hs
  apply Fin.ext
  change Game.inclusionCount (Bayes.deviated i a ((d, s), τ)) Γ.policy s i = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hin : i ∈ (Γ.policy j (L j) (s j)).val := (Finset.mem_filter.mp hj).2
  have hel := (mem_eligible_iff (L j) r i).mp (hs j hin)
  have hei : (L j) i = if j ∈ firstK τ a.routeCount then some a.bid else none := by
    simp [L, Game.observe, Game.deviate]
  by_cases hr : j ∈ firstK τ a.routeCount
  · have hb : r ≤ a.bid := by simpa [hei, hr, Bayes.entryBid] using hel.2
    exact (not_le_of_gt ha) hb
  · exact hel.1 (by simp [hei, hr])

theorem anonymous_outcome_below_reserve (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) (ha : a.bid < r) :
    (Bayes.problem Γ i).outcome a = FiniteLaw.dirac 0 := by
  apply FiniteLaw.ext_expect
  intro f
  rw [Bayes.problem_outcome, CountLaw.expect_ofMeasure,
    Bayes.integral_focalCount_eq_inputs, FiniteLaw.expect_dirac]
  have hi (x : (Fin m → Bayes.UserDraw n) × Equiv.Perm (Fin n)) :
      (∫ s, f (Bayes.focalCount Γ i a ((x.1, s), x.2))
        ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) = f 0 := by
    have he := anonymous_seed_count_zero Γ r hT i a ha x.1 x.2
    rw [integral_congr_ae (he.mono fun s hs => congrArg f hs)]
    simp
  simp only [hi, integral_const, probReal_univ, one_smul]

theorem below_reserve_deviation_zero (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) (ha : a.bid < r) (v : ℝ) :
    (Bayes.problem Γ i).payoff v a = 0 := by
  change ((Bayes.problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G = 0
  rw [anonymous_outcome_below_reserve Γ r hT i a ha]
  simp [CountLaw.utility, userPayoff, successIndicator, Γ.A.zero, Γ.G.zero]

def anonymousCost (Γ : Bayes.FiniteGame m n c Seed) (i : Fin m) (a : JointAction n) : ℝ :=
  a.bid * ((Bayes.problem Γ i).outcome a).charge Γ.A +
    Γ.g * ((Bayes.problem Γ i).outcome a).charge Γ.G

theorem measurable_anonymousCost (Γ : Bayes.FiniteGame m n c Seed) (i : Fin m) :
    Measurable (anonymousCost Γ i) :=
  ((measurable_bid n).mul (Bayes.measurable_outcome_expect Γ i _)).add
    ((Bayes.measurable_outcome_expect Γ i _).const_mul Γ.g)

theorem anonymous_cost_floor (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ)
    (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (a : JointAction n) :
    (Γ.g + r) * ((Bayes.problem Γ i).outcome a).success ≤ anonymousCost Γ i a := by
  by_cases hb : r ≤ a.bid
  · have hA := mul_le_mul_of_nonneg_left
      (((Bayes.problem Γ i).outcome a).success_le_charge Γ.A) hr
    have hG := mul_le_mul_of_nonneg_left
      (((Bayes.problem Γ i).outcome a).success_le_charge Γ.G) Γ.g_nonneg
    have hB := mul_le_mul_of_nonneg_right hb
      (((Bayes.problem Γ i).outcome a).charge_nonneg Γ.A)
    unfold anonymousCost
    nlinarith
  · have hz := anonymous_outcome_below_reserve Γ r hT i a (lt_of_not_ge hb)
    simp [anonymousCost, hz, CountLaw.success, CountLaw.charge,
      FiniteLaw.expect_dirac, successIndicator, Γ.A.zero, Γ.G.zero]

def anonymousInterim (Γ : Bayes.FiniteGame m n c Seed) (r : ℝ) (hr : 0 ≤ r)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) (i : Fin m) :
    InterimProblem (JointAction n) where
  g := Γ.g
  r := r
  success a := ((Bayes.problem Γ i).outcome a).success
  cost := anonymousCost Γ i
  success_nonneg a := ((Bayes.problem Γ i).outcome a).success_nonneg
  success_le_one a := ((Bayes.problem Γ i).outcome a).success_le_one
  cost_floor := anonymous_cost_floor Γ r hr hT i
  zero := Interim.abstain n
  success_zero := by simp [(Bayes.problem Γ i).abstention, CountLaw.success, successIndicator]
  cost_zero := by simp [anonymousCost, (Bayes.problem Γ i).abstention,
    CountLaw.charge, Γ.A.zero, Γ.G.zero]

@[simp] theorem anonymousInterim_payoff (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) (a : JointAction n) :
    (anonymousInterim Γ r hr hT i).payoff v a = (Bayes.problem Γ i).payoff v a := by
  change v * ((Bayes.problem Γ i).outcome a).success - anonymousCost Γ i a =
    ((Bayes.problem Γ i).outcome a).utility v a.bid Γ.g Γ.A Γ.G
  rw [CountLaw.utility_eq]
  unfold anonymousCost
  ring

@[simp] theorem anonymousInterim_envelope (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) :
    (anonymousInterim Γ r hr hT i).envelope v = (Bayes.problem Γ i).envelope v := by
  have he : (anonymousInterim Γ r hr hT i).payoff v = (Bayes.problem Γ i).payoff v :=
    funext (anonymousInterim_payoff Γ r hr hT i v)
  exact congrArg (fun f : JointAction n → ℝ => sSup (Set.range f)) he

@[simp] theorem anonymousInterim_bestResponse (Γ : Bayes.FiniteGame m n c Seed)
    (r : ℝ) (hr : 0 ≤ r) (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r)
    (i : Fin m) (v : ℝ) (a : JointAction n) :
    (anonymousInterim Γ r hr hT i).BestResponse v a ↔ (Bayes.problem Γ i).BestResponse v a := by
  simp only [InterimProblem.BestResponse, anonymousInterim_payoff, Interim.Problem.BestResponse]

end FCAppendix.CommonReserve
