import FCAppendix.Game.LocalInformation

namespace FCAppendix
namespace Interim

open MeasureTheory

noncomputable def abstain (n : ℕ) : Game.JointAction n where
  bid := 0
  bid_nonneg := le_rfl
  routeCount := 0
  routeCount_le := Nat.zero_le n

structure Problem (n : ℕ) where
  A : Schedule n
  G : Schedule n
  g : ℝ
  g_nonneg : 0 ≤ g
  outcome : Game.JointAction n → CountLaw n
  abstention : outcome (abstain n) = FiniteLaw.dirac 0

namespace Problem

variable {n : ℕ}

noncomputable def payoff (P : Problem n) (v : ℝ) (a : Game.JointAction n) : ℝ :=
  (P.outcome a).utility v a.bid P.g P.A P.G

noncomputable def envelope (P : Problem n) (v : ℝ) : ℝ :=
  sSup (Set.range (P.payoff v))

def BestResponse (P : Problem n) (v : ℝ) (a : Game.JointAction n) : Prop :=
  ∀ a', P.payoff v a' ≤ P.payoff v a

@[simp] theorem payoff_abstain (P : Problem n) (v : ℝ) : P.payoff v (abstain n) = 0 := by
  unfold payoff
  rw [P.abstention]
  unfold CountLaw.utility
  rw [FiniteLaw.expect_dirac]
  exact userPayoff_zero v 0 P.g P.A.charge P.G.charge P.A.zero P.G.zero

theorem payoff_affine (P : Problem n) (v w : ℝ) (a : Game.JointAction n) :
    P.payoff w a = P.payoff v a + (w - v) * (P.outcome a).success := by
  unfold payoff
  rw [CountLaw.utility_eq, CountLaw.utility_eq]
  ring

theorem payoff_upper (P : Problem n) (v : ℝ) (a : Game.JointAction n) :
    P.payoff v a ≤ max (v - P.g) 0 :=
  (P.outcome a).utility_le_positive_part v a.bid P.g P.A P.G a.bid_nonneg P.g_nonneg

theorem payoff_range_nonempty (P : Problem n) (v : ℝ) : (Set.range (P.payoff v)).Nonempty :=
  ⟨P.payoff v (abstain n), ⟨abstain n, rfl⟩⟩

theorem payoff_range_bounded (P : Problem n) (v : ℝ) : BddAbove (Set.range (P.payoff v)) := by
  refine ⟨max (v - P.g) 0, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact P.payoff_upper v a

theorem action_le_envelope (P : Problem n) (v : ℝ) (a : Game.JointAction n) :
    P.payoff v a ≤ P.envelope v :=
  le_csSup (P.payoff_range_bounded v) ⟨a, rfl⟩

theorem envelope_le (P : Problem n) (v M : ℝ) (h : ∀ a, P.payoff v a ≤ M) :
    P.envelope v ≤ M := by
  apply csSup_le (P.payoff_range_nonempty v)
  rintro _ ⟨a, rfl⟩
  exact h a

theorem envelope_nonneg (P : Problem n) (v : ℝ) : 0 ≤ P.envelope v := by
  simpa using P.action_le_envelope v (abstain n)

theorem envelope_upper (P : Problem n) (v : ℝ) : P.envelope v ≤ max (v - P.g) 0 :=
  P.envelope_le v _ (P.payoff_upper v)

theorem envelope_eq_zero_of_le_base (P : Problem n) (v : ℝ) (hv : v ≤ P.g) :
    P.envelope v = 0 := by
  have h := P.envelope_upper v
  rw [max_eq_right (sub_nonpos.mpr hv)] at h
  exact le_antisymm h (P.envelope_nonneg v)

@[simp] theorem envelope_at_base (P : Problem n) : P.envelope P.g = 0 :=
  P.envelope_eq_zero_of_le_base P.g le_rfl

theorem bestResponse_iff_attains (P : Problem n) (v : ℝ) (a : Game.JointAction n) :
    P.BestResponse v a ↔ P.payoff v a = P.envelope v := by
  constructor
  · intro h
    exact le_antisymm (P.action_le_envelope v a) (P.envelope_le v _ h)
  · intro h a'
    rw [h]
    exact P.action_le_envelope v a'

theorem supporting_line (P : Problem n) (v : ℝ) (a : Game.JointAction n)
    (ha : P.BestResponse v a) (w : ℝ) :
    P.envelope v + (w - v) * (P.outcome a).success ≤ P.envelope w := by
  have h := P.action_le_envelope w a
  rw [P.payoff_affine v w a, (P.bestResponse_iff_attains v a).mp ha] at h
  exact h

theorem success_order (P : Problem n) (v w : ℝ) (hvw : v < w)
    (a b : Game.JointAction n) (ha : P.BestResponse v a) (hb : P.BestResponse w b) :
    (P.outcome a).success ≤ (P.outcome b).success := by
  have h1 := P.supporting_line v a ha w
  have h2 := P.supporting_line w b hb v
  by_contra h
  have hS : (P.outcome b).success < (P.outcome a).success := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr hS)
  nlinarith

theorem envelope_monotone (P : Problem n) : Monotone P.envelope := by
  intro v w hvw
  apply P.envelope_le
  intro a
  have h := P.action_le_envelope w a
  rw [P.payoff_affine v w a] at h
  have hp := mul_nonneg (sub_nonneg.mpr hvw) (P.outcome a).success_nonneg
  linarith

theorem envelope_increment_le (P : Problem n) (v w : ℝ) (hvw : v ≤ w) :
    P.envelope w ≤ P.envelope v + (w - v) := by
  apply P.envelope_le
  intro a
  rw [P.payoff_affine v w a]
  have h := P.action_le_envelope v a
  have hS := (P.outcome a).success_le_one
  have hp : (w - v) * (P.outcome a).success ≤ w - v := by
    nlinarith
  linarith

theorem envelope_lipschitz_inequality (P : Problem n) (v w : ℝ) :
    |P.envelope v - P.envelope w| ≤ |v - w| := by
  by_cases h : v ≤ w
  · have hm := P.envelope_monotone h
    have hi := P.envelope_increment_le v w h
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · have hwv : w ≤ v := le_of_not_ge h
    have hm := P.envelope_monotone hwv
    have hi := P.envelope_increment_le w v hwv
    rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hwv)]
    linarith

theorem envelope_convex_combination (P : Problem n) (v w a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    P.envelope (a * v + b * w) ≤ a * P.envelope v + b * P.envelope w := by
  apply P.envelope_le
  intro act
  have he : P.payoff (a * v + b * w) act = a * P.payoff v act + b * P.payoff w act := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    unfold payoff
    rw [CountLaw.utility_eq, CountLaw.utility_eq, CountLaw.utility_eq]
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (P.action_le_envelope v act) ha)
    (mul_le_mul_of_nonneg_left (P.action_le_envelope w act) hb)

theorem envelope_convex (P : Problem n) : ConvexOn ℝ Set.univ P.envelope := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [smul_eq_mul] using P.envelope_convex_combination x y a b ha hb hab

theorem bestResponse_secants (P : Problem n) (v h : ℝ) (hh : 0 < h)
    (a : Game.JointAction n) (ha : P.BestResponse v a) :
    (P.envelope v - P.envelope (v - h)) / h ≤ (P.outcome a).success ∧
      (P.outcome a).success ≤ (P.envelope (v + h) - P.envelope v) / h := by
  have hl := P.supporting_line v a ha (v - h)
  have hu := P.supporting_line v a ha (v + h)
  constructor
  · apply (div_le_iff₀ hh).mpr
    nlinarith
  · apply (le_div_iff₀ hh).mpr
    nlinarith

theorem bestResponse_nonpositive (P : Problem n) (v : ℝ) (hv : v ≤ P.g)
    (a : Game.JointAction n) (ha : P.BestResponse v a) : P.payoff v a = 0 := by
  rw [(P.bestResponse_iff_attains v a).mp ha, P.envelope_eq_zero_of_le_base v hv]

noncomputable def ofBoundedCounts {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (K : Game.JointAction n → Ω → Fin (n + 1))
    (hK : ∀ a, Measurable (K a))
    (hbound : ∀ a ω, (K a ω).val ≤ a.routeCount) : Problem n where
  A := A
  G := G
  g := g
  g_nonneg := hg
  outcome a := CountLaw.ofMeasure μ (K a) (hK a)
  abstention := by
    have hz : ∀ ω, K (abstain n) ω = 0 := by
      intro ω
      apply Fin.ext
      have h := hbound (abstain n) ω
      change (K (abstain n) ω).val ≤ 0 at h
      simpa using Nat.eq_zero_of_le_zero h
    apply FiniteLaw.ext
    intro r
    simp [CountLaw.ofMeasure, FiniteLaw.dirac, hz, eq_comm]

noncomputable def ofLocalExperiment {m c : ℕ} {Ω Seed : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (background : Ω → Game.Realization m n) (i : Fin m)
    (R : Game.JointAction n → Ω → Finset (Fin n))
    (hR : ∀ a ω, (R a ω).card = a.routeCount)
    (policy : Fin n → Game.LocalPolicy m c Seed) (seeds : Ω → Fin n → Seed)
    (hMeas : ∀ a, Measurable (fun ω => Game.boundedCount
      (Game.deviate (background ω) i a.bid a.bid_nonneg (R a ω)) policy (seeds ω) i)) : Problem n :=
  ofBoundedCounts μ A G g hg
    (fun a ω => Game.boundedCount
      (Game.deviate (background ω) i a.bid a.bid_nonneg (R a ω)) policy (seeds ω) i)
    hMeas (by
      intro a ω
      have h := Game.inclusionCount_le_chosen
        (Game.deviate (background ω) i a.bid a.bid_nonneg (R a ω)) policy (seeds ω) i
      simpa [Game.boundedCount, Game.deviate, hR a ω] using h)

end Problem
end Interim
end FCAppendix
