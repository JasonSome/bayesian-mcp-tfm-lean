import FCAppendix.Finite.EnvelopeIntegral
import FCAppendix.Finite.NearPPILimit

noncomputable section
namespace FCAppendix.CommonReserve
open MeasureTheory Filter Topology

structure InterimProblem (Action : Type*) where
  g : ℝ
  r : ℝ
  success : Action → ℝ
  cost : Action → ℝ
  success_nonneg : ∀ a, 0 ≤ success a
  success_le_one : ∀ a, success a ≤ 1
  cost_floor : ∀ a, (g + r) * success a ≤ cost a
  zero : Action
  success_zero : success zero = 0
  cost_zero : cost zero = 0

namespace InterimProblem
variable {Action : Type*}

def payoff (P : InterimProblem Action) (v : ℝ) (a : Action) : ℝ :=
  v * P.success a - P.cost a

def envelope (P : InterimProblem Action) (v : ℝ) : ℝ := sSup (Set.range (P.payoff v))

def BestResponse (P : InterimProblem Action) (v : ℝ) (a : Action) : Prop :=
  ∀ a', P.payoff v a' ≤ P.payoff v a

@[simp] theorem payoff_abstain (P : InterimProblem Action) (v : ℝ) :
    P.payoff v P.zero = 0 := by simp [payoff, P.success_zero, P.cost_zero]

theorem payoff_affine (P : InterimProblem Action) (v w : ℝ) (a : Action) :
    P.payoff w a = P.payoff v a + (w - v) * P.success a := by unfold payoff; ring

theorem payoff_upper (P : InterimProblem Action) (v : ℝ) (a : Action) :
    P.payoff v a ≤ max (v - (P.g + P.r)) 0 := by
  have hc := P.cost_floor a
  have hs0 := P.success_nonneg a
  have hs1 := P.success_le_one a
  unfold payoff
  by_cases h : 0 ≤ v - (P.g + P.r)
  · rw [max_eq_left h]
    nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith

theorem payoff_range_nonempty (P : InterimProblem Action) (v : ℝ) : (Set.range (P.payoff v)).Nonempty :=
  ⟨P.payoff v P.zero, ⟨P.zero, rfl⟩⟩

theorem payoff_range_bounded (P : InterimProblem Action) (v : ℝ) : BddAbove (Set.range (P.payoff v)) := by
  refine ⟨max (v - (P.g + P.r)) 0, ?_⟩
  rintro _ ⟨a, rfl⟩
  exact P.payoff_upper v a

theorem action_le_envelope (P : InterimProblem Action) (v : ℝ) (a : Action) :
    P.payoff v a ≤ P.envelope v :=
  le_csSup (P.payoff_range_bounded v) ⟨a, rfl⟩

theorem envelope_le (P : InterimProblem Action) (v M : ℝ) (h : ∀ a, P.payoff v a ≤ M) :
    P.envelope v ≤ M := by
  apply csSup_le (P.payoff_range_nonempty v)
  rintro _ ⟨a, rfl⟩
  exact h a

theorem envelope_nonneg (P : InterimProblem Action) (v : ℝ) : 0 ≤ P.envelope v := by
  simpa using P.action_le_envelope v P.zero

theorem envelope_upper (P : InterimProblem Action) (v : ℝ) : P.envelope v ≤ max (v - (P.g + P.r)) 0 :=
  P.envelope_le v _ (P.payoff_upper v)

theorem envelope_eq_zero_of_le_base (P : InterimProblem Action) (v : ℝ) (hv : v ≤ (P.g + P.r)) :
    P.envelope v = 0 := by
  have h := P.envelope_upper v
  rw [max_eq_right (sub_nonpos.mpr hv)] at h
  exact le_antisymm h (P.envelope_nonneg v)

@[simp] theorem envelope_at_base (P : InterimProblem Action) : P.envelope (P.g + P.r) = 0 :=
  P.envelope_eq_zero_of_le_base (P.g + P.r) le_rfl

theorem bestResponse_iff_attains (P : InterimProblem Action) (v : ℝ) (a : Action) :
    P.BestResponse v a ↔ P.payoff v a = P.envelope v := by
  constructor
  · intro h
    exact le_antisymm (P.action_le_envelope v a) (P.envelope_le v _ h)
  · intro h a'
    rw [h]
    exact P.action_le_envelope v a'

theorem supporting_line (P : InterimProblem Action) (v : ℝ) (a : Action)
    (ha : P.BestResponse v a) (w : ℝ) :
    P.envelope v + (w - v) * P.success a ≤ P.envelope w := by
  have h := P.action_le_envelope w a
  rw [P.payoff_affine v w a, (P.bestResponse_iff_attains v a).mp ha] at h
  exact h

theorem success_order (P : InterimProblem Action) (v w : ℝ) (hvw : v < w)
    (a b : Action) (ha : P.BestResponse v a) (hb : P.BestResponse w b) :
    P.success a ≤ P.success b := by
  have h1 := P.supporting_line v a ha w
  have h2 := P.supporting_line w b hb v
  by_contra h
  have hS : P.success b < P.success a := lt_of_not_ge h
  have hp := mul_pos (sub_pos.mpr hvw) (sub_pos.mpr hS)
  nlinarith

theorem envelope_monotone (P : InterimProblem Action) : Monotone P.envelope := by
  intro v w hvw
  apply P.envelope_le
  intro a
  have h := P.action_le_envelope w a
  rw [P.payoff_affine v w a] at h
  have hp := mul_nonneg (sub_nonneg.mpr hvw) (P.success_nonneg a)
  linarith

theorem envelope_increment_le (P : InterimProblem Action) (v w : ℝ) (hvw : v ≤ w) :
    P.envelope w ≤ P.envelope v + (w - v) := by
  apply P.envelope_le
  intro a
  rw [P.payoff_affine v w a]
  have h := P.action_le_envelope v a
  have hS := P.success_le_one a
  have hp : (w - v) * P.success a ≤ w - v := by
    nlinarith
  linarith

theorem envelope_lipschitz_inequality (P : InterimProblem Action) (v w : ℝ) :
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

theorem envelope_convex_combination (P : InterimProblem Action) (v w a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    P.envelope (a * v + b * w) ≤ a * P.envelope v + b * P.envelope w := by
  apply P.envelope_le
  intro act
  have he : P.payoff (a * v + b * w) act = a * P.payoff v act + b * P.payoff w act := by
    have hb' : b = 1 - a := by linarith
    rw [hb']
    unfold payoff
    ring
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left (P.action_le_envelope v act) ha)
    (mul_le_mul_of_nonneg_left (P.action_le_envelope w act) hb)

theorem envelope_convex (P : InterimProblem Action) : ConvexOn ℝ Set.univ P.envelope := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simpa only [smul_eq_mul] using P.envelope_convex_combination x y a b ha hb hab

theorem bestResponse_secants (P : InterimProblem Action) (v h : ℝ) (hh : 0 < h)
    (a : Action) (ha : P.BestResponse v a) :
    (P.envelope v - P.envelope (v - h)) / h ≤ P.success a ∧
      P.success a ≤ (P.envelope (v + h) - P.envelope v) / h := by
  have hl := P.supporting_line v a ha (v - h)
  have hu := P.supporting_line v a ha (v + h)
  constructor
  · apply (div_le_iff₀ hh).mpr
    nlinarith
  · apply (le_div_iff₀ hh).mpr
    nlinarith

theorem bestResponse_nonpositive (P : InterimProblem Action) (v : ℝ) (hv : v ≤ (P.g + P.r))
    (a : Action) (ha : P.BestResponse v a) : P.payoff v a = 0 := by
  rw [(P.bestResponse_iff_attains v a).mp ha, P.envelope_eq_zero_of_le_base v hv]

theorem envelope_integral (P : InterimProblem Action) {x y : ℝ} (hxy : x ≤ y)
    (a : ℝ → Action) (ha : ∀ v ∈ Set.Icc x y, P.BestResponse v (a v)) :
    P.envelope y - P.envelope x = ∫ v in x..y, P.success (a v) := by
  exact Subgradient.sub_eq_integral hxy (fun v hv w _ => P.supporting_line v (a v) (ha v hv) w)

theorem bestResponse_success_tendsto (P : ℕ → InterimProblem Action)
    (c v : ℝ) (hv : v ≠ c) (a : ℕ → Action)
    (ha : ∀ m, (P m).BestResponse v (a m))
    (hU : ∀ w, Tendsto (fun m => (P m).envelope w) atTop (𝓝 (max (w - c) 0))) :
    Tendsto (fun m => (P m).success (a m)) atTop
      (𝓝 (NearPPI.cutoffSuccess (v - c))) := by
  let w := (v + c) / 2
  rcases lt_or_gt_of_ne hv with hvc | hcv
  · have hwc : w < c := by dsimp [w]; linarith
    have hvw : 0 < w - v := by dsimp [w]; linarith
    have hzero : Tendsto (fun m => ((P m).envelope w - (P m).envelope v) / (w - v))
        atTop (𝓝 0) := by
      have h := (hU w |>.sub (hU v)).div_const (w - v)
      simpa [max_eq_right (sub_nonpos.mpr hwc.le),
        max_eq_right (sub_nonpos.mpr hvc.le)] using h
    have hS : Tendsto (fun m => (P m).success (a m)) atTop (𝓝 0) := by
      apply squeeze_zero (fun m => ((P m).success_nonneg (a m))) _ hzero
      intro m
      apply (le_div_iff₀ hvw).mpr
      have h := (P m).supporting_line v (a m) (ha m) w
      nlinarith
    simpa [NearPPI.cutoffSuccess, not_lt.mpr (sub_nonpos.mpr hvc.le)] using hS
  · have hcw : c < w := by dsimp [w]; linarith
    have hwv : 0 < v - w := by dsimp [w]; linarith
    have hone : Tendsto (fun m => ((P m).envelope v - (P m).envelope w) / (v - w))
        atTop (𝓝 1) := by
      have h := (hU v |>.sub (hU w)).div_const (v - w)
      simpa [max_eq_left (sub_nonneg.mpr hcw.le),
        max_eq_left (sub_nonneg.mpr hcv.le), div_self hwv.ne'] using h
    have herr : Tendsto (fun m => 1 - (P m).success (a m)) atTop (𝓝 0) := by
      apply squeeze_zero
        (fun m => sub_nonneg.mpr ((P m).success_le_one (a m)))
        (g := fun m => 1 - ((P m).envelope v - (P m).envelope w) / (v - w))
      · intro m
        have h := (P m).supporting_line v (a m) (ha m) w
        have hs : ((P m).envelope v - (P m).envelope w) / (v - w) ≤
            (P m).success (a m) := by
          apply (div_le_iff₀ hwv).mpr
          nlinarith
        linarith
      · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hone
    have hS := (tendsto_const_nhds (x := (1 : ℝ))).sub herr
    simpa [NearPPI.cutoffSuccess, sub_pos.mpr hcv] using hS

theorem envelope_uniformOn_compact (P : ℕ → InterimProblem Action) (u : ℝ → ℝ)
    (hU : ∀ v, Tendsto (fun m => (P m).envelope v) atTop (𝓝 (u v)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun m => (P m).envelope) u atTop K := by
  apply NearPPI.uniformOn_compact_of_lipschitz 1 _ hU hK
  intro m
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (P m).envelope_lipschitz_inequality v w

end InterimProblem
end FCAppendix.CommonReserve
