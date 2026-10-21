import FCAppendix.Affine.Uniform07Finishing.Early.NativeRadius
import FCAppendix.Affine.Uniform07Finishing.Native.UpperBoundary
import FCAppendix.Affine.Uniform07Finishing.Early.Scalar
import FCAppendix.Affine.LowBody.ArrivalUnderflow
import FCAppendix.Probability.FiniteHoeffding

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope
open scoped BigOperators

theorem source_capacity_le_population (m : ℕ) : Uniform07.capacity m ≤ m := by
  have hf : (Uniform07.capacity m : ℝ) ≤ Uniform07.rho*(m : ℝ) := by
    rw [Early.capacity_floor_rho]
    exact Nat.floor_le (by norm_num [Uniform07.rho])
  have hle : (Uniform07.capacity m : ℝ) ≤ (m : ℝ) := by
    norm_num [Uniform07.rho] at hf
    nlinarith [Nat.cast_nonneg (α:=ℝ) m]
  exact_mod_cast hle

theorem source_capacity_lt_population (m : ℕ) (hm : 0 < m) :
    Uniform07.capacity m < m := by
  have hf : (Uniform07.capacity m : ℝ) ≤ Uniform07.rho*(m : ℝ) := by
    rw [Early.capacity_floor_rho]
    exact Nat.floor_le (by norm_num [Uniform07.rho])
  have hlt : (Uniform07.capacity m : ℝ) < (m : ℝ) := by
    have hp : (0 : ℝ) < m := by exact_mod_cast hm
    norm_num [Uniform07.rho] at hf
    nlinarith
  exact_mod_cast hlt

theorem source_capacity_le_rivals_add_one (m : ℕ) :
    Uniform07.capacity m ≤ m-1+1 := by
  have h := source_capacity_le_population m
  omega

theorem source_capacity_density_with_rivals :
    Tendsto (fun m : ℕ => (Uniform07.capacity m : ℝ)/(((m-1 : ℕ) : ℝ)+1))
      atTop (𝓝 Uniform07.rho) := by
  apply Early.capacity_density_limit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [Nat.cast_sub hm]
  norm_num

theorem source_capacity_rival_density :
    Tendsto (fun m : ℕ => (Uniform07.capacity m : ℝ)/((m-1 : ℕ) : ℝ))
      atTop (𝓝 Uniform07.rho) :=
  capacity_rival_density (fun m : ℕ => m-1) Uniform07.capacity
    (tendsto_sub_atTop_nat 1) source_capacity_density_with_rivals

theorem source_upper_rank_tendsto_one_at (i : Uniform07.Row) {v : ℝ}
    (hv : Uniform07.cutoff i ≤ v) :
    Tendsto (fun m => source_upper_rank i m v) atTop (𝓝 1) := by
  have htail : contactTail (upperValueMeasure i) 2 v ≤
      contactTail (upperValueMeasure i) 2 (Uniform07.cutoff i) := by
    unfold contactTail
    exact div_le_div_of_nonneg_right
      (measureReal_mono (Ioi_subset_Ioi hv)) (by norm_num)
  exact Hybrid.rank_floor_tendsto_one (upperValueMeasure i)
    (upperValueMeasure_mass_le_one i) (fun m : ℕ => m-1) Uniform07.capacity
    (tendsto_sub_atTop_nat 1) source_capacity_le_rivals_add_one
    Uniform07.rho v source_capacity_density_with_rivals
    (htail.trans_lt (uniform_upper_subcritical i))

theorem source_upper_rank_tendsto_one (i : Uniform07.Row) :
    Tendsto (fun m => source_upper_rank i m (Uniform07.cutoff i)) atTop (𝓝 1) :=
  source_upper_rank_tendsto_one_at i le_rfl

def sourceUpperFailure (i : Uniform07.Row) (m : ℕ) : ℝ :=
  1-source_upper_rank i m (Uniform07.cutoff i)

theorem sourceUpperFailure_nonneg (i : Uniform07.Row) (m : ℕ) :
    0 ≤ sourceUpperFailure i m :=
  sub_nonneg.mpr (source_upper_rank_bounds i m _).2

theorem sourceUpperFailure_tendsto_zero (i : Uniform07.Row) :
    Tendsto (sourceUpperFailure i) atTop (𝓝 0) := by
  convert! (tendsto_const_nhds (x := (1 : ℝ))).sub (source_upper_rank_tendsto_one i) using 1;
    simp only [sub_self]

theorem binomial_upper_hoeffding (N c : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hgap : (N : ℝ)*(p+ε) ≤ c) :
    (IndependentCounts.binomial N p hp0 hp1).prob (fun r => c ≤ r.val) ≤
      Real.exp (-2*(N : ℝ)*ε^2) := by
  let μ := IndependentCounts.bernoulli p hp0 hp1
  let E : Bool → Prop := fun b => b = true
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have he : μ.prob E = p := by
    rw [FiniteLaw.prob_eq_expect]
    change (IndependentCounts.bernoulli p hp0 hp1).expect (fun b => if b then 1 else 0) = p
    rw [IndependentCounts.expect_bernoulli]
    norm_num
  have hX : ∀ b : Bool, X b ∈ Icc (0 : ℝ) 1 := by
    intro b; cases b <;> norm_num [X]
  have hm : μ.expect X = p := by
    change (IndependentCounts.bernoulli p hp0 hp1).expect (fun b => if b then 1 else 0) = p
    rw [IndependentCounts.expect_bernoulli]
    norm_num
  have hsum (ω : Fin N → Bool) :
      ∑ j, X (ω j) = (Affine.LowBody.hitCount E ω : ℝ) := by
    simp [X, E, Affine.LowBody.hitCount]
  have hid := Affine.LowBody.expect_hitCount_binomial μ E N
    (fun k => if c ≤ k then (1 : ℝ) else 0)
  simp only [he] at hid
  have hid' : (CommonList.iid μ N).prob (fun ω => c ≤ Affine.LowBody.hitCount E ω) =
      (IndependentCounts.binomial N p hp0 hp1).prob (fun r => c ≤ r.val) := by
    simp_rw [FiniteLaw.prob_eq_expect]
    convert! hid using 1
  rw [← hid']
  have hsub : ∀ ω : Fin N → Bool, c ≤ Affine.LowBody.hitCount E ω →
      (N : ℝ)*(μ.expect X+ε) ≤ ∑ j, X (ω j) := by
    intro ω hω
    rw [hm, hsum]
    exact hgap.trans (by exact_mod_cast hω)
  exact ((CommonList.iid μ N).prob_mono hsub).trans
    (FiniteCramer.iid_upper_hoeffding μ X hX N hε)

def sourceUpperSlack (i : Uniform07.Row) : ℝ :=
  (Uniform07.rho-contactTail (upperValueMeasure i) 2 (Uniform07.cutoff i))/2

theorem sourceUpperSlack_pos (i : Uniform07.Row) : 0 < sourceUpperSlack i :=
  div_pos (sub_pos.mpr (uniform_upper_subcritical i)) (by norm_num)

theorem sourceUpperSlack_literal (i : Uniform07.Row) :
    sourceUpperSlack i = (Uniform07.cutoff i-Uniform07.delta)/4 := by
  rw [sourceUpperSlack, uniform_upper_contactTail i
    ⟨le_rfl, (Uniform07.cutoff_lt_one i).le⟩]
  norm_num [Uniform07.rho, Uniform07.delta]
  ring

theorem source_upper_failure_exponential (i : Uniform07.Row) :
    ∀ᶠ m in atTop,
      sourceUpperFailure i m ≤
        Real.exp (-2*((m-1 : ℕ) : ℝ)*(sourceUpperSlack i)^2) := by
  let p := contactTail (upperValueMeasure i) 2 (Uniform07.cutoff i)
  have hp := contactTail_bounds (upperValueMeasure i) (by norm_num : 2 ≤ (2 : ℕ))
    (upperValueMeasure_mass_le_one i) (Uniform07.cutoff i)
  have hbelow : p+sourceUpperSlack i < Uniform07.rho := by
    dsimp [p, sourceUpperSlack]
    linarith [uniform_upper_subcritical i]
  have he := source_capacity_rival_density.eventually (eventually_gt_nhds hbelow)
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with m hm hm2
  have hN : (0 : ℝ) < ((m-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hgap : (((m-1 : ℕ) : ℝ))*(p+sourceUpperSlack i) ≤ Uniform07.capacity m := by
    have h := (lt_div_iff₀ hN).mp hm
    nlinarith
  have hb := binomial_upper_hoeffding (m-1) (Uniform07.capacity m) p hp.1 hp.2.le
    (sourceUpperSlack_pos i).le hgap
  have hc := (IndependentCounts.binomial (m-1) p hp.1 hp.2.le).prob_compl
    (fun r => r.val < Uniform07.capacity m)
  simp only [not_lt] at hc
  change 1-rankSuccess (m-1) (Uniform07.capacity m) p ≤ _
  rw [rankSuccess_eq_prob _ _ ⟨hp.1, hp.2.le⟩, ← hc]
  exact hb

theorem source_upper_rank_monotone_eventually (i : Uniform07.Row) :
    ∀ᶠ m in atTop, Monotone (source_upper_rank i m) := by
  filter_upwards [Early.capacity_tendsto.eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℕ)] with m hc hm
  have hcm := source_capacity_lt_population m (by omega)
  have he : m-2+1=m-1 := by omega
  have h := rank_monotone (upperValueMeasure i) (r := m-2) hc
    (by omega) (by norm_num : 2 ≤ (2 : ℕ)) (upperValueMeasure_mass_le_one i)
  have heq : source_upper_rank i m = rank (upperValueMeasure i) (m-1) (Uniform07.capacity m) 2 := by
    funext v
    rfl
  rw [heq]
  simpa only [he] using h

theorem upper_failure_uniform_bound_eventually (i : Uniform07.Row) :
    ∀ᶠ m in atTop, ∀ v : ℝ, Uniform07.cutoff i ≤ v →
      0 ≤ 1-source_upper_rank i m v ∧
      1-source_upper_rank i m v ≤
        Real.exp (-2*((m-1 : ℕ) : ℝ)*(sourceUpperSlack i)^2) := by
  filter_upwards [source_upper_rank_monotone_eventually i,
    source_upper_failure_exponential i] with m hmono he
  intro v hv
  refine ⟨sub_nonneg.mpr (source_upper_rank_bounds i m v).2, ?_⟩
  exact (sub_le_sub_left (hmono hv) 1).trans he

variable (i : Uniform07.Row) (u : ℕ → ℝ)
variable (hU : Tendsto u atTop
  (𝓝 ((Uniform07.cutoff i-Uniform07.entry i)^2/Uniform07.cutoff i)))

include hU in
theorem source_endogenous_floor_tendsto :
    Tendsto (endogenousUpperFloor i u) atTop (𝓝 (Uniform07.limitingFloor i)) :=
  endogenous_floor_tendsto i u hU (source_upper_rank_tendsto_one i)

include hU in
theorem source_endogenous_floor_guards :
    ∀ᶠ m in atTop, 0 < Early.bidCap i ∧
      Early.bidCap i < endogenousUpperFloor i u m ∧
      endogenousUpperFloor i u m < Uniform07.cutoff i := by
  have hs := Early.upper_floor_interface i
  have hR := source_endogenous_floor_tendsto i u hU
  filter_upwards [hR.eventually (eventually_gt_nhds hs.2.2.1),
    hR.eventually (eventually_lt_nhds hs.2.2.2.1)] with m hlo hhi
  exact ⟨hs.2.1, hlo, hhi⟩

include hU in

theorem source_endogenous_root_sampling_margin :
    ∀ᶠ m in atTop,
      Uniform07.kappa i * endogenousUpperFloor i u m + Early.nativeRadius i <
        (27/50 : ℝ) * Uniform07.cutoff i := by
  have h := ((source_endogenous_floor_tendsto i u hU).const_mul
    (Uniform07.kappa i)).add_const (Early.nativeRadius i)
  exact h.eventually (eventually_lt_nhds
    (Early.kappa_limitingFloor_add_nativeRadius_lt_root_lower i))

def sourceMovingUpperError (i : Uniform07.Row) (u : ℕ → ℝ) (m : ℕ) : ℝ :=
  error (source_upper_rank i m) (Uniform07.cutoff i) (endogenousUpperFloor i u m)

include hU in
theorem source_moving_upper_error_bounds :
    ∀ᶠ m in atTop, 0 ≤ sourceMovingUpperError i u m ∧
      sourceMovingUpperError i u m ≤
        (1-endogenousUpperFloor i u m)*sourceUpperFailure i m := by
  have hs : ∀ᵐ v ∂upperValueMeasure i, v ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with v hv
    exact hv.2
  filter_upwards [source_endogenous_floor_guards i u hU,
    Early.capacity_tendsto.eventually_ge_atTop 1,
    eventually_ge_atTop (2 : ℕ)] with m hfloor hc hm
  have hcm := source_capacity_lt_population m (by omega)
  have he : m-2+1=m-1 := by omega
  refine ⟨error_nonneg hfloor.2.2.le
    (fun v => (source_upper_rank_bounds i m v).2), ?_⟩
  have h := Hybrid.bounded_rank_error_le (upperValueMeasure i) (m-2)
    (Uniform07.capacity m) hc (by omega) (upperValueMeasure_mass_le_one i)
    (Uniform07.cutoff i) (endogenousUpperFloor i u m) 1
    (Uniform07.cutoff_lt_one i).le hs
  have heq : source_upper_rank i m = rank (upperValueMeasure i) (m-1) (Uniform07.capacity m) 2 := by
    funext v
    rfl
  change error (source_upper_rank i m) _ _ ≤ (1-endogenousUpperFloor i u m)*(1-source_upper_rank i m _)
  rw [heq]
  simpa only [he] using h

include hU in
theorem source_moving_upper_error_tendsto_zero :
    Tendsto (sourceMovingUpperError i u) atTop (𝓝 0) := by
  have hR := source_endogenous_floor_tendsto i u hU
  have hB : Tendsto (fun m =>
      (1-endogenousUpperFloor i u m)*sourceUpperFailure i m) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hR).mul
        (sourceUpperFailure_tendsto_zero i)
  exact squeeze_zero' ((source_moving_upper_error_bounds i u hU).mono (fun _ h => h.1))
    ((source_moving_upper_error_bounds i u hU).mono (fun _ h => h.2)) hB

include hU in
theorem source_moving_upper_error_exponential :
    ∀ᶠ m in atTop, 0 ≤ sourceMovingUpperError i u m ∧
      sourceMovingUpperError i u m ≤
        Real.exp (-2*((m-1 : ℕ) : ℝ)*(sourceUpperSlack i)^2) := by
  filter_upwards [source_moving_upper_error_bounds i u hU,
    source_endogenous_floor_guards i u hU,
    source_upper_failure_exponential i] with m herror hfloor hexp
  refine ⟨herror.1, herror.2.trans (le_trans ?_ hexp)⟩
  have hR0 := hfloor.1.trans hfloor.2.1
  exact mul_le_of_le_one_left (sourceUpperFailure_nonneg i m) (by linarith)

include hU in

theorem source_eventual_hidden_upper_guard :
    ∀ᶠ m in atTop, sourceMovingUpperError i u m <
      Uniform07.eta i*endogenousUpperFloor i u m*(1-2*sourceUpperFailure i m) := by
  have hs := Early.upper_floor_interface i
  have hR0 : 0 < Uniform07.limitingFloor i := hs.2.1.trans hs.2.2.1
  exact eventually_hidden_guard_moving_floor
    (source_moving_upper_error_tendsto_zero i u hU) (sourceUpperFailure_tendsto_zero i)
    (source_endogenous_floor_tendsto i u hU) (Uniform07.eta_pos i) hR0

end FCAppendix.Affine.Uniform07Finishing
