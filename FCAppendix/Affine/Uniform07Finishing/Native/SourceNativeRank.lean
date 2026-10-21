import FCAppendix.Affine.Uniform07Finishing.Native.SourceNativeGame
import FCAppendix.Affine.Uniform07Finishing.Native.CompleteSourceGame
import FCAppendix.Affine.Uniform07Finishing.Native.StrictUpperRank
import FCAppendix.Affine.Uniform07Finishing.Native.NativeConditional
import FCAppendix.Affine.Hybrid.PopulationUpper
import FCAppendix.Affine.Hybrid.UpperNativeEnvelope
import FCAppendix.Affine.Hybrid.UpperNativeRoutes

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope
open StrictNative

theorem source_upper_rank_monotone (row : Uniform07.Row) (m : ℕ)
    (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m) :
    Monotone (source_upper_rank row m) := by
  have hcm := source_capacity_lt_population m (by omega)
  have he : m-2+1=m-1 := by omega
  have hh := rank_monotone (upperValueMeasure row) (r := m-2) hc
    (by omega) (by norm_num : 2 ≤ (2 : ℕ)) (upperValueMeasure_mass_le_one row)
  change Monotone (rank (upperValueMeasure row) (m-1) (Uniform07.capacity m) 2)
  simpa only [he] using hh

theorem source_upper_value_support (row : Uniform07.Row) :
    ∀ᵐ v ∂upperValueMeasure row, Uniform07.cutoff row ≤ v ∧ v ≤ 1 :=
  ae_restrict_mem (μ := volume) measurableSet_Icc

section Actual
variable {m : ℕ} [Nonempty (Fin m)]
variable (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row) (hΛ : 0 < Λ)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (α : ClassifiedContext m → unitInterval) (hα : Measurable α)

local notation "Γ" => sourceNativeGame row hc R Λ hΛ PL α hα
local notation "C" => sourceWeightedContext row hc R Λ hΛ PL α hα
local notation "q" => source_upper_rank row m
local notation "b" => sourceUpperBid row m R
local notation "t" => Uniform07.cutoff row
local notation "μ" => upperValueMeasure row

include hm hR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_bid_measure (B : Set ℝ)
    (hB : B ⊆ Ioi (Early.bidCap row)) :
    ((Γ).F ⊗ₘ (Γ).σ) {x | x.2.bid ∈ B} =
      ENNReal.ofReal (1-t) *
        (sourceUpperJoint row m hc R : Measure (ℝ × JointAction 2))
          {x | x.2.bid ∈ B} := by
  rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα]
  change Hybrid.populationJoint t 0 (1-t) PL PL (sourceUpperJoint row m hc R)
    {x | x.2.bid ∈ B} = _
  exact Hybrid.population_measure_above (Early.bidCap row) t 0 (1-t)
    PL PL (sourceUpperJoint row m hc R)
    (hLroute.mono (fun _ hx => hx.1)) (hLroute.mono (fun _ hx => hx.1)) B hB

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_visible_atomless :
    ∀ (j : Fin 2) (y : ℝ), R ≤ y →
      userLaw Γ {d | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = y} = 0 := by
  have hzero : ∀ y : ℝ, Early.bidCap row < y →
      ((Γ).F ⊗ₘ (Γ).σ) {x | x.2.bid = y} = 0 := by
    intro y hy
    have he := sourceNativeGame_upper_bid_measure row hm hc hR hRt hΛ
      PL hLvalue hLroute α hα {y}
      (fun z hz => by rw [mem_singleton_iff.mp hz]; exact hy)
    simpa only [mem_singleton_iff,
      (source_upper_joint_properties row m hm hc hR hRt).2.2 y, mul_zero] using he
  intro j y hy
  exact Hybrid.upper_visible_atomless_of_joint Γ (Early.bidCap row) hzero j y
    (hUR.trans_le hy)

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_alphaGt (j : Fin 2) (y : ℝ) (hy : R ≤ y) :
    alphaGt Γ j y = ((μ).map b).real (Ioi y) / 2 := by
  have hroute : ∀ᵐ x ∂(Γ).F ⊗ₘ (Γ).σ, y < x.2.bid → x.2.routeCount = 1 := by
    rw [sourceNativeGame_joint_law row hm hc hR hRt hΛ PL hLvalue hLroute α hα]
    filter_upwards [source_population_action_shape row m hm hc hR hUR hRt
      PL hLvalue hLroute] with x hx hxy
    rcases hx with hl | hh
    · exact (not_lt_of_ge (hl.1.trans (hUR.le.trans hy)) hxy).elim
    · exact hh.2
  rw [Hybrid.upper_alphaGt Γ j y hroute]
  have he := sourceNativeGame_upper_bid_measure row hm hc hR hRt hΛ
    PL hLvalue hLroute α hα (Ioi y) (fun _ hz => hUR.trans (hy.trans_lt hz))
  have hreal : ((Γ).F ⊗ₘ (Γ).σ).real {x | y < x.2.bid} =
      (1-t) * (sourceUpperJoint row m hc R : Measure (ℝ × JointAction 2)).real
        {x | y < x.2.bid} := by
    change (((Γ).F ⊗ₘ (Γ).σ) {x | x.2.bid ∈ Ioi y}).toReal = _
    rw [he, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Uniform07.cutoff_lt_one row).le)]
    rfl
  have hweighted := Hybrid.weighted_upper_bid_tail (sourceUpperValueLaw row)
    (sourceUpperJoint row m hc R) b
    (source_upper_joint_properties row m hm hc hR hRt).1 (1-t)
    (sub_nonneg.mpr (Uniform07.cutoff_lt_one row).le) y
  rw [sourceUpperValueLaw_weighted] at hweighted
  rw [hreal, ← hweighted]

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_mean_eq_bidRank (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    meanAcceptProb Γ i y = bidRank μ (m-1) (Uniform07.capacity m) 2 b y := by
  have hgame : (C).nativeGame Γ R = Γ := by rfl
  have hn := sourceNativeGame_upper_visible_atomless row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα
  have hr := (C).native_upper_meanAcceptProb Γ hR.le
    (by simpa only [hgame] using hn) i y hy
  rw [hgame, sourceNativeGame_upper_alphaGt row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα 0 y hy] at hr
  have hmass : ((μ).map b).real univ ≤ 1 := by
    rw [map_measureReal_apply (sourceUpperBid_measurable row m hc R) MeasurableSet.univ]
    simpa only [preimage_univ] using upperValueMeasure_mass_le_one row
  have hp := contactTail_bounds ((μ).map b) (by norm_num : 2 ≤ (2 : ℕ)) hmass y
  have hprob : ((μ).map b).real (Ioi y)/2 ∈ Icc (0 : ℝ) 1 := ⟨hp.1, hp.2.le⟩
  rw [hr, bidRank]
  simp only [Nat.cast_ofNat]
  rw [rankSuccess_eq_prob _ _ hprob,
    binomBelow_eq_prob _ _ (source_capacity_le_rivals_add_one m) _ hprob.1 hprob.2]

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_singleton_payoff (i : Fin m) (v : ℝ)
    (a : JointAction 2) (ha : a.routeCount = 1) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a =
      (v-a.bid) * bidRank μ (m-1) (Uniform07.capacity m) 2 b a.bid := by
  rw [singleton_payoff Γ (by norm_num : 0 < 2) i a ha,
    sourceNativeGame_upper_mean_eq_bidRank row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα i a.bid hb]
  change (v-0-a.bid)*_ = (v-a.bid)*_
  rw [sub_zero]

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_one_route_bound (i : Fin m) (v : ℝ)
    (a : JointAction 2) (ha : a.routeCount = 1) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a ≤ utility q t R v := by
  rw [sourceNativeGame_upper_singleton_payoff row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i v a ha hb]
  have hh := (source_upper_envelope row m hm hc hR hRt).one_route v a.bid hb
  simpa only [show m-2+1=m-1 by omega] using hh

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_mean_at_value (i : Fin m) (v : ℝ) (hv : t ≤ v) :
    meanAcceptProb Γ i (Hybrid.upperAction b v).bid = q v := by
  have H := source_upper_envelope row m hm hc hR hRt
  have hb := (H.bid_bounds v hv).1
  have hact : (Hybrid.upperAction b v).bid = b v := max_eq_left (hR.le.trans hb)
  rw [hact, sourceNativeGame_upper_mean_eq_bidRank row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i (b v) hb]
  letI : NullSingletonClass ((μ).map b) := H.atomless
  exact bidRank_at_report μ (sourceUpperBid_measurable row m hc R) hv
    (bid_monotoneOn (source_upper_rank_monotone row m hm hc) hRt.le
      (source_upper_rank_pos row m hc t))
    ((source_upper_value_support row).mono (fun _ hx => hx.1))
    (m-1) (Uniform07.capacity m) 2

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_attainment (i : Fin m) (v : ℝ) (hv : t ≤ v) :
    (problem Γ i).payoff v (Hybrid.upperAction b v) = utility q t R v := by
  have hb := ((source_upper_envelope row m hm hc hR hRt).bid_bounds v hv).1
  have hact : (Hybrid.upperAction b v).bid = b v := max_eq_left (hR.le.trans hb)
  rw [singleton_payoff Γ (by norm_num : 0 < 2) i (Hybrid.upperAction b v) rfl,
    sourceNativeGame_upper_mean_at_value row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα i v hv, hact]
  change (v-0-b v)*q v=utility q t R v
  rw [sub_zero, show b v=bid q t R v from rfl,
    report_payoff t R v v (source_upper_rank_pos row m hc v).ne']
  simp only [sub_self, zero_mul, add_zero]

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_mean_floor (i : Fin m) (y : ℝ) (hy : R ≤ y) :
    q t ≤ meanAcceptProb Γ i y := by
  rw [sourceNativeGame_upper_mean_eq_bidRank row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i y hy]
  have hcm := source_capacity_lt_population m (by omega)
  have hh := bidRank_floor_lower μ (r := m-2) hc (by omega)
    (by norm_num : 2 ≤ (2 : ℕ)) (upperValueMeasure_mass_le_one row) hRt
    ((source_upper_value_support row).mono (fun _ hx => hx.1)) hy
  rw [show m-2+1=m-1 by omega] at hh
  exact hh

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_singleton_below_boundary (i : Fin m) (v : ℝ)
    (hv : v ≤ t) (a : JointAction 2) (ha : a.routeCount = 1) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a ≤ (v-R)*q t := by
  rw [sourceNativeGame_upper_singleton_payoff row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i v a ha hb]
  have hcm := source_capacity_lt_population m (by omega)
  have hh := floor_contract_dominates_below μ (r := m-2) hc (by omega)
    (by norm_num : 2 ≤ (2 : ℕ)) (upperValueMeasure_mass_le_one row) hRt
    ((source_upper_value_support row).mono (fun _ hx => hx.1)) v a.bid hv hb
  rw [show m-2+1=m-1 by omega] at hh
  exact hh

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_upper_duplicates (i : Fin m) (a : JointAction 2)
    (ha : a.routeCount = 2) (hb : R ≤ a.bid) :
    1-2*sourceUpperFailure row m ≤ ((problem Γ i).outcome a).duplicates := by
  apply Hybrid.native_broadcast_duplicates_lower Γ i a ha (sourceUpperFailure row m)
  simpa only [sourceUpperFailure, sub_sub_cancel] using
    sourceNativeGame_upper_mean_floor row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα i a.bid hb

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_hidden_upper_above
    (hguard : error q t R < Uniform07.eta row*R*(1-2*sourceUpperFailure row m))
    (i : Fin m) (v : ℝ) (hv : t ≤ v) (a : JointAction 2)
    (ha : a.routeCount = 2) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a < utility q t R v := by
  have hint := rank_deficit_integrable_of_bounded μ (m-1) (Uniform07.capacity m)
    2 hc t ((source_upper_value_support row).mono (fun _ hx => hx.2))
  have hmean := sourceNativeGame_upper_mean_floor row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i a.bid hb
  exact Hybrid.native_hidden_upper_excluded Γ (Uniform07.eta_pos row).le
    (source_eta_lt_one row).le rfl rfl (source_upper_rank_monotone row m hm hc)
    (fun x => (source_upper_rank_bounds row m x).2) hR hRt
    (source_upper_rank_pos row m hc t) hint hguard hv i a ha hb
    (by simpa only [sourceUpperFailure, sub_sub_cancel] using hmean)

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_hidden_upper_between
    (hguard : error q t R < Uniform07.eta row*R*(1-2*sourceUpperFailure row m))
    (i : Fin m) (v : ℝ) (hvR : R ≤ v) (hvt : v ≤ t) (a : JointAction 2)
    (ha : a.routeCount = 2) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a < (v-R)*q t := by
  apply native_hidden_upper_below_boundary Γ (Uniform07.eta_pos row).le
    (source_eta_lt_one row).le rfl rfl
    (fun x => (source_upper_rank_bounds row m x).2) hR hRt hvR hvt hguard i a ha hb
  simpa only [sourceUpperFailure, sub_sub_cancel] using
    sourceNativeGame_upper_mean_floor row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα i a.bid hb

include hm hR hUR hRt hLvalue hLroute in
theorem sourceNativeGame_hidden_upper_below
    (hguard : error q t R < Uniform07.eta row*R*(1-2*sourceUpperFailure row m))
    (i : Fin m) (v : ℝ) (hvR : v ≤ R) (a : JointAction 2)
    (ha : a.routeCount = 2) (hb : R ≤ a.bid) :
    (problem Γ i).payoff v a < 0 := by
  apply native_hidden_upper_below_floor Γ (Uniform07.eta_pos row).le
    (source_eta_lt_one row).le rfl rfl
    (fun x => (source_upper_rank_bounds row m x).2) hR hRt hvR hguard i a ha hb
  simpa only [sourceUpperFailure, sub_sub_cancel] using
    sourceNativeGame_upper_mean_floor row hm hc hR hUR hRt hΛ
      PL hLvalue hLroute α hα i a.bid hb

include hm hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_upper_conditional_mass (v : ℝ) (hv : t ≤ v) (r : Fin 3) :
    (conditionalTypeCountLaw Γ (by omega : 0 < m) v).mass r =
      upperSingletonMass (q v) r := by
  apply actual_upper_conditional_mass Γ (by omega) v (q v)
    (Hybrid.upperAction b v) rfl
    (sourcePopulationVersion_upper row m hc R PL hv)
  exact fun i => sourceNativeGame_upper_mean_at_value row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα i v hv

include hm hR hUR hRt hLvalue hLroute in
theorem completeSourceNativeGame_upper_conditional_mass
    (v : ℝ) (hv : t ≤ v) (r : Fin 3) :
    (conditionalTypeCountLaw
      (completeSourceNativeGame row hc R Λ hΛ PL α hα) (by omega : 0 < m) v).mass r =
        upperSingletonMass (q v) r := by
  rw [completeSourceNativeGame_conditional_count]
  exact sourceNativeGame_upper_conditional_mass row hm hc hR hUR hRt hΛ
    PL hLvalue hLroute α hα v hv r

end Actual

theorem completeSourceNativeGame_upper_conditional_tendsto
    (row : Uniform07.Row) (M : ℕ → ℕ) [∀ k, Nonempty (Fin (M k))]
    (hM : ∀ k, 2 ≤ M k) (hM_top : Tendsto M atTop atTop)
    (hc : ∀ k, 1 ≤ Uniform07.capacity (M k))
    (R Λ : ℕ → ℝ) (hR : ∀ k, 0 < R k)
    (hUR : ∀ k, Early.bidCap row < R k)
    (hRt : ∀ k, R k < Uniform07.cutoff row) (hΛ : ∀ k, 0 < Λ k)
    (PL : ℕ → ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : ∀ k, (PL k : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ k, ∀ᵐ x ∂(PL k : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (α : (k : ℕ) → ClassifiedContext (M k) → unitInterval)
    (hα : ∀ k, Measurable (α k)) :
    ∀ v : ℝ, Uniform07.cutoff row ≤ v → ∀ r : Fin 3,
      Tendsto (fun k =>
        (conditionalTypeCountLaw
          (completeSourceNativeGame row (hc k) (R k) (Λ k) (hΛ k) (PL k) (α k) (hα k))
          (by have := hM k; omega : 0 < M k) v).mass r)
        atTop (𝓝 (sourceLimitMass row v r)) := by
  intro v hv r
  have hq := (source_upper_rank_tendsto_one_at row hv).comp hM_top
  have hcont : Continuous (fun q : ℝ => upperSingletonMass q r) := by
    fin_cases r <;> norm_num [upperSingletonMass] <;> fun_prop
  have hlim := (hcont.tendsto 1).comp hq
  have he : (fun k =>
      (conditionalTypeCountLaw
        (completeSourceNativeGame row (hc k) (R k) (Λ k) (hΛ k) (PL k) (α k) (hα k))
        (by have := hM k; omega : 0 < M k) v).mass r) =
      fun k => upperSingletonMass (source_upper_rank row (M k) v) r := by
    funext k
    exact completeSourceNativeGame_upper_conditional_mass row (hM k) (hc k)
      (hR k) (hUR k) (hRt k) (hΛ k) (PL k) (hLvalue k) (hLroute k) (α k) (hα k) v hv r
  rw [he]
  have hentry := (source_entry_lt_cutoff row).le.trans hv
  have hmass : upperSingletonMass 1 r = sourceLimitMass row v r := by
    fin_cases r <;> simp [upperSingletonMass, sourceLimitMass,
      not_lt.mpr hentry, not_lt.mpr hv]
  rw [← hmass]
  exact hlim

end FCAppendix.Affine.Uniform07Finishing
