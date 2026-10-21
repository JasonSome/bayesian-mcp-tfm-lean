import FCAppendix.Affine.Uniform07Finishing.Native.VisibleBids
import FCAppendix.Affine.Uniform07Finishing.Native.SourceProfile
import FCAppendix.Affine.Multiple07.ActualOutcomes

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology

theorem source_eta_le_one (i : Uniform07.Row) : Uniform07.eta i ≤ 1 := by
  cases i <;> norm_num [Uniform07.eta, Uniform07.etaQ]

theorem source_limitCoverage_pos (i : Uniform07.Row) :
    0 < Uniform07.limitCoverage i := by
  cases i
  · have h := Uniform07.dup_first_enclosure.2
    dsimp [Uniform07.limitCoverage, Uniform07.delta]
    linarith
  · have h := Uniform07.dup_second_enclosure.2
    dsimp [Uniform07.limitCoverage, Uniform07.delta]
    linarith

structure UniformNativePair where
  start : ℕ
  start_ge_two : 2 ≤ start
  game : (i : Uniform07.Row) → (k : ℕ) →
    FiniteGame (start + k) 2 (Uniform07.capacity (start + k)) unitInterval
  value_law : ∀ i k, (game i k).F = Uniform07.uniformLaw
  bid_schedule : ∀ i k, (game i k).A = Schedule.affine 2 (Uniform07.eta i)
    (Uniform07.eta_pos i).le (source_eta_le_one i)
  base_schedule : ∀ i k, (game i k).G = Schedule.once 2
  base_fee : ∀ i k, (game i k).g = 0
  seed_law : ∀ i k, (game i k).seedLaw = volume
  equilibrium : ∀ i k, IsBayesianEquilibrium (game i k)
  visible_atomless : ∀ i k j, NullSingletonClass (visibleBidMeasure (game i k) j)
  fixed_value_best_response : ∀ i k v, 0 < v → v ≤ 1 →
    ∀ᵐ a ∂(game i k).σ v, ∀ u : Fin (start + k), ∀ a' : JointAction 2,
      (problem (game i k) u).payoff v a' ≤ (problem (game i k) u).payoff v a
  fixed_value_routing : ∀ i k v, 0 < v → v ≤ 1 → v ≠ Uniform07.cutoff i →
    ∀ᵐ a ∂(game i k).σ v,
      a.routeCount = if v < Uniform07.cutoff i then 2 else 1
  conditional_law : ∀ i v, 0 < v → v ≤ 1 →
    v ≠ Uniform07.entry i → v ≠ Uniform07.cutoff i → ∀ r : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (game i k)
        (by omega) v).mass r) atTop (𝓝 (sourceLimitMass i v r))

namespace UniformNativePair

theorem positive (P : UniformNativePair) (k : ℕ) : 0 < P.start + k := by
  have h := P.start_ge_two
  omega

theorem conditional_law_as_count (P : UniformNativePair) (i : Uniform07.Row)
    {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1)
    (hl : v ≠ Uniform07.entry i) (ht : v ≠ Uniform07.cutoff i) :
    ∀ r, Tendsto (fun k => (conditionalTypeCountLaw (P.game i k)
      (P.positive k) v).mass r) atTop (𝓝 ((sourceLimitLaw i v).mass r)) := by
  intro r
  simpa only [sourceLimitLaw_mass] using P.conditional_law i v hv hv1 hl ht r

private theorem avoid_source_value (v : ℝ) :
    ∀ᵐ w ∂Uniform07.uniformLaw, w ≠ v := by
  apply measure_eq_zero_iff_ae_notMem.mp
  change Uniform07.uniformLaw {v} = 0
  unfold Uniform07.uniformLaw
  exact measure_singleton v

theorem common_conull_conditional_law (P : UniformNativePair) (i : Uniform07.Row) :
    ∀ᵐ v ∂Uniform07.uniformLaw, ∀ r,
      Tendsto (fun k => (conditionalTypeCountLaw (P.game i k)
        (P.positive k) v).mass r) atTop (𝓝 ((sourceLimitLaw i v).mass r)) := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc,
    avoid_source_value 0, avoid_source_value (Uniform07.entry i),
    avoid_source_value (Uniform07.cutoff i)] with v hv hv0 hl ht
  exact P.conditional_law_as_count i (lt_of_le_of_ne hv.1 (Ne.symm hv0)) hv.2 hl ht

theorem common_conull_users (P : UniformNativePair) (i : Uniform07.Row) (k : ℕ) :
    ∀ᵐ x ∂((P.game i k).F ⊗ₘ (P.game i k).σ),
      ∀ u : Fin (P.start + k), ∀ a' : JointAction 2,
        (problem (P.game i k) u).payoff x.1 a' ≤
          (problem (P.game i k) u).payoff x.1 x.2 :=
  (usersOptimal_iff_common_all_actions (P.game i k)).mp (P.equilibrium i k).users

theorem common_conull_users_all_markets (P : UniformNativePair) :
    ∀ᵐ v ∂Uniform07.uniformLaw,∀ row : Uniform07.Row,∀ k : ℕ,
      ∀ᵐ a ∂(P.game row k).σ v,∀ u : Fin (P.start+k),∀ dev : JointAction 2,
        (problem (P.game row k) u).payoff v dev≤
          (problem (P.game row k) u).payoff v a := by
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Icc,
    avoid_source_value 0] with v hv hzero
  intro row k
  exact P.fixed_value_best_response row k v
    (lt_of_le_of_ne hv.1 (Ne.symm hzero)) hv.2

theorem aggregate_limits (P : UniformNativePair) (i : Uniform07.Row) :
    Tendsto (fun k => finiteLoad (P.game i k)) atTop (𝓝 (999 / 1000 : ℝ)) ∧
    Tendsto (fun k => finiteLoad (P.game i k) - finiteCoverage (P.game i k))
      atTop (𝓝 (Uniform07.limitDup i)) ∧
    Tendsto (fun k => finiteCoverage (P.game i k)) atTop (𝓝 (Uniform07.limitCoverage i)) := by
  have h := Multiple07.actual_aggregate_limits (P.game i) P.positive
    Uniform07.uniformLaw (P.value_law i) (sourceLimitLaw i) (P.common_conull_conditional_law i)
  have hprofile := source_actual_profile_integrals i
  rw [hprofile.1] at h
  rw [hprofile.2.1, hprofile.2.2] at h
  exact ⟨by convert! h.2.1 using 1; norm_num [Uniform07.delta], h.2.2, h.1⟩

theorem aggregate_multiplicity_limit (P : UniformNativePair) (i : Uniform07.Row) :
    Tendsto (fun k => finiteMultiplicity (P.game i k)) atTop
      (𝓝 ((999 / 1000 : ℝ) / Uniform07.limitCoverage i)) ∧
    ∀ᶠ k in atTop, 0 < finiteCoverage (P.game i k) := by
  have h := P.aggregate_limits i
  exact Multiple07.actual_multiplicity_limit (P.game i) h.2.2 h.1
    (source_limitCoverage_pos i)

private theorem test_value_conditions (i : Uniform07.Row) :
    0 < Uniform07.testValue ∧ Uniform07.testValue ≤ 1 ∧
      Uniform07.testValue ≠ Uniform07.entry i ∧ Uniform07.testValue ≠ Uniform07.cutoff i := by
  refine ⟨by norm_num [Uniform07.testValue], by norm_num [Uniform07.testValue], ?_, ?_⟩
  · cases i
    · exact (source_entry_lt_cutoff .first |>.trans Uniform07.cutoff_test_order.1).ne'
    · exact Uniform07.entry_test_order.ne'
  · cases i
    · exact Uniform07.cutoff_test_order.1.ne'
    · exact Uniform07.cutoff_test_order.2.ne

theorem test_value_limits (P : UniformNativePair) :
    Tendsto (fun k => (conditionalTypeCountLaw (P.game .first k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 1) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 1) ∧
    Tendsto (fun k => (conditionalTypeCountLaw (P.game .second k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 Uniform07.testSuccess) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 Uniform07.testMultiplicity) := by
  have h₁ := test_value_conditions .first
  have h₂ := test_value_conditions .second
  have ho₁ := Multiple07.actual_fixed_value_outcomes (P.game .first) P.positive
    Uniform07.testValue (sourceLimitLaw .first Uniform07.testValue)
      (P.conditional_law_as_count .first h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2)
  have ho₂ := Multiple07.actual_fixed_value_outcomes (P.game .second) P.positive
    Uniform07.testValue (sourceLimitLaw .second Uniform07.testValue)
      (P.conditional_law_as_count .second h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2)
  have hfirstS : (sourceLimitLaw .first Uniform07.testValue).success = 1 := by
    rw [source_test_first]
    simp [CountLaw.success, FiniteLaw.expect_dirac, successIndicator]
  have hfirstL : (sourceLimitLaw .first Uniform07.testValue).load = 1 := by
    rw [source_test_first]
    simp [CountLaw.load, FiniteLaw.expect_dirac]
  refine ⟨by simpa [hfirstS] using ho₁.1, ?_,
    by simpa only [source_test_second.1] using ho₂.1, ?_⟩
  · have h := ho₁.2.2.2 (by rw [hfirstS]; norm_num)
    simpa [conditionalMultiplicity, hfirstS, hfirstL] using h
  · have h := ho₂.2.2.2 source_test_second.2.2
    simpa only [source_test_second.2.1] using h

theorem common_strict_comparisons (P : UniformNativePair) :
    ∃ K, ∀ k ≥ K,
      finiteLoad (P.game .first k) - finiteCoverage (P.game .first k) <
        finiteLoad (P.game .second k) - finiteCoverage (P.game .second k) ∧
      finiteCoverage (P.game .second k) < finiteCoverage (P.game .first k) ∧
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success <
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success ∧
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load <
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load := by
  have h₁ := P.aggregate_limits .first
  have h₂ := P.aggregate_limits .second
  have hv := P.test_value_limits
  have hs : Uniform07.testSuccess < 1 := by linarith [Uniform07.pointwise_numbers.2.1]
  have hmu : 1 < Uniform07.testMultiplicity := by linarith [Uniform07.pointwise_numbers.2.2.1]
  apply eventually_atTop.mp
  filter_upwards [Tendsto.eventually_lt h₁.2.1 h₂.2.1 Uniform07.strict_aggregates.1,
    Tendsto.eventually_lt h₂.2.2 h₁.2.2 Uniform07.strict_aggregates.2,
    Tendsto.eventually_lt hv.2.2.1 hv.1 hs,
    Tendsto.eventually_lt hv.2.1 hv.2.2.2 hmu] with k hd hq hs hmu
  exact ⟨hd, hq, hs, hmu⟩

theorem common_positive_strict_comparisons (P : UniformNativePair) :
    ∃ K, ∀ k ≥ K,
      0 < finiteCoverage (P.game .first k) ∧
      0 < finiteCoverage (P.game .second k) ∧
      0 < (conditionalTypeCountLaw (P.game .first k)
        (P.positive k) Uniform07.testValue).success ∧
      0 < (conditionalTypeCountLaw (P.game .second k)
        (P.positive k) Uniform07.testValue).success ∧
      finiteLoad (P.game .first k) - finiteCoverage (P.game .first k) <
        finiteLoad (P.game .second k) - finiteCoverage (P.game .second k) ∧
      finiteCoverage (P.game .second k) < finiteCoverage (P.game .first k) ∧
      finiteMultiplicity (P.game .first k) < finiteMultiplicity (P.game .second k) ∧
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success <
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success ∧
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load <
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load := by
  have hμ₁ := P.aggregate_multiplicity_limit .first
  have hμ₂ := P.aggregate_multiplicity_limit .second
  have hv := P.test_value_limits
  have hs₂ : 0 < Uniform07.testSuccess := by
    linarith [Uniform07.pointwise_numbers.1]
  have hμ : (999 / 1000 : ℝ) / Uniform07.limitCoverage .first <
      (999 / 1000 : ℝ) / Uniform07.limitCoverage .second :=
    div_lt_div_of_pos_left (by norm_num) (source_limitCoverage_pos .second)
      Uniform07.strict_aggregates.2
  apply eventually_atTop.mp
  filter_upwards [eventually_atTop.mpr P.common_strict_comparisons,
    hμ₁.2, hμ₂.2, hv.1.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)),
    hv.2.2.1.eventually (eventually_gt_nhds hs₂),
    Tendsto.eventually_lt hμ₁.1 hμ₂.1 hμ] with k hc hq₁ hq₂ hs₁ hs₂ hμk
  exact ⟨hq₁, hq₂, hs₁, hs₂, hc.1, hc.2.1, hμk, hc.2.2.1, hc.2.2.2⟩

end UniformNativePair

def AffUniformResult : Prop :=
  ∃ P : UniformNativePair,
    (∀ i v, 0 < v → v ≤ 1 →
      v ≠ Uniform07.entry i → v ≠ Uniform07.cutoff i → ∀ r : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (P.game i k)
        (P.positive k) v).mass r) atTop (𝓝 (sourceLimitMass i v r))) ∧
    (∀ i, Tendsto (fun k => finiteLoad (P.game i k)) atTop (𝓝 (999 / 1000 : ℝ)) ∧
      Tendsto (fun k => finiteLoad (P.game i k) - finiteCoverage (P.game i k))
        atTop (𝓝 (Uniform07.limitDup i)) ∧
      Tendsto (fun k => finiteCoverage (P.game i k)) atTop (𝓝 (Uniform07.limitCoverage i)) ∧
      Tendsto (fun k => finiteMultiplicity (P.game i k)) atTop
        (𝓝 ((999 / 1000 : ℝ) / Uniform07.limitCoverage i))) ∧
    (Tendsto (fun k => (conditionalTypeCountLaw (P.game .first k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 1) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 1) ∧
    Tendsto (fun k => (conditionalTypeCountLaw (P.game .second k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 Uniform07.testSuccess) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 Uniform07.testMultiplicity)) ∧
    Uniform07.limitDup .first < Uniform07.limitDup .second ∧
    Uniform07.limitCoverage .second < Uniform07.limitCoverage .first ∧
    (49009354366 / 10^11 : ℝ) < Uniform07.testSuccess ∧
    Uniform07.testSuccess < 49009354367 / 10^11 ∧
    (116680848997 / 10^11 : ℝ) < Uniform07.testMultiplicity ∧
    Uniform07.testMultiplicity < 116680848998 / 10^11 ∧
    (∃ K, ∀ k ≥ K,
      0 < finiteCoverage (P.game .first k) ∧
      0 < finiteCoverage (P.game .second k) ∧
      0 < (conditionalTypeCountLaw (P.game .first k)
        (P.positive k) Uniform07.testValue).success ∧
      0 < (conditionalTypeCountLaw (P.game .second k)
        (P.positive k) Uniform07.testValue).success ∧
      finiteLoad (P.game .first k) - finiteCoverage (P.game .first k) <
        finiteLoad (P.game .second k) - finiteCoverage (P.game .second k) ∧
      finiteCoverage (P.game .second k) < finiteCoverage (P.game .first k) ∧
      finiteMultiplicity (P.game .first k) < finiteMultiplicity (P.game .second k) ∧
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success <
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success ∧
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load <
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load)

theorem aff_uniform_result_of_native_pair (P : UniformNativePair) : AffUniformResult := by
  refine ⟨P, ?_, ?_, P.test_value_limits, Uniform07.strict_aggregates.1,
    Uniform07.strict_aggregates.2, Uniform07.pointwise_numbers.1,
    Uniform07.pointwise_numbers.2.1, Uniform07.pointwise_numbers.2.2.1,
    Uniform07.pointwise_numbers.2.2.2, P.common_positive_strict_comparisons⟩
  · exact P.conditional_law
  · intro i
    have h := P.aggregate_limits i
    exact ⟨h.1, h.2.1, h.2.2, (P.aggregate_multiplicity_limit i).1⟩

end FCAppendix.Affine.Uniform07Finishing
