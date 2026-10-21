import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalWindow
import FCAppendix.Affine.Uniform07Finishing.Native.LowerChainFamily

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
namespace Physical

def compactBroadcastBid (U : ℝ) (hU : 0 ≤ U) (a : JointAction 2) : Icc (0:ℝ) U :=
  ⟨min a.bid U,le_min a.bid_nonneg hU,min_le_right _ _⟩

theorem compactBroadcastBid_measurable (U : ℝ) (hU : 0 ≤ U) :
    Measurable (compactBroadcastBid U hU) :=
  ((measurable_bid 2).min measurable_const).subtype_mk

def compactBroadcastJoint (U : ℝ) (hU : 0 ≤ U)
    (PL : ProbabilityMeasure (ℝ × JointAction 2)) : ProbabilityMeasure (ℝ × Icc (0:ℝ) U) :=
  PL.map (measurable_fst.prodMk ((compactBroadcastBid_measurable U hU).comp measurable_snd)).aemeasurable

theorem compactBroadcastJoint_map_back (U : ℝ) (hU : 0 ≤ U)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hPL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount=2) :
    (compactBroadcastJoint U hU PL : Measure (ℝ × Icc (0:ℝ) U)).map
      (fun z => (z.1,sourceLowerBroadcastAction U z.2)) = (PL : Measure (ℝ × JointAction 2)) := by
  change ((PL : Measure (ℝ × JointAction 2)).map
    (fun x => (x.1,compactBroadcastBid U hU x.2))).map
      (fun z => (z.1,sourceLowerBroadcastAction U z.2)) = _
  have hmap := Measure.map_map (μ := (PL : Measure (ℝ × JointAction 2)))
    (measurable_fst.prodMk ((sourceLowerBroadcastAction_measurable U).comp measurable_snd))
    (measurable_fst.prodMk ((compactBroadcastBid_measurable U hU).comp measurable_snd))
  simp only [Function.comp_def] at hmap
  rw [hmap]
  calc
    _ = (PL : Measure (ℝ × JointAction 2)).map id := by
      apply Measure.map_congr
      filter_upwards [hPL] with x hx
      change (x.1,sourceLowerBroadcastAction U (compactBroadcastBid U hU x.2))=(x.1,x.2)
      congr 1
      rw [sourceLowerBroadcastAction_eq_two]
      change two (min x.2.bid U)=x.2
      rw [min_eq_left hx.1]
      exact (raw_two_eq x.2 hx.2).symm
    _ = _ := Measure.map_id

theorem compactBroadcastJoint_measurePreserving (U : ℝ) (hU : 0 ≤ U)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hPL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ U ∧ x.2.routeCount=2) :
    MeasurePreserving (fun z : ℝ × Icc (0:ℝ) U =>
      (z.1,sourceLowerBroadcastAction U z.2))
      (compactBroadcastJoint U hU PL : Measure (ℝ × Icc (0:ℝ) U))
      (PL : Measure (ℝ × JointAction 2)) :=
  ⟨measurable_fst.prodMk ((sourceLowerBroadcastAction_measurable U).comp measurable_snd),
    compactBroadcastJoint_map_back U hU PL hPL⟩

variable {row : Uniform07.Row} {m : ℕ}

theorem sourcePopulation_lower_restriction (D : UniformMarketData row m) :
    (sourcePopulation row m D.capacity_positive D.R D.lower : Measure (ℝ × JointAction 2)).restrict
      {z | z.1 ≤ Uniform07.cutoff row} =
        ENNReal.ofReal (Uniform07.cutoff row) • (D.lower : Measure (ℝ × JointAction 2)) := by
  have hL : ∀ᵐ z ∂(D.lower : Measure (ℝ × JointAction 2)), z.1≤ Uniform07.cutoff row := by
    have hv : ∀ᵐ z ∂(D.lower : Measure (ℝ × JointAction 2)), z.1∈Icc (0:ℝ) (Uniform07.cutoff row) := by
      apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mp
      rw [D.lower_value]
      exact sourceLowerValueLaw_support row
    exact hv.mono fun _ hz => hz.2
  have hLR : (D.lower : Measure (ℝ × JointAction 2)).restrict
      {z | z.1≤ Uniform07.cutoff row}=(D.lower : Measure (ℝ × JointAction 2)) := by
    exact Measure.restrict_eq_self_of_ae_mem hL
  have hHne := joint_value_ne_of_marginal (sourceUpperJoint row m D.capacity_positive D.R)
    (sourceUpperValueLaw row) (source_upper_joint_value_marginal row m D.capacity_positive D.R)
    (Uniform07.cutoff row)
  have hHR : (sourceUpperJoint row m D.capacity_positive D.R : Measure (ℝ × JointAction 2)).restrict
      {z | z.1≤ Uniform07.cutoff row}=0 := by
    apply Measure.restrict_eq_zero.mpr
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [(source_upper_joint_properties row m D.market_ge_two D.capacity_positive
      D.floor_positive D.floor_lt_cutoff).2.1,hHne] with z hz hne hbad
    exact (lt_of_le_of_ne hz.1.1 (Ne.symm hne)).not_ge hbad
  rw [sourcePopulation_literal,Measure.restrict_add,Measure.restrict_smul,
    Measure.restrict_smul,hLR,hHR,smul_zero,add_zero]

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover

namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology
open Crossover Crossover.Physical
variable {row : Uniform07.Row} {m : ℕ}

theorem UniformMarketData.native_lower_restriction (D : UniformMarketData row m) :
    (D.native.F ⊗ₘ D.native.σ).restrict {z : ℝ × JointAction 2 | z.1≤ Uniform07.cutoff row}=
      ENNReal.ofReal (Uniform07.cutoff row) • (D.lower : Measure (ℝ × JointAction 2)) := by
  letI : Nonempty (Fin m) := D.fin_nonempty
  rw [show D.native.F ⊗ₘ D.native.σ=
      (sourcePopulation row m D.capacity_positive D.R D.lower : Measure (ℝ × JointAction 2)) from
    sourceNativeGame_joint_law row D.market_ge_two D.capacity_positive D.floor_positive
      D.floor_lt_cutoff (source_guard_multiplier_positive row D.multiplier_lower) D.lower
      D.lower_value D.lower_routes (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
      (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin)]
  exact sourcePopulation_lower_restriction D

def UniformMarketData.broadcastLaw (D : UniformMarketData row m)
    (hpay : ∀ i : Fin m, ∀ z : ℝ × Icc (0:ℝ) (Early.bidCap row), 0 < z.2.1 →
      ContinuousAt (fun w : ℝ × Icc (0:ℝ) (Early.bidCap row) =>
        (problem D.native i).payoff w.1 (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z)
    (hIC : ∀ᵐ z ∂(D.lower : Measure (ℝ × JointAction 2)), ∀ i : Fin m,
      ∀ a : JointAction 2, a.routeCount=2 → a.bid< D.R →
        (problem D.native i).payoff z.1 a≤(problem D.native i).payoff z.1 z.2) :
    BroadcastLaw05 D.native (Uniform07.cutoff row) (Early.bidCap row) := by
  have hU : 0 ≤ Early.bidCap row :=
    (div_nonneg (Uniform07.cutoff_pos row).le (by norm_num : (0:ℝ) ≤ 2)).trans
      (source_seed_cutoff_lt_bidCap row).le
  refine {
    lower := compactBroadcastJoint (Early.bidCap row) hU D.lower
    literal := ?_
    atomless := ?_
    payoffContinuous := hpay
    broadcastIC := ?_ }
  · rw [D.native_lower_restriction,compactBroadcastJoint_map_back _ _ _ D.lower_routes]
  · constructor
    intro b
    change ((D.native.F ⊗ₘ D.native.σ).restrict {z : ℝ × JointAction 2 | z.1≤ Uniform07.cutoff row}).map
      (fun z => z.2.bid) {b}=0
    rw [D.native_lower_restriction,Measure.map_smul,Measure.smul_apply]
    have hmap := Measure.map_apply (μ := (D.lower : Measure (ℝ × JointAction 2)))
      ((measurable_bid 2).comp measurable_snd) (measurableSet_singleton b)
    simp only [Function.comp_def] at hmap
    rw [hmap]
    change ENNReal.ofReal (Uniform07.cutoff row)*(D.lower : Measure (ℝ × JointAction 2)) {z | z.2.bid=b}=0
    rw [D.lower_atomless b,mul_zero]
  · have h := (compactBroadcastJoint_measurePreserving (Early.bidCap row) hU D.lower
      D.lower_routes).quasiMeasurePreserving.ae hIC
    filter_upwards [h] with z hz
    intro i b
    exact hz i (sourceLowerBroadcastAction (Early.bidCap row) b) rfl
      (b.2.2.trans_lt D.cap_lt_floor)

end FCAppendix.Affine.Uniform07Finishing
