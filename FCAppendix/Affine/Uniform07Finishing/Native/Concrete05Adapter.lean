import FCAppendix.Affine.UniformFinite.Late.NativeConstruction
import FCAppendix.Affine.UniformFinite.OriginalPopulationRows
import FCAppendix.Affine.Uniform07Finishing.Early.NativeRadius
import FCAppendix.Affine.Uniform07Finishing.Native.SourceProducerAdapter

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators

theorem cap_eq (row : Uniform07.Row) : Uniform05.cap row=Early.bidCap row := by
  rw [Early.cap_literal_product_formula]
  simp only [Uniform05.cap,Uniform05.activeBid,Uniform05.lambda_eq_canonical,
    Uniform05.t_eq_canonical,Uniform05.xi_eq_canonical,Uniform05.kappa_eq_canonical]

theorem floor_eq (row : Uniform07.Row) (v : ℝ) :
    Uniform05.floorBid row v=Early.lowerFloor row v := by
  simp only [Uniform05.floorBid,Uniform05.chi,Uniform05.v0,Uniform05.s,
    Uniform05.zc,Uniform05.clip01,Uniform05.t_eq_canonical,
    Uniform05.lambda_eq_canonical,Early.lowerFloor,Early.chi,Early.smallValue,
    Early.floorStart,Early.categoryCutoff,Early.clip01,max_comm]

theorem demand_eq (row : Uniform07.Row) :
    Uniform05.requiredDemand row=Early.demandRatio row := by
  simp only [Uniform05.requiredDemand,Early.demandRatio,Uniform05.t_eq_canonical,
    Uniform05.delta,Uniform07.delta]

theorem rejection_scale_eq (row : Uniform07.Row) :
    Uniform05.rejectionScale row=Uniform07.cutoff row/1000 := by
  simp only [Uniform05.rejectionScale,Uniform05.t_eq_canonical]

theorem guardRadius_eq_nativeRadius (row : Uniform07.Row) :
    Uniform05.guardRadius row=Early.nativeRadius row := by
  simp only [Uniform05.guardRadius,Early.nativeRadius,Uniform05.t_eq_canonical]

theorem lower_value_measure_eq (row : Uniform07.Row) :
    Uniform05.lowerValueMeasure row=(sourceLowerValueLaw row : Measure ℝ) := by
  rw [sourceLowerValueLaw_literal]
  simp only [Uniform05.lowerValueMeasure,Uniform05.t_eq_canonical]

theorem guardRadius_lt_samplingMargin (row : Uniform07.Row) :
    Uniform05.guardRadius row< Early.samplingMargin row := by
  have ht := Uniform07.cutoff_pos row
  have hr : (1/60:ℝ)≤ Early.demandRatio row := by
    rw [←demand_eq]
    exact Uniform05.requiredDemand_ge_one_sixtieth row
  have hξ : (2/5:ℝ)≤ Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ]
  have hh := mul_le_mul hξ hr (by norm_num : (0:ℝ)≤ 1/60)
    (Uniform07.xi_pos row).le
  have hht := mul_le_mul_of_nonneg_left hh ht.le
  simp only [Uniform05.guardRadius,Uniform05.t_eq_canonical,Early.samplingMargin]
  nlinarith

theorem guardRadius_ne_samplingMargin (row : Uniform07.Row) :
    Uniform05.guardRadius row≠Early.samplingMargin row :=
  (guardRadius_lt_samplingMargin row).ne

section OneLaw
variable {row : Uniform07.Row} {m : ℕ}

def realJoint (E : UniformFinite.ExactRestrictedLaw row m) : Measure (ℝ×ℝ) :=
  (E.law.1 : Measure (ℝ×Uniform05.Bid row)).map
    (fun p=>(p.1,(p.2:ℝ)))

instance realJoint_probability (E : UniformFinite.ExactRestrictedLaw row m) :
    IsProbabilityMeasure (realJoint E) := by
  unfold realJoint
  exact Measure.isProbabilityMeasure_map
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)).aemeasurable

theorem realJoint_value (E : UniformFinite.ExactRestrictedLaw row m) :
    (realJoint E).map Prod.fst=(sourceLowerValueLaw row : Measure ℝ) := by
  rw [realJoint,Measure.map_map (f := fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ))) measurable_fst
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))]
  change (E.law.1 : Measure (ℝ×Uniform05.Bid row)).map Prod.fst=_
  rw [E.original_real_marginal,lower_value_measure_eq]

theorem realJoint_bid (E : UniformFinite.ExactRestrictedLaw row m) :
    (realJoint E).map Prod.snd=(E.realBid : Measure ℝ) := by
  rw [realJoint,Measure.map_map (f := fun p : ℝ×Uniform05.Bid row => (p.1,(p.2:ℝ))) measurable_snd
    (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))]
  change (E.law.1 : Measure (ℝ×Uniform05.Bid row)).map
    ((Subtype.val : Uniform05.Bid row→ℝ)∘Prod.snd)=_
  rw [←Measure.map_map measurable_subtype_coe measurable_snd]
  change (E.law.bidLaw : Measure (Uniform05.Bid row)).map Subtype.val=_
  rw [UniformFinite.ExactRestrictedLaw.law,UniformFinite.restrictedLaw_bidLaw]
  rfl

def lowerJoint (E : UniformFinite.ExactRestrictedLaw row m) :
    ProbabilityMeasure (ℝ×JointAction 2) :=
  UniformFinite.OriginalPopulation.lowerJoint E

theorem lowerJoint_value (E : UniformFinite.ExactRestrictedLaw row m) :
    (lowerJoint E : Measure (ℝ×JointAction 2)).map Prod.fst=
      (sourceLowerValueLaw row : Measure ℝ) := by
  have hm : Measurable (fun p : UniformFinite.Value row×unitInterval =>
      ((p.1:ℝ),UniformFinite.OriginalPopulation.lowerAction row p)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (UniformFinite.OriginalPopulation.measurable_lowerAction row)
  rw [lowerJoint,UniformFinite.OriginalPopulation.lowerJoint,
    ProbabilityMeasure.toMeasure_map]
  dsimp only [Function.comp_def]
  rw [Measure.map_map
      (f := fun p : UniformFinite.Value row×unitInterval =>
        ((p.1:ℝ),UniformFinite.OriginalPopulation.lowerAction row p)) measurable_fst hm]
  change (E.pi.1 : Measure (UniformFinite.Value row×unitInterval)).map
    ((Subtype.val : UniformFinite.Value row→ℝ)∘Prod.fst)=_
  rw [←Measure.map_map measurable_subtype_coe measurable_fst,E.original_marginal,
    UniformFinite.lowerMeasure_real,lower_value_measure_eq]

theorem lowerJoint_routes (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),
      x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2 := by
  simpa only [lowerJoint,cap_eq] using
    UniformFinite.OriginalPopulation.lowerJoint_shape E

theorem lowerJoint_bid_measure (E : UniformFinite.ExactRestrictedLaw row m) :
    (lowerJoint E : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=
      (E.realBid : Measure ℝ) :=
  UniformFinite.OriginalPopulation.lowerJoint_bidLaw E

theorem lowerJoint_atomless (E : UniformFinite.ExactRestrictedLaw row m) (b : ℝ) :
    (lowerJoint E : Measure (ℝ×JointAction 2)) {x|x.2.bid=b}=0 := by
  have hz := measure_singleton (μ:=(E.realBid : Measure ℝ)) b
  rw [←lowerJoint_bid_measure E,Measure.map_apply
    (f := fun x : ℝ×JointAction 2 => x.2.bid)
    ((measurable_bid 2).comp measurable_snd) (measurableSet_singleton b)] at hz
  exact hz

theorem lowerJoint_floor_no_overbid (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),
      Early.lowerFloor row x.1≤ x.2.bid ∧ x.2.bid≤ x.1 := by
  change ∀ᵐx∂((E.pi.1 : Measure (UniformFinite.Value row×unitInterval)).map
    (fun p=>((p.1:ℝ),UniformFinite.OriginalPopulation.lowerAction row p))), _
  apply (ae_map_iff
    ((measurable_subtype_coe.comp measurable_fst).prodMk
      (UniformFinite.OriginalPopulation.measurable_lowerAction row)).aemeasurable
    (by
      apply MeasurableSet.inter
      · have hf : Measurable (fun x : ℝ×JointAction 2 => Early.lowerFloor row x.1) := by
          unfold Early.lowerFloor Early.clip01
          fun_prop
        convert! measurableSet_le hf ((measurable_bid 2).comp measurable_snd) using 1
      · exact measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_fst)).mpr
  apply ae_of_all
  intro p
  change Early.lowerFloor row (p.1:ℝ)≤
    (UniformFinite.baseBid row p:ℝ) ∧
    (UniformFinite.baseBid row p:ℝ)≤(p.1:ℝ)
  rw [←floor_eq]
  have hb : (UniformFinite.baseBid row p:ℝ)∈
      Icc (Uniform05.floorBid row p.1) (UniformFinite.hiBid row p.1) :=
    UniformFinite.noisyRealBid_bounds row (0:unitInterval) p.1 p.2 0
  exact ⟨hb.1,hb.2.trans (min_le_left _ _)⟩

theorem lowerJoint_floor (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),
      Early.lowerFloor row x.1≤ x.2.bid :=
  (lowerJoint_floor_no_overbid E).mono (fun _ h=>h.1)

theorem lowerJoint_no_overbid (E : UniformFinite.ExactRestrictedLaw row m) :
    ∀ᵐx∂(lowerJoint E : Measure (ℝ×JointAction 2)),x.2.bid≤ x.1 :=
  (lowerJoint_floor_no_overbid E).mono (fun _ h=>h.2)

theorem multiplier_lower (E : UniformFinite.ExactRestrictedLaw row m) :
    (54/100:ℝ)*Uniform07.cutoff row< E.law.multiplier := by
  simpa only [Uniform05.t_eq_canonical] using E.law.multiplier_guards.1

theorem multiplier_upper (E : UniformFinite.ExactRestrictedLaw row m) :
    E.law.multiplier≤(1-Uniform07.xi row*Early.demandRatio row)*Early.bidCap row := by
  simpa only [Uniform05.xi_eq_canonical,demand_eq,cap_eq] using
    E.law.multiplier_guards.2.1

theorem rejection_root_bounds (E : UniformFinite.ExactRestrictedLaw row m) :
    (52/100:ℝ)*Uniform07.cutoff row< E.law.rejectionRoot ∧
      E.law.rejectionRoot< Early.bidCap row := by
  simpa only [Uniform05.t_eq_canonical,cap_eq] using E.law.rejectionRoot_guards

theorem multiplier_equation (E : UniformFinite.ExactRestrictedLaw row m) :
    (∫b : Uniform05.Bid row,ClippedResidual.exposure (Uniform07.xi row)
      E.law.multiplier (b:ℝ) ∂(E.law.bidLaw : Measure (Uniform05.Bid row)))=
        Early.demandRatio row := by
  simpa only [Uniform05.lawDemand,Uniform05.xi_eq_canonical,demand_eq] using
    E.law.multiplier_equation

theorem rejection_root_equation (E : UniformFinite.ExactRestrictedLaw row m) :
    (∫b : Uniform05.Bid row,Weighted.sourcePsi (Uniform07.cutoff row/1000)
      E.law.rejectionRoot (b:ℝ) ∂(E.law.bidLaw : Measure (Uniform05.Bid row)))=
        3*Early.demandRatio row := by
  simpa only [Uniform05.lawRejection,Uniform05.rejectionExposure,
    rejection_scale_eq,Weighted.sourcePsi,demand_eq] using E.law.rejectionRoot_equation

theorem lower_kernel_fixed {R : ℝ}
    (W : UniformFinite.NativeFiniteLowerConstruction row m R)
    (H : UniformFinite.OriginalPopulation.UpperPriorityLaw row R)
    (v : UniformFinite.Value row) :
    (W.game H).σ v=(W.finite.restricted.sigma v).map
      (fun q=>UniformFinite.OriginalPopulation.lowerAction row (v,q)) :=
  W.lower_kernel H v

theorem original_all_broadcast_IC {R : ℝ}
    (W : UniformFinite.NativeFiniteLowerConstruction row m R) :
    ∀ᵐp∂(W.finite.restricted.pi.1 :
        Measure (UniformFinite.Value row×unitInterval)),∀b : ℝ,
      0≤ b→ b< R→
      UniformFinite.Late.extendedRawUtility row (m-1) W.finite.restricted.law p.1 b≤
        UniformFinite.rawUtility row (m-1) W.finite.restricted.law p.1
          (UniformFinite.baseBid row p) :=
  W.finite.all_broadcast_IC

end OneLaw

theorem capacity_positive {m : ℕ} (hm : 3≤ m) : 1≤ Uniform07.capacity m := by
  unfold Uniform07.capacity
  omega

structure LowerFamily where
  start : ℕ
  start_ge_three : 3≤ start
  construction : (row : Uniform07.Row)→(k : ℕ)→
    UniformFinite.NativeFiniteLowerConstruction row (start+k) (sourceLowerPriceCeiling row)

theorem exists_lower_family : Nonempty LowerFamily := by
  obtain ⟨N₀,h₀⟩ := UniformFinite.exists_eventual_uniform_lower_construction Uniform07.Row.first
  obtain ⟨N₁,h₁⟩ := UniformFinite.exists_eventual_uniform_lower_construction Uniform07.Row.second
  let start := max 3 (max N₀ N₁)
  have hstart : 3≤ start := le_max_left _ _
  have hex (row : Uniform07.Row) (k : ℕ) :
      Nonempty (UniformFinite.NativeFiniteLowerConstruction row (start+k)
        (sourceLowerPriceCeiling row)) := by
    have hcap : Uniform05.cap row< sourceLowerPriceCeiling row := by
      rw [cap_eq]
      exact (Crossover.Physical.source_auxiliary_floor_guards row).2.1
    cases row
    · exact h₀ (start+k) (by dsimp [start]; omega) _ hcap
    · exact h₁ (start+k) (by dsimp [start]; omega) _ hcap
  exact ⟨⟨start,hstart,fun row k=>Classical.choice (hex row k)⟩⟩

def lowerFamily : LowerFamily := Classical.choice exists_lower_family

namespace LowerFamily

def marketData (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    UniformMarketData row (F.start+k) where
  market_ge_two := by have := F.start_ge_three; omega
  capacity_positive := capacity_positive (by have := F.start_ge_three; omega)
  R := sourceLowerPriceCeiling row
  Λ := (F.construction row k).finite.restricted.law.multiplier
  z := (F.construction row k).finite.restricted.law.rejectionRoot
  width := 10*UniformFinite.Source.commonGuardMargin row
  guardMargin := UniformFinite.Source.commonGuardMargin row
  floor_positive := (Crossover.Physical.source_auxiliary_floor_guards row).1
  cap_lt_floor := (Crossover.Physical.source_auxiliary_floor_guards row).2.1
  floor_lt_cutoff := (Crossover.Physical.source_auxiliary_floor_guards row).2.2.1
  multiplier_lower := multiplier_lower (F.construction row k).finite.restricted
  guard_margin_positive := UniformFinite.Source.common_guard_margin row
  lower := lowerJoint (F.construction row k).finite.restricted
  lower_value := lowerJoint_value (F.construction row k).finite.restricted
  lower_routes := lowerJoint_routes (F.construction row k).finite.restricted
  lower_atomless := lowerJoint_atomless (F.construction row k).finite.restricted

theorem market_floor (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    (F.marketData row k).R=sourceLowerPriceCeiling row := rfl

theorem market_no_overbid (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    ∀ᵐx∂((F.marketData row k).lower : Measure (ℝ×JointAction 2)),x.2.bid≤ x.1 :=
  lowerJoint_no_overbid (F.construction row k).finite.restricted

theorem market_lower_floor (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    ∀ᵐx∂((F.marketData row k).lower : Measure (ℝ×JointAction 2)),
      Early.lowerFloor row x.1≤ x.2.bid :=
  lowerJoint_floor (F.construction row k).finite.restricted

theorem market_rejection_root (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    (52/100:ℝ)*Uniform07.cutoff row<(F.marketData row k).z :=
  (rejection_root_bounds (F.construction row k).finite.restricted).1

theorem market_guard_margin (F : LowerFamily) (row : Uniform07.Row) (k : ℕ) :
    (F.marketData row k).guardMargin=UniformFinite.Source.commonGuardMargin row := rfl

end LowerFamily
end FCAppendix.Affine.Uniform07Finishing.Concrete05
