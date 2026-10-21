import FCAppendix.Existence.R01PayOnceLimitIC
import FCAppendix.Existence.R01PayOnceDisintegration
import FCAppendix.Existence.R01PayOnceZeroType

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory
open FCAppendix.Existence.Distributional

theorem exists_bounded_broadcast_law (W : ℝ) (hW : 0<W)
    (N n c : ℕ) (hN : 0<N) (hn : 2≤n) (hc1 : 1≤c) (hcm : c<N+1)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] :
    ∃ (π : FloorLaw 0 W μ) (σ : Kernel (Value W) (FloorAction 0 W)),
      IsMarkovKernel σ ∧ μ ⊗ₘ σ=(π.1 : Measure (Value W × FloorAction 0 W)) ∧
      (∀ᵐz ∂(π.1 : Measure (Value W × FloorAction 0 W)),∀a : FloorAction 0 W,
        positivePayoff N n c π.1 (z.1,a)≤positivePayoff N n c π.1 z) ∧
      (∀ᵐw ∂μ,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
        positivePayoff N n c π.1 (w,a')≤positivePayoff N n c π.1 (w,a)) ∧
      (∀ᵐw ∂μ,∀ᵐa ∂σ w,(w.1=0 ↔ present a=false) ∧ (present a=true→0<bid a)) ∧
      (π.1 : Measure (Value W × FloorAction 0 W))
        {z|present z.2=true ∧ bid z.2=0}=0 := by
  obtain ⟨ε,hε,π,ν₀,hεW,hε0,hIC,hν,hposzero⟩ :=
    exists_floor_limit_without_positive_active_zero W hW N n c hN hn hc1 hcm μ
  have hzerotype := actual_floor_limit_no_zero_type_active W N n c hn hc1 hcm.le μ
    ε hε π hIC ν₀ hν
  have hinactive := actual_floor_limit_no_positive_inactive W N n c hn hc1 μ
    ε hε hεW hε0 π hIC ν₀ hν
  have hzero : (ν₀.1 : Measure (Value W × FloorAction 0 W))
      {z|present z.2=true ∧ bid z.2=0}=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hposzero,
      measure_eq_zero_iff_ae_notMem.mp hzerotype] with z hzpos hz0
    rintro ⟨hp,hb⟩
    by_cases hw : z.1.1=0
    · exact hz0 ⟨hw,hp⟩
    · exact hzpos ⟨lt_of_le_of_ne z.1.2.1 (Ne.symm hw),hp,hb⟩
  have hM : ∀b : PositiveBid W,improvementMass N n c ν₀.1 (positiveAction b)=0 :=
    actual_floor_limit_positive_improvement_zero W hW N n c hn μ ε hε hε0 π hIC ν₀ hν hzero
  have hMInactive := actual_floor_limit_inactive_improvement_zero W hW N n c hn μ
    ε hε π hIC ν₀ hν hzero
  have hIC0 := common_allAction_IC_of_improvementMass_zero N n c hn hW.le ν₀.1 hM hMInactive
  obtain ⟨σ,hσ,hdis,hσIC⟩ := disintegrate_zeroPayoff_allAction N n c hn μ ν₀ hIC0
  refine ⟨ν₀,σ,hσ,hdis,hIC0,hσIC,?_,hzero⟩
  let S : Set (Value W × FloorAction 0 W) := {z|¬zeroClass z ∧
    ¬(0<z.1.1 ∧ present z.2=false) ∧ ¬(present z.2=true ∧ bid z.2=0)}
  have hS : MeasurableSet S := measurableSet_zeroClass.compl.inter
    (((measurableSet_lt measurable_const (measurable_fst.subtype_val)).inter
      (measurableSet_eq_fun (continuous_present.measurable.comp measurable_snd) measurable_const)).compl.inter
      (((measurableSet_eq_fun (continuous_present.measurable.comp measurable_snd) measurable_const).inter
        (measurableSet_eq_fun (continuous_bid.measurable.comp measurable_snd) measurable_const)).compl))
  have hSae : ∀ᵐz ∂(ν₀.1 : Measure (Value W × FloorAction 0 W)),z∈S := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzerotype,
      measure_eq_zero_iff_ae_notMem.mp hinactive,measure_eq_zero_iff_ae_notMem.mp hzero] with z hz0 hzi hzb
    exact ⟨hz0,hzi,hzb⟩
  rw [←hdis] at hSae
  have hSdis := (Measure.ae_compProd_iff hS).mp hSae
  filter_upwards [hSdis] with w hw
  filter_upwards [hw] with a ha
  have hpres : w.1=0 ↔ present a=false := by
    constructor
    · intro hz
      cases hp : present a with
      | false => rfl
      | true => exact False.elim (ha.1 ⟨hz,hp⟩)
    · intro hp
      by_contra hz
      exact ha.2.1 ⟨lt_of_le_of_ne w.2.1 (Ne.symm hz),hp⟩
  refine ⟨hpres,?_⟩
  intro hp
  have hb0 : 0≤bid a := (floor_bid_bounds le_rfl hW.le a).1
  have hbne : bid a≠0 := fun hb=>ha.2.2 ⟨hp,hb⟩
  exact lt_of_le_of_ne hb0 (Ne.symm hbne)

end FCAppendix.Existence.PayOnceBounded
