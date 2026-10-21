import FCAppendix.Affine.Tail04.CoefficientOneEarly
import FCAppendix.Affine.Tail04.OriginalFixedConditional
import FCAppendix.Affine.Tail04.FeasibleListNormalization
import FCAppendix.PayOnce.KernelAgreement

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open Existence.RankEnvelope OriginalValues

structure BoundedRow {P : ValueParameters} (p : ScalarInput P) (m : ℕ) where
  C : Hybrid.ContextPolicy m (marketCapacity m) unitInterval
  PL : ProbabilityMeasure (ℝ×JointAction 2)
  PA : ProbabilityMeasure (ℝ×JointAction 2)
  PH0 : ProbabilityMeasure (ℝ×JointAction 2)
  low_value : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalLowLaw.map Subtype.val
  active_value : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=P.originalPartialLaw.map Subtype.val
  low_shape : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ p.U ∧ x.2.routeCount=2
  active_shape : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ p.U ∧ x.2.routeCount=2
  upper_shape : ∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), p.R≤ x.2.bid ∧ x.2.routeCount=1
  upper_bounded : ∃ H : ℝ,∀ᵐ x ∂(PH0 : Measure (ℝ×JointAction 2)), x.1∈Icc (P.vA-P.w) H

  low_atomless : ∀ y : ℝ,(PL : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0
  active_atomless : ∀ y : ℝ,(PA : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0
  upper_atomless : ∀ y : ℝ,(PH0 : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0
  error : ℝ
  error_nonnegative : 0≤ error

namespace BoundedRow
variable {P : ValueParameters} {p : ScalarInput P} {m : ℕ} (d : BoundedRow p m)

def reference : FiniteGame m 2 (marketCapacity m) unitInterval :=
  P.originalFixedReference d.C p.U p.R d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0

theorem low_closed : ∀ᵐ x ∂(d.PL : Measure (ℝ×JointAction 2)), x.2.bid< p.R ∧ x.2.routeCount=2 :=
  d.low_shape.mono (fun _ hx => ⟨hx.1.trans_lt p.cap_below_floor,hx.2⟩)
theorem active_closed : ∀ᵐ x ∂(d.PA : Measure (ℝ×JointAction 2)), x.2.bid< p.R ∧ x.2.routeCount=2 :=
  d.active_shape.mono (fun _ hx => ⟨hx.1.trans_lt p.cap_below_floor,hx.2⟩)

def referencePosterior : PosteriorSystem d.reference :=
  ClosedUpperPriority.closedPosterior _ p.R
    (P.originalFixedReference_closedProfiles d.C p.U p.R d.PL d.PA p.eta p.eta_pos.le
      p.eta_lt_one d.PH0 d.low_closed d.active_closed d.upper_shape)

def original (hm : 200≤ m) : FiniteGame m 2 (marketCapacity m) unitInterval :=
  P.originalFixedConditionalGame hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
    p.eta p.eta_pos.le p.eta_lt_one d.PH0

def normalized (hm : 200≤ m) : FiniteGame m 2 (marketCapacity m) unitInterval :=
  FeasibleListNormalization.game (d.original hm)

end BoundedRow

structure BoundedProof {P : ValueParameters} {p : ScalarInput P} {m : ℕ}
    (d : BoundedRow p m) : Prop where
  low_kernel : (P.originalLowLaw.map Subtype.val)⊗ₘd.reference.σ=(d.PL : Measure (ℝ×JointAction 2))
  active_kernel : (P.originalPartialLaw.map Subtype.val)⊗ₘd.reference.σ=(d.PA : Measure (ℝ×JointAction 2))
  low_joint_BR : ∀ i,∀ᵐ x ∂(d.PL : Measure (ℝ×JointAction 2)),
    (problem d.reference i).BestResponse x.1 x.2
  active_joint_BR : ∀ i,∀ᵐ x ∂(d.PA : Measure (ℝ×JointAction 2)),
    (problem d.reference i).BestResponse x.1 x.2
  lower_success : ∀ (i : Fin m) (act : JointAction 2),act.bid< p.R →
    ((problem d.reference i).outcome act).success≤1-p.rho+d.error
  lower_kernel_support : ∀ v∈lowerValues P,∀ᵐ act ∂d.reference.σ v,act.bid< p.R
  proposers : ∀ j L,FeasibleObservedList j L → ∀ s,
    Finite.Optimal (marketCapacity m)
      (beliefReceipts d.reference.A (posteriorCountBelief d.reference d.referencePosterior j L) L)
      (d.reference.policy j L s).val

structure BoundedFamily {P : ValueParameters} (p : ScalarInput P) where
  N : ℕ → ℕ
  cofinal : Tendsto N atTop atTop
  large : ∀ k,200≤ N k
  row : ∀ k,BoundedRow p (N k)
  proofs : ∀ k,BoundedProof (row k)
  errors_vanish : Tendsto (fun k => (row k).error) atTop (𝓝 0)
  lowerLimit : ℝ → CountLaw 2
  lower_count_limits : ∀ v∈lowerValues P,∀ f : Fin 3 → ℝ,
    Tendsto (fun k => (conditionalTypeCountLaw (row k).reference
      (by have := large k;omega) v).expect f) atTop (𝓝 ((lowerLimit v).expect f))

namespace BoundedRow
variable {P : ValueParameters} {p : ScalarInput P} {m : ℕ}
  (d : BoundedRow p m) (hd : BoundedProof d) (hm : 200≤ m)

def finiteGuards : Prop :=
  Existence.RankEnvelope.error (rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2) (P.vA-P.w) p.R<
    p.eta*p.R*(1-2*(1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w))) ∧
  1-p.rho+d.error< rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w) ∧
  (P.vA-P.w)*(1-p.rho+d.error)≤
    (P.vA-P.w-p.R)*rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w)

theorem raw_joint_BR_of_bounds
    (hLBR : ∀ i,∀ᵐ x ∂(d.PL : Measure (ℝ×JointAction 2)),
      (problem d.reference i).BestResponse x.1 x.2)
    (hABR : ∀ i,∀ᵐ x ∂(d.PA : Measure (ℝ×JointAction 2)),
      (problem d.reference i).BestResponse x.1 x.2)
    (hSuccess : ∀ (i : Fin m) (act : JointAction 2),act.bid < p.R →
      ((problem d.reference i).outcome act).success ≤ 1-p.rho+d.error)
    (hg : d.finiteGuards) (i : Fin m) :
    ∀ᵐ x ∂Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      d.PL d.PA (P.originalFixedUpperJoint m hm p.R p.floor_pos p.floor_below_upper),
    (problem (P.originalFixedGame hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
      p.eta p.eta_pos.le p.eta_lt_one) i).BestResponse x.1 x.2 := by
  let G := P.originalFixedGame hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
    p.eta p.eta_pos.le p.eta_lt_one
  have hLcap := d.low_shape.mono (fun _ hx => hx.1)
  have hAcap := d.active_shape.mono (fun _ hx => hx.1)
  have hvalL : ∀ᵐ x ∂(d.PL : Measure (ℝ×JointAction 2)),x.1≤ P.d0 := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Iic).mp
    rw [d.low_value]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hvalA : ∀ᵐ x ∂(d.PA : Measure (ℝ×JointAction 2)),x.1≤2+P.w := by
    apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Iic).mp
    rw [d.active_value]
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Iic).mpr
    exact Eventually.of_forall (fun v => v.property.2)
  have hL : ∀ᵐ x ∂(d.PL : Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2 := by
    filter_upwards [hLBR i,d.low_closed,hvalL] with x hx hb hv
    exact P.originalFixed_lower_bestResponse_of_reference hm d.C p.U p.R p.floor_pos
      p.floor_below_upper d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one p.cap_below_floor
      hLcap hAcap d.PH0 d.upper_shape d.upper_atomless hg.1 i x.1
      (by linarith [P.low_partial_gap,P.partial_active_gap,P.w_pos]) x.2 hb.1 hx
  have hA : ∀ᵐ x ∂(d.PA : Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2 := by
    filter_upwards [hABR i,d.active_closed,hvalA] with x hx hb hv
    exact P.originalFixed_lower_bestResponse_of_reference hm d.C p.U p.R p.floor_pos
      p.floor_below_upper d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one p.cap_below_floor
      hLcap hAcap d.PH0 d.upper_shape d.upper_atomless hg.1 i x.1
      (hv.trans P.partial_active_gap.le) x.2 hb.1 hx
  have hboundary : ∀ (j : Fin m) (act : JointAction 2),act.bid< p.R →
      (problem d.reference j).payoff (P.vA-P.w) act≤
        (P.vA-P.w-p.R)*rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 (P.vA-P.w) := by
    intro j act ha
    have hu := ((problem d.reference j).outcome act).utility_le_bid_net_success
      (P.vA-P.w) act.bid 0 d.reference.A d.reference.G act.bid_nonneg le_rfl
    change (problem d.reference j).payoff (P.vA-P.w) act≤
      (P.vA-P.w-0-act.bid)*((problem d.reference j).outcome act).success at hu
    have hs := mul_le_mul_of_nonneg_left (hSuccess j act ha) P.fixedUpperBase_pos.le
    have hn := mul_nonneg act.bid_nonneg ((problem d.reference j).outcome act).success_nonneg
    linarith [hg.2.2]
  have hH : ∀ᵐ x ∂(P.originalFixedUpperJoint m hm p.R p.floor_pos p.floor_below_upper :
      Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2 := by
    filter_upwards [P.originalFixedUpperJoint_graph m hm p.R p.floor_pos p.floor_below_upper] with x hx
    rw [hx.2]
    exact P.originalFixed_upper_bestResponse hm d.C p.U p.R p.floor_pos p.floor_below_upper
      d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one p.cap_below_floor hLcap hAcap d.PH0
      d.upper_shape (1-p.rho+d.error) hg.2.1 hboundary hSuccess hg.1 i x.1 hx.1
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hL _,Measure.ae_smul_measure hA _⟩,Measure.ae_smul_measure hH _⟩

include hd in
theorem raw_joint_BR (hg : d.finiteGuards) (i : Fin m) :
    ∀ᵐ x ∂Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta)
      d.PL d.PA (P.originalFixedUpperJoint m hm p.R p.floor_pos p.floor_below_upper),
    (problem (P.originalFixedGame hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
      p.eta p.eta_pos.le p.eta_lt_one) i).BestResponse x.1 x.2 :=
  d.raw_joint_BR_of_bounds hm hd.low_joint_BR hd.active_joint_BR hd.lower_success hg i

include hd in
theorem original_users (hg : d.finiteGuards) : UsersOptimal (d.original hm) := by
  intro i
  apply Measure.ae_ae_of_ae_compProd
    (p := fun x : ℝ × JointAction 2 => (problem (d.original hm) i).BestResponse x.1 x.2)
  unfold BoundedRow.original
  rw [P.originalFixedConditionalGame_joint hm d.C p.U p.R p.floor_pos p.floor_below_upper
    d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel]
  simp_rw [P.originalFixedConditionalGame_problem hm d.C p.U p.R p.floor_pos p.floor_below_upper
    d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel]
  exact d.raw_joint_BR hd hm hg i

def originalPosterior : PosteriorSystem (d.original hm) :=
  ConditionalVersions.withStrategy_posterior _ _
    (P.originalFixedConditionalGame_kernel_ae hm d.C p.U p.R p.floor_pos p.floor_below_upper
      d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel)
    (P.originalFixedPosterior hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
      p.eta p.eta_pos.le p.eta_lt_one d.low_closed d.active_closed)

theorem original_proposers : ∀ j L,FeasibleObservedList j L → ∀ s,
    Finite.Optimal (marketCapacity m)
      (beliefReceipts (d.original hm).A
        (posteriorCountBelief (d.original hm) (d.originalPosterior hd hm) j L) L)
      ((d.original hm).policy j L s).val := by
  exact P.originalFixedGame_feasible_proposers_transfer hm d.C p.U p.R p.floor_pos p.floor_below_upper
    d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_closed d.active_closed d.upper_shape hd.proposers

include hd in
theorem normalized_equilibrium (hg : d.finiteGuards) : IsBayesianEquilibrium (d.normalized hm) :=
  FeasibleListNormalization.equilibrium _ (d.original_users hd hm hg)
    (d.originalPosterior hd hm) (d.original_proposers hd hm)

theorem normalized_value : (d.normalized hm).F=valueLaw P :=
  P.originalFixedConditionalGame_value hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
    p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value

include hd in
theorem normalized_joint :
    (d.normalized hm).F⊗ₘ(d.normalized hm).σ=
      Hybrid.populationJoint (lowMass P.theta) partialMass (activeMass P.theta) d.PL d.PA
        (P.originalFixedUpperJoint m hm p.R p.floor_pos p.floor_below_upper) :=
  P.originalFixedConditionalGame_joint hm d.C p.U p.R p.floor_pos p.floor_below_upper d.PL d.PA
    p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel

include hd in
theorem normalized_joint_bid_atomless (y : ℝ) :
    ((d.normalized hm).F⊗ₘ(d.normalized hm).σ) {x | x.2.bid=y}=0 := by
  rw [d.normalized_joint hd hm]
  have hH := (P.originalFixedUpperJoint_properties m hm p.R p.floor_pos
    p.floor_below_upper).2.2.2 y
  simp only [Hybrid.populationJoint,Measure.add_apply,Measure.smul_apply,
    smul_eq_mul,d.low_atomless y,d.active_atomless y,hH,mul_zero,zero_add]

include hd in
theorem normalized_bid_atomless : NullSingletonClass (Bayes.realBidLaw (d.normalized hm)) := by
  refine ⟨fun y => ?_⟩
  rw [Bayes.realBidLaw_eq_action_map,Measure.map_apply
    (show Measurable (fun x : ℝ × JointAction 2 => x.2.bid) from
      (measurable_bid 2).comp measurable_snd) (measurableSet_singleton y)]
  exact d.normalized_joint_bid_atomless hd hm y

include hd in
theorem normalized_visible_atomless : VisibleAtomless (d.normalized hm) := by
  intro j y
  have hz : userLaw (d.normalized hm) {z : UserDraw 2 | z.1.2.bid=y}=0 := by
    have he : {z : UserDraw 2 | z.1.2.bid=y}=
        {x : ℝ×JointAction 2 | x.2.bid=y}×ˢuniv := by
      ext z
      simp
    rw [he,userLaw,Measure.prod_prod,d.normalized_joint_bid_atomless hd hm y,zero_mul]
  exact measure_mono_null (fun _ hx => hx.2) hz

include hd in
theorem normalized_lower_count (v : ℝ) (hv : v∈lowerValues P) :
    conditionalTypeCountLaw (d.normalized hm) (by omega) v=
      conditionalTypeCountLaw d.reference (by omega) v := by
  rw [normalized,FeasibleListNormalization.conditionalCount_eq]
  exact P.originalFixedConditionalGame_lower_law hm d.C p.U p.R p.floor_pos p.floor_below_upper
    d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel
    d.upper_shape v (lowerValues_below v hv) (hd.lower_kernel_support v hv)

include hd in
theorem normalized_upper_expect (v : ℝ) (hv : P.vA-P.w≤ v) (f : Fin 3 → ℝ) :
    (conditionalTypeCountLaw (d.normalized hm) (by omega) v).expect f=
      (1-rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v)*f 0+
        rank P.fixedUpperMeasure (m-1) (marketCapacity m) 2 v*f 1 := by
  rw [normalized,FeasibleListNormalization.conditionalCount_eq]
  exact P.originalFixedConditionalGame_upper_expect hm d.C p.U p.R p.floor_pos p.floor_below_upper
    d.PL d.PA p.eta p.eta_pos.le p.eta_lt_one d.PH0 d.low_value d.active_value hd.low_kernel hd.active_kernel
    p.cap_below_floor (d.low_shape.mono (fun _ hx => hx.1))
    (d.active_shape.mono (fun _ hx => hx.1)) v hv f

end BoundedRow

namespace BoundedFamily
variable {P : ValueParameters} {p : ScalarInput P} (D : BoundedFamily p)

theorem eventually_finiteGuards : ∀ᶠ k in atTop,(D.row k).finiteGuards := by
  let q := fun k => rank P.fixedUpperMeasure (D.N k-1) (marketCapacity (D.N k)) 2 (P.vA-P.w)
  have hq : Tendsto q atTop (𝓝 1) :=
    (original_fixed_rank_tendsto_one P.fixedUpperMeasure P.fixedUpperMeasure_mass_small (P.vA-P.w)).comp D.cofinal
  have hE := (original_fixed_error_tendsto_zero P.fixedUpperMeasure P.fixedUpperMeasure_mass_small
    (P.vA-P.w) p.R P.M (activeMass P.theta*P.zeta) P.fixedUpperBase_pos p.floor_below_upper.le
    P.fixedUpperBase_le_tail P.original_tail_weight_bounds P.fixedUpperMeasure_tail).comp D.cofinal
  have hhidden : Tendsto (fun k => p.eta*p.R*(1-2*(1-q k))-
      Existence.RankEnvelope.error (rank P.fixedUpperMeasure (D.N k-1) (marketCapacity (D.N k)) 2) (P.vA-P.w) p.R)
      atTop (𝓝 (p.eta*p.R)) := by
    convert! ((tendsto_const_nhds (x:=p.eta*p.R)).mul
      ((tendsto_const_nhds (x:=(1:ℝ))).sub
        ((tendsto_const_nhds (x:=(2:ℝ))).mul ((tendsto_const_nhds (x:=(1:ℝ))).sub hq)))).sub hE using 1
    norm_num
  have hslope : Tendsto (fun k => q k-(1-p.rho+(D.row k).error)) atTop (𝓝 p.rho) := by
    convert! hq.sub ((tendsto_const_nhds (x:=1-p.rho)).add D.errors_vanish) using 1
    ring
  have hboundary : Tendsto (fun k => (P.vA-P.w-p.R)*q k-
      (P.vA-P.w)*(1-p.rho+(D.row k).error)) atTop (𝓝 ((P.vA-P.w)*p.rho-p.R)) := by
    convert! ((tendsto_const_nhds (x:=P.vA-P.w-p.R)).mul hq).sub
      ((tendsto_const_nhds (x:=P.vA-P.w)).mul
        ((tendsto_const_nhds (x:=1-p.rho)).add D.errors_vanish)) using 1
    ring
  filter_upwards [hhidden.eventually (Ioi_mem_nhds (mul_pos p.eta_pos p.floor_pos)),
    hslope.eventually (Ioi_mem_nhds p.rho_pos),
    hboundary.eventually (Ioi_mem_nhds (sub_pos.mpr p.upper_gap_rho))] with k hh hs hb
  change Existence.RankEnvelope.error
    (rank P.fixedUpperMeasure (D.N k-1) (marketCapacity (D.N k)) 2) (P.vA-P.w) p.R<
      p.eta*p.R*(1-2*(1-q k)) ∧
    1-p.rho+(D.row k).error< q k ∧
    (P.vA-P.w)*(1-p.rho+(D.row k).error)≤(P.vA-P.w-p.R)*q k
  exact ⟨by linarith,by linarith,by linarith⟩

theorem original_family :
    ∃ (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hN200 : ∀ k,200≤ N k)
      (Γ : ∀ k,FiniteGame (N k) 2 (marketCapacity (N k)) unitInterval),
      (∀ k,(Γ k).F=valueLaw P ∧ (Γ k).g=0 ∧
        (Γ k).A=Schedule.affine 2 p.eta p.eta_pos.le p.eta_lt_one.le ∧
        IsBayesianEquilibrium (Γ k) ∧
        NullSingletonClass (Bayes.realBidLaw (Γ k)) ∧ VisibleAtomless (Γ k)) ∧
      (∀ v∈lowerValues P,∀ f : Fin 3 → ℝ,
        Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f)
          atTop (𝓝 ((D.lowerLimit v).expect f))) ∧
      (∀ v,P.vA-P.w≤ v → ∀ f : Fin 3 → ℝ,
        Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f)
          atTop (𝓝 (f 1))) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp D.eventually_finiteGuards
  let N := fun k => D.N (K+k)
  have hshift : Tendsto (fun k : ℕ => K+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k K) tendsto_id
  have hN : Tendsto N atTop atTop := D.cofinal.comp hshift
  have hlarge : ∀ k,200≤ N k := fun k => D.large (K+k)
  let Γ := fun k => (D.row (K+k)).normalized (D.large (K+k))
  refine ⟨N,hN,hlarge,Γ,?_,?_,?_⟩
  · intro k
    exact ⟨(D.row (K+k)).normalized_value (D.large (K+k)),rfl,rfl,
      (D.row (K+k)).normalized_equilibrium (D.proofs (K+k)) (D.large (K+k)) (hK _ (Nat.le_add_right K k)),
      (D.row (K+k)).normalized_bid_atomless (D.proofs (K+k)) (D.large (K+k)),
      (D.row (K+k)).normalized_visible_atomless (D.proofs (K+k)) (D.large (K+k))⟩
  · intro v hv f
    have he (k : ℕ) := (D.row (K+k)).normalized_lower_count (D.proofs (K+k)) (D.large (K+k)) v hv
    dsimp only [Γ]
    simp_rw [he]
    exact (D.lower_count_limits v hv f).comp hshift
  · intro v hv f
    have he (k : ℕ) := (D.row (K+k)).normalized_upper_expect (D.proofs (K+k)) (D.large (K+k)) v hv f
    dsimp only [Γ]
    simp_rw [he]
    have hq := (original_fixed_rank_tendsto_one P.fixedUpperMeasure P.fixedUpperMeasure_mass_small v).comp hN
    simpa only [sub_self,zero_mul,one_mul,zero_add,Function.comp_def] using
      (((tendsto_const_nhds (x:=(1:ℝ))).sub hq).mul_const (f 0)).add (hq.mul_const (f 1))

end BoundedFamily

theorem from_parametrized_bounded02_producer
    (P : ValueParameters) (X : Type*) (Good : X → Prop)
    (adapt03 : ∀ x,Good x → ScalarInput P)
    (produce02 : ∀ x (hx : Good x),Nonempty (BoundedFamily (adapt03 x hx)))
    (x : X) (hx : Good x) :
    ∃ D : BoundedFamily (adapt03 x hx),
      ∃ (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hN200 : ∀ k,200≤ N k)
        (Γ : ∀ k,FiniteGame (N k) 2 (marketCapacity (N k)) unitInterval),
        (∀ k,(Γ k).F=valueLaw P ∧ (Γ k).g=0 ∧
          (Γ k).A=Schedule.affine 2 (adapt03 x hx).eta
            (adapt03 x hx).eta_pos.le (adapt03 x hx).eta_lt_one.le ∧
          IsBayesianEquilibrium (Γ k) ∧
        NullSingletonClass (Bayes.realBidLaw (Γ k)) ∧ VisibleAtomless (Γ k)) ∧
        (∀ v∈lowerValues P,∀ f : Fin 3 → ℝ,
          Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f)
            atTop (𝓝 ((D.lowerLimit v).expect f))) ∧
        (∀ v,P.vA-P.w≤ v → ∀ f : Fin 3 → ℝ,
          Tendsto (fun k => (conditionalTypeCountLaw (Γ k) (by have := hN200 k;omega) v).expect f)
            atTop (𝓝 (f 1))) := by
  obtain ⟨D⟩ := produce02 x hx
  exact ⟨D,D.original_family⟩

end FCAppendix.Affine.Tail04.CoefficientOne
