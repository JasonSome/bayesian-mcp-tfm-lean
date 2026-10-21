import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05CompactJoint
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapIC
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05ScalarGuard
import FCAppendix.Affine.Uniform07Finishing.Native.ZeroBroadcastDomination

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover.Physical

theorem eventual_native_broadcast_all (row : Uniform07.Row) :
    ∀ᶠ M : ℕ in atTop,
      ∀W : UniformFinite.NativeFiniteLowerConstruction row M (sourceLowerPriceCeiling row),
      ∀hc : 1≤ Uniform07.capacity M,
      ∀ᵐx∂(Concrete05.lowerJoint W.finite.restricted : Measure (ℝ×JointAction 2)),
        ∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ A.bid< sourceLowerPriceCeiling row→
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 A≤
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 x.2 := by
  filter_upwards [Concrete05.eventual_native_broadcast row] with M hM
  intro W hc
  let E:=W.finite.restricted
  letI : NeZero M:=E.marketNeZero
  letI : Nonempty (Fin M):=inferInstance
  let ε:=UniformFinite.Source.commonGuardMargin row
  let Γ:=literalSourceNativeGame row hc (sourceLowerPriceCeiling row) E.law.multiplier
    E.law.rejectionRoot (10*ε) ε (Concrete05.multiplier_lower E) (Concrete05.lowerJoint E)
  let reference : Fin M:=⟨0,by have hh:=E.cluster.market_two_le; omega⟩
  have hG:=source_auxiliary_floor_guards row
  have hz : Uniform07.cutoff row/2≤ E.law.rejectionRoot := by
    have hz':=(Concrete05.rejection_root_bounds E).1
    have ht:=Uniform07.cutoff_pos row
    linarith
  have heq (i : Fin M) (v : ℝ) (A : JointAction 2) :
      (problem Γ i).payoff v A=
        (problem (Concrete05.exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v A := by
    have hgame : sourceNativeGame row hc (sourceLowerPriceCeiling row) E.law.multiplier
        (source_guard_multiplier_positive row (Concrete05.multiplier_lower E))
        (Concrete05.lowerJoint E)
        (literalSourceAlpha row E.law.multiplier E.law.rejectionRoot (10*ε) ε)
        (measurable_literalSourceAlpha row (Concrete05.multiplier_lower E)
          E.law.rejectionRoot (10*ε) ε)=
        Concrete05.exactNativeGame E hc (sourceLowerPriceCeiling row) := by
      rfl
    unfold Γ literalSourceNativeGame
    rw [completeSourceNativeGame_payoff,hgame]
  have hpos : ∀ᵐx∂(Concrete05.lowerJoint E : Measure (ℝ×JointAction 2)),∀A : JointAction 2,
      0< A.bid→ A.routeCount=2→ A.bid< sourceLowerPriceCeiling row→
      (problem Γ reference).payoff x.1 A≤(problem Γ reference).payoff x.1 x.2 := by
    filter_upwards [hM W hc] with x hx
    intro A hA h2 hR
    rw [heq,heq]
    exact hx reference A h2 hA hR
  have hfull : ∀ᵐx∂(Concrete05.lowerJoint E : Measure (ℝ×JointAction 2)),
      ∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ A.bid<sourceLowerPriceCeiling row→
        (problem Γ i).payoff x.1 A≤(problem Γ i).payoff x.1 x.2 :=
    literalSourceNativeGame_common_broadcast_IC_of_positive_reference
    (width:=10*ε)
    row E.cluster.market_two_le hc hG.1 hG.2.1 hG.2.2.1 (Concrete05.multiplier_lower E)
    (Concrete05.auxiliary_guard row E.law) hz (UniformFinite.Source.common_guard_margin row)
    (Concrete05.lowerJoint E) (Concrete05.lowerJoint_value E) (Concrete05.lowerJoint_routes E)
    (Concrete05.lowerJoint_atomless E) reference hpos
  filter_upwards [hfull] with x hx
  intro i A h2 hR
  rw [←heq i x.1 A,←heq i x.1 x.2]
  exact hx i A h2 hR

structure BroadcastLowerFamily extends ReadyLowerFamily where
  broadcast : ∀row k,∀ᵐx∂((toReadyLowerFamily.market row k).lower : Measure (ℝ×JointAction 2)),
    ∀i : Fin (start+k),∀A : JointAction 2,A.routeCount=2→ A.bid<(toReadyLowerFamily.market row k).R→
      (problem (toReadyLowerFamily.market row k).native i).payoff x.1 A≤
        (problem (toReadyLowerFamily.market row k).native i).payoff x.1 x.2

theorem exists_broadcast_lower_family : Nonempty BroadcastLowerFamily := by
  have hrow (row : Uniform07.Row) : ∀ᶠ M : ℕ in atTop,
      Nonempty (UniformFinite.NativeFiniteLowerConstruction row M (sourceLowerPriceCeiling row)) ∧
      (∀E : UniformFinite.ExactRestrictedLaw row M,readyPredicate row M E) ∧
      (∀W : UniformFinite.NativeFiniteLowerConstruction row M (sourceLowerPriceCeiling row),
        ∀hc : 1≤ Uniform07.capacity M,
        ∀ᵐx∂(Concrete05.lowerJoint W.finite.restricted : Measure (ℝ×JointAction 2)),
        ∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ A.bid< sourceLowerPriceCeiling row→
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 A≤
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 x.2) := by
    obtain ⟨N,hN⟩:=UniformFinite.exists_eventual_uniform_lower_construction row
    filter_upwards [eventually_ge_atTop N,eventually_ready row,eventual_native_broadcast_all row]
      with M hM hr hb
    refine ⟨hN M hM _ ?_,hr,hb⟩
    rw [Concrete05.cap_eq]
    exact (source_auxiliary_floor_guards row).2.1
  have hboth := (hrow Uniform07.Row.first).and (hrow Uniform07.Row.second)
  obtain ⟨N,hN⟩:=eventually_atTop.mp hboth
  let start:=max 3 N
  have htail (k : ℕ) (row : Uniform07.Row) :
      Nonempty (UniformFinite.NativeFiniteLowerConstruction row (start+k) (sourceLowerPriceCeiling row)) ∧
      (∀E : UniformFinite.ExactRestrictedLaw row (start+k),readyPredicate row (start+k) E) ∧
      (∀W : UniformFinite.NativeFiniteLowerConstruction row (start+k) (sourceLowerPriceCeiling row),
        ∀hc : 1≤ Uniform07.capacity (start+k),
        ∀ᵐx∂(Concrete05.lowerJoint W.finite.restricted : Measure (ℝ×JointAction 2)),
        ∀i : Fin (start+k),∀A : JointAction 2,A.routeCount=2→ A.bid< sourceLowerPriceCeiling row→
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 A≤
          (problem (Concrete05.exactNativeGame W.finite.restricted hc
            (sourceLowerPriceCeiling row)) i).payoff x.1 x.2) := by
    have h:=hN (start+k) (by dsimp [start]; omega)
    cases row
    · exact h.1
    · exact h.2
  let W (row : Uniform07.Row) (k : ℕ):=Classical.choice (htail k row).1
  let F : ReadyLowerFamily:={
    start:=start
    start_ge_three:=le_max_left _ _
    construction:=W
    ready:=fun row k=>(htail k row).2.1 (W row k).finite.restricted }
  refine ⟨{toReadyLowerFamily:=F,broadcast:=?_}⟩
  intro row k
  exact (htail k row).2.2 (W row k) (F.market row k).capacity_positive

def broadcastLowerFamily : BroadcastLowerFamily:=Classical.choice exists_broadcast_lower_family

namespace ReadyLowerFamily

theorem scalar_concentration (F : ReadyLowerFamily) (row : Uniform07.Row) :
    ∀ᶠ k in atTop,∀u : Fin (F.start+k),∀a : JointAction 2,a.bid<(F.market row k).R→
    ∀τ : Equiv.Perm (Fin 2),∀j : Fin 2,∀l : Fin 5,
      (userProfileLaw (F.market row k).native).real
        (sourceScalarGuardFailure row (F.market row k).R (F.market row k).Λ
          (F.market row k).z (F.market row k).width (F.market row k).guardMargin u a τ j l)≤
      18*Real.exp (-((UniformFinite.Source.commonGuardMargin row)^2/2)*((F.start+k:ℕ):ℝ)) := by
  have hsize : ∀ᶠ k in atTop,
      2/((F.start+k:ℕ):ℝ)≤ UniformFinite.Source.commonGuardMargin row :=
    ((tendsto_const_div_atTop_nhds_zero_nat (2:ℝ)).comp
      (tail_population_tendsto F.start)).eventually
        (Iic_mem_nhds (UniformFinite.Source.common_guard_margin row))
  filter_upwards [hsize] with k hk
  let M:=F.market row k
  letI : Nonempty (Fin (F.start+k)):=M.fin_nonempty
  intro u a ha τ j l
  have hG:=source_auxiliary_floor_guards row
  have h:=Concrete05.native_scalar_guard_failure_le row (F.law row k).1 M.capacity_positive
    hG.1 hG.2.1 hG.2.2.1 hk u a ha τ j l
  convert h using 1
  congr 2
  rw [show -(UniformFinite.Source.commonGuardMargin row^2/2)*((F.start+k:ℕ):ℝ)=
    -((F.start+k:ℕ):ℝ)*UniformFinite.Source.commonGuardMargin row^2/2 by ring]

end ReadyLowerFamily

def BroadcastLowerFamily.toAuxiliaryData (F : BroadcastLowerFamily) : UniformAuxiliaryData05 where
  start:=F.start
  start_ge_two:=by have hh:=F.start_ge_three; omega
  market:=F.toReadyLowerFamily.market
  auxiliary_floor:=fun _ _=>rfl
  lower_no_overbid:=F.toReadyLowerFamily.toLowerFamily.market_no_overbid
  lower_floor:=F.toReadyLowerFamily.toLowerFamily.market_lower_floor
  rejection_root:=F.toReadyLowerFamily.toLowerFamily.market_rejection_root
  fixed_guard_margin:=UniformFinite.Source.commonGuardMargin
  fixed_guard_margin_positive:=UniformFinite.Source.common_guard_margin
  guard_margin_eq:=fun _ _=>rfl
  lower_broadcast:=F.broadcast
  guard_constant:=fun _=>18
  guard_rate:=fun row=>(UniformFinite.Source.commonGuardMargin row)^2/2
  guard_constant_nonnegative:=fun _=>by norm_num
  guard_rate_positive:=fun row=>by have hh:=UniformFinite.Source.common_guard_margin row; positivity
  scalar_concentration:=F.toReadyLowerFamily.scalar_concentration

def auxiliaryData : UniformAuxiliaryData05:=broadcastLowerFamily.toAuxiliaryData

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
