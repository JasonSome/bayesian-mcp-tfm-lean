import FCAppendix.Affine.Uniform07Finishing.Native.SourceBroadcastIC
import FCAppendix.Affine.Uniform07Finishing.Native.FinalApplication

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative Weighted ConditionalSuccess Crossover.Physical

structure UniformPhysicalLowerData05 where
  start : ℕ
  start_ge_two : 2≤ start
  market : (row : Uniform07.Row)→(k : ℕ)→ UniformMarketData row (start+k)
  auxiliary_floor : ∀ row k, (market row k).R=sourceLowerPriceCeiling row
  lower_no_overbid : ∀ row k, ∀ᵐ x ∂((market row k).lower : Measure (ℝ×JointAction 2)),
    x.2.bid≤ x.1
  lower_floor : ∀ row k, ∀ᵐ x ∂((market row k).lower : Measure (ℝ×JointAction 2)),
    Early.lowerFloor row x.1≤ x.2.bid
  rejection_root : ∀ row k, (52/100:ℝ)*Uniform07.cutoff row<(market row k).z
  fixed_guard_margin : Uniform07.Row→ℝ
  fixed_guard_margin_positive : ∀ row, 0< fixed_guard_margin row
  guard_margin_eq : ∀ row k, (market row k).guardMargin=fixed_guard_margin row
  reference : ∀ _row k, Fin (start+k)
  physical_broadcast : ∀ row k,
    ∀ᵐ x ∂((market row k).lower : Measure (ℝ×JointAction 2)), ∀ a : JointAction 2,
      0< a.bid → a.routeCount=2 → a.bid<(market row k).R →
      @literalSourceBroadcastUtility (start+k) (market row k).fin_nonempty row
        (market row k).capacity_positive (market row k).R (market row k).Λ
        (market row k).z (market row k).width (market row k).guardMargin
        (market row k).lower (reference row k) x.1 a≤
      @literalSourceBroadcastUtility (start+k) (market row k).fin_nonempty row
        (market row k).capacity_positive (market row k).R (market row k).Λ
        (market row k).z (market row k).width (market row k).guardMargin
        (market row k).lower (reference row k) x.1 x.2
  guard_constant : Uniform07.Row→ℝ
  guard_rate : Uniform07.Row→ℝ
  guard_constant_nonnegative : ∀ row, 0≤ guard_constant row
  guard_rate_positive : ∀ row, 0< guard_rate row
  scalar_concentration : ∀ row, ∀ᶠ k in atTop,
    ∀ u : Fin (start+k), ∀ a : JointAction 2, a.bid<(market row k).R →
    ∀ τ : Equiv.Perm (Fin 2), ∀ j : Fin 2, ∀ l : Fin 5,
      (userProfileLaw (market row k).native).real
        (sourceScalarGuardFailure row (market row k).R (market row k).Λ
          (market row k).z (market row k).width (market row k).guardMargin u a τ j l)≤
            guard_constant row*Real.exp (-guard_rate row*((start+k:ℕ):ℝ))

theorem UniformPhysicalLowerData05.native_broadcast
    (P : UniformPhysicalLowerData05) (row : Uniform07.Row) (k : ℕ) :
    ∀ᵐ x ∂((P.market row k).lower : Measure (ℝ×JointAction 2)),
      ∀ u : Fin (P.start+k), ∀ a : JointAction 2,
        a.routeCount=2 → a.bid<(P.market row k).R →
          (problem (P.market row k).native u).payoff x.1 a≤
            (problem (P.market row k).native u).payoff x.1 x.2 := by
  let M:=P.market row k
  letI : Nonempty (Fin (P.start+k)):=M.fin_nonempty
  have hguard : Uniform07.kappa row*M.R< M.Λ-Early.nativeRadius row := by
    have hg:=(source_auxiliary_floor_guards row).2.2.2
    have hR:M.R=sourceLowerPriceCeiling row:=P.auxiliary_floor row k
    rw [hR]
    have hΛ:=M.multiplier_lower
    have h54 : (54/100:ℝ)=27/50 := by norm_num
    rw [h54] at hΛ
    linarith
  have hz : Uniform07.cutoff row/2≤ M.z := by
    have hh:=P.rejection_root row k
    have ht:=Uniform07.cutoff_pos row
    linarith
  have h:=literalSourceNativeGame_common_broadcast_IC_of_physical row M.market_ge_two
    M.capacity_positive M.floor_positive M.cap_lt_floor M.floor_lt_cutoff M.multiplier_lower
    hguard hz M.guard_margin_positive M.lower M.lower_value M.lower_routes M.lower_atomless
    (P.reference row k) (P.physical_broadcast row k)
  simpa only [literalSourceNativeGame,completeSourceNativeGame_payoff,UniformMarketData.native]
    using h

def UniformPhysicalLowerData05.toAuxiliary (P : UniformPhysicalLowerData05) :
    UniformAuxiliaryData05 where
  start:=P.start
  start_ge_two:=P.start_ge_two
  market:=P.market
  auxiliary_floor:=P.auxiliary_floor
  lower_no_overbid:=P.lower_no_overbid
  lower_floor:=P.lower_floor
  rejection_root:=P.rejection_root
  fixed_guard_margin:=P.fixed_guard_margin
  fixed_guard_margin_positive:=P.fixed_guard_margin_positive
  guard_margin_eq:=P.guard_margin_eq
  lower_broadcast:=P.native_broadcast
  guard_constant:=P.guard_constant
  guard_rate:=P.guard_rate
  guard_constant_nonnegative:=P.guard_constant_nonnegative
  guard_rate_positive:=P.guard_rate_positive
  scalar_concentration:=P.scalar_concentration

def uniform_native_pair_from_physical_lower_producers
    (P : UniformPhysicalLowerData05) (K : UniformAuxiliaryKernels05_06 P.toAuxiliary) :
    UniformNativePair :=
  uniform_native_pair_from_lower_producers P.toAuxiliary K

theorem aff_uniform_result_from_physical_lower_producers
    (P : UniformPhysicalLowerData05) (K : UniformAuxiliaryKernels05_06 P.toAuxiliary) :
    AffUniformResult :=
  aff_uniform_result_from_lower_producers P.toAuxiliary K

end FCAppendix.Affine.Uniform07Finishing
