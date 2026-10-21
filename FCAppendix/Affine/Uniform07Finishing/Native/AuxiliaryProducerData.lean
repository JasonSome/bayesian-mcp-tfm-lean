import FCAppendix.Affine.Uniform07Finishing.Crossover.NativeFloorTransfer
import FCAppendix.Affine.Uniform07Finishing.Native.SourceSuccessBadEvents
import FCAppendix.Affine.Uniform07Finishing.Native.PositiveBidContinuity

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative ConditionalSuccess
open Crossover.Physical

structure UniformAuxiliaryData05 where
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
  lower_broadcast : ∀ row k, ∀ᵐ x ∂((market row k).lower : Measure (ℝ×JointAction 2)),
    ∀ u : Fin (start+k), ∀ a : JointAction 2, a.routeCount=2 → a.bid<(market row k).R →
      (problem (market row k).native u).payoff x.1 a≤
        (problem (market row k).native u).payoff x.1 x.2
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

structure UniformAuxiliaryKernels05_06 (D : UniformAuxiliaryData05) where
  physical : ∀ row, AuxiliaryLowerData05_06 row (D.market row)

namespace UniformAuxiliaryData05

def population (D : UniformAuxiliaryData05) (k : ℕ) : ℕ := D.start+k

theorem population_tendsto (D : UniformAuxiliaryData05) :
    Tendsto D.population atTop atTop := tail_population_tendsto D.start

theorem positive_bid_continuity (D : UniformAuxiliaryData05)
    (row : Uniform07.Row) (k : ℕ) :
    ∀ u : Fin (D.start+k), ∀ z : ℝ×Icc (0:ℝ) (Early.bidCap row),
      0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem (D.market row k).native u).payoff w.1
          (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z := by
  let M:=D.market row k
  letI : Nonempty (Fin (D.start+k)):=M.fin_nonempty
  have hguard : Uniform07.kappa row*M.R< M.Λ-Early.nativeRadius row := by
    have hg:=(source_auxiliary_floor_guards row).2.2.2
    have hR:M.R=sourceLowerPriceCeiling row:=D.auxiliary_floor row k
    rw [hR]
    have hΛ:=M.multiplier_lower
    have h54 : (54/100:ℝ)=27/50 := by norm_num
    rw [h54] at hΛ
    linarith
  have hzG : Uniform07.cutoff row/2≤ M.z := by
    have hz:=D.rejection_root row k
    have ht:=Uniform07.cutoff_pos row
    linarith
  intro u z hz
  simpa only [UniformMarketData.native] using
    sourceNativeGame_positive_bid_payoff_continuousAt row M.market_ge_two
      M.capacity_positive M.floor_positive M.cap_lt_floor M.floor_lt_cutoff
      M.multiplier_lower hguard hzG M.guard_margin_positive
      M.lower M.lower_value M.lower_routes M.lower_atomless u z hz

theorem exists_auxiliary_boundary (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ) :
    ∃ a : JointAction 2, a.bid≤ Early.bidCap row ∧ a.routeCount=2 ∧
      (∀ u : Fin (D.start+k), ∀ b : JointAction 2, b.routeCount=2 → b.bid<(D.market row k).R →
        (problem (D.market row k).native u).payoff (Uniform07.cutoff row) b≤
          (problem (D.market row k).native u).payoff (Uniform07.cutoff row) a) := by
  let M:=D.market row k
  letI : Nonempty (Fin (D.start+k)):=M.fin_nonempty
  exact sourceNativeGame_exists_boundary_broadcast_best row M.market_ge_two M.capacity_positive
    M.floor_positive M.cap_lt_floor M.floor_lt_cutoff
    (source_guard_multiplier_positive row M.multiplier_lower) M.lower M.lower_value M.lower_routes
    (literalSourceAlpha row M.Λ M.z M.width M.guardMargin)
    (measurable_literalSourceAlpha row M.multiplier_lower M.z M.width M.guardMargin)
    (D.positive_bid_continuity row k) (D.lower_broadcast row k)

def auxiliaryBoundary (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ) : JointAction 2 :=
  Classical.choose (D.exists_auxiliary_boundary row k)

theorem auxiliaryBoundary_spec (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ) :
    (D.auxiliaryBoundary row k).bid≤ Early.bidCap row ∧
    (D.auxiliaryBoundary row k).routeCount=2 ∧
    (∀ u : Fin (D.start+k), ∀ b : JointAction 2, b.routeCount=2 → b.bid<(D.market row k).R →
      (problem (D.market row k).native u).payoff (Uniform07.cutoff row) b≤
        (problem (D.market row k).native u).payoff (Uniform07.cutoff row)
          (D.auxiliaryBoundary row k)) :=
  Classical.choose_spec (D.exists_auxiliary_boundary row k)

def auxiliaryBoundaryBid (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ) :
    Icc (0:ℝ) (Early.bidCap row) :=
  ⟨(D.auxiliaryBoundary row k).bid,
    (D.auxiliaryBoundary row k).bid_nonneg,(D.auxiliaryBoundary_spec row k).1⟩

def focal (D : UniformAuxiliaryData05) (k : ℕ) : Fin (D.start+k) :=
  ⟨0,by have := D.start_ge_two; omega⟩

def matchedFloor (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ) : ℝ :=
  actualMatchedUpperFloor row (D.market row k).native (D.focal k) (D.auxiliaryBoundary row k)

theorem matchedFloor_tendsto (D : UniformAuxiliaryData05)
    (K : UniformAuxiliaryKernels05_06 D) (row : Uniform07.Row) :
    Tendsto (D.matchedFloor row) atTop (𝓝 (Uniform07.limitingFloor row)) := by
  have h := actualMatchedUpperFloor_tendsto_of_moments row D.population D.population_tendsto
    (fun k=>(D.market row k).native) (fun _=>rfl) (fun _=>rfl) D.focal
    (D.auxiliaryBoundaryBid row) (K.physical row).product.nativeMomentError
    (Eventually.of_forall ((K.physical row).product.nativeMomentError_nonneg))
    (K.physical row).product.nativeMomentError_tendsto
    (Eventually.of_forall (fun k b=>by
      have ha:sourceLowerBroadcastAction (Early.bidCap row) (D.auxiliaryBoundaryBid row k)=
          D.auxiliaryBoundary row k :=
        sourceLowerBroadcastAction_eq (Early.bidCap row) (D.auxiliaryBoundary row k)
          (D.auxiliaryBoundary_spec row k).1 (D.auxiliaryBoundary_spec row k).2.1
      rw [ha]
      exact (D.auxiliaryBoundary_spec row k).2.2 (D.focal k)
        (sourceLowerBroadcastAction (Early.bidCap row) b) rfl
        (b.2.2.trans_lt (D.market row k).cap_lt_floor)))
    (K.physical row).product.eventually_native_moments
  have he (k : ℕ) : sourceLowerBroadcastAction (Early.bidCap row) (D.auxiliaryBoundaryBid row k)=
      D.auxiliaryBoundary row k :=
    sourceLowerBroadcastAction_eq (Early.bidCap row) (D.auxiliaryBoundary row k)
      (D.auxiliaryBoundary_spec row k).1 (D.auxiliaryBoundary_spec row k).2.1
  change Tendsto (fun k => actualMatchedUpperFloor row (D.market row k).native
    (D.focal k) (D.auxiliaryBoundary row k)) atTop (𝓝 (Uniform07.limitingFloor row))
  simp only [he] at h
  convert! h using 1

theorem auxiliaryBoundary_eventually_above_entry (D : UniformAuxiliaryData05)
    (K : UniformAuxiliaryKernels05_06 D) (row : Uniform07.Row) :
    ∀ᶠ k in atTop, Uniform07.entry row<(D.auxiliaryBoundary row k).bid := by
  let Q:ℝ:=(Uniform07.cutoff row-Uniform07.entry row)^2/Uniform07.cutoff row
  have hQ:0< Q:=div_pos (sq_pos_of_pos (sub_pos.mpr (source_entry_lt_cutoff row)))
    (Uniform07.cutoff_pos row)
  have he0:Tendsto (fun k=>4*(Uniform07.cutoff row+Early.bidCap row)*
      (K.physical row).product.nativeMomentError k) atTop (𝓝 0):=by
    simpa only [mul_zero] using (K.physical row).product.nativeMomentError_tendsto.const_mul
      (4*(Uniform07.cutoff row+Early.bidCap row))
  filter_upwards [(K.physical row).product.eventually_native_moments,
    he0.eventually (Iio_mem_nhds hQ)] with k hm hs
  by_contra hn
  have hb:(D.auxiliaryBoundary row k).bid≤ Uniform07.entry row:=le_of_not_gt hn
  let b:=D.auxiliaryBoundaryBid row k
  have ha:sourceLowerBroadcastAction (Early.bidCap row) b=D.auxiliaryBoundary row k:=
    sourceLowerBroadcastAction_eq (Early.bidCap row) (D.auxiliaryBoundary row k)
      (D.auxiliaryBoundary_spec row k).1 (D.auxiliaryBoundary_spec row k).2.1
  have hIC:∀ b' : Icc (0:ℝ) (Early.bidCap row),
      (problem (D.market row k).native (D.focal k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b')≤
      (problem (D.market row k).native (D.focal k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b):=by
    intro b'
    rw [ha]
    exact (D.auxiliaryBoundary_spec row k).2.2 (D.focal k)
      (sourceLowerBroadcastAction (Early.bidCap row) b') rfl
      (b'.2.2.trans_lt (D.market row k).cap_lt_floor)
  have hboundary:=actual_boundary_utility_error row (D.market row k).native rfl rfl
    (D.focal k) ((K.physical row).product.nativeMomentError k)
    ((K.physical row).product.nativeMomentError_nonneg k) b hIC (hm (D.focal k))
  have hlow:=actual_product_payoff_error_of_moments row (D.market row k).native rfl rfl
    (D.focal k) (Uniform07.cutoff row) ((K.physical row).product.nativeMomentError k)
    (Uniform07.cutoff_pos row).le ((K.physical row).product.nativeMomentError_nonneg k) b
    (hm (D.focal k) b).1 (hm (D.focal k) b).2
  have hb' : (b:ℝ) ≤ Uniform07.entry row := hb
  have hp:sourceProductProbability row b=0:=by
    simp only [sourceProductProbability,if_pos hb']
  rw [hp] at hlow
  simp only [lowerProductQuadratic,mul_zero,pow_two,sub_zero] at hlow
  have h₁ : -((2:ℝ)*(Uniform07.cutoff row+Early.bidCap row)*
      (K.physical row).product.nativeMomentError k)≤
      (problem (D.market row k).native (D.focal k)).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b)-Q:=
    (abs_le.mp hboundary).1
  have h₂:=(abs_le.mp hlow).2
  linarith

theorem auxiliaryBoundary_eventually_positive (D : UniformAuxiliaryData05)
    (K : UniformAuxiliaryKernels05_06 D) (row : Uniform07.Row) :
    ∀ᶠ k in atTop, 0<(D.auxiliaryBoundary row k).bid := by
  filter_upwards [D.auxiliaryBoundary_eventually_above_entry K row] with k hk
  exact (source_entry_positive row).trans hk

end UniformAuxiliaryData05
end FCAppendix.Affine.Uniform07Finishing
