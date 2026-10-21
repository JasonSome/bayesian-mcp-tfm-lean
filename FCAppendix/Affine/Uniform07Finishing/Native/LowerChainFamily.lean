import FCAppendix.Affine.Uniform07Finishing.Native.FamilyFromMoments
import FCAppendix.Affine.Uniform07Finishing.Native.EndogenousBoundaryMatch

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Existence.RankEnvelope StrictNative

structure UniformMarketData (row : Uniform07.Row) (m : ℕ) where
  market_ge_two : 2≤ m
  capacity_positive : 1≤ Uniform07.capacity m
  R : ℝ
  Λ : ℝ
  z : ℝ
  width : ℝ
  guardMargin : ℝ
  floor_positive : 0< R
  cap_lt_floor : Early.bidCap row< R
  floor_lt_cutoff : R< Uniform07.cutoff row
  multiplier_lower : (54/100:ℝ)*Uniform07.cutoff row<Λ
  guard_margin_positive : 0< guardMargin
  lower : ProbabilityMeasure (ℝ×JointAction 2)
  lower_value : (lower : Measure (ℝ×JointAction 2)).map Prod.fst=
    (sourceLowerValueLaw row : Measure ℝ)
  lower_routes : ∀ᵐ x ∂(lower : Measure (ℝ×JointAction 2)),
    x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2
  lower_atomless : ∀ b : ℝ, (lower : Measure (ℝ×JointAction 2)) {x|x.2.bid=b}=0

namespace UniformMarketData
variable {row : Uniform07.Row} {m : ℕ} (D : UniformMarketData row m)

abbrev fin_nonempty : Nonempty (Fin m) := ⟨⟨0,by have := D.market_ge_two; omega⟩⟩

def native : FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  @sourceNativeGame m D.fin_nonempty row D.capacity_positive D.R D.Λ
    (source_guard_multiplier_positive row D.multiplier_lower) D.lower
    (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
    (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin)

def completedPolicy : FiniteGame m 2 (Uniform07.capacity m) unitInterval :=
  @literalSourceNativeGame m D.fin_nonempty row D.capacity_positive D.R D.Λ
    D.z D.width D.guardMargin D.multiplier_lower D.lower

structure Completed where
  game : FiniteGame m 2 (Uniform07.capacity m) unitInterval
  value : game.F=Uniform07.uniformLaw
  bid_schedule : game.A=Schedule.affine 2 (Uniform07.eta row)
    (Uniform07.eta_pos row).le (source_eta_le_one row)
  base_schedule : game.G=Schedule.once 2
  base_fee : game.g=0
  private_seed : game.seedLaw=volume
  joint : game.F⊗ₘgame.σ=
    (sourcePopulation row m D.capacity_positive D.R D.lower : Measure (ℝ×JointAction 2))
  equilibrium : IsBayesianEquilibrium game
  visible : VisibleAtomless game
  outcome : ∀ u : Fin m, ∀ a : JointAction 2,
    (problem game u).outcome a=(problem D.native u).outcome a
  fixed_best : ∀ v : ℝ, 0< v → v≤ 1 → ∀ᵐ a ∂game.σ v,
    ∀ u : Fin m, ∀ d : JointAction 2,
      (problem game u).payoff v d≤(problem game u).payoff v a
  lower_shape : ∀ v : ℝ, 0< v → v< Uniform07.cutoff row → ∀ᵐ a ∂game.σ v,
    a.bid≤ Early.bidCap row ∧ a.routeCount=2
  upper_kernel : ∀ v : ℝ, Uniform07.cutoff row≤ v → game.σ v=
    Measure.dirac (Hybrid.upperAction (sourceUpperBid row m D.R) v)
  routing : ∀ v : ℝ, 0< v → v≤ 1 → v≠Uniform07.cutoff row →
    ∀ᵐ a ∂game.σ v, a.routeCount=if v< Uniform07.cutoff row then 2 else 1

end UniformMarketData

structure UniformLowerChain {row : Uniform07.Row} {m : ℕ}
    (D : UniformMarketData row m) where
  floor_ceiling : D.R≤ sourceLowerPriceCeiling row
  upper_success_gap : sourceLowerSuccessCap row< source_upper_rank row m (Uniform07.cutoff row)
  hidden_guard : error (source_upper_rank row m) (Uniform07.cutoff row) D.R<
    Uniform07.eta row*D.R*(1-2*sourceUpperFailure row m)
  boundary : JointAction 2
  boundary_cap : boundary.bid≤ Early.bidCap row
  boundary_routes : boundary.routeCount=2
  boundary_broadcast : ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount=2 → b.bid< D.R →
    (problem D.native u).payoff (Uniform07.cutoff row) b≤
      (problem D.native u).payoff (Uniform07.cutoff row) boundary
  boundary_match : ∀ u : Fin m,
    (problem D.native u).payoff (Uniform07.cutoff row) boundary=
      utility (source_upper_rank row m) (Uniform07.cutoff row) D.R (Uniform07.cutoff row)
  singleton : ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ u : Fin m,
    ∀ a : JointAction 2, a.routeCount=1 → a.bid< D.R →
      ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid< D.R ∧
        (problem D.native u).payoff v a<(problem D.native u).payoff v b
  bad_event : ∀ u (a : JointAction 2), a.bid< D.R →
    (userProfileLaw D.completedPolicy).real
      (@sourceSuccessGood m D.fin_nonempty row D.capacity_positive D.R D.Λ
        D.z D.width D.guardMargin D.lower u a)ᶜ≤(1-sourceLowerMarginalCap row)^2/2
  positive_bid_continuity : ∀ u : Fin m, ∀ z : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(z.2:ℝ) →
    ContinuousAt (fun w : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
      (problem D.native u).payoff w.1 (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z
  lower_broadcast : ∀ᵐ x ∂(D.lower : Measure (ℝ×JointAction 2)),
    ∀ u : Fin m, ∀ b : JointAction 2, b.routeCount=2 → b.bid< D.R →
      (problem D.native u).payoff x.1 b≤(problem D.native u).payoff x.1 x.2

theorem UniformLowerChain.exists_completed {row : Uniform07.Row} {m : ℕ}
    {D : UniformMarketData row m} (C : UniformLowerChain D) : Nonempty D.Completed := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  obtain ⟨κ,hκM,hκ,hoff,hF,hA,hG,hg,hseed,hjoint,hEQ,hVis,hout,hIC,hshape,hupper,hroute⟩ :=
    literal_source_fixed_value_completion row D.market_ge_two D.capacity_positive
      D.floor_positive D.cap_lt_floor D.floor_lt_cutoff D.multiplier_lower
      D.guard_margin_positive D.lower D.lower_value D.lower_routes D.lower_atomless
      C.floor_ceiling C.upper_success_gap C.hidden_guard C.boundary C.boundary_cap
      C.boundary_routes C.boundary_broadcast C.boundary_match C.singleton C.bad_event
      C.positive_bid_continuity C.lower_broadcast
  letI : IsMarkovKernel κ:=hκM
  refine ⟨{
    game:=withStrategy D.completedPolicy κ
    value:=hF
    bid_schedule:=hA
    base_schedule:=hG
    base_fee:=hg
    private_seed:=hseed
    joint:=hjoint
    equilibrium:=hEQ
    visible:=hVis
    outcome:=hout
    fixed_best:=hIC
    lower_shape:=hshape
    upper_kernel:=hupper
    routing:=hroute }⟩

def UniformLowerChain.complete {row : Uniform07.Row} {m : ℕ}
    {D : UniformMarketData row m} (C : UniformLowerChain D) : D.Completed :=
  Classical.choice C.exists_completed

theorem UniformMarketData.Completed.upper_mass {row : Uniform07.Row} {m : ℕ}
    {D : UniformMarketData row m} (G : D.Completed) (v : ℝ)
    (hv : Uniform07.cutoff row≤ v) (r : Fin 3) :
    (conditionalTypeCountLaw G.game (by have := D.market_ge_two; omega) v).mass r=
      upperSingletonMass (source_upper_rank row m v) r := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  apply actual_upper_conditional_mass_of_raw_outcome_equality G.game D.native
    (by have := D.market_ge_two; omega) v _
    (Hybrid.upperAction (sourceUpperBid row m D.R) v) rfl (G.upper_kernel v hv)
    (fun u=>G.outcome u _)
  intro u
  exact sourceNativeGame_upper_mean_at_value row D.market_ge_two D.capacity_positive
    D.floor_positive D.cap_lt_floor D.floor_lt_cutoff
    (source_guard_multiplier_positive row D.multiplier_lower) D.lower D.lower_value D.lower_routes
    (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
    (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin) u v hv

def uniformNativePair_from_lower_chains
    (start : ℕ) (hstart : 2≤ start)
    (D : (row : Uniform07.Row)→(k : ℕ)→ UniformMarketData row (start+k))
    (C : ∀ row k, UniformLowerChain (D row k))
    (ε : Uniform07.Row→ℕ→ℝ) (hεpos : ∀ row k, 0≤ε row k)
    (hε0 : ∀ row, Tendsto (ε row) atTop (𝓝 0))
    (hmom : ∀ row, ∀ᶠ k in atTop, ∀ u : Fin (start+k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (D row k).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).load-2*sourceProductProbability row b|≤ε row k ∧
      |((problem (D row k).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-(sourceProductProbability row b)^2|≤ε row k) :
    UniformNativePair := by
  let G := fun row k=>(C row k).complete
  apply uniformNativePair_from_actual_moments start hstart (fun row k=>(G row k).game)
    (fun row k=>(G row k).value) (fun row k=>(G row k).bid_schedule)
    (fun row k=>(G row k).base_schedule) (fun row k=>(G row k).base_fee)
    (fun row k=>(G row k).private_seed) (fun row k=>(G row k).equilibrium)
    (fun row k=>(G row k).visible) (fun row k=>(G row k).fixed_best)
    (fun row k=>(G row k).lower_shape) (fun row k=>(G row k).routing)
    ε hεpos hε0
  · intro row
    filter_upwards [hmom row] with k hk
    intro u b
    simpa only [(G row k).outcome u] using hk u b
  · intro row k v hv r
    exact (G row k).upper_mass v hv r

theorem aff_uniform_result_from_lower_chains
    (start : ℕ) (hstart : 2≤ start)
    (D : (row : Uniform07.Row)→(k : ℕ)→ UniformMarketData row (start+k))
    (C : ∀ row k, UniformLowerChain (D row k))
    (ε : Uniform07.Row→ℕ→ℝ) (hεpos : ∀ row k, 0≤ε row k)
    (hε0 : ∀ row, Tendsto (ε row) atTop (𝓝 0))
    (hmom : ∀ row, ∀ᶠ k in atTop, ∀ u : Fin (start+k),
      ∀ b : Icc (0:ℝ) (Early.bidCap row),
      |((problem (D row k).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).load-2*sourceProductProbability row b|≤ε row k ∧
      |((problem (D row k).native u).outcome
        (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-(sourceProductProbability row b)^2|≤ε row k) :
    AffUniformResult :=
  aff_uniform_result_of_native_pair
    (uniformNativePair_from_lower_chains start hstart D C ε hεpos hε0 hmom)

end FCAppendix.Affine.Uniform07Finishing
