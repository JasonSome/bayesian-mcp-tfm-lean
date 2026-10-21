import FCAppendix.Affine.Uniform07Finishing.Native.AuxiliaryProducerData

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative Existence.RankEnvelope Crossover.Physical

structure MatchedScalarGuards (D : UniformAuxiliaryData05)
    (row : Uniform07.Row) (k : ℕ) : Prop where
  positive : 0< D.matchedFloor row k
  cap_below : Early.bidCap row< D.matchedFloor row k
  below_cutoff : D.matchedFloor row k< Uniform07.cutoff row
  below_auxiliary : D.matchedFloor row k<(D.market row k).R
  price_ceiling : D.matchedFloor row k< sourceLowerPriceCeiling row
  mixed_receipt : Uniform07.kappa row*D.matchedFloor row k+Early.nativeRadius row<
    (27/50:ℝ)*Uniform07.cutoff row
  upper_success : sourceLowerSuccessCap row< source_upper_rank row (D.start+k) (Uniform07.cutoff row)
  hidden : error (source_upper_rank row (D.start+k)) (Uniform07.cutoff row) (D.matchedFloor row k)<
    Uniform07.eta row*D.matchedFloor row k*(1-2*sourceUpperFailure row (D.start+k))

theorem UniformAuxiliaryData05.eventually_matched_scalar_guards
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) (row : Uniform07.Row) :
    ∀ᶠ k in atTop, MatchedScalarGuards D row k := by
  have h := source_common_native_guards_of_floor_limit row D.population D.population_tendsto
    (D.matchedFloor row) (D.matchedFloor_tendsto K row)
  filter_upwards [h] with k hk
  rcases hk with ⟨hm,hc,hR,hUR,hRt,hceil,hmix,hq,hhidden⟩
  refine ⟨hR,hUR,hRt,?_,hceil,hmix,hq,hhidden⟩
  simpa only [D.auxiliary_floor row k] using hceil

theorem UniformAuxiliaryData05.eventually_all_matched_scalar_guards
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    ∀ᶠ k in atTop, ∀ row : Uniform07.Row, MatchedScalarGuards D row k := by
  filter_upwards [D.eventually_matched_scalar_guards K .first,
    D.eventually_matched_scalar_guards K .second] with k h₁ h₂
  intro row
  cases row
  · exact h₁
  · exact h₂

def matchedMarket (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ)
    (h : MatchedScalarGuards D row k) : UniformMarketData row (D.start+k) :=
  replaceUpperFloor (D.market row k) (D.matchedFloor row k) h.positive h.cap_below h.below_cutoff

theorem matchedMarket_lower_broadcast (D : UniformAuxiliaryData05) (row : Uniform07.Row)
    (k : ℕ) (h : MatchedScalarGuards D row k) :
    ∀ᵐ x ∂((matchedMarket D row k h).lower : Measure (ℝ×JointAction 2)),
      ∀ u : Fin (D.start+k), ∀ a : JointAction 2, a.routeCount=2 → a.bid<(matchedMarket D row k h).R →
        (problem (matchedMarket D row k h).native u).payoff x.1 a≤
          (problem (matchedMarket D row k h).native u).payoff x.1 x.2 :=
  replaceUpperFloor_lower_broadcast_IC (D.market row k) h.positive h.cap_below h.below_cutoff
    h.below_auxiliary.le (D.lower_broadcast row k)

theorem matchedMarket_positive_bid_continuity (D : UniformAuxiliaryData05) (row : Uniform07.Row)
    (k : ℕ) (h : MatchedScalarGuards D row k) :
    ∀ u : Fin (D.start+k), ∀ z : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem (matchedMarket D row k h).native u).payoff w.1
          (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z :=
  replaceUpperFloor_positive_bid_continuity (D.market row k) h.positive h.cap_below h.below_cutoff
    (D.positive_bid_continuity row k)

theorem UniformAuxiliaryData05.eventually_matched_routes_and_moments
    (D : UniformAuxiliaryData05) (K : UniformAuxiliaryKernels05_06 D) :
    ∀ᶠ k in atTop, ∀ row : Uniform07.Row, ∀ h : MatchedScalarGuards D row k,
      (∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ u : Fin (D.start+k),
        ∀ a : JointAction 2, a.routeCount=1 → a.bid<(matchedMarket D row k h).R →
          ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid<(matchedMarket D row k h).R ∧
            (problem (matchedMarket D row k h).native u).payoff v a<
              (problem (matchedMarket D row k h).native u).payoff v b) ∧
      (∀ u : Fin (D.start+k), ∀ b : Icc (0:ℝ) (Early.bidCap row),
        |((problem (matchedMarket D row k h).native u).outcome
          (sourceLowerBroadcastAction (Early.bidCap row) b)).load-2*sourceProductProbability row b|≤
            (K.physical row).product.nativeMomentError k ∧
        |((problem (matchedMarket D row k h).native u).outcome
          (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-(sourceProductProbability row b)^2|≤
            (K.physical row).product.nativeMomentError k) := by
  filter_upwards [(K.physical .first).eventually_after_every_smaller_floor,
    (K.physical .second).eventually_after_every_smaller_floor] with k h₁ h₂
  intro row h
  cases row
  · exact h₁ (D.matchedFloor .first k) h.positive h.cap_below h.below_cutoff h.below_auxiliary.le
  · exact h₂ (D.matchedFloor .second k) h.positive h.cap_below h.below_cutoff h.below_auxiliary.le

end FCAppendix.Affine.Uniform07Finishing
