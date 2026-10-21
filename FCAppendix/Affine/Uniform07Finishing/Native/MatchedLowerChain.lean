import FCAppendix.Affine.Uniform07Finishing.Native.MatchedScalarData
import FCAppendix.Affine.Uniform07Finishing.Native.SourceBadEventFloorTransfer

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative Existence.RankEnvelope Crossover.Physical

theorem UniformAuxiliaryData05.exists_matched_boundary
    (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ)
    (h : MatchedScalarGuards D row k)
    (hIdentity : ∀ u : Fin (D.start+k),
      (problem (D.market row k).native u).outcome (D.auxiliaryBoundary row k)=
        (problem (D.market row k).native (D.focal k)).outcome (D.auxiliaryBoundary row k)) :
    ∃ aT : JointAction 2, aT.bid≤ Early.bidCap row ∧ aT.routeCount=2 ∧
      (∀ u : Fin (D.start+k), ∀ b : JointAction 2, b.routeCount=2 →
        b.bid<(matchedMarket D row k h).R →
          (problem (matchedMarket D row k h).native u).payoff (Uniform07.cutoff row) b≤
            (problem (matchedMarket D row k h).native u).payoff (Uniform07.cutoff row) aT) ∧
      (∀ u : Fin (D.start+k),
        (problem (matchedMarket D row k h).native u).payoff (Uniform07.cutoff row) aT=
          utility (source_upper_rank row (D.start+k)) (Uniform07.cutoff row)
            (matchedMarket D row k h).R (Uniform07.cutoff row)) := by
  let M:=D.market row k
  letI : Nonempty (Fin (D.start+k)):=M.fin_nonempty
  have hCap : ∀ u : Fin (D.start+k), ∀ b : Icc (0:ℝ) (Early.bidCap row),
      (problem M.native u).payoff (Uniform07.cutoff row)
        (sourceLowerBroadcastAction (Early.bidCap row) b)≤
      (problem M.native u).payoff (Uniform07.cutoff row) (D.auxiliaryBoundary row k) := by
    intro u b
    exact (D.auxiliaryBoundary_spec row k).2.2 u
      (sourceLowerBroadcastAction (Early.bidCap row) b) rfl (b.2.2.trans_lt M.cap_lt_floor)
  exact sourceNativeGame_exists_endogenously_matched_boundary row M.market_ge_two M.capacity_positive
    M.floor_positive M.cap_lt_floor M.floor_lt_cutoff
    (source_guard_multiplier_positive row M.multiplier_lower) M.lower M.lower_value M.lower_routes
    (literalSourceAlpha row M.Λ M.z M.width M.guardMargin)
    (measurable_literalSourceAlpha row M.multiplier_lower M.z M.width M.guardMargin)
    (D.focal k) (D.auxiliaryBoundary row k)
    (D.auxiliaryBoundary_spec row k).1 (D.auxiliaryBoundary_spec row k).2.1 hCap hIdentity
    h.positive h.cap_below h.below_cutoff
    (matchedMarket_positive_bid_continuity D row k h)
    (matchedMarket_lower_broadcast D row k h)

theorem matchedMarket_bad_event_from_auxiliary
    (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ)
    (h : MatchedScalarGuards D row k)
    (hbad : ∀ u : Fin (D.start+k), ∀ a : JointAction 2, a.bid<(D.market row k).R →
      (userProfileLaw (D.market row k).native).real
        (@sourceSuccessGood (D.start+k) (D.market row k).fin_nonempty row
          (D.market row k).capacity_positive (D.market row k).R (D.market row k).Λ
          (D.market row k).z (D.market row k).width (D.market row k).guardMargin
          (D.market row k).lower u a)ᶜ≤(1-sourceLowerMarginalCap row)^2/2) :
    ∀ u : Fin (D.start+k), ∀ a : JointAction 2, a.bid<(matchedMarket D row k h).R →
      (userProfileLaw (matchedMarket D row k h).completedPolicy).real
        (@sourceSuccessGood (D.start+k) (matchedMarket D row k h).fin_nonempty row
          (matchedMarket D row k h).capacity_positive (matchedMarket D row k h).R
          (matchedMarket D row k h).Λ (matchedMarket D row k h).z
          (matchedMarket D row k h).width (matchedMarket D row k h).guardMargin
          (matchedMarket D row k h).lower u a)ᶜ≤(1-sourceLowerMarginalCap row)^2/2 := by
  let M:=D.market row k
  letI : Nonempty (Fin (D.start+k)):=M.fin_nonempty
  intro u a ha
  have ha₀:a.bid< M.R:=ha.trans h.below_auxiliary
  have hsame:=sourceSuccessGood_bad_mass_floor_invariant (z := M.z) (width := M.width)
    (ε := M.guardMargin) row M.market_ge_two M.capacity_positive
    M.floor_positive M.cap_lt_floor M.floor_lt_cutoff h.positive h.cap_below h.below_cutoff
    M.multiplier_lower M.lower M.lower_value M.lower_routes u a ha₀ ha
  change (userProfileLaw (matchedMarket D row k h).native).real
    (sourceSuccessGood row M.capacity_positive (D.matchedFloor row k) M.Λ M.z M.width M.guardMargin
      M.lower u a)ᶜ≤ _
  calc
    _ = (userProfileLaw M.native).real
        (sourceSuccessGood row M.capacity_positive M.R M.Λ M.z M.width M.guardMargin
          M.lower u a)ᶜ := by
      convert! hsame using 1
    _ ≤ _ := hbad u a ha₀

theorem UniformAuxiliaryData05.construct_matched_lower_chain
    (D : UniformAuxiliaryData05) (row : Uniform07.Row) (k : ℕ)
    (h : MatchedScalarGuards D row k)
    (hIdentity : ∀ u : Fin (D.start+k),
      (problem (D.market row k).native u).outcome (D.auxiliaryBoundary row k)=
        (problem (D.market row k).native (D.focal k)).outcome (D.auxiliaryBoundary row k))
    (hcross : ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ u : Fin (D.start+k),
      ∀ a : JointAction 2, a.routeCount=1 → a.bid<(matchedMarket D row k h).R →
        ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid<(matchedMarket D row k h).R ∧
          (problem (matchedMarket D row k h).native u).payoff v a<
            (problem (matchedMarket D row k h).native u).payoff v b)
    (hbad : ∀ u : Fin (D.start+k), ∀ a : JointAction 2, a.bid<(D.market row k).R →
      (userProfileLaw (D.market row k).native).real
        (@sourceSuccessGood (D.start+k) (D.market row k).fin_nonempty row
          (D.market row k).capacity_positive (D.market row k).R (D.market row k).Λ
          (D.market row k).z (D.market row k).width (D.market row k).guardMargin
          (D.market row k).lower u a)ᶜ≤(1-sourceLowerMarginalCap row)^2/2) :
    Nonempty (UniformLowerChain (matchedMarket D row k h)) := by
  obtain ⟨aT,hTU,hT2,hT,hmatch⟩:=D.exists_matched_boundary row k h hIdentity
  exact ⟨{
    floor_ceiling:=h.price_ceiling.le
    upper_success_gap:=h.upper_success
    hidden_guard:=h.hidden
    boundary:=aT
    boundary_cap:=hTU
    boundary_routes:=hT2
    boundary_broadcast:=hT
    boundary_match:=hmatch
    singleton:=hcross
    bad_event:=matchedMarket_bad_event_from_auxiliary D row k h hbad
    positive_bid_continuity:=matchedMarket_positive_bid_continuity D row k h
    lower_broadcast:=matchedMarket_lower_broadcast D row k h }⟩

end FCAppendix.Affine.Uniform07Finishing
