import FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
import FCAppendix.Affine.Tail04.OrderedSourceNativeUnusedCount

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open SourceMovingScalarGuards OrderedSourceFiniteStartingPoint MenuError SourceMenuPopulation
open SourceMomentRectangle SourceMultiplierRectangle SourceGlobalMargins
open RouteMenuStatistics CanonicalFailure CanonicalSourceGlobal

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width} {N : ℕ}
  (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

abbrev regions : Observable.Regions := OrderedNativeZeroNoiseSource.regions A.D P
  (A.forget.low_gap hlow) A.H A.upper_gap

def «public» : PublicScenario.Data := OrderedZeroNativeBindings.publicData A.D P (cutoff N)
  A.point.range.cutoff_gt_M (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint
  A.sequence.limit A.upperBid A.upperBid_measurable A.upper_floor

def canonical (b : ℝ) : CountLaw 2 :=
  UnusedFiniteCountError.canonicalMixture («public» A hlow) (multiplier A hlow) b

lemma canonical_eq (b : ℝ) : canonical A hlow b=
    CanonicalSourceGlobal.mixture
      (IndependentCounts.bernoulli («public» A hlow).θ («public» A hlow).θ_nonneg
        («public» A hlow).θ_le_one) ξ (multiplier A hlow) b := rfl

variable (hwγ : width≤ γ ξ)
  (hsize : ∀reg,4*ξ/((N:ℝ)*centerMoment P reg)≤ γ ξ)
  (hbulk : 1≤ P.bulkWeight*(N:ℝ)/2)

include hwγ hsize hbulk in
theorem unused_count_error (i : Fin (N+1)) (b : ℝ)
    (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U)
    (f : Fin 3→ℝ) :
    |((problem (A.native hlow) i).outcome (RawRoutes.action b hb.1 2)).expect f-
      (canonical A hlow b).expect f|≤ MenuError.oscillation f*SourceUnusedConstants.rate P ξ u N :=
  OrderedSourceNativeUnusedCount.original_count_error A.D P (cutoff N) A.point.range.cutoff_gt_M
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable (A.forget.low_gap hlow)
    A.H A.upper_gap A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using A.forget.rare)
    (NativeLowSourceIC.categories P (cutoff N) A.point.range.cutoff_gt_M.le) A.point.low rfl
    rfl A.point.range.rivals_positive rfl (by intro r;cases r <;> rfl) hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ hsize hbulk i b hb htag hout f

include hwγ hsize hbulk in
theorem unused_payoff_error (i : Fin (N+1)) (v b : ℝ) (hv : 0≤ v)
    (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    |(problem (A.native hlow) i).payoff v (RawRoutes.action b hb.1 q)-
      (canonical A hlow b).expect (statistic (1-2*ξ) v b q)|≤
        (v+2*Central.B ξ)*SourceUnusedConstants.rate P ξ u N := by
  have he := unused_count_error A hlow hwγ hsize hbulk i b hb htag hout
    (statistic (1-2*ξ) v b q)
  have hp := native_payoff (A.native hlow) (1-2*ξ) A.D.heta0 A.D.heta1 rfl rfl i v b hb.1 q
  rw [←hp] at he
  exact he.trans (mul_le_mul_of_nonneg_right (oscillation_bound A.D.heta0 A.D.heta1 hv hb q)
    (SourceUnusedConstants.rate_nonneg P hξ A.forget.base_bulk_below N))

include hwγ hsize hbulk in
theorem unused_active_upper (hθ : P.theta≤ ξ/100) (hwval : P.w≤ ξ/1000)
    (hvA : P.vA=11*ξ/(10*P.theta)) (i : Fin (N+1)) (v b : ℝ) (hv : P.vA-P.w≤ v)
    (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    (problem (A.native hlow) i).payoff v (RawRoutes.action b hb.1 q)≤
      v-Central.B ξ-ξ/40+(v+2*Central.B ξ)*SourceUnusedConstants.rate P ξ u N := by
  have hv0 : 0≤ v := by linarith [(active_value_large P hξ hξh hθ hwval hvA).trans hv]
  have he := unused_payoff_error A hlow hwγ hsize hbulk i v b hv0 hb htag hout q
  have hm := CanonicalSourceGlobal.active_all_routes P hξ hξh hθ hwval hvA
    (IndependentCounts.bernoulli («public» A hlow).θ («public» A hlow).θ_nonneg («public» A hlow).θ_le_one)
    (multiplier A hlow)
    (fun reg=> by have hh:=(multiplier_margins A hlow reg).1;unfold γ at hh;linarith)
    (multiplier_floor A hlow) hv hb q
  rw [←canonical_eq A hlow b] at hm
  linarith [(abs_le.mp he).2]

include hwγ hsize hbulk in
theorem unused_partial_center (hθ : P.theta≤ ξ/100) (i : Fin (N+1)) (b : ℝ)
    (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    (problem (A.native hlow) i).payoff 2 (RawRoutes.action b hb.1 q)≤
      (2-Central.R ξ)*(1-P.theta)-ξ/2+
        (2+2*Central.B ξ)*SourceUnusedConstants.rate P ξ u N := by
  have he := unused_payoff_error A hlow hwγ hsize hbulk i 2 b (by norm_num) hb htag hout q
  have hm := CanonicalSourceGlobal.partial_all_routes P hξ hξh hθ
    (IndependentCounts.bernoulli («public» A hlow).θ («public» A hlow).θ_nonneg («public» A hlow).θ_le_one)
    (multiplier A hlow)
    (fun reg=> by have hh:=(multiplier_margins A hlow reg).1;unfold γ at hh;linarith)
    (multiplier_floor A hlow) hb q
  rw [←canonical_eq A hlow b] at hm
  linarith [(abs_le.mp he).2]

include hwγ hsize hbulk in
theorem unused_all_routes_failure (i : Fin (N+1)) (b : ℝ)
    (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    (probabilityGap ξ)^2-SourceUnusedConstants.rate P ξ u N≤
      1-((problem (A.native hlow) i).outcome (RawRoutes.action b hb.1 q)).success := by
  have hf := CanonicalSourceGlobal.failure
    (IndependentCounts.bernoulli («public» A hlow).θ («public» A hlow).θ_nonneg («public» A hlow).θ_le_one)
    hξ (by linarith : ξ≤1) (multiplier A hlow)
    (fun reg=>(multiplier_margins A hlow reg).1) hb
  rw [←canonical_eq A hlow b] at hf
  have he := unused_count_error A hlow hwγ hsize hbulk i b hb htag hout (fun r : Fin 3=>successIndicator r.val)
  rw [OrderedSourceNativeLowerFailure.success_oscillation,one_mul] at he
  have hs := OrderedSourceNativeLowerFailure.route_success_le_broadcast (A.native hlow) i b hb.1 q
  change |_ - _|≤_ at he
  dsimp only [CountLaw.success] at hf hs ⊢
  linarith [(abs_le.mp he).2]

theorem lower_bid_cases {b : ℝ} (hb : b< A.H) :
    b≤ P.d0 ∨ b∈Icc A.D.R A.D.Up ∨ b∈Icc (1:ℝ) A.D.U ∨
      ((regions A hlow).localTag (some b)=1 ∧ b∉Icc (1:ℝ) A.D.U) := by
  by_cases hd : b≤ P.d0
  · exact Or.inl hd
  by_cases hp : b∈Icc A.D.R A.D.Up
  · exact Or.inr (Or.inl hp)
  by_cases hc : b∈Icc (1:ℝ) A.D.U
  · exact Or.inr (Or.inr (Or.inl hc))
  refine Or.inr (Or.inr (Or.inr ⟨?_,hc⟩))
  have hn : b∉(regions A hlow).privateBids := by
    rintro (h | h)
    · exact hp h
    · exact not_le.mpr hb h
  simp only [Observable.Regions.localTag,show ¬b≤(regions A hlow).d from hd,if_false,hn]

end FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
