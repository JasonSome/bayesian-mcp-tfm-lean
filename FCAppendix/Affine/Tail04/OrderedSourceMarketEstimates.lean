import FCAppendix.Affine.Tail04.OrderedSourceRestrictedNative
import FCAppendix.Affine.Tail04.OrderedNativeActiveSingleton
import FCAppendix.Affine.Tail04.NativeSourceMultiplierFloor
import FCAppendix.Affine.Tail04.OrderedSourcePartialGlobal
import FCAppendix.Affine.Tail04.OrderedSourceNativeLowerFailure
import FCAppendix.Affine.Tail04.CanonicalSourceGlobal
import FCAppendix.Affine.Tail04.SourceUnusedConstants
import FCAppendix.Affine.Tail04.OrderedSourceLowCountLaws

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open SourceMovingScalarGuards OrderedSourceFiniteStartingPoint MenuError SourceMenuPopulation
open SourceMomentRectangle SourceMultiplierRectangle SourceGlobalMargins

def commonRate (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  SourceMovingMenuRates.rate (OrderedSourceCommonMenuError.commonCoefficient P ξ)
    (lowMass P.theta) P.bulkWeight N

lemma commonRate_nonneg (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (N : ℕ) :
    0≤ commonRate P ξ N :=
  SourceMovingMenuRates.rate_nonneg (OrderedSourceCommonMenuError.commonCoefficient_nonnegative P hξ)
    P.bulkWeight_pos.le N

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width} {N : ℕ}
  (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

local notation "Γ" => A.native hlow
local notation "tN" => cutoff N
local notation "htN" => A.point.range.cutoff_gt_M
local notation "cats" => NativeLowSourceIC.categories P tN (LT.lt.le htN)

def multiplier (reg : Bool) : ℝ :=
  ZeroSourceCommonMenuError.lambda A.D P tN htN A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor
    N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) reg

theorem multiplier_margins (reg : Bool) :
    (1-ξ)*Central.B ξ+2*γ ξ≤ multiplier A hlow reg ∧
      multiplier A hlow reg+2*γ ξ≤1 :=
  ZeroSourceMultiplierRectangle.actual_nominal_margins A.D P tN htN
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare)
    rfl (by intro r;cases r <;> rfl) A.forget.base_bulk_below hξh rfl
    A.forget.base_partial_guard A.forget.base_moment_guard A.point.range.upper_mass_guard reg

theorem multiplier_floor (reg : Bool) : multiplierFloor ξ≤ multiplier A hlow reg :=
  NativeSourceMultiplierFloor.actual_floor A.D P tN htN A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable (A.forget.low_gap hlow) A.H A.upper_gap
    A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) rfl (by intro r;cases r <;> rfl)
    A.forget.base_bulk_below hξh A.forget.base_moment_guard reg

theorem multiplier_mem {ρ : ℝ} {Λ : Set (ℝ×ℝ)} (hrect : MomentInvariant P ξ ρ Λ)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ) :
    (multiplier A hlow false,multiplier A hlow true)∈Λ :=
  ZeroSourceMultiplierRectangle.actual_mem A.D P tN htN A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable (A.forget.low_gap hlow) A.H A.upper_gap
    A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) rfl (by intro r;cases r <;> rfl)
    A.forget.base_bulk_below hrect hρ

variable (hwγ : width≤ γ ξ)

include hwγ in
theorem common_payoff_error (i : Fin (N+1)) (v : ℝ) (hv : 0≤ v) (b : Icc (1:ℝ) A.D.U) :
    |(problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)-
      SourceMenuIdentity.menuUtility P ξ (multiplier A hlow false) (multiplier A hlow true) v b|≤
        (v+2*Central.B ξ)*commonRate P ξ N := by
  letI := A.common_compact_atomless
  exact OrderedZeroNativeMenuPayoff.original_payoff_error A.D P tN htN (A.forget.low_gap hlow)
    A.H A.upper_gap A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) cats A.point.low rfl rfl A.point.range.rivals_positive
    rfl (by intro r;cases r <;> rfl) rfl rfl hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ i v hv b

include hwγ in
theorem common_singleton_upper (i : Fin (N+1)) (v : ℝ) (hv : Central.B ξ≤ v)
    (b : Icc (1:ℝ) A.D.U) :
    (problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 1)≤
      (3/5)*v+(v+2*Central.B ξ)*commonRate P ξ N := by
  letI := A.common_compact_atomless
  exact OrderedNativeActiveSingleton.payoff_upper A.D P tN htN (A.forget.low_gap hlow)
    A.H A.upper_gap A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) cats A.point.low rfl rfl A.point.range.rivals_positive
    rfl (by intro r;cases r <;> rfl) rfl hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ i v hv b

include hwγ in
theorem common_all_routes_failure (hk : 0< k) (i : Fin (N+1))
    (b : Icc (1:ℝ) A.D.U) (q : Fin 3) :
    CanonicalFailure.movingCoefficient P ξ k/tN^2-commonRate P ξ N≤
      1-((problem Γ i).outcome (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) q)).success := by
  letI := A.common_compact_atomless
  exact OrderedSourceNativeLowerFailure.active_all_routes A.D P tN htN (A.forget.low_gap hlow)
    A.H A.upper_gap A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    A.upper_floor N (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) cats A.point.low rfl rfl A.point.range.rivals_positive
    rfl (by intro r;cases r <;> rfl) rfl hξh rfl
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ k hk le_rfl i b q

include hwγ in
theorem partial_success (i : Fin (N+1)) (b : Icc A.D.R A.D.Up) (q : Fin 3) :
    ((problem Γ i).outcome (RawRoutes.action b (A.D.hR.le.trans b.2.1) q)).success≤
      1-P.theta+OrderedZeroSourcePartialCount.error P ξ N :=
  OrderedSourcePartialGlobal.all_routes_success P ξ u Up (cap ξ k N) width N hξ hξh hu
    A.point.range.base_contains_bulk hRUp.le hUp A.point.range.base_below_nominal hw
    tN htN (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) A.point.range.rivals_positive
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ A.point.range.room cats A.point.low rfl i b q

include hwγ in
theorem partial_upper (i : Fin (N+1)) (v : ℝ) (hv : A.D.Up≤ v)
    (b : Icc A.D.R A.D.Up) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) q)≤
      (v-Central.R ξ)*(1-P.theta)+v*OrderedZeroSourcePartialCount.error P ξ N :=
  OrderedSourcePartialGlobal.all_routes_payoff_upper P ξ u Up (cap ξ k N) width N hξ hξh hu
    A.point.range.base_contains_bulk hRUp.le hUp A.point.range.base_below_nominal hw
    tN htN (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) A.point.range.rivals_positive
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ A.point.range.room cats A.point.low rfl i v hv b q

include hwγ in
theorem partial_bottom (i : Fin (N+1)) (v : ℝ) (hv : Central.R ξ≤ v) :
    (v-Central.R ξ)*(1-P.theta)-v*OrderedZeroSourcePartialCount.error P ξ N≤
      (problem Γ i).payoff v (RawRoutes.action A.D.R A.D.hR.le 1) :=
  OrderedSourcePartialGlobal.bottom_payoff_lower P ξ u Up (cap ξ k N) width N hξ hξh hu
    A.point.range.base_contains_bulk hRUp.le hUp A.point.range.base_below_nominal hw
    tN htN (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) A.point.range.rivals_positive
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ A.point.range.room cats A.point.low rfl i v hv

include hwγ in
theorem partial_broadcast_penalty (i : Fin (N+1)) (v : ℝ) (b : Icc A.D.R A.D.Up) :
    (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) 2)-
      (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) 1)≤
        -(1-2*ξ)*Central.R ξ*(1-P.theta)+(2*|v|+4)*OrderedZeroSourcePartialCount.error P ξ N :=
  OrderedSourcePartialGlobal.broadcast_penalty P ξ u Up (cap ξ k N) width N hξ hξh hu
    A.point.range.base_contains_bulk hRUp.le hUp A.point.range.base_below_nominal hw
    tN htN (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
    A.upperBid A.upperBid_measurable A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) A.point.range.rivals_positive
    A.forget.base_bulk_below A.forget.base_partial_guard A.forget.base_moment_guard
    A.point.range.upper_mass_guard hwγ A.point.range.room cats A.point.low rfl i v b

theorem low_success
    (hroom : (A.D.c:ℝ)≤(N:ℝ)*(activeMass P.theta-
      activeMass P.theta*P.zeta*powerTail P.M 10 tN-OrderedSourceLowCountLaws.gap P))
    (i : Fin (N+1)) (b : ℝ) (hb : 0≤ b) (hbd : b≤ P.d0) (q : Fin 3) :
    ((problem Γ i).outcome (RawRoutes.action b hb q)).success≤ OrderedSourceLowCountLaws.error P N := by
  have h := OrderedSourceLowCountLaws.original_load_le A.D P tN htN (A.forget.low_gap hlow)
    A.H A.upper_gap N A.point.low A.sequence.limit A.upperBid A.upperBid_measurable
    A.upper_floor (by simpa only [Nat.cast_add,Nat.cast_one] using! A.forget.rare) (OrderedSourceLowCountLaws.gap P)
    (OrderedSourceLowCountLaws.gap_positive P).le A.point.range.rivals_positive hroom
    i (RawRoutes.action b hb 2) rfl hbd
  exact (OrderedSourceNativeLowerFailure.route_success_le_broadcast Γ i b hb q).trans
    (((problem Γ i).outcome (RawRoutes.action b hb 2)).success_le_load.trans h)

theorem low_payoff
    (hroom : (A.D.c:ℝ)≤(N:ℝ)*(activeMass P.theta-
      activeMass P.theta*P.zeta*powerTail P.M 10 tN-OrderedSourceLowCountLaws.gap P))
    (i : Fin (N+1)) (v b : ℝ) (hv : 0≤ v) (hb : 0≤ b) (hbd : b≤ P.d0) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb q)≤ v*OrderedSourceLowCountLaws.error P N := by
  have hs := low_success A hlow hroom i b hb hbd q
  have hp := ((problem Γ i).outcome (RawRoutes.action b hb q)).utility_le_bid_net_success
    v b (Γ).g (Γ).A (Γ).G hb (Γ).g_nonneg
  change (problem Γ i).payoff v (RawRoutes.action b hb q)≤(v-0-b)*_ at hp
  have he := mul_le_mul_of_nonneg_left hs hv
  have hc := mul_nonneg hb ((problem Γ i).outcome (RawRoutes.action b hb q)).success_nonneg
  nlinarith

end FCAppendix.Affine.Tail04.OrderedSourceMarketEstimates
