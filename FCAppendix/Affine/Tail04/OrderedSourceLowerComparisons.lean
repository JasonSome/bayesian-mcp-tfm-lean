import FCAppendix.Affine.Tail04.OrderedSourceCommonGlobal

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceLowerComparisons
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open SourceMovingScalarGuards MenuError SourceMenuPopulation SourceMomentRectangle
open OrderedSourceMarketEstimates OrderedSourceGlobalRates OrderedSourceCommonGlobal SourceGlobalMargins CanonicalFailure

lemma active_large (P : ValueParameters) {ξ v : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hθ : P.theta≤ ξ/100)
    (hwval : P.w≤ ξ/1000) (hvA : P.vA=11*ξ/(10*P.theta))
    (hv : P.vA-P.w≤ v) : 100≤ v :=
  (active_value_large P hξ hξh hθ hwval hvA).trans hv

lemma partial_value_bounds {P : ValueParameters} {ξ v : ℝ}
    (hξh : ξ<1/2) (hwval : P.w≤ ξ/1000)
    (hv : v∈Icc (2-P.w) (2+P.w)) :
    1≤ v ∧ v≤3 ∧ |v-2|≤ P.w := by
  exact ⟨by linarith [hv.1],by linarith [hv.2],
    abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩⟩

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width} {N : ℕ}
  (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
  {κ : ℝ} (bud : OrderedSourceGlobalRates.Budgets P ξ u k κ N)
  (hθ : P.theta≤ ξ/100) (hwval : P.w≤ ξ/1000)
  (hvA : P.vA=11*ξ/(10*P.theta))

local notation "Γ" => A.native hlow
local notation "err" => utilityError P ξ u N
local notation "tot" => total P ξ u N

lemma raw_eq (a : JointAction 2) :
    a=RawRoutes.action a.bid a.bid_nonneg ⟨a.routeCount,by have h:=a.routeCount_le;omega⟩ := by
  cases a
  rfl

lemma zero_payoff (i : Fin (N+1)) (v b : ℝ) (hb : 0≤ b) :
    (problem Γ i).payoff v (RawRoutes.action b hb 0)=0 :=
  (RawRoutes.all_route_payoffs Γ i b hb A.D.eta A.D.heta0 A.D.heta1 rfl rfl v).1

include hwγ bud hθ hwval hvA in
theorem active_singleton_below_face (i : Fin (N+1)) (v : ℝ)
    (hv : P.vA-P.w≤ v) (hvt : v≤ cutoff N) (b : Icc (1:ℝ) A.D.U) :
    (problem Γ i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 1)<
      v-Central.B ξ := by
  have hv100 := active_large P hξ hξh hθ hwval hvA hv
  have hv0 : 0≤ v := by linarith
  have hBv : Central.B ξ≤ v := by unfold Central.B;linarith
  have hp := common_singleton_upper A hlow hwγ i v hBv b
  have he := common_error_bound A hv0 hvt
  have hg := active_singleton_gap P hξ hξh hθ hwval hvA hv
  linarith [bud.utility_small]

include hwγ bud hθ hwval hvA in
theorem active_partial_below_face (i : Fin (N+1)) (v : ℝ)
    (hv : P.vA-P.w≤ v) (hvt : v≤ cutoff N) (b : Icc A.D.R A.D.Up) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) q)< v-Central.B ξ := by
  have hv100 := active_large P hξ hξh hθ hwval hvA hv
  have hv0 : 0≤ v := by linarith
  have hp := partial_upper A hlow hwγ i v (by change Up≤ v;linarith) b q
  have he := partial_error_bound A hv0 hvt
  have hg := active_partial_gap P hξ hξh hθ hwval hvA hv
  nlinarith [bud.utility_small]

include hwγ bud hθ hwval hvA in
theorem active_unused_below_face (i : Fin (N+1)) (v b : ℝ)
    (hv : P.vA-P.w≤ v) (hvt : v≤ cutoff N) (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb.1 q)< v-Central.B ξ := by
  have hv0 : 0≤ v := by linarith [active_large P hξ hξh hθ hwval hvA hv]
  have hp := unused_active_upper A hlow hwγ bud.unused_room.1 bud.unused_room.2
    hθ hwval hvA i v b hv hb htag hout q
  have he := unused_error_bound A hv0 hvt
  linarith [bud.utility_small]

include bud hθ hwval hvA in
theorem active_low_below_face (i : Fin (N+1)) (v b : ℝ)
    (hv : P.vA-P.w≤ v) (hvt : v≤ cutoff N) (hb : 0≤ b) (hbd : b≤ P.d0) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb q)< v-Central.B ξ := by
  have hv100 := active_large P hξ hξh hθ hwval hvA hv
  have hp := low_payoff A hlow bud.low_room i v b (by linarith) hb hbd q
  have he := low_error_bound A (by linarith : 0≤ v) hvt
  have hB : Central.B ξ<2 := by unfold Central.B;linarith
  linarith [bud.utility_small]

include hwγ bud hθ hwval hvA in
theorem active_dichotomy (hH : A.H< Central.B ξ) (i : Fin (N+1)) (v : ℝ)
    (hv : P.vA-P.w≤ v) (hvt : v≤ cutoff N) (a : JointAction 2) (ha : a.bid< A.H) :
    (a.bid∈Icc (1:ℝ) A.D.U ∧ a.routeCount=2) ∨
      (problem Γ i).payoff v a< v-Central.B ξ := by
  let q : Fin 3 := ⟨a.routeCount,by have h:=a.routeCount_le;omega⟩
  have he : a=RawRoutes.action a.bid a.bid_nonneg q := raw_eq a
  rcases lower_bid_cases A hlow ha with hd | hp | hc | hu
  · right
    rw [he]
    exact active_low_below_face A hlow bud hθ hwval hvA i v a.bid hv hvt a.bid_nonneg hd q
  · right
    rw [he]
    exact active_partial_below_face A hlow hwγ bud hθ hwval hvA i v hv hvt ⟨a.bid,hp⟩ q
  · by_cases hq : q=2
    · left
      refine ⟨hc,?_⟩
      exact congrArg Fin.val hq
    · right
      rw [he]
      have hcases : q=0 ∨ q=1 ∨ q=2 := by omega
      rcases hcases with hq0 | hq1 | hq2
      · rw [hq0,zero_payoff A hlow]
        have hv100 := active_large P hξ hξh hθ hwval hvA hv
        unfold Central.B
        linarith
      · simpa only [hq1] using
          active_singleton_below_face A hlow hwγ bud hθ hwval hvA i v hv hvt ⟨a.bid,hc⟩
      · exact (hq hq2).elim
  · right
    rw [he]
    exact active_unused_below_face A hlow hwγ bud hθ hwval hvA i v a.bid hv hvt
      ⟨a.bid_nonneg,(ha.trans hH).le⟩ hu.1 hu.2 q

include hwγ bud hθ hwval in
theorem partial_bottom_positive (i : Fin (N+1)) (v : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) :
    0<(problem Γ i).payoff v (RawRoutes.action A.D.R A.D.hR.le 1) := by
  have hvb := partial_value_bounds hξh hwval hv
  have hR : Central.R ξ≤ v := by unfold Central.R;linarith [hvb.1]
  have hp := partial_bottom A hlow hwγ i v hR
  have hg := partial_high_price_gap P hξ hξh hθ hwval hv
  have he := partial_error_bound A (v:=v) (by linarith [hvb.1]) (by linarith [hvb.2.1,bud.cutoff_large])
  linarith [bud.utility_small,hvb.1]

include hwγ bud hθ hwval in
theorem partial_high_below_bottom (i : Fin (N+1)) (v : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) (a : JointAction 2) (ha : 1≤ a.bid) :
    (problem Γ i).payoff v a<
      (problem Γ i).payoff v (RawRoutes.action A.D.R A.D.hR.le 1) := by
  have hvb := partial_value_bounds hξh hwval hv
  have hR : Central.R ξ≤ v := by unfold Central.R;linarith [hvb.1]
  have hp := partial_bottom A hlow hwγ i v hR
  have hg := partial_high_price_gap P hξ hξh hθ hwval hv
  have he := partial_error_bound A (v:=v) (by linarith [hvb.1]) (by linarith [hvb.2.1,bud.cutoff_large])
  have hu := GlobalLower.payoff_le_value_sub_one (problem Γ i) v hvb.1 a ha
  linarith [bud.utility_small]

include hwγ bud hθ hwval in
theorem partial_low_below_bottom (i : Fin (N+1)) (v b : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) (hb : 0≤ b) (hbd : b≤ P.d0) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb q)<
      (problem Γ i).payoff v (RawRoutes.action A.D.R A.D.hR.le 1) := by
  have hvb := partial_value_bounds hξh hwval hv
  have hv0 : 0≤ v := by linarith [hvb.1]
  have hvt : v≤ cutoff N := by linarith [hvb.2.1,bud.cutoff_large]
  have hR : Central.R ξ≤ v := by unfold Central.R;linarith [hvb.1]
  have hp := partial_bottom A hlow hwγ i v hR
  have hg := partial_high_price_gap P hξ hξh hθ hwval hv
  have he := partial_error_bound A hv0 hvt
  have hl := low_payoff A hlow bud.low_room i v b hv0 hb hbd q
  have hel := low_error_bound A hv0 hvt
  linarith [bud.utility_small,hvb.1]

include hwγ bud hwval in
theorem partial_broadcast_le_singleton (i : Fin (N+1)) (v : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) (b : Icc A.D.R A.D.Up) :
    (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) 2)≤
      (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) 1) := by
  have hvb := partial_value_bounds hξh hwval hv
  have hab : |v|≤3 := by rw [abs_of_nonneg (by linarith [hvb.1])];exact hvb.2.1
  have hp := partial_broadcast_penalty A hlow hwγ i v b
  have he := (components_le P hξ A.forget.base_bulk_below N).2.2.1
  have hp0 := OrderedZeroSourcePartialCount.error_nonnegative P ξ N
  have hc := mul_le_mul_of_nonneg_right (show 2*|v|+4≤10 by linarith) hp0
  have hh := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤10)
  linarith [bud.partial_duplicate]

include hwγ bud hθ hwval in
theorem partial_unused_below_bottom (i : Fin (N+1)) (v b : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) (hb : b∈Icc (0:ℝ) (Central.B ξ))
    (htag : (regions A hlow).localTag (some b)=1) (hout : b∉Icc (1:ℝ) A.D.U) (q : Fin 3) :
    (problem Γ i).payoff v (RawRoutes.action b hb.1 q)<
      (problem Γ i).payoff v (RawRoutes.action A.D.R A.D.hR.le 1) := by
  have hR : Central.R ξ≤2 := by unfold Central.R;linarith
  have hp := partial_bottom A hlow hwγ i 2 hR
  have hu := unused_partial_center A hlow hwγ bud.unused_room.1 bud.unused_room.2
    hθ i b hb htag hout q
  have heP := partial_error_bound A (by norm_num : (0:ℝ)≤2) (by linarith [bud.cutoff_large])
  have heU := unused_error_bound A (by norm_num : (0:ℝ)≤2) (by linarith [bud.cutoff_large])
  have hgap : ξ/2-2*err≤
      (problem Γ i).payoff 2 (RawRoutes.action A.D.R A.D.hR.le 1)-
        (problem Γ i).payoff 2 (RawRoutes.action b hb.1 q) := by linarith
  have hvb := partial_value_bounds hξh hwval hv
  have ht := GlobalLower.action_gap_transport (problem Γ i)
    (RawRoutes.action A.D.R A.D.hR.le 1) (RawRoutes.action b hb.1 q)
    v 2 (ξ/2-2*err) P.w hgap hvb.2.2
  linarith [bud.utility_small]

include hwγ bud hθ hwval in
theorem partial_covered (hH : A.H< Central.B ξ) (i : Fin (N+1)) (v : ℝ)
    (hv : v∈Icc (2-P.w) (2+P.w)) (a : JointAction 2) (ha : a.bid< A.H) :
    ∃b : Icc A.D.R A.D.Up,
      (problem Γ i).payoff v a≤
        (problem Γ i).payoff v (RawRoutes.action b (A.D.hR.le.trans b.2.1) 1) := by
  let bot : Icc A.D.R A.D.Up := ⟨A.D.R,le_rfl,A.D.hRUp⟩
  let q : Fin 3 := ⟨a.routeCount,by have h:=a.routeCount_le;omega⟩
  have he : a=RawRoutes.action a.bid a.bid_nonneg q := raw_eq a
  by_cases hh : 1≤ a.bid
  · exact ⟨bot,(partial_high_below_bottom A hlow hwγ bud hθ hwval i v hv a hh).le⟩
  rcases lower_bid_cases A hlow ha with hd | hp | hc | hu
  · refine ⟨bot,?_⟩
    rw [he]
    exact (partial_low_below_bottom A hlow hwγ bud hθ hwval i v a.bid hv a.bid_nonneg hd q).le
  · rw [he]
    have hcases : q=0 ∨ q=1 ∨ q=2 := by omega
    rcases hcases with hq0 | hq1 | hq2
    · refine ⟨bot,?_⟩
      rw [hq0,zero_payoff A hlow]
      exact (partial_bottom_positive A hlow hwγ bud hθ hwval i v hv).le
    · exact ⟨⟨a.bid,hp⟩,by rw [hq1]⟩
    · exact ⟨⟨a.bid,hp⟩,by
        simpa only [hq2] using
          partial_broadcast_le_singleton A hlow hwγ bud hwval i v hv ⟨a.bid,hp⟩⟩
  · exact (hh hc.1).elim
  · refine ⟨bot,?_⟩
    rw [he]
    exact (partial_unused_below_bottom A hlow hwγ bud hθ hwval i v a.bid hv
      ⟨a.bid_nonneg,(ha.trans hH).le⟩ hu.1 hu.2 q).le

include hwγ bud in
theorem all_lower_success (hk : 0< k) (hH : A.H< Central.B ξ)
    (i : Fin (N+1)) (a : JointAction 2) (ha : a.bid< A.H) :
    ((problem Γ i).outcome a).success≤1-movingCoefficient P ξ k/(4*cutoff N^2) := by
  let C := movingCoefficient P ξ k
  let d := C/(4*cutoff N^2)
  have ht : 0< cutoff N := movingThreshold_pos (N+1) (by omega)
  have hC : 0< C := movingCoefficient_pos P hξ hk
  have hparts := components_le P hξ A.forget.base_bulk_below N
  have hθb : d+tot< P.theta := bud.other_failure.trans_le (min_le_left _ _)
  have hdb : d+tot<(probabilityGap ξ)^2 :=
    bud.other_failure.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h1b : d+tot<1 :=
    bud.other_failure.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let q : Fin 3 := ⟨a.routeCount,by have h:=a.routeCount_le;omega⟩
  have he : a=RawRoutes.action a.bid a.bid_nonneg q := raw_eq a
  rcases lower_bid_cases A hlow ha with hd | hp | hc | hu
  · have hs := low_success A hlow bud.low_room i a.bid a.bid_nonneg hd q
    rw [he]
    change _≤1-d
    linarith [hparts.2.2.2]
  · have hs := partial_success A hlow hwγ i ⟨a.bid,hp⟩ q
    rw [he]
    change _≤1-d
    linarith [hparts.2.2.1]
  · have hs := common_all_routes_failure A hlow hwγ hk i ⟨a.bid,hc⟩ q
    have hr : commonRate P ξ N≤ C/(2*cutoff N^2) := by
      apply (le_div_iff₀ (by positivity : 0<2*cutoff N^2)).mpr
      have hh := mul_le_mul_of_nonneg_left hparts.1 (sq_nonneg (cutoff N))
      linarith [bud.active_failure]
    have hd' : d≤ C/cutoff N^2-C/(2*cutoff N^2) := by
      dsimp only [d]
      field_simp [ht.ne']; nlinarith
    rw [he]
    change _≤1-d
    dsimp only [C] at hr hd'
    linarith
  · have hs := unused_all_routes_failure A hlow hwγ bud.unused_room.1 bud.unused_room.2
      i a.bid ⟨a.bid_nonneg,(ha.trans hH).le⟩ hu.1 hu.2 q
    rw [he]
    change _≤1-d
    linarith [hparts.2.1]

end FCAppendix.Affine.Tail04.OrderedSourceLowerComparisons
