import FCAppendix.Affine.Tail04.OrderedSourceLowerContracts
import FCAppendix.Affine.Tail04.OrderedSourceLowerComparisons
import FCAppendix.Affine.Tail04.OrderedSourceBoundaryBenchmark

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceGlobalLower
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation LowBody Hybrid
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open SourceMovingScalarGuards OrderedSourceFiniteStartingPoint OrderedSourceEndogenousFloor
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMultiplierRectangle
open OrderedSourceGlobalRates OrderedSourceMarketEstimates OrderedSourceCommonGlobal OrderedSourceLowerComparisons
open SourceBulkAnalyticAdapter SourceTailTaylor

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  (hlow : P.d0<1-ξ)

section Finite
variable {N : ℕ}
  (E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N)
  {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
  (hk0 : 0< k) (hκ : 0< κ) (hmin : 0< Amin) (hkhi : k<1/(2*Amax))
  (hwγ : width≤ γ ξ) (huB : 1+u< Central.B ξ)
  (hUpMargin : Up≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
  (hleading : ∀lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
  (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
  (hθ : P.theta≤ ξ/100) (hwval : P.w≤ ξ/1000)
  (hvA : P.vA=11*ξ/(10*P.theta))
  (bud : OrderedSourceGlobalRates.Budgets P ξ u k κ N)
  (floorBud : SourceFloorRates.Budgets P ξ Amin Amax k N)

local notation "A" => E.market
local notation "Γ" => OrderedSourceRestrictedNative.Market.native E.market hlow
local notation "V" => boundaryValue P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow
local notation "a0" => boundaryBid P ξ Up u k width hξ hξh hu hRUp hUp hw E.point hlow

include hk0 hκ hmin hkhi hwγ huB hUpMargin hsmall hrect hder hleading hρ hθ hwval hvA bud floorBud in

theorem raw_lower : RawLower E := by
  have hface : cutoff N-Central.B ξ< V :=
    OrderedSourceBoundaryBenchmark.boundary_above_face P ξ Up u k width hξ hξh hu hRUp hUp hw
      E.point hlow hk0 hmin hkhi huB hUpMargin hsmall hwγ hrect hleading hρ floorBud
  have hbenchmark (i : Fin (N+1)) (v : ℝ) (hvt : v≤ cutoff N) :
      v-Central.B ξ<(problem Γ i).payoff v (bandAction (by norm_num) 2 le_rfl a0) :=
    OrderedSourceBoundaryBenchmark.final_lower_benchmark P ξ Up u k width hξ hξh hu hRUp hUp hw
      E.point hlow hk0 hmin hkhi huB hUpMargin hsmall hwγ hrect hleading hρ floorBud
      E.ready i v hvt
  refine ⟨?_,?_,?_⟩
  · intro q
    fin_cases q
    · filter_upwards [bulk_all_active A hlow hwγ hκ hrect hder hρ bud] with x hx
      intro i a ha
      have hv : P.vA-P.w≤(x.1:ℝ) := x.1.2.1
      have hvt : (x.1:ℝ)≤ cutoff N := by
        have hv' : (x.1:ℝ)≤ P.vA+P.w := x.1.2.2
        linarith [P.active_tail_gap,(A).point.range.cutoff_gt_M]
      rcases active_dichotomy A hlow hwγ bud hθ hwval hvA E.ready.below_nominal
        i x.1 hv hvt a ha with hc | hs
      · have he : a=RawRoutes.action a.bid a.bid_nonneg 2 := by
          cases a with
          | mk b hb r hr =>
            dsimp at hc
            cases hc.2
            rfl
        rw [he]
        exact (hx i).2 ⟨a.bid,hc.1⟩
      · exact hs.le.trans (hx i).1.le
    · filter_upwards [(A).band_all_labels hlow (1:Fin 3)] with x hx
      intro i a ha
      have hv : P.vA-P.w≤(x.1:ℝ) := by
        have hv' : P.M≤(x.1:ℝ) := x.1.2.1
        linarith [P.active_tail_gap,P.w_pos]
      have hvt : (x.1:ℝ)≤ cutoff N := x.1.2.2
      have hgood : (x.1:ℝ)-Central.B ξ<
          (problem Γ i).payoff (x.1:ℝ)
            (bandAction (bidLo_pos (A).D 1).le 2 (by norm_num) x.2) :=
        (hbenchmark i x.1 hvt).trans_le (hx i a0)
      rcases active_dichotomy A hlow hwγ bud hθ hwval hvA E.ready.below_nominal
        i x.1 hv hvt a ha with hc | hs
      · have he : a=RawRoutes.action a.bid a.bid_nonneg 2 := by
          cases a with
          | mk b hb r hr =>
            dsimp at hc
            cases hc.2
            rfl
        rw [he]
        exact hx i ⟨a.bid,hc.1⟩
      · exact hs.le.trans hgood.le
    · filter_upwards [(A).band_all_labels hlow (2:Fin 3)] with x hx
      intro i a ha
      have hv : (x.1:ℝ)∈Icc (2-P.w) (2+P.w) := x.1.2
      obtain ⟨b,hb⟩ := partial_covered A hlow hwγ bud hθ hwval E.ready.below_nominal
        i x.1 hv a ha
      exact hb.trans (hx i b)
  · intro i a ha
    have hv : P.vA-P.w≤ cutoff N := by
      linarith [P.active_tail_gap,P.w_pos,(A).point.range.cutoff_gt_M]
    rcases active_dichotomy A hlow hwγ bud hθ hwval hvA E.ready.below_nominal
      i (cutoff N) hv le_rfl a ha with hc | hs
    · have he : a=RawRoutes.action a.bid a.bid_nonneg 2 := by
        cases a with
        | mk b hb r hr =>
          dsimp at hc
          cases hc.2
          rfl
      rw [he]
      exact final_boundary_max P ξ Up u k width hξ hξh hu hRUp hUp hw
        E.point hlow E.ready i ⟨a.bid,hc.1⟩
    · exact hs.le.trans hface.le
  · exact all_lower_success A hlow hwγ bud hk0 E.ready.below_nominal

end Finite

theorem eventually_all_lower {ρ κ Amin Amax : ℝ} {Λ : Set (ℝ×ℝ)}
    (hu0 : 0< u) (hκ : 0< κ) (hmin : 0< Amin)
    (hklo : 1/(4*Amin)< k) (hkhi : k<1/(2*Amax))
    (hwγ : width≤ γ ξ) (huB : 1+u< Central.B ξ)
    (hUpMargin : Up≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hrect : MomentInvariant P ξ ρ Λ) (hder : BulkDerivativeBound P ξ κ Λ)
    (hleading : ∀lam∈Λ,Amin≤ leadingA P ξ lam.1 lam.2 ∧ leadingA P ξ lam.1 lam.2≤ Amax)
    (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
    (hθ : P.theta≤ ξ/100) (hwval : P.w≤ ξ/1000)
    (hvA : P.vA=11*ξ/(10*P.theta)) :
    ∀ᶠN in atTop,∀E : Envelope P ξ Up u k width hξ hξh hu hRUp hUp hw hlow N,RawLower E := by
  have hk0 : 0< k := (by positivity : 0<1/(4*Amin)).trans hklo
  have hmax : 0< Amax := by
    have hh := one_div_pos.mp (hk0.trans hkhi)
    linarith
  filter_upwards [OrderedSourceGlobalRates.eventually_budgets P hξ hξh hu0 huB hk0 hκ,
    SourceFloorRates.eventually_budgets P hξ hmin hmax hklo] with N hbud hfloor
  intro E
  exact raw_lower P ξ Up u k width hξ hξh hu hRUp hUp hw hlow E hk0 hκ hmin hkhi
    hwγ huB hUpMargin hsmall hrect hder hleading hρ hθ hwval hvA hbud hfloor

end FCAppendix.Affine.Tail04.OrderedSourceGlobalLower
