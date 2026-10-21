import FCAppendix.Affine.Tail04.OrderedSourceMarketUnused
import FCAppendix.Affine.Tail04.OrderedSourceGlobalRates
import FCAppendix.Affine.Tail04.SourceBulkAnalyticAdapter

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceCommonGlobal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation LowBody
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedSourceRestrictedNative
open SourceMovingScalarGuards MenuError SourceMenuPopulation SourceMomentRectangle
open SourceMultiplierRectangle OrderedSourceMarketEstimates OrderedSourceGlobalRates SourceBulkAnalyticAdapter

lemma menu_at_face (P : ValueParameters) (ξ lamA lamR v : ℝ) :
    SourceMenuIdentity.menuUtility P ξ lamA lamR v (Central.B ξ)=v-Central.B ξ := by
  simp [SourceMenuIdentity.menuUtility,SourceMenuIdentity.payment,
    SourceMenuIdentity.served,SourceMenuIdentity.duplicates,SourceMenuIdentity.mixedProbability]

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width} {N : ℕ}
  (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)

include A in
lemma common_error_bound {v : ℝ} (_hv : 0≤ v) (hvt : v≤ cutoff N) :
    (v+2*Central.B ξ)*commonRate P ξ N≤ (utilityError P ξ u N) := by
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  have h0 := commonRate_nonneg P hξ N
  have ht0 := total_nonneg P hξ A.forget.base_bulk_below N
  have hc := (components_le P hξ A.forget.base_bulk_below N).1
  exact (mul_le_mul_of_nonneg_right (add_le_add hvt (le_refl (2*Central.B ξ))) h0).trans
    (mul_le_mul_of_nonneg_left hc (by
      have ht : 0< cutoff N := movingThreshold_pos (N+1) (by omega)
      linarith))

include A in
lemma unused_error_bound {v : ℝ} (_hv : 0≤ v) (hvt : v≤ cutoff N) :
    (v+2*Central.B ξ)*SourceUnusedConstants.rate P ξ u N≤ (utilityError P ξ u N) := by
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  have h0 := SourceUnusedConstants.rate_nonneg P hξ A.forget.base_bulk_below N
  have hc := (components_le P hξ A.forget.base_bulk_below N).2.1
  exact (mul_le_mul_of_nonneg_right (add_le_add hvt (le_refl (2*Central.B ξ))) h0).trans
    (mul_le_mul_of_nonneg_left hc (by
      have ht : 0< cutoff N := movingThreshold_pos (N+1) (by omega)
      linarith))

include A in
lemma partial_error_bound {v : ℝ} (hv : 0≤ v) (hvt : v≤ cutoff N) :
    v*OrderedZeroSourcePartialCount.error P ξ N≤ (utilityError P ξ u N) := by
  have hc := (components_le P hξ A.forget.base_bulk_below N).2.2.1
  have h0 := OrderedZeroSourcePartialCount.error_nonnegative P ξ N
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  exact (mul_le_mul_of_nonneg_right (show v≤ cutoff N+2*Central.B ξ by linarith) h0).trans
    (mul_le_mul_of_nonneg_left hc (by linarith))

include A in
lemma low_error_bound {v : ℝ} (hv : 0≤ v) (hvt : v≤ cutoff N) :
    v*OrderedSourceLowCountLaws.error P N≤ (utilityError P ξ u N) := by
  have hc := (components_le P hξ A.forget.base_bulk_below N).2.2.2
  have h0 : 0≤ OrderedSourceLowCountLaws.error P N := by unfold OrderedSourceLowCountLaws.error;positivity
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  exact (mul_le_mul_of_nonneg_right (show v≤ cutoff N+2*Central.B ξ by linarith) h0).trans
    (mul_le_mul_of_nonneg_left hc (by linarith))

variable {ρ κ : ℝ} {Λ : Set (ℝ×ℝ)}
  (hκ : 0< κ) (hrect : MomentInvariant P ξ ρ Λ)
  (hder : BulkDerivativeBound P ξ κ Λ)
  (hρ : relativeError P.zeta u (Central.B ξ)≤ ρ)
  (bud : OrderedSourceGlobalRates.Budgets P ξ u k κ N)

include hwγ hκ hrect hder hρ bud in
theorem bulk_outside_box_le_bottom (i : Fin (N+1))
    (v : ℝ) (hv : v∈Icc (P.vA-P.w) (P.vA+P.w))
    (b : Icc (1:ℝ) A.D.U) (hb : 1+u≤(b:ℝ)) :
    (problem (A.native hlow) i).payoff v (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)≤
      (problem (A.native hlow) i).payoff v (RawRoutes.action 1 (by norm_num) 2) := by
  have hv0 : 0≤ v := by
    linarith [hv.1,P.low_partial_gap,P.partial_active_gap,P.w_pos,P.d0_pos]
  have hvt : v≤ cutoff N := by linarith [hv.2,P.active_tail_gap,A.point.range.cutoff_gt_M]
  have hB1 : 1≤ Central.B ξ := by unfold Central.B;linarith
  have hbB : (b:ℝ)∈Icc (1:ℝ) (Central.B ξ) :=
    ⟨b.2.1,b.2.2.trans A.point.range.base_below_nominal.le⟩
  let a : Icc (1:ℝ) A.D.U := ⟨1,le_rfl,A.D.hU⟩
  have hd := source_slope P hder ((multiplier A hlow false),(multiplier A hlow true)) (multiplier_mem A hlow hrect hρ)
    v hv 1 b ⟨le_rfl,hB1⟩ hbB b.2.1
  have ha := common_payoff_error A hlow hwγ i v hv0 a
  have hb' := common_payoff_error A hlow hwγ i v hv0 b
  have he := common_error_bound A hv0 hvt
  have hg := mul_le_mul_of_nonneg_left (show u≤(b:ℝ)-1 by linarith) hκ.le
  have ha' := (abs_le.mp (ha.trans he)).1
  have hb'' := (abs_le.mp (hb'.trans he)).2
  change _≤(problem (A.native hlow) i).payoff v (RawRoutes.action (a:ℝ) (by norm_num [a]) 2)
  dsimp only [a,Subtype.coe_mk] at ha' hd
  linarith [bud.bulk_extension]

include hwγ hκ hrect hder hρ bud in
theorem bulk_bottom_above_face (i : Fin (N+1))
    (v : ℝ) (hv : v∈Icc (P.vA-P.w) (P.vA+P.w)) :
    v-Central.B ξ<(problem (A.native hlow) i).payoff v (RawRoutes.action 1 (by norm_num) 2) := by
  have hv0 : 0≤ v := by
    linarith [hv.1,P.low_partial_gap,P.partial_active_gap,P.w_pos,P.d0_pos]
  have hvt : v≤ cutoff N := by linarith [hv.2,P.active_tail_gap,A.point.range.cutoff_gt_M]
  have hB1 : 1≤ Central.B ξ := by unfold Central.B;linarith
  have hd := source_slope P hder ((multiplier A hlow false),(multiplier A hlow true)) (multiplier_mem A hlow hrect hρ)
    v hv 1 (Central.B ξ) ⟨le_rfl,hB1⟩ ⟨hB1,le_rfl⟩ hB1
  rw [menu_at_face] at hd
  let a : Icc (1:ℝ) A.D.U := ⟨1,le_rfl,A.D.hU⟩
  have he := common_payoff_error A hlow hwγ i v hv0 a
  have he' := (abs_le.mp (he.trans (common_error_bound A hv0 hvt))).1
  have huB := A.forget.base_bulk_below
  have hg := mul_lt_mul_of_pos_left (show u< Central.B ξ-1 by linarith) hκ
  have hn := utilityError_nonneg P hξ A.forget.base_bulk_below N
  dsimp only [a,Subtype.coe_mk] at he'
  linarith [bud.bulk_extension]

def bulkJoint : ProbabilityMeasure
    (Hybrid.ActiveValue (valueLo P 0) (valueHi P (cutoff N) 0) ×
      Hybrid.ActiveBaseBid (bidLo A.D 0) (bidHi A.D 0)) :=
  (A.sequence.limit (0:Fin 3)).1

include hwγ hκ hrect hder hρ bud in

theorem bulk_all_active :
    ∀ᵐx ∂(ProbabilityMeasure.toMeasure (bulkJoint A)),∀i : Fin (N+1),
      (x.1:ℝ)-Central.B ξ<
        (problem (A.native hlow) i).payoff (x.1:ℝ)
          (bandAction (bidLo_pos A.D 0).le 2 (by norm_num) x.2) ∧
      ∀b : Icc (1:ℝ) A.D.U,
        (problem (A.native hlow) i).payoff (x.1:ℝ)
          (RawRoutes.action b ((by norm_num : (0:ℝ)≤1).trans b.2.1) 2)≤
        (problem (A.native hlow) i).payoff (x.1:ℝ)
          (bandAction (bidLo_pos A.D 0).le 2 (by norm_num) x.2) := by
  filter_upwards [A.band_all_labels hlow 0] with x hx
  intro i
  let a : Hybrid.ActiveBaseBid (bidLo A.D 0) (bidHi A.D 0) :=
    ⟨1,le_rfl,by change 1≤1+u;linarith⟩
  have ha := hx i a
  change (problem (A.native hlow) i).payoff (x.1:ℝ) (RawRoutes.action 1 (by norm_num) 2)≤_ at ha
  have hv : (x.1:ℝ)∈Icc (P.vA-P.w) (P.vA+P.w) := x.1.2
  refine ⟨(bulk_bottom_above_face A hlow hwγ hκ hrect hder hρ bud i x.1 hv).trans_le ha,?_⟩
  intro b
  by_cases hb : (b:ℝ)≤1+u
  · exact hx i ⟨b,b.2.1,hb⟩
  · exact (bulk_outside_box_le_bottom A hlow hwγ hκ hrect hder hρ bud i x.1 hv b
      (le_of_not_ge hb)).trans ha

end FCAppendix.Affine.Tail04.OrderedSourceCommonGlobal
