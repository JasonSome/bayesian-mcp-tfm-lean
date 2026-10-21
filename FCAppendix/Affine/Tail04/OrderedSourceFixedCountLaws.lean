import FCAppendix.Affine.Tail04.OrderedActiveCountPassage
import FCAppendix.Affine.Tail04.SourceTailOptimizer

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceFixedCountLaws
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues SourceMenuIdentity SourceTailOptimizer SourceMultiplierRectangle
open SourceBulkAnalyticAdapter SourceMomentRectangle SourceMovingScalarGuards
open OrderedSourceRestrictedNative OrderedSourceActiveCountData OrderedSourceActiveSpecified

variable (P : ValueParameters) (ξ Up u k width : ℝ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u)
  (hRUp : Central.R ξ< Up) (hUp : Up<1) (hw : 0< width)
  (hlow : P.d0<1-ξ) (hwγ : width≤ γ ξ)
  (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
  (A : ∀j,Market P ξ Up u k width hξ hξh hu hRUp hUp hw (N j))

local notation "B0" => Central.B ξ
local notation "ls" => fun j=> lambda (A j) hlow
local notation "G" => fun j=> specified (A j) hlow

include hξ hN in
lemma fixed_error_tendsto (v : ℝ) :
    Tendsto (fun j=>2*ActiveFixedValueVersions.error ξ (rate P ξ (N j)) v) atTop (𝓝 0) := by
  have hh:=((rate_tendsto_zero P hξ).comp hN).const_mul (2*(max 0 v+2*B0))
  simpa only [ActiveFixedValueVersions.error,Function.comp_apply,mul_assoc,mul_zero] using hh

include u hξ hlow N hN A in
theorem bulk_bid_concentration {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (hls : Tendsto ls atTop (𝓝 lam)) (v : ℝ) (hv : v∈P.bulkValues)
    (δ : ℝ) (hδ : 0< δ) :
    ∀ᶠj in atTop,∀ᵐa ∂(G j).σ v,
      a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) B0 ∧ |a.bid-1|< δ := by
  have hB : 1≤ B0 := by unfold Central.B;linarith
  let b : Icc (1:ℝ) B0:=⟨1,le_rfl,hB⟩
  have hstrict : ∀a : Icc (1:ℝ) B0,a≠b→
      menuUtility P ξ lam.1 lam.2 v a< menuUtility P ξ lam.1 lam.2 v b := by
    intro a ha
    have ha' : 1<(a:ℝ) := lt_of_le_of_ne a.2.1 (fun hh=> ha (Subtype.ext hh.symm))
    have hh:=source_slope P hder lam hlam v hv 1 a b.2 a.2 a.2.1
    have hp:=mul_pos hκ (sub_pos.mpr ha')
    linarith
  exact OrderedActiveCountPassage.conditional_neighborhood P ξ B0 v lam ls hls
    (fun _=>1+u) (fun _=> by linarith)
    (fun j=>(A j).forget.base_bulk_below.le) (fun j=>(G j).σ v)
    (fun j=>2*ActiveFixedValueVersions.error ξ (rate P ξ (N j)) v)
    (fixed_error_tendsto (P:=P) (ξ:=ξ) (hξ:=hξ) (N:=N) (hN:=hN) v)
    b hstrict (Eventually.of_forall fun _=> by dsimp [b];linarith)
    (Eventually.of_forall fun j=> specified_bulk (A j) hlow v hv) δ hδ

include k hlow N hN A in
theorem tail_bid_concentration {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (hls : Tendsto ls atTop (𝓝 lam)) (v : ℝ) (hv : P.M≤ v)
    (δ : ℝ) (hδ : 0< δ) :
    ∀ᶠj in atTop,∀ᵐa ∂(G j).σ v,
      a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) B0 ∧
        |a.bid-(beta P ξ hξ lam v:ℝ)|< δ := by
  have hb:=beta_spec P ξ hξ hgeom lam hlam v hv
  have hf : ∀ᶠj in atTop,(beta P ξ hξ lam v:ℝ)≤(A j).D.U := by
    have hh:=((cap_tendsto ξ k).comp hN).eventually (lt_mem_nhds hb.1.2)
    exact hh.mono fun j hj=> hj.le
  have hregret : ∀ᶠj in atTop,∀ᵐa ∂(G j).σ v,
      a.routeCount=2 ∧ a.bid∈Icc (1:ℝ) (A j).D.U ∧
        ∀y : Icc (1:ℝ) (A j).D.U,
          menuUtility P ξ (ls j).1 (ls j).2 v y≤
            menuUtility P ξ (ls j).1 (ls j).2 v a.bid+
              2*ActiveFixedValueVersions.error ξ (rate P ξ (N j)) v := by
    filter_upwards [(cutoff_tendsto.comp hN).eventually_ge_atTop v] with j hj
    exact specified_tail (A j) hlow v ⟨hv,hj⟩
  exact OrderedActiveCountPassage.conditional_neighborhood P ξ B0 v lam ls hls
    (fun j=>(A j).D.U) (fun j=>(A j).D.hU)
    (fun j=>(A j).point.range.base_below_nominal.le) (fun j=>(G j).σ v)
    (fun j=>2*ActiveFixedValueVersions.error ξ (rate P ξ (N j)) v)
    (fixed_error_tendsto (P:=P) (ξ:=ξ) (hξ:=hξ) (N:=N) (hN:=hN) v)
    (beta P ξ hξ lam v) hb.2.2 hf hregret δ hδ

include Up u k width hξ hξh hu hRUp hUp hw hlow hwγ hN A in
theorem original_fixed_bulk_limit {κ : ℝ} (hκ : 0< κ) {Λ : Set (ℝ×ℝ)}
    (hder : BulkDerivativeBound P ξ κ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (hls : Tendsto ls atTop (𝓝 lam)) :
    ∀v∈P.bulkValues,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((ParametricMenuCount.law P ξ lam 1).mass r)) := by
  intro v hv r
  have hB : 1≤ B0 := by unfold Central.B;linarith
  refine OrderedActiveCountPassage.native_count_tendsto P ξ B0
    (fun j=> N j+1) (fun j=>(A j).D.c) (fun _=> NativeLocalPolicy.Seed) G
    (fun j=> Nat.succ_pos (N j)) v lam ls hls ⟨1,le_rfl,hB⟩
    (fun j=> rate P ξ (N j)) ((rate_tendsto_zero P hξ).comp hN) ?_ r ?_
  · exact bulk_bid_concentration P ξ Up u k width hξ hξh hu hRUp hUp hw hlow
      N hN A hκ hder lam hlam hls v hv
  · apply Eventually.of_forall
    intro j i
    filter_upwards [specified_bulk (A j) hlow v hv] with a ha
    rw [specified_problem (A j) hlow hwγ i]
    exact count_mass_error (A j) hlow hwγ i a ha.1
      ⟨ha.2.1.1,ha.2.1.2.trans (A j).D.huU⟩ r

include Up u k width hξh hu hRUp hUp hw hlow hwγ hN A in
theorem original_fixed_tail_limit {Λ : Set (ℝ×ℝ)}
    (hgeom : DerivativeGeometry P ξ Λ) (lam : ℝ×ℝ) (hlam : lam∈Λ)
    (hls : Tendsto ls atTop (𝓝 lam)) :
    ∀v,P.M≤ v→∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((ParametricMenuCount.law P ξ lam (beta P ξ hξ lam v)).mass r)) := by
  intro v hv r
  refine OrderedActiveCountPassage.native_count_tendsto P ξ B0
    (fun j=> N j+1) (fun j=>(A j).D.c) (fun _=> NativeLocalPolicy.Seed) G
    (fun j=> Nat.succ_pos (N j)) v lam ls hls (beta P ξ hξ lam v)
    (fun j=> rate P ξ (N j)) ((rate_tendsto_zero P hξ).comp hN) ?_ r ?_
  · exact tail_bid_concentration P ξ Up u k width hξ hξh hu hRUp hUp hw hlow
      N hN A hgeom lam hlam hls v hv
  · filter_upwards [(cutoff_tendsto.comp hN).eventually_ge_atTop v] with j hj
    intro i
    filter_upwards [specified_tail (A j) hlow v ⟨hv,hj⟩] with a ha
    rw [specified_problem (A j) hlow hwγ i]
    exact count_mass_error (A j) hlow hwγ i a ha.1 ha.2.1 r

include ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ hN A in
theorem original_fixed_low_limit :
    ∀v∈Icc (0:ℝ) P.d0,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)) := by
  intro v hv r
  have hh:=OrderedSourcePartialCountLaws.original_fixed_low_limit P ξ Up u k width hξ hξh hu
    hRUp hUp hw hlow N hN (fun j=>(A j).forget) v hv r
  simpa only [specified_lower_count (A _) hlow hwγ v (Or.inl hv)] using hh

include ξ Up u k width hξ hξh hu hRUp hUp hw hlow hwγ hN A in
theorem original_fixed_partial_limit :
    ∀v∈P.partialValues,∀r : Fin 3,
      Tendsto (fun j=>(conditionalTypeCountLaw (G j) (Nat.succ_pos (N j)) v).mass r)
        atTop (𝓝 ((Counts.singletonLaw (1-P.theta)
          ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩).mass r)) := by
  intro v hv r
  have hh:=OrderedSourcePartialCountLaws.original_fixed_partial_limit P ξ Up u k width hξ hξh hu
    hRUp hUp hw hlow hwγ N hN (fun j=>(A j).forget) v hv r
  simpa only [specified_lower_count (A _) hlow hwγ v (Or.inr hv)] using hh

end FCAppendix.Affine.Tail04.OrderedSourceFixedCountLaws
