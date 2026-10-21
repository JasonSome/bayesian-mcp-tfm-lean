import FCAppendix.Affine.Uniform06.ZeroWeightFocal
import FCAppendix.Affine.Uniform06.RawSamplingBounds
import FCAppendix.Affine.Uniform06.MaskedReciprocal

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawPathAdapter

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 RawMixedSource RawTiltedSource RawMarkedLaplace LiteralExperiment
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open PathNumerator ZeroWeightFocal FiniteSampledLaplace SampledCellDomination
open LiteralCoarsePath LiteralKernelIdentity RawDeficitGeometry FixedPriceRawDerivative

variable {N : ℕ} [Nonempty (Fin N)]

structure ValidCounts (c : ℕ) (ω : Fin N → RowRival) : Prop where
  upper₀ : classCount 1 ω+classCount 2 ω ≤ c
  upper₁ : classCount 1 ω+classCount 3 ω ≤ c
  lower₀ : c-classCount 1 ω-classCount 2 ω ≤ 1+classCount 0 ω
  lower₁ : c-classCount 1 ω-classCount 3 ω ≤ 1+classCount 0 ω

omit [Nonempty (Fin N)] in
lemma literal_weights_eq_lift (ξ : ℝ) (g : GuardData) (c : ℕ) (b : ℝ)
    (hb : b ≤ g.multiplier) (hr : 0 < g.requiredDemand) (ω : Fin N → RowRival) :
    weights ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)=
      liftWeights (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω) := by
  apply Subtype.ext
  funext j
  refine Fin.cases ?_ (fun q => ?_) j
  · have hzero := SourceGuardGeometry.low_focal_weight_zero (ξ := ξ) g
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0 hr
      (by simpa only [rowBids,Fin.cons_zero] using hb)
    simpa only [liftWeights,Fin.cons_zero] using hzero
  · by_cases ht : (ω q).1=0
    · simp [weights,succ_mem,ht,rowBids,liftWeights,rowWeights,rawWeight]
    · simp [weights,succ_mem,ht,rowBids,liftWeights,rowWeights,rawWeight]

omit [Nonempty (Fin N)] in
lemma literal_imbalance_eq (c : ℕ) (ω : Fin N → RowRival) (hc : ValidCounts c ω) :
    imbalance (patternTemplate c (fun j => (ω j).1))=(imbalanceSum ω).natAbs :=
  (template_imbalance_eq_draws c ω hc.upper₀ hc.upper₁ hc.lower₀ hc.lower₁).trans
    (draws_eq_natAbs ω)

omit [Nonempty (Fin N)] in
lemma literal_balanced_deficit_eq (i : Row) (c : ℕ) {b : ℝ} (hb : 0 < b)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω) :
    balancedTemplateDeficit (xi i) (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0=
      (c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω :=
  template_deficit_eq_raw i c hb ω hc.upper₀ hc.upper₁ hc.lower₀ hc.lower₁

def selectedProfile (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) (E : Finset (Fin N)) :
    Fin (N+1) → ℝ :=
  maskedBids (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) (liftSet E)

def selectedResponse (i : Row) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival)
    (k : ℕ) (p : Path (Fin N) k) : ℝ :=
  EqualCapacity.positiveMarginal (xi i)
    (small (patternTemplate c (fun j => (ω j).1)))
      (selectedProfile c b ω (finalSet k ∅ p)) 0

lemma selectedProfile_focal (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) (E : Finset (Fin N)) :
    selectedProfile c b ω E 0=b := by
  simp only [selectedProfile,maskedBids,Finset.mem_sdiff,focal_mem,zero_not_liftSet,
    not_false_eq_true,and_self,if_true,rowBids,Fin.cons_zero]

omit [Nonempty (Fin N)] in
lemma selectedProfile_cap (c : ℕ) {b U : ℝ} (hU : 0 ≤ U) (hbU : b ≤ U)
    (ω : Fin N → RowRival) (hcap : ∀ j,(ω j).1=0 → (ω j).2 ≤ U)
    (E : Finset (Fin N)) : ∀ j,selectedProfile c b ω E j ≤ U := by
  intro j
  unfold selectedProfile maskedBids
  split_ifs
  · refine Fin.cases (by simpa only [rowBids,Fin.cons_zero] using hbU) (fun q => ?_) j
    by_cases ht : (ω q).1=0
    · simpa only [rowBids,Fin.cons_succ,if_pos ht] using hcap q ht
    · simpa only [rowBids,Fin.cons_succ,if_neg ht] using hU
  · exact hU

theorem selected_h_identity (ξ : ℝ) (g : GuardData) (b : ℝ) (ω : Fin N → RowRival)
    (k : ℕ) (hW : (k:ℝ) < totalWeight (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω))
    (p : Path (Fin N) k)
    (hp : 0 < (pathLaw (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω) k ∅).mass p) :
    (∑ j ∈ liftSet (finalSet k ∅ p),(1/2-exposure ξ b (rowBids b ω j)))=
      ∑ j,rawH ξ b (ω (tuple k p j)) := by
  let w := rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω
  have hw : ((∅:Finset (Fin N)).card:ℝ)+k < totalWeight w := by simpa only [Finset.card_empty,Nat.cast_zero,zero_add,w] using hW
  have hpos := finalSet_weight_pos w k ∅ hw (by simp) p hp
  have hs := selectedSum_eq_setSum w (fun j => rawH ξ b (ω j)) k ∅ hw p hp
  rw [tuple_sum_eq_selectedSum (fun j => rawH ξ b (ω j)) k p,hs]
  simp only [Finset.sum_empty,sub_zero]
  rw [liftSet,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have ht : (ω j).1=0 := by
      by_contra hn
      have hh := hpos j hj
      simp only [w,rowWeights,rawWeight,if_neg hn] at hh
      exact (lt_irrefl 0) hh
    simp [rowBids,rawH,RawMixedSource.demand,ht]
  · intro x hx y hy he
    exact Fin.succ_inj.mp he

theorem selected_deficit_identity (i : Row) (c : ℕ) (g : GuardData) {b : ℝ}
    (hb : 0 < b) (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ) < totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0 < (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p) :
    (small (patternTemplate c (fun j => (ω j).1)):ℝ)-
      remainingDemand (xi i) (selectedProfile c b ω (finalSet k ∅ p)) {0} b=
        (c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω-
          ∑ j,rawH (xi i) b (ω (tuple k p j)) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let E := liftSet (finalSet k ∅ p)
  have himb : imbalance T=k := (literal_imbalance_eq c ω hc).trans hk.symm
  have hcard : E.card=imbalance T := by
    rw [liftSet_card]
    have hh := finalSet_card (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
      k ∅ (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW) p hp
    simpa only [Finset.card_empty,zero_add,himb] using hh
  have he := focalDeficit_eq_balanced (xi i) T B E 0 (zero_not_liftSet _) hcard
  rw [literal_balanced_deficit_eq i c hb ω hc] at he
  have hs := selected_h_identity (xi i) g b ω k hW p hp
  change (∑ j ∈ E,(1/2-exposure (xi i) b (B j)))=_ at hs
  have hB0 : B 0=b := rfl
  simp only [focalDeficit,hB0,hs] at he
  rw [selectedProfile,masked_demand_eq T B E 0 hb (rowBids_outside _ _ _)]
  exact he

theorem actual_rival_path_transport (ξ : ℝ) (g : GuardData) (c : ℕ) (b : ℝ)
    (hb : b ≤ g.multiplier) (hr : 0 < g.requiredDemand) (ω : Fin N → RowRival)
    (k : ℕ) (hW : (k:ℝ) < totalWeight (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω))
    (F : Path (Fin (N+1)) k → ℝ) :
    (pathLaw (weights ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) k ∅).expect F=
      (pathLaw (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω) k ∅).expect
        (fun p => F (liftPath k p)) := by
  rw [literal_weights_eq_lift ξ g c b hb hr ω]
  simpa only [liftSet,Finset.image_empty,Finset.card_empty,zero_add] using
    expect_lift (rowWeights (rawWeight ξ g) (rawWeight_bounds ξ g) ω) k ∅
      (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW) F

end FCAppendix.Affine.Uniform06.RawPathAdapter
