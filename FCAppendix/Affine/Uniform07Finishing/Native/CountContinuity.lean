import FCAppendix.Affine.Uniform07Finishing.Native.SourcePhysicalCounts
import FCAppendix.Affine.Uniform07Finishing.Native.SourceBalancedExperiment
import FCAppendix.Affine.EqualCapacityBoundary

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine LowBody StrictNative Weighted
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

namespace FiniteCountContinuity
open FCAppendix.Affine.WeightedSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem continuousAt_oneDraw_mass_guarded (S : Finset ι) (i : ι)
    (w₀ : FCAppendix.Affine.WeightedSampling.Weights ι)
    (hw : 0 < FCAppendix.Affine.WeightedSampling.remainingWeight w₀ S) :
    ContinuousAt (fun w : FCAppendix.Affine.WeightedSampling.Weights ι =>
      (FCAppendix.Affine.WeightedSampling.oneDraw w S).mass i) w₀ := by
  have hn : Continuous (fun w : Weights ι => if i ∈ S then (0 : ℝ) else w.1 i) := by
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      exact continuous_const
    · simp only [if_neg hi]
      exact (continuous_apply i).comp continuous_subtype_val
  have hc := hn.continuousAt.div (continuous_remainingWeight S).continuousAt hw.ne'
  apply hc.congr_of_eventuallyEq
  filter_upwards [(FCAppendix.Affine.WeightedSampling.continuous_remainingWeight S).continuousAt
    (Ioi_mem_nhds hw)] with w hw'
  exact FCAppendix.Affine.WeightedSampling.oneDraw_mass w S hw' i

theorem continuousAt_pathLaw_mass_guarded
    (n : ℕ) (S : Finset ι) (p : FCAppendix.Affine.WeightedSampling.Path ι n)
    (w₀ : FCAppendix.Affine.WeightedSampling.Weights ι)
    (hw : (S.card : ℝ)+n < FCAppendix.Affine.WeightedSampling.totalWeight w₀) :
    ContinuousAt (fun w : FCAppendix.Affine.WeightedSampling.Weights ι =>
      (FCAppendix.Affine.WeightedSampling.pathLaw w n S).mass p) w₀ := by
  induction n generalizing S with
  | zero => exact continuousAt_const
  | succ n ih =>
    have hd : 0 < FCAppendix.Affine.WeightedSampling.remainingWeight w₀ S := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hw
      linarith [FCAppendix.Affine.WeightedSampling.denominator_lower w₀ S]
    have hc : ((insert p.1 S).card : ℝ) ≤ (S.card : ℝ)+1 := by
      exact_mod_cast Finset.card_insert_le p.1 S
    have hw' : ((insert p.1 S).card : ℝ)+n <
        FCAppendix.Affine.WeightedSampling.totalWeight w₀ := by
      push_cast at hw
      linarith
    exact (continuousAt_oneDraw_mass_guarded S p.1 w₀ hd).mul
      (ih (insert p.1 S) p.2 hw')

end FiniteCountContinuity

namespace Weighted
variable {m : ℕ}

def cappedFocalContext {U : ℝ} (X : ClassifiedContext m) (i : Fin m)
    (b : Icc (0 : ℝ) U) : ClassifiedContext m :=
  (Function.update X.1 i (some (b : ℝ)),X.2)

theorem cappedFocalContext_self {U : ℝ} (X : ClassifiedContext m) (i : Fin m)
    (b : Icc (0 : ℝ) U) (hi : X.1 i = some (b : ℝ)) :
    cappedFocalContext X i b = X := by
  apply Prod.ext
  · funext k
    by_cases hk : k=i
    · subst k
      simpa only [cappedFocalContext,Function.update_self] using hi.symm
    · simp only [cappedFocalContext,Function.update_of_ne hk]
  · rfl

theorem cappedFocalContext_present {U : ℝ} (X : ClassifiedContext m) (i : Fin m)
    (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) (k : Fin m) :
    (cappedFocalContext X i b).1 k ≠ none ↔ X.1 k ≠ none := by
  by_cases hk : k=i
  · subst k
    simp only [cappedFocalContext,Function.update_self]
    exact iff_of_true (Option.some_ne_none _) hi
  · simp only [cappedFocalContext,Function.update_of_ne hk]

@[simp] theorem cappedFocalContext_presentSet {U : ℝ} (X : ClassifiedContext m)
    (i : Fin m) (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) :
    presentSet (cappedFocalContext X i b).1 = presentSet X.1 := by
  ext k
  simp only [presentSet,Finset.mem_filter,Finset.mem_univ,true_and,
    cappedFocalContext_present X i hi b k]

@[simp] theorem cappedFocalContext_budget {U : ℝ} (X : ClassifiedContext m)
    (i : Fin m) (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) (c : ℕ) (j : Fin 2) :
    budget c j (cappedFocalContext X i b) = budget c j X := by
  simp only [budget,cappedFocalContext_presentSet X i hi b]
  rfl

@[simp] theorem cappedFocalContext_commonBudget {U : ℝ} (X : ClassifiedContext m)
    (i : Fin m) (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) (c : ℕ) :
    commonBudget c (cappedFocalContext X i b) = commonBudget c X := by
  simp only [commonBudget,cappedFocalContext_budget X i hi b]

@[simp] theorem cappedFocalContext_larger {U : ℝ} (X : ClassifiedContext m)
    (i : Fin m) (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) (c : ℕ) :
    larger c (cappedFocalContext X i b) = larger c X := by
  simp only [larger,cappedFocalContext_budget X i hi b]

theorem cappedFocalContext_nonnegative {U : ℝ} (X : ClassifiedContext m)
    (hX : NonnegativeList X.1) (i : Fin m) (b : Icc (0 : ℝ) U) :
    NonnegativeList (cappedFocalContext X i b).1 := by
  intro k
  by_cases hk : k=i
  · subst k
    simpa only [cappedFocalContext,Function.update_self,entryBid] using b.2.1
  · simpa only [cappedFocalContext,Function.update_of_ne hk] using hX k

theorem cappedFocalContext_bid_le {U : ℝ} (X : ClassifiedContext m)
    (hX : ∀k, entryBid (X.1 k) ≤ U) (i : Fin m) (b : Icc (0 : ℝ) U) :
    ∀k, entryBid ((cappedFocalContext X i b).1 k) ≤ U := by
  intro k
  by_cases hk : k=i
  · subst k
    simpa only [cappedFocalContext,Function.update_self,entryBid] using b.2.2
  · simpa only [cappedFocalContext,Function.update_of_ne hk] using hX k

theorem continuous_cappedFocalContext_entry {U : ℝ} (X : ClassifiedContext m)
    (i k : Fin m) : Continuous (fun b : Icc (0 : ℝ) U =>
      entryBid ((cappedFocalContext X i b).1 k)) := by
  by_cases hk : k=i
  · subst k
    simpa only [cappedFocalContext,Function.update_self,entryBid] using
      (continuous_subtype_val : Continuous (fun b : Icc (0 : ℝ) U => (b : ℝ)))
  · simp only [cappedFocalContext,Function.update_of_ne hk]
    exact continuous_const

theorem continuous_cappedFocalContext_listBids {U : ℝ} (X : ClassifiedContext m)
    (i : Fin m) : Continuous (fun b : Icc (0 : ℝ) U =>
      listBids (cappedFocalContext X i b).1) := by
  apply continuous_pi
  intro k
  simpa only [listBids_eq_entry] using continuous_cappedFocalContext_entry X i k

theorem continuous_cappedFocalContext_remainderBids {U : ℝ}
    (X : ClassifiedContext m) (i : Fin m) (E : Finset (Fin m)) :
    Continuous (fun b : Icc (0 : ℝ) U =>
      listBids (remainder (cappedFocalContext X i b).1 E)) := by
  apply continuous_pi
  intro k
  have he : (fun b : Icc (0:ℝ) U=>listBids (remainder (cappedFocalContext X i b).1 E) k)=
      (fun b=>if k∈E then 0 else listBids (cappedFocalContext X i b).1 k) := by
    funext b; exact remainder_bid _ E k
  rw [he]
  by_cases hk : k ∈ E
  · simp only [if_pos hk]; exact continuous_const
  · simp only [if_neg hk,listBids_eq_entry]
    exact continuous_cappedFocalContext_entry X i k

theorem continuous_cappedFocalContext_sourceWeights {ξ Λ r U : ℝ}
    (hξ : 0 < ξ) (hΛ : 0 < Λ) (X : ClassifiedContext m) (i : Fin m) :
    Continuous (fun b : Icc (0 : ℝ) U => sourceWeights ξ Λ r U (cappedFocalContext X i b).1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  by_cases hk : k=i
  · subst k
    have he : (fun b : Icc (0 : ℝ) U =>
        eligibleWeight ξ Λ r U ((cappedFocalContext X i b).1 i)) =
        (fun b : Icc (0:ℝ) U=>guardWeight r (ClippedResidual.exposure ξ Λ (b : ℝ))) := by
      funext b
      simp only [eligibleWeight,cappedFocalContext,Function.update_self,
        if_pos b.2.2]
    rw [he]
    exact (continuous_guardWeight r).comp
      ((ClippedResidual.continuous_exposure hξ hΛ).comp continuous_subtype_val)
  · simp only [cappedFocalContext,Function.update_of_ne hk]
    exact continuous_const

theorem continuous_cappedFocalContext_alpha
    {ξ Λ a r U d₀ z t width ε : ℝ} (hξ : 0 < ξ) (ha : 0 < a)
    (hlo : 0 < Λ-a) (hd : 0 < d₀) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (hi : X.1 i ≠ none) :
    Continuous (fun b : Icc (0 : ℝ) U =>
      (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c (cappedFocalContext X i b) : ℝ)) := by
  have hΛ : 0 < Λ := by linarith
  have hhi : 0 < Λ+a := by linarith
  have hD (v : ℝ) (hv : 0 < v) : Continuous (fun b : Icc (0 : ℝ) U =>
      sourceDemand ξ v (cappedFocalContext X i b).1) := by
    apply continuous_finsetSum
    intro k _
    exact (ClippedResidual.continuous_exposure hξ hv).comp
      (continuous_cappedFocalContext_entry X i k)
  have hJ : Continuous (fun b : Icc (0 : ℝ) U =>
      sourceRejectionDemand d₀ z (cappedFocalContext X i b).1) := by
    apply continuous_finsetSum
    intro k _
    exact (continuous_sourcePsi hd z).comp (continuous_cappedFocalContext_entry X i k)
  have hW := FCAppendix.Affine.WeightedSampling.continuous_totalWeight.comp
    (continuous_cappedFocalContext_sourceWeights (r := r) (U := U) hξ hΛ X i)
  have hC (b : Icc (0 : ℝ) U) :
      sourceCountSlacks t width (cappedFocalContext X i b) = sourceCountSlacks t width X := by
    simp only [sourceCountSlacks,cappedFocalContext_presentSet X i hi b]
    rfl
  have hS (k : Fin 7) : Continuous (fun b : Icc (0 : ℝ) U =>
      sourcePolicySlacks ξ Λ a r U d₀ z t width c (cappedFocalContext X i b) k) := by
    fin_cases k <;>
      dsimp only [sourcePolicySlacks,sourceSlacks] <;>
      simp only [cappedFocalContext_budget X i hi,cappedFocalContext_commonBudget X i hi,hC]
    · exact ((hD _ hlo).sub continuous_const).sub continuous_const
    · exact continuous_const.sub (hD _ hhi)
    · exact hW.sub continuous_const
    · exact (hJ.sub continuous_const).sub continuous_const
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  change Continuous (fun b : Icc (0:ℝ) U=>∏k : Fin 7,
    sourceRamp (ε*m) (sourcePolicySlacks ξ Λ a r U d₀ z t width c (cappedFocalContext X i b) k))
  convert! continuous_finsetProd Finset.univ
    (fun k _ => (continuous_sourceRamp (ε*m)).comp (hS k)) using 1

theorem cappedFocalContext_feasible {U : ℝ} (X : ClassifiedContext m) (i : Fin m)
    (hi : X.1 i ≠ none) (b : Icc (0 : ℝ) U) (c : ℕ)
    (P : ResidualPotential.Pair m) :
    ResidualPotential.Feasible (cappedFocalContext X i b).1
      (budget c 0 (cappedFocalContext X i b)) (budget c 1 (cappedFocalContext X i b)) P ↔
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P := by
  simp only [ResidualPotential.Feasible,LocallyFeasible,cappedFocalContext_budget X i hi b,
    cappedFocalContext_present X i hi b]

variable [Nonempty (Fin m)]

theorem cappedFocalContext_pureCopy_eventually
    {ξ U : ℝ} (hξ1 : ξ < 1) (c : ℕ) (X : ClassifiedContext m)
    (i : Fin m) (b₀ : Icc (0 : ℝ) U) (hi : X.1 i = some (b₀ : ℝ))
    (hg : contextCopyGeneric (1-ξ) i X) :
    ∀ᶠb : Icc (0 : ℝ) U in 𝓝 b₀,
      focalCopy (purePair ξ c (cappedFocalContext X i b)) i = focalCopy (purePair ξ c X) i := by
  have hip : X.1 i ≠ none := by rw [hi]; exact Option.some_ne_none _
  let f : Icc (0 : ℝ) U → ResidualPotential.Pair m → ℝ := fun b P =>
    ResidualPotential.objective (1-ξ) (cappedFocalContext X i b).1
      (budget c 0 X) (budget c 1 X) P
  let P₀ := purePair ξ c X
  let label : ResidualPotential.Pair m → Fin 3 := fun P =>
    if ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P then
      focalCopy P i else focalCopy P₀ i
  have hf (P : ResidualPotential.Pair m) : Continuous (fun b => f b P) := by
    have hfe (b : Icc (0 : ℝ) U) :
        ResidualPotential.Feasible (cappedFocalContext X i b).1
          (budget c 0 X) (budget c 1 X) P ↔
          ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P := by
      simpa only [cappedFocalContext_budget X i hip b] using
        cappedFocalContext_feasible X i hip b c P
    by_cases hP : ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P
    · have hpot : Continuous (fun b : Icc (0 : ℝ) U =>
          CompleteInformation.potential (1-ξ)
            (ResidualPotential.bid (cappedFocalContext X i b).1) P.1 P.2) := by
        unfold CompleteInformation.potential
        have hb (k : Fin m) : Continuous (fun b : Icc (0:ℝ) U=>
            max (entryBid ((cappedFocalContext X i b).1 k)) 0) :=
          (continuous_cappedFocalContext_entry X i k).max continuous_const
        exact (continuous_finsetSum _ (fun k _ => hb k)).add
          (continuous_const.mul (continuous_finsetSum _ (fun k _ => hb k)))
      simpa only [f,ResidualPotential.objective,hfe,if_pos hP] using hpot
    · simpa only [f,ResidualPotential.objective,hfe,if_neg hP] using
        (continuous_const : Continuous (fun _ : Icc (0 : ℝ) U => (-1 : ℝ)))
  have he : cappedFocalContext X i b₀ = X := cappedFocalContext_self X i b₀ hi
  have hgeneric : ∀P Q, f b₀ P = f b₀ Q → label P = label Q := by
    intro P Q hpq
    by_cases hP : ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P <;>
      by_cases hQ : ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) Q
    · simp only [f,he,ResidualPotential.objective,if_pos hP,if_pos hQ] at hpq
      simpa only [label,if_pos hP,if_pos hQ] using hg P Q hpq
    · have hn := ResidualPotential.potential_nonneg (1-ξ) (by linarith) X.1 P
      simp only [f,he,ResidualPotential.objective,if_pos hP,if_neg hQ] at hpq
      linarith
    · have hn := ResidualPotential.potential_nonneg (1-ξ) (by linarith) X.1 Q
      simp only [f,he,ResidualPotential.objective,if_neg hP,if_pos hQ] at hpq
      linarith
    · simp only [label,if_neg hP,if_neg hQ]
  have hs := selected_label_eventually_eq f hf label b₀ hgeneric
  filter_upwards [hs] with b hb
  have hfe := ResidualPotential.selection_feasible (1-ξ) (by linarith)
    (cappedFocalContext X i b).1 (budget c 0 X) (budget c 1 X)
  have hfe' : ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X)
      (FiniteSelector.select (f b)) := by
    apply (cappedFocalContext_feasible X i hip b c _).mp
    simpa only [cappedFocalContext_budget X i hip b,f,ResidualPotential.selection] using hfe
  have hf₀ := ResidualPotential.selection_feasible (1-ξ) (by linarith)
    X.1 (budget c 0 X) (budget c 1 X)
  have hf₀' : ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X)
      (FiniteSelector.select (f b₀)) := by
    simpa only [f,he,ResidualPotential.selection] using hf₀
  simp only [label,if_pos hfe',if_pos hf₀'] at hb
  simpa only [f,he,purePair,ResidualPotential.selection,cappedFocalContext_budget X i hip b] using hb

theorem continuousAt_cappedFocalContext_privateNone
    {ξ U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (i : Fin m)
    (b₀ : Icc (0 : ℝ) U) (hb₀ : 0 < (b₀ : ℝ)) (hi : X.1 i = some (b₀ : ℝ))
    (hg : contextCopyGeneric (1-ξ) i X) (q : Fin 3 → ℝ) :
    ContinuousAt (fun b : Icc (0 : ℝ) U =>
      privateCountMoment ξ hξ hξ1 c (cappedFocalContext X i b) none i q) b₀ := by
  have hip : X.1 i ≠ none := by rw [hi]; exact Option.some_ne_none _
  by_cases he : budget c 0 X = budget c 1 X
  · have hp : ContinuousAt (fun b : Icc (0 : ℝ) U =>
        EqualCapacity.positiveMarginal ξ (budget c 0 X)
          (listBids (cappedFocalContext X i b).1) i) b₀ := by
      have h := EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 (budget c 0 X)
        (listBids X.1) (fun k=>by simpa only [listBids_eq_entry] using hX k) i
        (by simpa only [listBids_eq_entry,hi,entryBid] using hb₀)
      have hv := (continuous_cappedFocalContext_listBids X i).continuousAt (x := b₀)
      have hc : ContinuousAt (fun bids=>EqualCapacity.positiveMarginal ξ (budget c 0 X) bids i)
          (listBids (cappedFocalContext X i b₀).1) := by
        rw [cappedFocalContext_self X i b₀ hi]
        exact h
      convert! hc.comp (f:=fun b : Icc (0:ℝ) U=>
        listBids (cappedFocalContext X i b).1) hv using 1
    have hpoly : ContinuousAt (fun b : Icc (0 : ℝ) U =>
        twoCountPolynomial q
          (EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids (cappedFocalContext X i b).1) i)
          (EqualCapacity.positiveMarginal ξ (budget c 0 X) (listBids (cappedFocalContext X i b).1) i)) b₀ := by
      exact (continuousAt_const.add (continuousAt_const.mul (hp.add hp))).add
        (continuousAt_const.mul (hp.mul hp))
    convert hpoly using 1
    funext b
    rw [privateCountMoment_equal ξ hξ hξ1 c _ none
      (by simpa only [cappedFocalContext_budget X i hip b] using he),
      cappedFocalContext_budget X i hip b]
  · apply (continuousAt_const : ContinuousAt (fun _ : Icc (0 : ℝ) U =>
      q (focalCopy (purePair ξ c X) i)) b₀).congr_of_eventuallyEq
    filter_upwards [cappedFocalContext_pureCopy_eventually hξ1 c X i b₀ hi hg] with b hb
    rw [privateCountMoment_none ξ hξ hξ1 c _
      (by simpa only [cappedFocalContext_budget X i hip b] using he),hb]

def balancedCountPolynomial (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (i : Fin m) (q : Fin 3 → ℝ) : ℝ :=
  let p := EqualCapacity.positiveMarginal ξ (commonBudget c X) (listBids (remainder X.1 E)) i
  twoCountPolynomial q
    (if (0 : Fin 2)=larger c X ∧ i∈E then 1 else p)
    (if (1 : Fin 2)=larger c X ∧ i∈E then 1 else p)

omit [Nonempty (Fin m)] in
theorem continuousAt_cappedFocalContext_balancedPolynomial
    {ξ U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1) (i : Fin m)
    (b₀ : Icc (0 : ℝ) U) (hb₀ : 0 < (b₀ : ℝ)) (hi : X.1 i = some (b₀ : ℝ))
    (E : Finset (Fin m)) (q : Fin 3 → ℝ) :
    ContinuousAt (fun b : Icc (0 : ℝ) U =>
      balancedCountPolynomial ξ c (cappedFocalContext X i b) E i q) b₀ := by
  have hip : X.1 i ≠ none := by rw [hi]; exact Option.some_ne_none _
  have hp : ContinuousAt (fun b : Icc (0 : ℝ) U =>
      EqualCapacity.positiveMarginal ξ (commonBudget c X)
        (listBids (remainder (cappedFocalContext X i b).1 E)) i) b₀ := by
    by_cases hiE : i ∈ E
    · have hz (b : Icc (0 : ℝ) U) : EqualCapacity.positiveMarginal ξ (commonBudget c X)
          (listBids (remainder (cappedFocalContext X i b).1 E)) i = 0 := by
        apply EqualCapacity.onSupport_outside
        rw [Existence.PayOnceBounded.mem_positiveSupport,remainder_bid,if_pos hiE]
        exact lt_irrefl 0
      simpa only [hz] using (continuousAt_const : ContinuousAt (fun _ : Icc (0 : ℝ) U => (0 : ℝ)) b₀)
    · have hrem := remainder_nonnegative X.1 hX E
      have hpos : 0 < listBids (remainder X.1 E) i := by
        rw [remainder_bid,if_neg hiE,listBids_eq_entry,hi]
        exact hb₀
      have h := EqualCapacity.continuousAt_positiveMarginal_focal hξ hξ1 (commonBudget c X)
        (listBids (remainder X.1 E)) (fun k=>by simpa only [listBids_eq_entry] using hrem k) i hpos
      have hv := (continuous_cappedFocalContext_remainderBids X i E).continuousAt (x:=b₀)
      have hc : ContinuousAt (fun bids=>EqualCapacity.positiveMarginal ξ (commonBudget c X) bids i)
          (listBids (remainder (cappedFocalContext X i b₀).1 E)) := by
        rw [cappedFocalContext_self X i b₀ hi]
        exact h
      convert! hc.comp (f:=fun b : Icc (0:ℝ) U=>
        listBids (remainder (cappedFocalContext X i b).1 E)) hv using 1
  have h₀ : ContinuousAt (fun b : Icc (0 : ℝ) U =>
      if (0 : Fin 2)=larger c X ∧ i∈E then (1 : ℝ) else
        EqualCapacity.positiveMarginal ξ (commonBudget c X)
          (listBids (remainder (cappedFocalContext X i b).1 E)) i) b₀ := by
    split_ifs <;> first | exact continuousAt_const | exact hp
  have h₁ : ContinuousAt (fun b : Icc (0 : ℝ) U =>
      if (1 : Fin 2)=larger c X ∧ i∈E then (1 : ℝ) else
        EqualCapacity.positiveMarginal ξ (commonBudget c X)
          (listBids (remainder (cappedFocalContext X i b).1 E)) i) b₀ := by
    split_ifs <;> first | exact continuousAt_const | exact hp
  simp only [balancedCountPolynomial,cappedFocalContext_commonBudget X i hip,
    cappedFocalContext_larger X i hip,twoCountPolynomial]
  exact (continuousAt_const.add (continuousAt_const.mul (h₀.add h₁))).add
    (continuousAt_const.mul (h₀.mul h₁))

theorem abs_finitePathCountCorrection_le_mul_alpha
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (Λ r U : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (X : ClassifiedContext m)
    (i : Fin m) (q : Fin 3 → ℝ) :
    |finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q| ≤
      (α X : ℝ)*(2*∑r : Fin 3, |q r|) := by
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights ξ Λ r U X.1
  let P := FCAppendix.Affine.WeightedSampling.pathLaw w Δ ∅
  have hB := abs_privateCountMoment_le ξ hξ hξ1 c X none i q
  have hM : |P.expect (fun p => privateCountMoment ξ hξ hξ1 c X
      (some (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p)) i q)| ≤ ∑r : Fin 3, |q r| := by
    apply (FCAppendix.Affine.WeightedSampling.abs_expect_le P _).trans
    exact FCAppendix.Affine.WeightedSampling.expect_le_const P _ _
      (fun p _ => abs_privateCountMoment_le ξ hξ hξ1 c X _ i q)
  unfold finitePathCountCorrection
  dsimp only
  split_ifs
  · rw [abs_mul,abs_of_nonneg (α X).2.1]
    apply mul_le_mul_of_nonneg_left _ (α X).2.1
    exact (abs_sub _ _).trans (by change _ ≤ 2*∑r : Fin 3, |q r|; linarith)
  · simp only [abs_zero]
    exact mul_nonneg (α X).2.1 (mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))

theorem finitePathCountCorrection_zero_alpha
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (Λ r U : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (X : ClassifiedContext m)
    (hα : (α X : ℝ)=0) (i : Fin m) (q : Fin 3 → ℝ) :
    finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q=0 := by
  unfold finitePathCountCorrection
  dsimp only
  split_ifs <;> simp only [hα,zero_mul]

theorem finitePathCountCorrection_equal_budget
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (Λ r U : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (X : ClassifiedContext m)
    (he : budget c 0 X=budget c 1 X) (i : Fin m) (q : Fin 3 → ℝ) :
    finitePathCountCorrection ξ hξ hξ1 Λ r U c α X i q=0 := by
  rw [←integral_sourceCountCorrection]
  simp_rw [sourceCountCorrection_equal ξ hξ hξ1 Λ r U c α X _ he i q]
  simp only [integral_zero]

theorem finitePathCountCorrection_balanced
    (row : Uniform07.Row) {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k, entryBid (X.1 k) ≤ R)
    (hExc : (exceptionalSet (Early.bidCap row) X.1).card ≤ 1)
    (he : budget c 0 X ≠ budget c 1 X)
    (hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ))
    (i : Fin m) (q : Fin 3 → ℝ) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
    let w := sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1
    finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row) c α X i q =
      (α X : ℝ)*((FCAppendix.Affine.WeightedSampling.pathLaw w Δ ∅).expect
        (fun p => balancedCountPolynomial (Uniform07.xi row) c X
          (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p) i q)-
        privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
          (source_xi_lt_one row) c X none i q) := by
  have ho := sourceGuardAlpha_outer c hm hε X hα 2
  change ε*m < FCAppendix.Affine.WeightedSampling.totalWeight
    (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)-
      ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ) at ho
  have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have hW : ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ) <
      FCAppendix.Affine.WeightedSampling.totalWeight
        (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1) := by
    linarith
  dsimp only
  rw [finitePathCountCorrection,if_pos ⟨hExc,hW⟩]
  apply congrArg (fun y : ℝ =>
    (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ)*(y-
      privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) c X none i q))
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : 0 < (FCAppendix.Affine.WeightedSampling.pathLaw
      (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).mass p
  · have hvalid := literal_source_path_certificate row hΛ hR hguard hm hε c X hX hbid hα p hp
    congr 1
    change privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row) c X
      (some (FCAppendix.Affine.WeightedSampling.finalSet
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p)) i q=_
    rw [privateCountMoment_weighted _ _ _ _ _ _ he hvalid]
    rfl
  · have hz := le_antisymm (le_of_not_gt hp)
      (FCAppendix.Affine.WeightedSampling.mass_nonneg _ p)
    simp only [hz,zero_mul]

omit [Nonempty (Fin m)] in
theorem exceptionalSet_empty_of_all_le {U : ℝ} (L : LocalList m)
    (hL : ∀k, entryBid (L k) ≤ U) : exceptionalSet U L = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  exact (not_lt_of_ge (hL k)) (Finset.mem_filter.mp hk).2.2

theorem continuousAt_cappedFocalContext_finiteCorrection
    (row : Uniform07.Row) {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hUR : Early.bidCap row < R) (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hcap : ∀k, entryBid (X.1 k) ≤ Early.bidCap row)
    (i : Fin m) (b₀ : Icc (0 : ℝ) (Early.bidCap row))
    (hb₀ : 0 < (b₀ : ℝ)) (hi : X.1 i = some (b₀ : ℝ))
    (hg : contextCopyGeneric (1-Uniform07.xi row) i X) (q : Fin 3 → ℝ) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    ContinuousAt (fun b : Icc (0 : ℝ) (Early.bidCap row) =>
      finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row) c α
        (cappedFocalContext X i b) i q) b₀ := by
  let ξ := Uniform07.xi row
  let U := Early.bidCap row
  let α := sourceGuardAlpha (m:=m) ξ Λ (Early.nativeRadius row) (Early.demandRatio row) U
    (Uniform07.cutoff row/1000) zG (Uniform07.cutoff row) width ε c
  let C := fun b : Icc (0 : ℝ) U => cappedFocalContext X i b
  let F := fun b : Icc (0 : ℝ) U => finitePathCountCorrection ξ (Uniform07.xi_pos row)
    (source_xi_lt_one row) Λ (Early.demandRatio row) U c α (C b) i q
  have hip : X.1 i ≠ none := by rw [hi]; exact Option.some_ne_none _
  have hself : C b₀=X := cappedFocalContext_self X i b₀ hi
  have ha : Continuous (fun b : Icc (0 : ℝ) U => (α (C b) : ℝ)) :=
    continuous_cappedFocalContext_alpha (Uniform07.xi_pos row)
      (Early.native_sampling_margin_guards row).1 (source_guard_root_positive row hΛ)
      (div_pos (Uniform07.cutoff_pos row) (by norm_num)) c X i hip
  have hB := continuousAt_cappedFocalContext_privateNone (Uniform07.xi_pos row)
    (source_xi_lt_one row) c X hX i b₀ hb₀ hi hg q
  change ContinuousAt F b₀
  by_cases he : budget c 0 X=budget c 1 X
  · have hz (b : Icc (0 : ℝ) U) : F b=0 :=
      finitePathCountCorrection_equal_budget ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) U c α (C b)
        (by simpa only [C,cappedFocalContext_budget X i hip b] using he) i q
    have heF : F=(fun _ : Icc (0:ℝ) U=>(0:ℝ)) := funext hz
    rw [heF]
    exact continuousAt_const
  by_cases hz : (α X : ℝ)=0
  · have hzF : F b₀=0 := by
      change finitePathCountCorrection ξ (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) U c α (C b₀) i q=0
      rw [hself]
      exact finitePathCountCorrection_zero_alpha _ _ _ _ _ _ _ α X hz i q
    change Tendsto F (𝓝 b₀) (𝓝 (F b₀))
    rw [hzF]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hl : Tendsto (fun b : Icc (0 : ℝ) U =>
        (α (C b) : ℝ)*(2*∑r : Fin 3, |q r|)) (𝓝 b₀) (𝓝 0) := by
      simpa only [hself,hz,zero_mul] using (ha.continuousAt (x:=b₀)).tendsto.mul_const (2*∑r : Fin 3, |q r|)
    apply squeeze_zero (fun _ => norm_nonneg _) _ hl
    intro b
    simpa only [Real.norm_eq_abs,F] using abs_finitePathCountCorrection_le_mul_alpha ξ
      (Uniform07.xi_pos row) (source_xi_lt_one row) Λ (Early.demandRatio row) U c α (C b) i q
  · have hp : 0 < (α X : ℝ) := lt_of_le_of_ne (α X).2.1 (Ne.symm hz)
    let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
    let w := fun b : Icc (0 : ℝ) U => sourceWeights ξ Λ (Early.demandRatio row) U (C b).1
    have hw : Continuous w := continuous_cappedFocalContext_sourceWeights
      (Uniform07.xi_pos row) (source_guard_multiplier_positive row hΛ) X i
    have ho := sourceGuardAlpha_outer c hm hε X hp 2
    change ε*m < FCAppendix.Affine.WeightedSampling.totalWeight
      (sourceWeights ξ Λ (Early.demandRatio row) U X.1)-(Δ : ℝ) at ho
    have hW : (Δ : ℝ) < FCAppendix.Affine.WeightedSampling.totalWeight (w b₀) := by
      have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
      simp only [w,hself]
      change (Δ : ℝ) < _
      linarith
    let H := fun b : Icc (0 : ℝ) U =>
      (FCAppendix.Affine.WeightedSampling.pathLaw (w b) Δ ∅).expect
        (fun p => balancedCountPolynomial ξ c (C b)
          (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p) i q)
    have hterm (p : FCAppendix.Affine.WeightedSampling.Path (Fin m) Δ) :
        ContinuousAt (fun b : Icc (0 : ℝ) U =>
          (FCAppendix.Affine.WeightedSampling.pathLaw (w b) Δ ∅).mass p *
            balancedCountPolynomial ξ c (C b)
              (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p) i q) b₀ := by
      have hmass := (FiniteCountContinuity.continuousAt_pathLaw_mass_guarded
        Δ ∅ p (w b₀) (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW)).comp
          hw.continuousAt
      exact hmass.mul (continuousAt_cappedFocalContext_balancedPolynomial (Uniform07.xi_pos row)
        (source_xi_lt_one row) c X hX i b₀ hb₀ hi _ q)
    have hH : ContinuousAt H b₀ := by
      change ContinuousAt (fun b : Icc (0 : ℝ) U => ∑p,
        (FCAppendix.Affine.WeightedSampling.pathLaw (w b) Δ ∅).mass p *
          balancedCountPolynomial ξ c (C b)
            (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p) i q) b₀
      have hs (s : Finset (FCAppendix.Affine.WeightedSampling.Path (Fin m) Δ)) :
          ContinuousAt (fun b : Icc (0 : ℝ) U => ∑p ∈ s,
            (FCAppendix.Affine.WeightedSampling.pathLaw (w b) Δ ∅).mass p *
              balancedCountPolynomial ξ c (C b)
                (FCAppendix.Affine.WeightedSampling.finalSet Δ ∅ p) i q) b₀ := by
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          exact continuousAt_const
        | @insert p s hpS ihS =>
          simp only [Finset.sum_insert hpS]
          convert! (hterm p).add ihS using 1
      exact hs Finset.univ
    have hprod : ContinuousAt (fun b : Icc (0 : ℝ) U => (α (C b) : ℝ)*
        (H b-privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (C b) none i q)) b₀ :=
      ha.continuousAt.mul (hH.sub hB)
    apply hprod.congr_of_eventuallyEq
    have hevent : ∀ᶠb : Icc (0 : ℝ) U in 𝓝 b₀, 0 < (α (C b) : ℝ) := by
      apply ha.continuousAt (Ioi_mem_nhds _)
      simpa only [hself] using hp
    filter_upwards [hevent] with b hb
    have hcapb := cappedFocalContext_bid_le X hcap i b
    have hEx : (exceptionalSet U (C b).1).card ≤ 1 := by
      rw [exceptionalSet_empty_of_all_le (C b).1 hcapb]
      simp
    have h := finitePathCountCorrection_balanced row hΛ hR hguard hm hε c (C b)
      (cappedFocalContext_nonnegative X hX i b) (fun k => (hcapb k).trans hUR.le)
      hEx (by simpa only [C,cappedFocalContext_budget X i hip b] using he) hb i q
    let K : ℕ→ℝ:=fun n=>(α (C b):ℝ)*
      ((FCAppendix.Affine.WeightedSampling.pathLaw (w b) n ∅).expect
        (fun p=>balancedCountPolynomial ξ c (C b)
          (FCAppendix.Affine.WeightedSampling.finalSet n ∅ p) i q)-
        privateCountMoment ξ (Uniform07.xi_pos row) (source_xi_lt_one row) c (C b) none i q)
    have hd : max (budget c 0 (C b)) (budget c 1 (C b))-commonBudget c (C b)=Δ := by
      dsimp only [C,Δ]
      rw [cappedFocalContext_budget X i hip b,cappedFocalContext_budget X i hip b,
        cappedFocalContext_commonBudget X i hip b]
    have hh : F b=K (max (budget c 0 (C b)) (budget c 1 (C b))-commonBudget c (C b)) := by
      convert! h using 1
    exact hh.trans (congrArg K hd)

end Weighted
end FCAppendix.Affine.Uniform07Finishing
