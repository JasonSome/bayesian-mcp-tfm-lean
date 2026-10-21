import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Guard
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Counts
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapGuard

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open Uniform06 Uniform06.LiteralExperiment
open scoped BigOperators
variable {m : ℕ}

def rowCountCoordinates (D : UniformFinite.Source.CountRow m) : Fin 3→ℝ :=
  ![(D.lower.card:ℝ)/m,(D.upper0:ℝ)/m,(D.upper1:ℝ)/m]

def rowGuardData (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (D : UniformFinite.Source.CountRow m) : GuardData :=
  { received06GuardData i m G.multiplier G.rejectionRoot with
    countMargin:=encodedCount (UniformFinite.Source.commonGuardMargin i) (m:ℝ)
      (rowCountCoordinates D) (categoryMean i) }

@[simp] theorem rowGuardData_small (D : UniformFinite.Source.CountRow m) :
    small (UniformFinite.Source.lowerTemplate D)=UniformFinite.Source.small D := rfl

@[simp] theorem rowGuardData_imbalance (D : UniformFinite.Source.CountRow m) :
    imbalance (UniformFinite.Source.lowerTemplate D)=UniformFinite.Source.imbalance D := rfl

@[simp] theorem mask_lower_idempotent (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    UniformFinite.Source.lowerBids D (UniformFinite.Source.lowerBids D b)=
      UniformFinite.Source.lowerBids D b := by
  funext j
  by_cases hj : j∈D.lower <;> simp [UniformFinite.Source.lowerBids,hj]

theorem received_weights_eq (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    weights (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) (UniformFinite.Source.lowerBids D b)=
      UniformFinite.Source.sourceWeights i G D b := by
  apply Subtype.ext
  funext j
  by_cases hj : j∈D.lower
  · simp only [weights,UniformFinite.Source.lowerTemplate,hj,if_true,
      UniformFinite.Source.lowerBids_of_mem D b hj,UniformFinite.Source.sourceWeights,
      FiniteGuards.eligibility,Uniform05.lawWeight,Uniform05.guardWeight,
      Uniform05.xi_eq_canonical,demand_eq,rowGuardData,received06GuardData,
      SourcePrefixConstructor.sourceGuard,FiniteGuards.clip01,Uniform05.clip01]
  · simp [weights,UniformFinite.Source.lowerTemplate,UniformFinite.Source.sourceWeights,hj]

theorem sum_supported_mask {f : ℝ→ℝ} (hf : f 0=0)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    (∑ j∈D.lower,f (UniformFinite.Source.lowerBids D b j))=
      ∑ j,f (UniformFinite.Source.lowerBids D b j) := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp only [UniformFinite.Source.lowerBids_of_not_mem D b hj,hf]

theorem received_demand_eq (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    demand (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D)
      (UniformFinite.Source.lowerBids D b) ((rowGuardData i G D).multiplier-(rowGuardData i G D).radius)=
      UniformFinite.Source.lowDemand i G D b ∧
    demand (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D)
      (UniformFinite.Source.lowerBids D b) ((rowGuardData i G D).multiplier+(rowGuardData i G D).radius)=
      UniformFinite.Source.highDemand i G D b := by
  have hz:=UniformFinite.Source.rootBounds i G
  constructor
  · change (∑j∈D.lower,ClippedResidual.exposure (Uniform07.xi i)
      (G.multiplier-SourcePrefixConstructor.radius i) (UniformFinite.Source.lowerBids D b j))=_
    rw [←radius_eq i]
    change (∑j∈D.lower,ClippedResidual.exposure (Uniform07.xi i)
      (UniformFinite.Source.rootLo i G) (UniformFinite.Source.lowerBids D b j))=_
    rw [sum_supported_mask (ClippedResidual.exposure_zero hz.1.le)]
    simp only [UniformFinite.Source.lowDemand,Uniform05.xi_eq_canonical]
  · change (∑j∈D.lower,ClippedResidual.exposure (Uniform07.xi i)
      (G.multiplier+SourcePrefixConstructor.radius i) (UniformFinite.Source.lowerBids D b j))=_
    rw [←radius_eq i]
    change (∑j∈D.lower,ClippedResidual.exposure (Uniform07.xi i)
      (UniformFinite.Source.rootHi i G) (UniformFinite.Source.lowerBids D b j))=_
    rw [sum_supported_mask (ClippedResidual.exposure_zero (hz.1.trans hz.2.1).le)]
    simp only [UniformFinite.Source.highDemand,Uniform05.xi_eq_canonical]

theorem received_rejection_eq (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    (∑ j∈D.lower,PrefixRoot.psi ((rowGuardData i G D).rejectionScale)
      (rowGuardData i G D).rejectionRoot (UniformFinite.Source.lowerBids D b j))=
      UniformFinite.Source.rejectionSum i G D b := by
  have hz : 0≤ G.rejectionRoot := by
    have ht:=Uniform05.t_pos i
    nlinarith [G.rejectionRoot_guards.1]
  have hz0 : PrefixRoot.psi (Uniform07.cutoff i/1000) G.rejectionRoot 0=0 := by
    unfold PrefixRoot.psi
    rw [show max 0 (0-G.rejectionRoot)=0 by exact max_eq_left (by linarith)]
    simp
  change (∑j∈D.lower,PrefixRoot.psi (Uniform07.cutoff i/1000) G.rejectionRoot
    (UniformFinite.Source.lowerBids D b j))=_
  rw [sum_supported_mask hz0]
  simp only [UniformFinite.Source.rejectionSum,Uniform05.rejectionExposure,
    PrefixRoot.psi,Concrete05.rejection_scale_eq]

theorem received_seed_iff (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    seeded (rowGuardData i G D) (UniformFinite.Source.lowerTemplate D)
      (UniformFinite.Source.lowerBids D b) ↔ UniformFinite.Source.seedCount i D b≠0 := by
  simp only [seeded,rowGuardData,received06GuardData,SourcePrefixConstructor.sourceGuard,
    UniformFinite.Source.lowerTemplate,UniformFinite.Source.seedCount,
    Finset.card_ne_zero,Finset.filter_nonempty_iff,Uniform05.t_eq_canonical]
  exact exists_congr fun j=>by
    constructor
    · rintro ⟨hj,hb⟩
      exact ⟨hj,by simpa only [UniformFinite.Source.lowerBids_of_mem D b hj] using hb⟩
    · rintro ⟨hj,hb⟩
      exact ⟨hj,by simpa only [UniformFinite.Source.lowerBids_of_mem D b hj] using hb⟩

theorem received_guardAlpha_eq (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (hm : 0< m) (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) :
    guardAlpha (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) (UniformFinite.Source.lowerBids D b)=
      UniformFinite.Source.guardAlpha i G D b := by
  have hs:=received_seed_iff i G D b
  by_cases hz : UniformFinite.Source.seedCount i D b=0
  · have hn : ¬seeded (rowGuardData i G D) (UniformFinite.Source.lowerTemplate D)
        (UniformFinite.Source.lowerBids D b) := fun h=>hs.mp h hz
    simp only [guardAlpha,FiniteGuards.alpha,UniformFinite.Source.guardAlpha,hz,
      if_true,if_neg hn]
  · rw [guardAlpha,FiniteGuards.alpha,if_pos (hs.mpr hz),
      UniformFinite.Source.guardAlpha,if_neg hz]
    have hd:=received_demand_eq i G D b
    have hr:=received_rejection_eq i G D b
    unfold slackVector
    rw [received_weights_eq,hd.1,hd.2,rowGuardData_small,rowGuardData_imbalance]
    simp only [UniformFinite.Source.lowerTemplate]
    rw [hr]
    have hseven:=seven_factors_eq_five (UniformFinite.Source.common_guard_margin i)
      (Nat.cast_pos.mpr hm)
      ![UniformFinite.Source.lowDemand i G D b-(UniformFinite.Source.small D:ℝ)-
          UniformFinite.Source.imbalance D,
        (UniformFinite.Source.small D:ℝ)-UniformFinite.Source.highDemand i G D b,
        WeightedSampling.totalWeight (UniformFinite.Source.sourceWeights i G D b)-
          UniformFinite.Source.imbalance D,
        UniformFinite.Source.rejectionSum i G D b-
          (UniformFinite.Source.residual D 0:ℝ)-UniformFinite.Source.residual D 1]
      (rowCountCoordinates D) (categoryMean i)
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at hseven
    change (∏ j : Fin 5,FiniteGuards.ramp
      (2*UniformFinite.Source.commonGuardMargin i*(m:ℝ))
      (UniformFinite.Source.commonGuardMargin i*(m:ℝ))
      (![UniformFinite.Source.lowDemand i G D b-(UniformFinite.Source.small D:ℝ)-
          UniformFinite.Source.imbalance D,
        (UniformFinite.Source.small D:ℝ)-UniformFinite.Source.highDemand i G D b,
        WeightedSampling.totalWeight (UniformFinite.Source.sourceWeights i G D b)-
          UniformFinite.Source.imbalance D,
        UniformFinite.Source.rejectionSum i G D b-
          (UniformFinite.Source.residual D 0:ℝ)-UniformFinite.Source.residual D 1,
        encodedCount (UniformFinite.Source.commonGuardMargin i) (m:ℝ)
          (rowCountCoordinates D) (categoryMean i)] j))=_
    rw [hseven]
    simp only [UniformFinite.Source.rawAlpha,UniformFinite.Source.sourceSlacks,
      UniformFinite.Source.totalResidual,Nat.cast_add,sub_add_eq_sub_sub,
      rowCountCoordinates,categoryMean,Uniform05.t_eq_canonical,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons]

def successTest (k : Fin 3) : ℝ := if k=0 then 0 else 1
def duplicateTest (k : Fin 3) : ℝ := if k=2 then 1 else 0

theorem successTest_pairCount (j : Fin m) (P : UniformFinite.Allocation m) :
    successTest (UniformFinite.pairCount j P)=first j P := by
  by_cases h0 : j∈P.1 <;> by_cases h1 : j∈P.2 <;>
    simp [successTest,UniformFinite.pairCount,first,LiteralExperiment.indicator,h0,h1]

theorem duplicateTest_pairCount (j : Fin m) (P : UniformFinite.Allocation m) :
    duplicateTest (UniformFinite.pairCount j P)=duplicate j P := by
  by_cases h0 : j∈P.1 <;> by_cases h1 : j∈P.2 <;>
    simp [duplicateTest,UniformFinite.pairCount,duplicate,LiteralExperiment.indicator,h0,h1]

theorem first05_eq06 (j : Fin m) (P : UniformFinite.Allocation m) :
    UniformFinite.Literal.firstCopy j P=first j P := rfl

theorem duplicate05_eq06 (j : Fin m) (P : UniformFinite.Allocation m) :
    UniformFinite.Literal.duplicateCopy j P=duplicate j P := rfl

theorem lowerBids_eq_of_outside (D : UniformFinite.Source.CountRow m)
    (b : Fin m→ℝ) (hb : ∀j,j∉D.lower→ b j=0) :
    UniformFinite.Source.lowerBids D b=b := by
  funext j
  by_cases hj : j∈D.lower <;> simp [UniformFinite.Source.lowerBids,hj,hb j]

theorem received_complement_eq_native (D : UniformFinite.Source.CountRow m)
    (b : Fin m→ℝ) (_hb : ∀j,j∉D.lower→ b j=0) (E : Finset (Fin m)) (xi : ℝ) :
    complementMarginal xi (UniformFinite.Source.lowerTemplate D) b E=
      EqualCapacity.positiveMarginal xi
        (Weighted.commonBudget (Uniform07.capacity m) (Concrete05.rowContext D b))
        (Existence.PayOnceBounded.listBids
          (Weighted.remainder (Concrete05.rowContext D b).1 E)) := by
  have hd:=Concrete05.decoded_small (Concrete05.rowContext D b) (Concrete05.rowContext_valid D b)
  rw [Concrete05.rowContext_decode] at hd
  unfold complementMarginal
  rw [rowGuardData_small,hd]
  have hbid : maskedBids (UniformFinite.Source.lowerTemplate D) b E=
      Existence.PayOnceBounded.listBids
        (Weighted.remainder (Concrete05.rowContext D b).1 E) := by
    funext j
    by_cases hj : j∈D.lower <;> by_cases he : j∈E <;>
      simp [maskedBids,UniformFinite.Source.lowerTemplate,Concrete05.rowContext,
        Weighted.remainder,Existence.PayOnceBounded.listBids,hj,he]
  rw [hbid]

variable [Nonempty (Fin m)]

theorem received_canonical_tests_eq_native (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (D : UniformFinite.Source.CountRow m)
    (b : Fin m→ℝ) (hb : ∀j,j∉D.lower→ b j=0)
    (hU : ∀j,b j≤ Early.bidCap i) (j : Fin m) :
    (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (first j)=
      (Weighted.sourceBalancedAllocationLaw (Uniform07.xi i) G.multiplier
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.capacity m)
          (Concrete05.rowContext D b)).expect (fun P=>successTest (focalCopy P j)) ∧
    (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (duplicate j)=
      (Weighted.sourceBalancedAllocationLaw (Uniform07.xi i) G.multiplier
        (Early.demandRatio i) (Early.bidCap i) (Uniform07.capacity m)
          (Concrete05.rowContext D b)).expect (fun P=>duplicateTest (focalCopy P j)) := by
  let X:=Concrete05.rowContext D b
  have hX:=Concrete05.rowContext_valid D b
  have hB:=lowerBids_eq_of_outside D b hb
  have hentry : (fun k=>entryBid (X.1 k))=b := by
    simpa only [X,Concrete05.rowContext_entry] using hB
  have hXu : ∀k,entryBid (X.1 k)≤ Early.bidCap i := by
    intro k
    rw [show entryBid (X.1 k)=b k from congrFun hentry k]
    exact hU k
  have hweights:=Concrete05.decoded_sourceWeights i G X hXu
  simp only [X,Concrete05.rowContext_decode,Concrete05.rowContext_entry,hB] at hweights
  have hweights06:=received_weights_eq i G D b
  rw [hB] at hweights06
  have himb:=Concrete05.decoded_imbalance X hX
  simp only [X,Concrete05.rowContext_decode] at himb
  constructor
  · rw [canonical_path_first (Uniform07.xi_pos i) (source_xi_lt_one i),
      Weighted.sourceBalancedAllocationLaw_expect (Uniform07.xi_pos i) (source_xi_lt_one i),
      hweights06,hweights,rowGuardData_imbalance,himb]
    apply FiniteLaw.expect_congr
    intro p
    rw [Concrete05.sourceBalancedPolynomial_eq_unoriented,
      ←received_complement_eq_native D b hb]
    by_cases he : j∈WeightedSampling.finalSet _ ∅ p <;>
      simp [he,twoCountPolynomial,successTest] <;> ring
  · rw [canonical_path_duplicate (Uniform07.xi_pos i) (source_xi_lt_one i),
      Weighted.sourceBalancedAllocationLaw_expect (Uniform07.xi_pos i) (source_xi_lt_one i),
      hweights06,hweights,rowGuardData_imbalance,himb]
    apply FiniteLaw.expect_congr
    intro p
    rw [Concrete05.sourceBalancedPolynomial_eq_unoriented,
      ←received_complement_eq_native D b hb]
    by_cases he : j∈WeightedSampling.finalSet _ ∅ p
    · rw [complement_marginal_zero _ _ _ _ _ he]
      simp [he,twoCountPolynomial,duplicateTest]
    · simp [he,twoCountPolynomial,duplicateTest]
      ring

theorem received_canonical_tests_eq05 (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) [NeZero m] (hm : 0< m)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ)
    (hb : ∀j,j∉D.lower→ b j=0) (hU : ∀j,b j≤ Early.bidCap i)
    (ha : 0< UniformFinite.Source.rawAlpha i G D b) (j : Fin m) :
    (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (first j)=
      (UniformFinite.canonicalLaw i G D b).expect (UniformFinite.Literal.firstCopy j) ∧
    (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (duplicate j)=
      (UniformFinite.canonicalLaw i G D b).expect (UniformFinite.Literal.duplicateCopy j) := by
  let X:=Concrete05.rowContext D b
  have hX:=Concrete05.rowContext_valid D b
  have hB:=lowerBids_eq_of_outside D b hb
  have hentry : (fun k=>entryBid (X.1 k))=b := by
    simpa only [X,Concrete05.rowContext_entry] using hB
  have hXu : ∀k,entryBid (X.1 k)≤ Early.bidCap i := by
    intro k
    rw [show entryBid (X.1 k)=b k from congrFun hentry k]
    exact hU k
  have haX : 0< UniformFinite.Source.rawAlpha i G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k)) := by
    simpa only [X,Concrete05.rowContext_decode,Concrete05.rowContext_entry,hB] using ha
  have hS:=Concrete05.decoded_canonical_count_moment i G hm X hX hXu haX j successTest
  have hD:=Concrete05.decoded_canonical_count_moment i G hm X hX hXu haX j duplicateTest
  simp only [X,Concrete05.rowContext_decode,Concrete05.rowContext_entry,hB,
    successTest_pairCount,duplicateTest_pairCount] at hS hD
  have h06:=received_canonical_tests_eq_native i G D b hb hU j
  exact ⟨h06.1.trans hS.symm,h06.2.trans hD.symm⟩

theorem received_continuation_tests_eq05 (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) [NeZero m] (hm : 0< m)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ)
    (hb : ∀j,j∉D.lower→ b j=0) (hU : ∀j,b j≤ Early.bidCap i) (j : Fin m) :
    (continuationLaw (Uniform07.xi i) (Uniform07.kappa i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (first j)=
      UniformFinite.successProbability i G D b j ∧
    (continuationLaw (Uniform07.xi i) (Uniform07.kappa i) (rowGuardData i G D)
      (UniformFinite.Source.lowerTemplate D) b).expect (duplicate j)=
      UniformFinite.duplicateProbability i G D b j := by
  have hB:=lowerBids_eq_of_outside D b hb
  have ha:=received_guardAlpha_eq i G hm D b
  rw [hB] at ha
  by_cases he : UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1
  · have hmask : maskedBids (UniformFinite.Source.lowerTemplate D) b ∅=b := by
      funext k
      by_cases hk : k∈D.lower <;> simp [maskedBids,UniformFinite.Source.lowerTemplate,hk,hb k]
    have hlot : complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅=
        UniformFinite.equalLottery i D b := by
      change ExactCapacity.symmetricLottery
        (EqualCapacity.positiveMarginal (Uniform07.xi i) (UniformFinite.Source.small D)
          (maskedBids (UniformFinite.Source.lowerTemplate D) b ∅))=
        ExactCapacity.symmetricLottery
        (EqualCapacity.positiveMarginal (Uniform05.xi i) (UniformFinite.Source.small D)
          (UniformFinite.Source.lowerBids D b))
      rw [hmask,hB,Uniform05.xi_eq_canonical]
    have heq : continuationLaw (Uniform07.xi i) (Uniform07.kappa i) (rowGuardData i G D)
        (UniformFinite.Source.lowerTemplate D) b=UniformFinite.equalLaw i D b := by
      unfold continuationLaw
      rw [if_pos (show (UniformFinite.Source.lowerTemplate D).residual₀=
        (UniformFinite.Source.lowerTemplate D).residual₁ from he),hlot]
      rfl
    change (_ : FiniteLaw (UniformFinite.Allocation m)).expect (first j)=
        (UniformFinite.continuationLaw i G D b).expect (first j) ∧
      (_ : FiniteLaw (UniformFinite.Allocation m)).expect (duplicate j)=
        (UniformFinite.continuationLaw i G D b).expect (duplicate j)
    rw [heq,UniformFinite.continuationLaw,if_pos he]
    exact ⟨rfl,rfl⟩
  · have hneg : (UniformFinite.Source.lowerTemplate D).residual₀≠
        (UniformFinite.Source.lowerTemplate D).residual₁ := he
    simp only [continuationLaw,if_neg hneg,UniformFinite.successProbability,
      UniformFinite.duplicateProbability,UniformFinite.continuationLaw,if_neg he,
      FiniteLaw.expect_mixture,ha,UniformFinite.pureLaw,FiniteLaw.expect_dirac,
      hB,Uniform05.kappa_eq_canonical,first05_eq06,duplicate05_eq06]
    by_cases hz : UniformFinite.Source.guardAlpha i G D b=0
    · simp only [hz,zero_mul,zero_add]
      constructor <;> trivial
    · have ha0 : 0< UniformFinite.Source.guardAlpha i G D b :=
        lt_of_le_of_ne (UniformFinite.Source.guardAlpha_bounds i G D b).1 (Ne.symm hz)
      have haraw : 0< UniformFinite.Source.rawAlpha i G D b := by
        unfold UniformFinite.Source.guardAlpha at ha0
        split_ifs at ha0
        · exact False.elim ((lt_irrefl 0) ha0)
        · exact ha0
      have hcan:=received_canonical_tests_eq05 i G hm D b hb hU haraw j
      rw [hcan.1,hcan.2]
      exact ⟨rfl,rfl⟩

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
