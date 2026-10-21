import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Guard
import FCAppendix.Affine.Uniform07Finishing.Native.SourceBalancedExperiment

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

theorem received_kappa_eq (row : Uniform07.Row) :
    Uniform05.kappa row=1-Uniform07.xi row := by
  rw [Uniform05.kappa_eq_canonical]
  cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ]

omit [Nonempty (Fin m)] in
theorem pairCount_eq_focalCopy (i : Fin m) (P : UniformFinite.Allocation m) :
    UniformFinite.pairCount i P=focalCopy P i := by
  apply Fin.ext
  by_cases h0 : i∈P.1 <;> by_cases h1 : i∈P.2 <;>
    simp [UniformFinite.pairCount,focalCopy,h0,h1]

omit [Nonempty (Fin m)] in
theorem pairCount_orient (row : UniformFinite.Source.CountRow m)
    (i : Fin m) (P : UniformFinite.Allocation m) :
    UniformFinite.pairCount i (UniformFinite.orient row P)=UniformFinite.pairCount i P := by
  unfold UniformFinite.orient
  split_ifs
  · simp only [UniformFinite.pairCount,Finset.inter_comm P.2 P.1,Finset.union_comm P.2 P.1]
  · rfl

omit [Nonempty (Fin m)] in
theorem decoded_feasible (X : ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (P : UniformFinite.Allocation m) :
    (UniformFinite.Source.lowerTemplate (UniformFinite.NativeContext.decode X)).Feasible P ↔
      ResidualPotential.Feasible X.1 (Weighted.budget (Uniform07.capacity m) 0 X)
        (Weighted.budget (Uniform07.capacity m) 1 X) P := by
  simp only [PureTemplate.Feasible,UniformFinite.Source.lowerTemplate,
    decoded_residual X hX,decoded_lower,ResidualPotential.Feasible,LocallyFeasible,
    Finset.subset_iff,Weighted.presentSet,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

omit [Nonempty (Fin m)] in
theorem decoded_potential_bids (X : ClassifiedContext m) (h0 : NonnegativeList X.1) :
    UniformFinite.Source.lowerBids (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))=ResidualPotential.bid X.1 := by
  rw [decoded_lowerBids]
  funext k
  exact (max_eq_left (h0 k)).symm

omit [Nonempty (Fin m)] in
theorem listBids_eq_entries (X : ClassifiedContext m) :
    Existence.PayOnceBounded.listBids X.1=(fun k=>entryBid (X.1 k)) := by
  funext k
  exact Weighted.listBids_eq_entry X.1 k

theorem decoded_pure_focalCopy (row : Uniform07.Row) (X : ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (h0 : NonnegativeList X.1)
    (i : Fin m) (hg : contextCopyGeneric (1-Uniform07.xi row) i X) :
    UniformFinite.pairCount i
      ((UniformFinite.Source.lowerTemplate (UniformFinite.NativeContext.decode X)).selection
        (Uniform05.kappa row)
        (UniformFinite.Source.lowerBids (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k))))=
      focalCopy (Weighted.purePair (Uniform07.xi row) (Uniform07.capacity m) X) i := by
  let κ := 1-Uniform07.xi row
  let T := UniformFinite.Source.lowerTemplate (UniformFinite.NativeContext.decode X)
  let P := T.selection κ (ResidualPotential.bid X.1)
  let Q := ResidualPotential.selection κ X.1
    (Weighted.budget (Uniform07.capacity m) 0 X) (Weighted.budget (Uniform07.capacity m) 1 X)
  have hκ : 0≤κ := (sub_pos.mpr (source_xi_lt_one row)).le
  have hP : ResidualPotential.Feasible X.1 (Weighted.budget (Uniform07.capacity m) 0 X)
      (Weighted.budget (Uniform07.capacity m) 1 X) P :=
    (decoded_feasible X hX P).mp (T.selection_feasible κ (ResidualPotential.bid X.1))
  have hQ : ResidualPotential.Feasible X.1 (Weighted.budget (Uniform07.capacity m) 0 X)
      (Weighted.budget (Uniform07.capacity m) 1 X) Q :=
    ResidualPotential.selection_feasible κ hκ X.1 _ _
  have hQP : CompleteInformation.potential κ (ResidualPotential.bid X.1) Q.1 Q.2≤
      CompleteInformation.potential κ (ResidualPotential.bid X.1) P.1 P.2 :=
    T.selection_max κ (ResidualPotential.bid X.1) Q ((decoded_feasible X hX Q).mpr hQ)
  have hPQ : CompleteInformation.potential κ (ResidualPotential.bid X.1) P.1 P.2≤
      CompleteInformation.potential κ (ResidualPotential.bid X.1) Q.1 Q.2 := by
    have h := FiniteSelector.select_max
      (ResidualPotential.objective κ X.1 (Weighted.budget (Uniform07.capacity m) 0 X)
        (Weighted.budget (Uniform07.capacity m) 1 X)) P
    change ResidualPotential.objective κ X.1 _ _ P≤
      ResidualPotential.objective κ X.1 _ _ Q at h
    simpa only [ResidualPotential.objective,if_pos hP,if_pos hQ] using h
  have hc := hg P Q (le_antisymm hPQ hQP)
  simpa only [pairCount_eq_focalCopy,received_kappa_eq,decoded_potential_bids X h0,
    Weighted.purePair,κ,T,P,Q] using hc

theorem decoded_equal_count_moment (row : Uniform07.Row) (X : ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X)
    (he : Weighted.budget (Uniform07.capacity m) 0 X=
      Weighted.budget (Uniform07.capacity m) 1 X) (i : Fin m) (q : Fin 3→ℝ) :
    (UniformFinite.equalLaw row (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P))=
      Weighted.privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) (Uniform07.capacity m) X none i q := by
  rw [UniformFinite.equalLaw]
  simp only [pairCount_eq_focalCopy]
  rw [Weighted.finite_pair_count_moment,Weighted.privateCountMoment_equal _ _ _ _ _ _ he]
  have hs : UniformFinite.equalLottery row (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))=
      EqualCapacity.canonicalLottery (Uniform07.xi row)
        (Weighted.budget (Uniform07.capacity m) 0 X)
        (Existence.PayOnceBounded.listBids X.1) := by
    simp only [UniformFinite.equalLottery,EqualCapacity.canonicalLottery,
      Uniform05.xi_eq_canonical,decoded_small X hX,Weighted.commonBudget,
      he,min_self,decoded_lowerBids,listBids_eq_entries]
  have hp := (EqualCapacity.canonicalLottery_implements (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Weighted.budget (Uniform07.capacity m) 0 X)
      (Existence.PayOnceBounded.listBids X.1)).2 i
  simpa only [hs,FiniteLaw.prob_eq_expect] using congrArg (fun p=>twoCountPolynomial q p p) hp

theorem decoded_pure_count_moment (row : Uniform07.Row) (X : ClassifiedContext m)
    (hX : UniformFinite.NativeContext.Valid X) (h0 : NonnegativeList X.1)
    (he : Weighted.budget (Uniform07.capacity m) 0 X≠
      Weighted.budget (Uniform07.capacity m) 1 X)
    (i : Fin m) (hg : contextCopyGeneric (1-Uniform07.xi row) i X) (q : Fin 3→ℝ) :
    (UniformFinite.pureLaw row (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P))=
      Weighted.privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) (Uniform07.capacity m) X none i q := by
  rw [UniformFinite.pureLaw,FiniteLaw.expect_dirac,
    decoded_pure_focalCopy row X hX h0 i hg,
    Weighted.privateCountMoment_none _ _ _ _ _ he]

theorem twoCountPolynomial_comm (q : Fin 3→ℝ) (p r : ℝ) :
    twoCountPolynomial q p r=twoCountPolynomial q r p := by
  unfold twoCountPolynomial
  ring

omit [Nonempty (Fin m)] in

theorem literal_conditional_count_moment {ξ z : ℝ} (hξ : 0<ξ) (hz : 0< z)
    (b : Fin m→ℝ) (E : Finset (Fin m)) (d : ℕ)
    (hr : ClippedResidual.remainingDemand ξ b E z=(d:ℝ))
    (i : Fin m) (q : Fin 3→ℝ) :
    (UniformFinite.Literal.conditionalCompletion ξ z b E).expect
      (fun P=>q (UniformFinite.pairCount i P))=
      twoCountPolynomial q (ClippedResidual.largeMarginal ξ z b E i)
        (ClippedResidual.smallMarginal ξ z b E i) := by
  rw [UniformFinite.Literal.conditionalCompletion]
  simp only [pairCount_eq_focalCopy]
  rw [Weighted.finite_pair_count_moment]
  have hS := (UniformFinite.Literal.completion_implements hξ hz b E d hr).2 i
  have hL := (UniformFinite.Literal.largeCompletion_implements hξ hz b E d hr).2 i
  simp only [FiniteLaw.prob_eq_expect] at hS hL
  rw [hS,hL]

omit [Nonempty (Fin m)] in
theorem canonical_remainder_eq_smallMarginal (row : Uniform07.Row)
    (X : ClassifiedContext m) (E : Finset (Fin m)) (d : ℕ) {z : ℝ}
    (hz : 0< z) (hguard : (1-Uniform07.xi row)*Early.bidCap row≤ z)
    (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row)
    (hr : ClippedResidual.remainingDemand (Uniform07.xi row)
      (fun k=>entryBid (X.1 k)) E z=(d:ℝ)) :
    EqualCapacity.positiveMarginal (Uniform07.xi row) d
      (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E))=
      ClippedResidual.smallMarginal (Uniform07.xi row) z (fun k=>entryBid (X.1 k)) E := by
  have hrem : ∀k,Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E) k≤
      Early.bidCap row := by
    intro k
    rw [Weighted.listBids_eq_entry,Weighted.remainder_entry]
    split_ifs
    · simpa only [cap_eq] using (Uniform05.cap_pos row).le
    · exact hU k
  have hroot : (∑k,ClippedResidual.exposure (Uniform07.xi row) z
      (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E) k))=(d:ℝ) := by
    calc
      _=ClippedResidual.remainingDemand (Uniform07.xi row)
          (fun k=>entryBid (X.1 k)) E z := by
        unfold ClippedResidual.remainingDemand
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k∈E <;>
          simp [Weighted.remainder_entry,Weighted.listBids_eq_entry,hk,
            ClippedResidual.exposure_zero hz.le]
      _=_ := hr
  rw [Weighted.canonical_eq_clipped_at_root _ d (Uniform07.xi_pos row)
    (source_xi_lt_one row) hz hguard hrem hroot]
  funext k
  by_cases hk : k∈E <;>
    simp [ClippedResidual.smallMarginal,Weighted.remainder_entry,
      Weighted.listBids_eq_entry,hk,ClippedResidual.exposure_zero hz.le]

omit [Nonempty (Fin m)] in
theorem sourceBalancedPolynomial_eq_unoriented (ξ : ℝ) (c : ℕ)
    (X : ClassifiedContext m) (E : Finset (Fin m)) (i : Fin m) (q : Fin 3→ℝ) :
    Weighted.sourceBalancedPolynomial ξ c X E i q=
      twoCountPolynomial q
        (if i∈E then 1 else EqualCapacity.positiveMarginal ξ (Weighted.commonBudget c X)
          (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E)) i)
        (EqualCapacity.positiveMarginal ξ (Weighted.commonBudget c X)
          (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E)) i) := by
  by_cases hi : i∈E
  · have hl : Weighted.larger c X=0 ∨ Weighted.larger c X=1 := by
      have hh := (Weighted.larger c X).isLt
      omega
    rcases hl with hl|hl
    · simp [Weighted.sourceBalancedPolynomial,hi,hl]
    · simpa [Weighted.sourceBalancedPolynomial,hi,hl] using
        twoCountPolynomial_comm q
          (EqualCapacity.positiveMarginal ξ (Weighted.commonBudget c X)
            (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E)) i) 1
  · simp [Weighted.sourceBalancedPolynomial,hi]

theorem decoded_canonical_count_moment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m] (hm : 0< m)
    (X : ClassifiedContext m) (hX : UniformFinite.NativeContext.Valid X)
    (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row)
    (ha : 0< UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))) (i : Fin m) (q : Fin 3→ℝ) :
    (UniformFinite.canonicalLaw row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P))=
      (Weighted.sourceBalancedAllocationLaw (Uniform07.xi row) G.multiplier
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m) X).expect
          (fun P=>q (focalCopy P i)) := by
  letI : NeZero m := ⟨hm.ne'⟩
  let D := UniformFinite.NativeContext.decode X
  let b := fun k=>entryBid (X.1 k)
  have hb : ∀k∈D.lower,b k≤ Uniform05.cap row := by
    intro k _
    simpa only [b,cap_eq] using hU k
  have hg := UniformFinite.Source.rawAlpha_pos row G D b hm hb ha
  have hbr := UniformFinite.Source.rootBounds row G
  rw [UniformFinite.canonicalLaw,FiniteLaw.expect_map,
    UniformFinite.Literal.weightedExperiment,WeightedSampling.expect_pairLaw,
    Weighted.sourceBalancedAllocationLaw_expect (Uniform07.xi_pos row) (source_xi_lt_one row)]
  simp only [pairCount_orient]
  rw [←decoded_sourceWeights row G X hU,←decoded_imbalance X hX]
  apply UniformFinite.Literal.expect_congr_support
  intro p hp
  let E := WeightedSampling.finalSet (UniformFinite.Source.imbalance D) ∅ p
  let z := UniformFinite.Literal.root (Uniform05.xi row)
    (UniformFinite.Source.rootLo row G) (UniformFinite.Source.rootHi row G)
    (UniformFinite.Source.lowerBids D b) E (UniformFinite.Source.small D)
  have hs := UniformFinite.Literal.weighted_path_root
    (UniformFinite.Source.lowerBids D b) (UniformFinite.Source.sourceWeights row G D b)
    (UniformFinite.Source.small D) (UniformFinite.Source.imbalance D)
    (Uniform05.xi_range row).1 (Uniform05.xi_range row).2 (Uniform05.cap_pos row)
    hbr.1 hbr.2.1 hbr.2.2 hg.2.1 hg.2.2 hg.1 p hp
  have hz : 0< z := hbr.1.trans_le hs.2.1.1
  have hclear : ClippedResidual.remainingDemand (Uniform07.xi row) b E z=
      (Weighted.commonBudget (Uniform07.capacity m) X:ℝ) := by
    simpa only [Uniform05.xi_eq_canonical,decoded_lowerBids,
      decoded_small X hX,D,b,E,z] using hs.2.2.1
  have hguard : (1-Uniform07.xi row)*Early.bidCap row≤ z := by
    convert! hbr.2.2.trans hs.2.1.1 using 1
    simp only [Uniform05.xi_eq_canonical,cap_eq]
  have hcan := canonical_remainder_eq_smallMarginal row X E
    (Weighted.commonBudget (Uniform07.capacity m) X) hz hguard hU hclear
  rw [literal_conditional_count_moment (Uniform05.xi_range row).1 hz
    (UniformFinite.Source.lowerBids D b) E (UniformFinite.Source.small D) hs.2.2.1,
    sourceBalancedPolynomial_eq_unoriented (Uniform07.xi row) (Uniform07.capacity m) X E i q]
  simp only [Uniform05.xi_eq_canonical,decoded_lowerBids,hcan,
    ClippedResidual.largeMarginal,ClippedResidual.smallMarginal,D,b]
  split_ifs <;> rfl

omit [Nonempty (Fin m)] in

theorem decoded_exceptional_conditional_count_moment {ξ : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (i : Fin m) (q : Fin 3→ℝ) :
    (UniformFinite.Late.Exceptional.conditionalCompletion ξ (Weighted.commonBudget c X)
      (fun k=>entryBid (X.1 k)) E).expect (fun P=>q (UniformFinite.pairCount i P))=
      Weighted.sourceBalancedPolynomial ξ c X E i q := by
  have hlot : UniformFinite.Late.Exceptional.completion ξ (Weighted.commonBudget c X)
      (fun k=>entryBid (X.1 k)) E=Weighted.sourceResidualLottery ξ c X E := by
    unfold UniformFinite.Late.Exceptional.completion Weighted.sourceResidualLottery
      EqualCapacity.canonicalLottery
    congr 2
    funext k
    simp only [UniformFinite.Late.Exceptional.masked,Weighted.remainder_entry,
      Weighted.listBids_eq_entry]
  let p := EqualCapacity.positiveMarginal ξ (Weighted.commonBudget c X)
    (Existence.PayOnceBounded.listBids (Weighted.remainder X.1 E)) i
  have hS : (UniformFinite.Late.Exceptional.completion ξ (Weighted.commonBudget c X)
      (fun k=>entryBid (X.1 k)) E).expect (fun S=>if i∈S then (1:ℝ) else 0)=p := by
    rw [hlot]
    exact Weighted.sourceResidualLottery_marginal hξ hξ1 c X E i
  have hL : (UniformFinite.Late.Exceptional.largeCompletion ξ (Weighted.commonBudget c X)
      (fun k=>entryBid (X.1 k)) E).expect (fun S=>if i∈S then (1:ℝ) else 0)=
        if i∈E then 1 else p := by
    rw [UniformFinite.Late.Exceptional.largeCompletion,FiniteLaw.expect_map]
    by_cases hi : i∈E
    · simp only [Finset.mem_union,hi,true_or,if_true,FiniteLaw.expect_const]
    · simpa only [Finset.mem_union,hi,false_or,if_false] using hS
  rw [UniformFinite.Late.Exceptional.conditionalCompletion]
  simp only [pairCount_eq_focalCopy]
  rw [Weighted.finite_pair_count_moment,hS,hL,
    sourceBalancedPolynomial_eq_unoriented]

theorem decoded_exceptional_canonical_count_moment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m]
    (X : ClassifiedContext m) (hX : UniformFinite.NativeContext.Valid X) (a : Fin m)
    (hw : UniformFinite.Late.Exceptional.weight row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k)) a=
      Weighted.sourceWeights (Uniform07.xi row) G.multiplier (Early.demandRatio row)
        (Early.bidCap row) X.1) (i : Fin m) (q : Fin 3→ℝ) :
    (UniformFinite.Late.Exceptional.canonicalLaw row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k)) a).expect (fun P=>q (UniformFinite.pairCount i P))=
      (Weighted.sourceBalancedAllocationLaw (Uniform07.xi row) G.multiplier
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.capacity m) X).expect
          (fun P=>q (focalCopy P i)) := by
  rw [UniformFinite.Late.Exceptional.canonicalLaw,FiniteLaw.expect_map,
    WeightedSampling.expect_pairLaw,
    Weighted.sourceBalancedAllocationLaw_expect (Uniform07.xi_pos row) (source_xi_lt_one row)]
  simp only [pairCount_orient,hw,decoded_small X hX,decoded_lowerBids,Uniform05.xi_eq_canonical]
  let K := fun n : ℕ =>
    (WeightedSampling.pathLaw
      (Weighted.sourceWeights (Uniform07.xi row) G.multiplier (Early.demandRatio row)
        (Early.bidCap row) X.1) n ∅).expect (fun p =>
      (UniformFinite.Late.Exceptional.conditionalCompletion (Uniform07.xi row)
        (Weighted.commonBudget (Uniform07.capacity m) X) (fun k=>entryBid (X.1 k))
        (WeightedSampling.finalSet n ∅ p)).expect (fun P=>q (UniformFinite.pairCount i P)))
  change K (UniformFinite.Source.imbalance (UniformFinite.NativeContext.decode X)) = _
  rw [congrArg K (decoded_imbalance X hX)]
  apply FiniteLaw.expect_congr
  intro p
  exact decoded_exceptional_conditional_count_moment
    (Uniform07.xi_pos row) (source_xi_lt_one row) (Uniform07.capacity m) X _ i q

def nativeContextCountMoment (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row)
    (X : ClassifiedContext m) (rivalSeed : Prop) [Decidable rivalSeed]
    (i : Fin m) (q : Fin 3→ℝ) : ℝ :=
  Weighted.privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) (Uniform07.capacity m) X none i q +
  if rivalSeed then
    Weighted.finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.capacity m)
      (Weighted.sourceGuardAlpha (Uniform07.xi row) G.multiplier (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        G.rejectionRoot (Uniform07.cutoff row) (10*UniformFinite.Source.commonGuardMargin row)
        (UniformFinite.Source.commonGuardMargin row) (Uniform07.capacity m)) X i q
  else 0

omit [Nonempty (Fin m)] in
theorem capped_exceptionalSet_empty (row : Uniform07.Row) (X : ClassifiedContext m)
    (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row) :
    Weighted.exceptionalSet (Early.bidCap row) X.1=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro k hk
  exact not_lt.mpr (hU k) (Finset.mem_filter.mp hk).2.2

theorem decoded_raw_count_correction (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m] (hm : 0< m)
    (X : ClassifiedContext m) (hX : UniformFinite.NativeContext.Valid X)
    (h0 : NonnegativeList X.1) (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row)
    (i : Fin m) (q : Fin 3→ℝ) :
    let α := Weighted.sourceGuardAlpha (m:=m) (Uniform07.xi row) G.multiplier
      (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.cutoff row/1000) G.rejectionRoot (Uniform07.cutoff row)
      (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
      (Uniform07.capacity m)
    Weighted.finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row)
      (source_xi_lt_one row) G.multiplier (Early.demandRatio row) (Early.bidCap row)
      (Uniform07.capacity m) α X i q=
      UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
        (fun k=>entryBid (X.1 k))*
        ((UniformFinite.canonicalLaw row G (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P))-
          Weighted.privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
            (source_xi_lt_one row) (Uniform07.capacity m) X none i q) := by
  dsimp only
  let α := Weighted.sourceGuardAlpha (m:=m) (Uniform07.xi row) G.multiplier
    (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.cutoff row/1000) G.rejectionRoot (Uniform07.cutoff row)
    (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
    (Uniform07.capacity m)
  have hαeq := rawAlpha_eq_sourceGuardAlpha row G hm X hX hU
  change UniformFinite.Source.rawAlpha row G (UniformFinite.NativeContext.decode X)
    (fun k=>entryBid (X.1 k))=(α X:ℝ) at hαeq
  by_cases ha : 0<(α X:ℝ)
  · have hΛ : (54/100:ℝ)*Uniform07.cutoff row< G.multiplier := by
      simpa only [Uniform05.t_eq_canonical] using G.multiplier_guards.1
    have hcap : 0< Early.bidCap row := by simpa only [cap_eq] using Uniform05.cap_pos row
    have hguard : Uniform07.kappa row*Early.bidCap row<
        G.multiplier-Early.nativeRadius row :=
      (le_max_left _ _).trans_lt ((Early.native_sampling_margin_guards row).2 G.multiplier hΛ).1
    have hW := Weighted.sourceGuardAlpha_outer (Uniform07.capacity m) hm
      (UniformFinite.Source.common_guard_margin row) X ha 2
    change UniformFinite.Source.commonGuardMargin row*m<
      WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi row) G.multiplier
        (Early.demandRatio row) (Early.bidCap row) X.1)-
        ((max (Weighted.budget (Uniform07.capacity m) 0 X)
          (Weighted.budget (Uniform07.capacity m) 1 X)-
            Weighted.commonBudget (Uniform07.capacity m) X:ℕ):ℝ) at hW
    have hW' : ((max (Weighted.budget (Uniform07.capacity m) 0 X)
        (Weighted.budget (Uniform07.capacity m) 1 X)-
          Weighted.commonBudget (Uniform07.capacity m) X:ℕ):ℝ)<
        WeightedSampling.totalWeight (Weighted.sourceWeights (Uniform07.xi row) G.multiplier
          (Early.demandRatio row) (Early.bidCap row) X.1) := by
      have hεm : 0< UniformFinite.Source.commonGuardMargin row*(m:ℝ) :=
        mul_pos (UniformFinite.Source.common_guard_margin row) (by exact_mod_cast hm)
      linarith
    rw [Weighted.literal_finitePathCountCorrection_eq_balanced row hΛ hcap hguard hm
      (UniformFinite.Source.common_guard_margin row) (Uniform07.capacity m) X h0 hU i q]
    simp only [capped_exceptionalSet_empty row X hU,Finset.card_empty,
      show (0:ℕ)≤ 1 by omega,hW',and_self,if_true]
    rw [hαeq,decoded_canonical_count_moment row G hm X hX hU
      (by rwa [hαeq]) i q]
  · have hz : (α X:ℝ)=0 := le_antisymm (le_of_not_gt ha) (α X).property.1
    rw [Weighted.finitePathCountCorrection_zero_alpha _ _ _ _ _ _ _ α X hz i q,
      hαeq,hz,zero_mul]

theorem decoded_continuation_count_moment (row : Uniform07.Row)
    (G : Uniform05.RestrictedLaw row) [NeZero m] (hm : 0< m)
    (X : ClassifiedContext m) (hX : UniformFinite.NativeContext.Valid X)
    (h0 : NonnegativeList X.1) (hU : ∀k,entryBid (X.1 k)≤ Early.bidCap row)
    (i : Fin m) (hg : contextCopyGeneric (1-Uniform07.xi row) i X) (q : Fin 3→ℝ) :
    (UniformFinite.continuationLaw row G (UniformFinite.NativeContext.decode X)
      (fun k=>entryBid (X.1 k))).expect (fun P=>q (UniformFinite.pairCount i P))=
      nativeContextCountMoment row G X
        (0< UniformFinite.Source.seedCount row (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k))) i q := by
  let α := Weighted.sourceGuardAlpha (m:=m) (Uniform07.xi row) G.multiplier
    (Early.nativeRadius row) (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.cutoff row/1000) G.rejectionRoot (Uniform07.cutoff row)
    (10*UniformFinite.Source.commonGuardMargin row) (UniformFinite.Source.commonGuardMargin row)
    (Uniform07.capacity m)
  by_cases he : Weighted.budget (Uniform07.capacity m) 0 X=
      Weighted.budget (Uniform07.capacity m) 1 X
  · have he' : UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 0=
        UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 1 := by
      simpa only [decoded_residual X hX] using he
    rw [UniformFinite.continuationLaw,if_pos he',decoded_equal_count_moment row X hX he]
    unfold nativeContextCountMoment
    rw [Weighted.finitePathCountCorrection_equal_budget _ _ _ _ _ _ _ α X he i q]
    simp only [ite_self,add_zero]
  · have he' : UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 0≠
        UniformFinite.Source.residual (UniformFinite.NativeContext.decode X) 1 := by
      simpa only [decoded_residual X hX] using he
    rw [UniformFinite.continuationLaw,if_neg he',FiniteLaw.expect_mixture,
      decoded_pure_count_moment row X hX h0 he i hg q]
    unfold nativeContextCountMoment
    rw [decoded_raw_count_correction row G hm X hX h0 hU i q]
    by_cases hs : UniformFinite.Source.seedCount row (UniformFinite.NativeContext.decode X)
        (fun k=>entryBid (X.1 k))=0
    · simp only [UniformFinite.Source.guardAlpha,hs,if_true,lt_self_iff_false,
        if_false,zero_mul,sub_zero,one_mul,add_zero,zero_add]
    · have hs' : 0< UniformFinite.Source.seedCount row (UniformFinite.NativeContext.decode X)
          (fun k=>entryBid (X.1 k)) := Nat.pos_of_ne_zero hs
      simp only [UniformFinite.Source.guardAlpha,if_neg hs,if_pos hs']
      ring

end FCAppendix.Affine.Uniform07Finishing.Concrete05
