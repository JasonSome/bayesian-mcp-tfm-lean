import FCAppendix.Affine.Tail04.UnequalPartialCountPayoff
import FCAppendix.Affine.Tail04.OriginalOwnerCount

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialPublicWeights
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy NativeTypicalCount
open OriginalOwnerCount UnequalPartialCountPayoff

variable {N : ℕ}

theorem actual_owner_weight (H0 H1 c : ℕ) (ξ B R Rp width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (target : Fin N) (flags : Fin N → Bool)
    (AB : Finset (Fin N)×Finset (Fin N))
    (hAB : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags))).mass AB≠0) :
    publicWeight N H0 H1 c ξ B R Rp width ν0 ν1 (planParameter p target flags AB)=
      targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width
        (regime p.1.1) ν0 ν1) (publicBids p) target flags := by
  let P := countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1
  let I := targetMixedSet target flags
  obtain ⟨hsub,hA,hB,hdis,hcover⟩ := Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty target flags)
    (quota_le N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags)) AB.1 AB.2 hAB
  have hBcard : AB.2.card=P.owner1 I.card := by
    rw [hB,Finset.card_sdiff_of_subset hsub,hA,exclusive_card]
    rfl
  have hAcard : AB.1.card=P.owner0 I.card := hA
  have hI : Disjoint I (AB.1∪AB.2) := by
    rw [hcover]
    exact Finset.sdiff_disjoint.symm
  have hfull : I∪(AB.1∪AB.2)=Finset.univ := by
    rw [hcover]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ I)
  exact TypicalGuardStatistics.actual_weight_phi N H0 H1 c ξ B R Rp width
    (regime p.1.1) I AB.1 AB.2 (publicBids p) ν0 ν1 hdis hI hfull hAcard hBcard

theorem owner_weight_expect [Nonempty (Fin N)] (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) :
    (integerOwnerPlanLaw (publicBids p) (sourceFlagProb e0 F (publicBids p))
      (sourceFlagProb_nonneg _ _ _) (sourceFlagProb_le_one _ _ _)
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1)).expect
        (fun out => publicWeight N H0 H1 c ξ B R Rp width ν0 ν1
          (planParameter p out.1.1 out.1.2 out.2))=
      rawWeight N H0 H1 c ξ B R Rp width e0 F (regime p.1.1) true ν0 ν1 (publicBids p) := by
  have hN : N≠0 := by
    have hh : 0< N := by simpa using (Fintype.card_pos : 0< Fintype.card (Fin N))
    omega
  rw [integerOwnerPlanLaw_expect]
  simp only [rawWeight,dif_neg hN,ite_true]
  apply FiniteLaw.expect_congr
  intro target
  apply FiniteLaw.expect_congr
  intro flags
  rw [←FiniteLaw.expect_const
    (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags)))
    (targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width
      (regime p.1.1) ν0 ν1) (publicBids p) target flags)]
  apply Hybrid.expect_congr_on_support
  intro AB hAB
  exact actual_owner_weight H0 H1 c ξ B R Rp width ν0 ν1 p target flags AB hAB

theorem rawWeight_relabel (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (b∘e.symm)=
      rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b := by
  by_cases hN : N=0
  · simp only [rawWeight,dif_pos hN]
  · letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hN)
    cases lowPresent
    · simp only [rawWeight,dif_neg hN,Bool.false_eq_true,ite_false]
    · simp only [rawWeight,dif_neg hN,ite_true]
      rw [Hybrid.rankLaw_relabel,FiniteLaw.expect_map]
      apply FiniteLaw.expect_congr
      intro target
      change (independentFlagLaw ((sourceFlagProb e0 F b)∘e.symm) _ _).expect _=_
      let f : (Fin N → Bool) → ℝ := fun z =>
        targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
          (b∘e.symm) (e target) z
      have hf := independentFlagLaw_expect_relabel (sourceFlagProb e0 F b)
        (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b) e f
      have hg : (independentFlagLaw (sourceFlagProb e0 F b)
          (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)).expect
          (fun flags=>f (relabelFlags e flags))=
        (independentFlagLaw (sourceFlagProb e0 F b)
          (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)).expect
          (fun flags=>targetTypicalWeight
            (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1) b target flags) := by
        apply FiniteLaw.expect_congr
        intro flags
        exact targetTypicalWeight_relabel _ b e target flags
      convert! hf.trans hg using 1

theorem rawWeight_sorted (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) :
    rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 (SortedAllNoise.sorted b)=
      rawWeight N H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b := by
  simpa only [SortedAllNoise.sorted,Equiv.symm_symm] using
    rawWeight_relabel H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b
      (PrivateRowSorting.permutation b).symm

end FCAppendix.Affine.Tail04.PartialPublicWeights
