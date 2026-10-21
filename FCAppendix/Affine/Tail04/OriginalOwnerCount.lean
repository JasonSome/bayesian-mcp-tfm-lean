import FCAppendix.Affine.Tail04.TypicalGuardStatistics
import FCAppendix.Affine.Hybrid.GuardedPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalOwnerCount
open MeasureTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy NativeTypicalCount
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

def planParameter {N H : ℕ} {R Rp B : ℝ} (p : Parameters N H R Rp B)
    (target : Fin N) (flags : Fin N → Bool) (AB : Finset (Fin N) × Finset (Fin N)) :
    Parameters N H R Rp B :=
  (((regime p.1.1,(targetMixedSet target flags,(AB.1,AB.2))),p.1.2),p.2)

theorem fallbackCount_congr_bids (N H0 H1 c : ℕ) (ξ B R Rp Rm : ℝ)
    (p q : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hb : publicBids p=publicBids q) (i : Fin N) :
    fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i =
      fallbackCount N H0 H1 c ξ B R Rp Rm q θ0 θ1 i := by
  unfold fallbackCount originalIndependentCountLaw
  apply FiniteLaw.ofMeasure_congr_ae
  exact ae_of_all _ fun z => by
    simp only [originalPairCount,localAccept,fallback0,fallback1,hb]
    rfl

theorem exclusive_card {N : ℕ} (target : Fin N) (flags : Fin N → Bool) :
    (forcedExclusiveSet target flags).card=N-(targetMixedSet target flags).card := by
  unfold forcedExclusiveSet targetMixedSet
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin]

def quota (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (z : Fin N × (Fin N → Bool)) : ℕ :=
  (countParameters N H0 H1 c ξ reg ν0 ν1).owner0 (targetMixedSet z.1 z.2).card

theorem quota_le (N H0 H1 c : ℕ) (ξ : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (z : Fin N × (Fin N → Bool)) :
    quota N H0 H1 c ξ reg ν0 ν1 z ≤ (forcedExclusiveSet z.1 z.2).card := by
  rw [exclusive_card]
  exact (countParameters N H0 H1 c ξ reg ν0 ν1).owner0_le _

theorem plan_count_law (N H0 H1 c : ℕ) {ξ B : ℝ} (R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (θ0 : Measure (Row H0 R Rp Rm))
    (θ1 : Measure (Row H1 R Rp Rm)) [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (target : Fin N) (flags : Fin N → Bool) (AB : Finset (Fin N) × Finset (Fin N))
    (hAB : (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags))).mass AB ≠ 0)
    (i : Fin N) :
    originalJoinedCountLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1
      (planParameter p target flags AB) θ0 θ1 i =
      FiniteLaw.mixture
        (targetStateCount (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
          (publicBids p) target flags i)
        (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i)
        (targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width
          (regime p.1.1) ν0 ν1) (publicBids p) target flags)
        (targetTypicalWeight_bounds _ _ target flags).1
        (targetTypicalWeight_bounds _ _ target flags).2 := by
  let P := countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1
  let I := targetMixedSet target flags
  obtain ⟨hsub,hA,hB,hdis,hcover⟩ := Hybrid.ownerDivision_support
    (forcedExclusiveSet_nonempty target flags)
    (quota_le N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags)) AB.1 AB.2 hAB
  have hBcard : AB.2.card=P.owner1 I.card := by
    rw [hB,Finset.card_sdiff_of_subset hsub,hA,exclusive_card]
    rfl
  have hAcard : AB.1.card=P.owner0 I.card := hA
  have hI : Disjoint I (AB.1 ∪ AB.2) := by
    rw [hcover]
    exact Finset.sdiff_disjoint.symm
  have hfull : I ∪ (AB.1 ∪ AB.2)=Finset.univ := by
    rw [hcover]
    exact Finset.union_sdiff_of_subset (Finset.subset_univ I)
  have hweight :
      (weightParameter N H0 H1 c ξ B R Rp width ν0 ν1 (planParameter p target flags AB):ℝ) =
      targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width
        (regime p.1.1) ν0 ν1) (publicBids p) target flags := by
    exact TypicalGuardStatistics.actual_weight_phi N H0 H1 c ξ B R Rp width
      (regime p.1.1) I AB.1 AB.2 (publicBids p) ν0 ν1 hdis hI hfull hAcard hBcard
  have he := originalJoinedCountLaw_balanced N H0 H1 c R Rp Rm width ν0 ν1
    hξ hξ1 hw (planParameter p target flags AB) θ0 θ1 hν0 hν1 hAcard hBcard i
  rw [he]
  apply FiniteLaw.ext_expect
  intro f
  simp only [FiniteLaw.expect_mixture]
  rw [hweight,fallbackCount_congr_bids N H0 H1 c ξ B R Rp Rm
    (planParameter p target flags AB) p θ0 θ1 rfl i]
  rfl

def countLaw (N H0 H1 c : ℕ) [Nonempty (Fin N)] (ξ B R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (p : Parameters N H0 R Rp B) (prob : Fin N → ℝ)
    (hp0 : ∀ j, 0 ≤ prob j) (hp1 : ∀ j, prob j ≤ 1)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1] (i : Fin N) : CountLaw 2 :=
  FiniteLaw.finiteMix
    (integerOwnerPlanLaw (publicBids p) prob hp0 hp1
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1))
    (fun out => originalJoinedCountLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1
      (planParameter p out.1.1 out.1.2 out.2) θ0 θ1 i)

theorem countLaw_eq (N H0 H1 c : ℕ) [Nonempty (Fin N)] {ξ B : ℝ} (R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (p : Parameters N H0 R Rp B) (prob : Fin N → ℝ)
    (hp0 : ∀ j, 0 ≤ prob j) (hp1 : ∀ j, prob j ≤ 1)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (i : Fin N) :
    countLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p prob hp0 hp1 θ0 θ1 i =
      typicalRankCount (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
        (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width (regime p.1.1) ν0 ν1)
        (publicBids p) prob hp0 hp1 i (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [countLaw,FiniteLaw.expect_finiteMix,integerOwnerPlanLaw_expect]
  simp only [typicalRankCount,conditionalTargetCount,FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro target
  apply FiniteLaw.expect_congr
  intro flags
  rw [← FiniteLaw.expect_const
    (Hybrid.ownerDivision (forcedExclusiveSet target flags)
      (quota N H0 H1 c ξ (regime p.1.1) ν0 ν1 (target,flags)))
    ((FiniteLaw.mixture
      (targetStateCount (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
        (publicBids p) target flags i)
      (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i)
      (targetTypicalWeight (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width
        (regime p.1.1) ν0 ν1) (publicBids p) target flags)
      (targetTypicalWeight_bounds _ _ target flags).1
      (targetTypicalWeight_bounds _ _ target flags).2).expect f)]
  apply Hybrid.expect_congr_on_support
  intro AB hAB
  rw [plan_count_law N H0 H1 c R Rp Rm width ν0 ν1 hξ hξ1 hw p θ0 θ1
    hν0 hν1 target flags AB hAB i]

theorem countLaw_source_flags (N H0 H1 c : ℕ) [Nonempty (Fin N)]
    {ξ B e0 : ℝ} (R Rp Rm width : ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hw : 0 < width)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hB : 1 < B)
    (p : Parameters N H0 R Rp B)
    (θ0 : Measure (Row H0 R Rp Rm)) (θ1 : Measure (Row H1 R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hν0 : θ0.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν0)
    (hν1 : θ1.map (fun row => marks (signal row))=FiniteLaw.probabilityMeasure ν1)
    (i : Fin N) :
    countLaw N H0 H1 c ξ B R Rp Rm width ν0 ν1 p
      (fun j => mixedFlagProbability e0 B (publicBids p j))
      (fun _ => mixedFlagProbability_nonneg he0)
      (fun j => mixedFlagProbability_le_one he0 he1 hB (p.1.2 j).2) θ0 θ1 i =
      typicalRankCount (countParameters N H0 H1 c ξ (regime p.1.1) ν0 ν1).mixedCount
        (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width (regime p.1.1) ν0 ν1)
        (publicBids p) (sourceFlagProb e0 B (publicBids p))
        (sourceFlagProb_nonneg e0 B (publicBids p)) (sourceFlagProb_le_one e0 B (publicBids p))
        i (fallbackCount N H0 H1 c ξ B R Rp Rm p θ0 θ1 i) := by
  have hp : sourceFlagProb e0 B (publicBids p) =
      (fun j => mixedFlagProbability e0 B (publicBids p j)) := by
    funext j
    exact sourceFlagProb_eq he0 he1 hB (publicBids p) j (p.1.2 j).2
  simpa only [hp] using countLaw_eq N H0 H1 c R Rp Rm width ν0 ν1 hξ hξ1 hw p
    (fun j => mixedFlagProbability e0 B (publicBids p j))
    (fun _ => mixedFlagProbability_nonneg he0)
    (fun j => mixedFlagProbability_le_one he0 he1 hB (p.1.2 j).2) θ0 θ1 hν0 hν1 i

end FCAppendix.Affine.Tail04.OriginalOwnerCount
