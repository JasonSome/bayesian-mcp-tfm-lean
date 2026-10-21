import FCAppendix.Affine.Hybrid.ActivePatternGuards
import FCAppendix.Affine.Hybrid.SeedCountBounds
import FCAppendix.Affine.Hybrid.SourceTypicalGuardedData

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Classical
open scoped BigOperators
variable {N : ℕ}

def activeFocalPrefix : Fin 1 → Fin 4 := fun _ => 1

lemma classCount_patternRow (k : Fin 4) (kind : Fin N → Fin 4) :
    LowBody.classCount k (LowBody.patternRow kind)=categoryCount k kind := by
  unfold LowBody.classCount LowBody.patternRow categoryCount LowBody.hitCount
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> rfl

lemma fullCategoryCount_activeFocal (k : Fin 4) (kind : Fin N → Fin 4) :
    fullCategoryCount activeFocalPrefix kind k=(if (1 : Fin 4)=k then 1 else 0)+categoryCount k kind := by
  unfold fullCategoryCount activeFocalPrefix categoryCount LowBody.hitCount
  simp only [Fin.sum_univ_one]
  split_ifs <;> congr 1

lemma activePattern_count_active (kind : Fin N → Fin 4) :
    fullCategoryCount activeFocalPrefix kind 1=Fintype.card (ActivePatternIndex kind) := by
  rw [fullCategoryCount_activeFocal,if_pos rfl,activePatternIndex_card]

lemma activePattern_count_low (kind : Fin N → Fin 4) :
    fullCategoryCount activeFocalPrefix kind 0=LowBody.classCount 0 (LowBody.patternRow kind) := by
  rw [fullCategoryCount_activeFocal,if_neg (by decide),zero_add,classCount_patternRow]

lemma activePattern_count_upper (kind : Fin N → Fin 4) (j : Fin 2) :
    fullCategoryCount activeFocalPrefix kind ⟨2+j.val,by omega⟩=activePatternUpper kind j := by
  rw [fullCategoryCount_activeFocal,if_neg (by intro hh; have he := congrArg Fin.val hh; dsimp at he; omega),zero_add]
  exact (classCount_patternRow _ kind).symm

lemma activePatternCapacity_eq_countResidual (c : ℕ) (kind : Fin N → Fin 4) (j : Fin 2) :
    activePatternCapacity c kind j=activeResidual c
      (fullCategoryCount activeFocalPrefix kind 1)
      (fullCategoryCount activeFocalPrefix kind ⟨2+j.val,by omega⟩) := by
  rw [activePattern_count_active,activePattern_count_upper]
  rfl

lemma activePatternOwner_sum_of_ne (c : ℕ) (z : ℝ) (kind : Fin N → Fin 4)
    (hne : activePatternCapacity c kind 0 ≠ activePatternCapacity c kind 1) :
    activePatternOwner c z kind 0+activePatternOwner c z kind 1=
      2*activePatternQuota z kind+activePatternGap c kind := by
  rcases lt_or_gt_of_ne hne with hd | hd
  · simp [activePatternOwner,hd,not_lt_of_ge hd.le]
    omega
  · simp [activePatternOwner,hd,not_lt_of_ge hd.le]
    omega

theorem activePatternGuarded_of_region {xi L U : ℝ} (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4)
    (hne : activePatternCapacity c kind 0 ≠ activePatternCapacity c kind 1)
    (hregion : NormalizedGuardRegion xi L U (finiteCountPoint (N+1)
      (Fintype.card (ActivePatternIndex kind)) (activePatternSmall c kind)
      (activePatternQuota z kind) (activePatternGap c kind)))
    (hlow : 0 < LowBody.classCount 0 (LowBody.patternRow kind)) :
    activePatternGuarded xi L U c z kind := by
  obtain ⟨_,hK⟩ := count_region_integer_tests (N+1) (Fintype.card (ActivePatternIndex kind))
    (activePatternSmall c kind) (activePatternQuota z kind) (activePatternGap c kind) (by omega) hregion
  have hpos : 0 < 2*activePatternQuota z kind+activePatternGap c kind := by
    dsimp [activePatternGap,residualDifference]
    omega
  have hs := activePatternOwner_sum_of_ne c z kind hne
  exact ⟨by omega,hne,by omega,by omega,hregion,hlow⟩

end FCAppendix.Affine.Hybrid
