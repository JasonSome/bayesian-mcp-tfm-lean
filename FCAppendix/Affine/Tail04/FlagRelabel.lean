import FCAppendix.Affine.Tail04.RankForcedFlags
import FCAppendix.Affine.Tail04.BidDependentFlags
import FCAppendix.Affine.Tail04.TypicalLottery

noncomputable section
namespace FCAppendix.Affine.Tail04
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def relabelFlags (e : Equiv.Perm ι) (flags : ι → Bool) : ι → Bool := flags ∘ e.symm

def relabelFlagEquiv (e : Equiv.Perm ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := relabelFlags e
  invFun := fun flags => flags ∘ e
  left_inv := by intro flags; funext i; simp [relabelFlags]
  right_inv := by intro flags; funext i; simp [relabelFlags]

theorem independentFlagLaw_relabel (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (e : Equiv.Perm ι) :
    independentFlagLaw (p ∘ e.symm) (fun i => hp0 (e.symm i)) (fun i => hp1 (e.symm i)) =
      (independentFlagLaw p hp0 hp1).map (relabelFlagEquiv e) := by
  apply FiniteLaw.ext
  intro flags
  rw [BidDependentFlags.map_equiv_mass]
  change (∏ i, if flags i then p (e.symm i) else 1-p (e.symm i)) =
    ∏ i, if flags (e i) then p i else 1-p i
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp e (fun i => if flags i then p (e.symm i) else 1-p (e.symm i))).symm

theorem independentFlagLaw_expect_relabel (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (e : Equiv.Perm ι)
    (f : (ι → Bool) → ℝ) :
    (independentFlagLaw (p ∘ e.symm) (fun i => hp0 (e.symm i)) (fun i => hp1 (e.symm i))).expect f =
      (independentFlagLaw p hp0 hp1).expect (fun flags => f (relabelFlags e flags)) := by
  rw [independentFlagLaw_relabel,FiniteLaw.expect_map]
  rfl

omit [Fintype ι] in
theorem forceExclusive_relabel (e : Equiv.Perm ι) (target : ι) (flags : ι → Bool) :
    forceExclusive (e target) (relabelFlags e flags)=
      relabelFlags e (forceExclusive target flags) := by
  funext i
  by_cases hi : i=e target
  · subst i
    simp [forceExclusive,relabelFlags]
  · have hpre : e.symm i ≠ target := by
      intro h
      apply hi
      calc
        i=e (e.symm i) := (e.apply_symm_apply i).symm
        _=e target := congrArg e h
    simp only [forceExclusive,Function.update_of_ne hi,relabelFlags,
      Function.comp_apply,Function.update_of_ne hpre]

omit [DecidableEq ι] in
theorem flaggedMixedSet_relabel (e : Equiv.Perm ι) (flags : ι → Bool) :
    flaggedMixedSet (relabelFlags e flags)=(flaggedMixedSet flags).map e.toEmbedding := by
  ext i
  constructor
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨e.symm i,?_,e.apply_symm_apply i⟩
    simpa only [flaggedMixedSet,Finset.mem_filter,Finset.mem_univ,true_and,
      relabelFlags,Function.comp_apply] using h
  · rintro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp h
    have hj' : flags j=true := (Finset.mem_filter.mp hj).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change flags (e.symm (e j))=true
    rw [e.symm_apply_apply]
    exact hj'

theorem forcedMixedSet_relabel (e : Equiv.Perm ι) (target : ι) (flags : ι → Bool) :
    flaggedMixedSet (forceExclusive (e target) (relabelFlags e flags))=
      (flaggedMixedSet (forceExclusive target flags)).map e.toEmbedding := by
  rw [forceExclusive_relabel,flaggedMixedSet_relabel]

omit [Fintype ι] [DecidableEq ι] in
theorem mixedReciprocalSum_relabel (b : ι → ℝ) (I : Finset ι) (e : Equiv.Perm ι) :
    mixedReciprocalSum (I.map e.toEmbedding) (b ∘ e.symm)=mixedReciprocalSum I b := by
  simp [mixedReciprocalSum,Finset.sum_map]

end FCAppendix.Affine.Tail04
