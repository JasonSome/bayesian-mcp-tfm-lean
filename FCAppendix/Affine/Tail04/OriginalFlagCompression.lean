import FCAppendix.Affine.Tail04.PartialFocalGuard
import FCAppendix.Affine.Tail04.OriginalOwnerCount
import FCAppendix.Affine.Tail04.FlagRelabel

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalFlagCompression
open MeasureTheory ProbabilityTheory Set Classical
open MenuError NativeTypicalCount EqualPrivateSignal
open scoped BigOperators

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (active : ι→ Bool)

abbrev Active := {i : ι // active i=true}

def fullMixedBit (flags : ι→ Bool) (target : ι) (i : ι) : Bool :=
  if active i then if i=target then false else flags i else false

def fullMixedCount (flags : ι→ Bool) (target : ι) : ℕ :=
  boolCount (fullMixedBit active flags target)

def fullReciprocal (bid : ι→ℝ) (flags : ι→ Bool) (target : ι) : ℝ :=
  ∑ i,if active i=true ∧ i≠target ∧ flags i=true then 1/bid i else 0

omit [DecidableEq ι] in
theorem sum_compression {V : Type*} [AddCommMonoid V] {A : ℕ}
    (e : Fin A≃Active active) (f : ι→ V) :
    (∑ j : Fin A,f (e j).val)=∑ i,if active i=true then f i else 0 := by
  have hs := Fintype.sum_subtype_add_sum_subtype (p:=fun i : ι => active i=true)
    (fun i => if active i=true then f i else 0)
  have hz : (∑ i : {i : ι // ¬active i=true},if active i.val=true then f i.val else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg i.property
  rw [hz,add_zero] at hs
  have he := Equiv.sum_comp e (fun i : Active active => f i.val)
  exact he.trans ((Finset.sum_congr rfl (fun i _ => (if_pos i.property).symm)).trans hs)

omit [DecidableEq ι] in
theorem active_card {A : ℕ} (e : Fin A≃Active active) : boolCount active=A := by
  have hs := sum_compression active e (fun _ => (1:ℕ))
  change (∑ i,if active i = true then (1:ℕ) else 0) = A
  rw [←hs]
  simp

def compressedFlags {A : ℕ} (e : Fin A≃Active active) (flags : ι→ Bool) : Fin A→ Bool :=
  fun j => flags (e j).val

def compressedBids {A : ℕ} (e : Fin A≃Active active) (bid : ι→ℝ) : Fin A→ℝ :=
  fun j => bid (e j).val

omit [Fintype ι] [DecidableEq ι] in
lemma original_target_iff {A : ℕ} (e : Fin A≃Active active) (t j : Fin A) :
    (e j).val=(e t).val ↔ j=t := by
  constructor
  · intro h;exact e.injective (Subtype.ext h)
  · intro h;exact congrArg (fun k => (e k).val) h

theorem mixed_card_compression {A : ℕ} (e : Fin A≃Active active)
    (flags : ι→ Bool) (t : Fin A) :
    (targetMixedSet t (compressedFlags active e flags)).card=
      fullMixedCount active flags (e t).val := by
  unfold targetMixedSet flaggedMixedSet
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  have hs := sum_compression active e (fun i =>
    if i=(e t).val then (0:ℕ) else if flags i then 1 else 0)
  calc
    _ = ∑ j : Fin A,if (e j).val=(e t).val then 0 else if flags (e j).val then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=t
      · subst j;simp [forceExclusive]
      · have ho : (e j).val≠(e t).val := (original_target_iff active e t j).not.mpr hj
        simp only [forceExclusive,Function.update_of_ne hj,compressedFlags,if_neg ho]
    _ = _ := by
      rw [hs]
      unfold fullMixedCount boolCount fullMixedBit
      apply Finset.sum_congr rfl
      intro i _
      cases ha : active i <;> by_cases ht : i=(e t).val <;>
        cases hf : flags i <;> simp_all

theorem reciprocal_compression {A : ℕ} (e : Fin A≃Active active)
    (bid : ι→ℝ) (flags : ι→ Bool) (t : Fin A) :
    mixedReciprocalSum (targetMixedSet t (compressedFlags active e flags))
      (compressedBids active e bid)=fullReciprocal active bid flags (e t).val := by
  unfold mixedReciprocalSum targetMixedSet flaggedMixedSet
  rw [Finset.sum_filter]
  have hs := sum_compression active e (fun i =>
    if i≠(e t).val ∧ flags i=true then 1/bid i else 0)
  calc
    _ = ∑ j : Fin A,if (e j).val≠(e t).val ∧ flags (e j).val=true
        then 1/bid (e j).val else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j=t
      · subst j;simp [forceExclusive]
      · have ho : (e j).val≠(e t).val := (original_target_iff active e t j).not.mpr hj
        simp_all [forceExclusive,compressedFlags,compressedBids]
    _ = _ := by
      rw [hs]
      unfold fullReciprocal
      apply Finset.sum_congr rfl
      intro i _
      by_cases ha : active i=true <;> by_cases ht : i=(e t).val <;>
        cases hf : flags i <;> simp_all

theorem actual_phi_compression (N H0 H1 : ℕ) (hN : 0< N)
    (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (reg : Bool) (hshareLo : lowerShare reg≤ share)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hmean0 : privateMean H0 reg ν0=share*H0)
    (hmean1 : privateMean H1 reg ν1=share*H1)
    {A : ℕ} (e : Fin A≃Active active) (bid : ι→ℝ) (flags : ι→ Bool) (t : Fin A) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi A H0 H1 (iidCapacity ρ N) ξ B R Rp width reg ν0 ν1)
      (compressedBids active e bid) t (compressedFlags active e flags)=
      scalarSourceWeight N (boolCount active) (fullMixedCount active flags (e t).val)
        H0 H1 ξ share ρ B R Rp width hshare reg
        (fullReciprocal active bid flags (e t).val/(N:ℝ)) := by
  rw [targetTypicalWeight,mixed_card_compression,reciprocal_compression]
  rw [active_card active e]
  unfold TypicalGuardStatistics.phi
  simp only [countParameters,TypicalCountParameters.owner0,TypicalCountParameters.owner1,
    hmean0,hmean1]
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hs := actual_weight_eq_scalarSourceWeight N A (fullMixedCount active flags (e t).val)
    H0 H1 ξ share ρ B R Rp width hshare reg
    (fullReciprocal active bid flags (e t).val/(N:ℝ)) hshareLo ν0 ν1 hmean0 hmean1
  simpa only [clampedOwner,mul_div_cancel₀ _ hN0] using hs

theorem actual_phi_compression_capacity (H0 H1 c : ℕ)
    (ξ share B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hmean0 : privateMean H0 reg ν0=share*H0)
    (hmean1 : privateMean H1 reg ν1=share*H1)
    {A : ℕ} (e : Fin A≃Active active) (bid : ι→ℝ) (flags : ι→ Bool) (t : Fin A) :
    targetTypicalWeight (TypicalGuardStatistics.phi A H0 H1 c ξ B R Rp width reg ν0 ν1)
      (compressedBids active e bid) t (compressedFlags active e flags)=
      let M := fullMixedCount active flags (e t).val
      let Q := clampedOwner (boolCount active-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 c Q (boolCount active-M-Q) M
        ξ B R Rp width reg ν0 ν1 (fullReciprocal active bid flags (e t).val) := by
  rw [targetTypicalWeight,mixed_card_compression,reciprocal_compression,active_card active e]
  simp only [TypicalGuardStatistics.phi,countParameters,TypicalCountParameters.owner0,
    TypicalCountParameters.owner1,hmean0,hmean1,clampedOwner]

end Finite

section Partial
variable {X : Type*} {N A : ℕ} (row : Fin N→ X×unitInterval)
    (active : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)
    (e : Fin A≃Active (fun i : Fin N => active (row i).1)) (t : Fin A)

def partialTarget : Fin (N+1) := ((e t).val).succ

theorem partial_mixed_compression :
    (targetMixedSet t (fun j => Empirical.flag (p (row (e j).val).1) (row (e j).val).2)).card=
      flaggedMixedCount N (fun _ : Unit => row) (fun _ => partialTarget row active e t)
        active p false () := by
  change (targetMixedSet t (compressedFlags (fun i => active (row i).1) e
    (fun i => Empirical.flag (p (row i).1) (row i).2))).card = _
  rw [mixed_card_compression (fun i : Fin N => active (row i).1) e
    (fun i => Empirical.flag (p (row i).1) (row i).2) t]
  unfold flaggedMixedCount boolCount
  rw [Fin.sum_univ_succ]
  simp [flaggedMixedBit,partialTarget, (Fin.succ_ne_zero ((e t).val)).symm]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold fullMixedCount boolCount fullMixedBit
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : i=(e t).val <;> cases ha : active (row i).1 <;>
    cases hf : Empirical.flag (p (row i).1) (row i).2 <;>
    simp [ht,ha,hf,activeFlag]

theorem partial_reciprocal_compression (hN : 0< N)
    (hb : ∀ i,active (row i).1=true → 1≤ bid (row i).1) :
    mixedReciprocalSum
      (targetMixedSet t (fun j => Empirical.flag (p (row (e j).val).1) (row (e j).val).2))
      (fun j => bid (row (e j).val).1)=
      (N:ℝ)*flaggedReciprocal N (fun _ : Unit => row)
        (fun _ => partialTarget row active e t) active p bid 1 false () := by
  change mixedReciprocalSum
    (targetMixedSet t (compressedFlags (fun i => active (row i).1) e
      (fun i => Empirical.flag (p (row i).1) (row i).2)))
    (compressedBids (fun i => active (row i).1) e (fun i => bid (row i).1)) = _
  rw [reciprocal_compression (fun i : Fin N => active (row i).1) e
    (fun i => bid (row i).1) (fun i => Empirical.flag (p (row i).1) (row i).2) t]
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold flaggedReciprocal forcedMean
  rw [mul_div_cancel₀ _ hN0,Fin.sum_univ_succ]
  simp only [partialTarget, (Fin.succ_ne_zero ((e t).val)).symm, if_false, prefixWeight,
    Fin.cases_zero, Fin.cases_succ]
  norm_num only [Bool.false_eq_true, ite_false, zero_add]
  simp only [Fin.succ_inj]
  unfold fullReciprocal
  apply Finset.sum_congr rfl
  intro i _
  by_cases ht : i=(e t).val <;> cases ha : active (row i).1 <;>
    cases hf : Empirical.flag (p (row i).1) (row i).2
  all_goals try simp [ht,ha,hf,Empirical.markedStatistic,reciprocalWeight]
  all_goals exact hb i ha

theorem partial_phi_exact (hN : 0< N)
    (private0 private1 : X→ Bool) (side : Fin 2)
    (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (reg : Bool) (hshareLo : lowerShare reg≤ share)
    (ν0 : FiniteLaw (Marks (partialPrivateCount N (fun _ : Unit => row) private0 side 0 ())))
    (ν1 : FiniteLaw (Marks (partialPrivateCount N (fun _ : Unit => row) private1 side 1 ())))
    (hmean0 : privateMean _ reg ν0=share*partialPrivateCount N (fun _ : Unit => row) private0 side 0 ())
    (hmean1 : privateMean _ reg ν1=share*partialPrivateCount N (fun _ : Unit => row) private1 side 1 ())
    (hb : ∀ i,active (row i).1=true → 1≤ bid (row i).1) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi A
        (partialPrivateCount N (fun _ : Unit => row) private0 side 0 ())
        (partialPrivateCount N (fun _ : Unit => row) private1 side 1 ())
        (iidCapacity ρ N) ξ B R Rp width reg ν0 ν1)
      (fun j => bid (row (e j).val).1) t
      (fun j => Empirical.flag (p (row (e j).val).1) (row (e j).val).2)=
      partialGuardWeight N (fun _ : Unit => row) (fun _ => partialTarget row active e t)
        active private0 private1 p bid ξ share ρ B R Rp width hshare reg side () := by
  let a : Fin N→ Bool := fun i => active (row i).1
  let f : Fin N→ Bool := fun i => Empirical.flag (p (row i).1) (row i).2
  let b : Fin N→ℝ := fun i => bid (row i).1
  have hs := actual_phi_compression a N
    (partialPrivateCount N (fun _ : Unit => row) private0 side 0 ())
    (partialPrivateCount N (fun _ : Unit => row) private1 side 1 ()) hN
    ξ share ρ B R Rp width hshare reg hshareLo ν0 ν1 hmean0 hmean1 e b f t
  have hM : fullMixedCount a f (e t).val=
      flaggedMixedCount N (fun _ : Unit => row) (fun _ => partialTarget row active e t)
        active p false () :=
    (mixed_card_compression a e f t).symm.trans (partial_mixed_compression row active p e t)
  have hW : fullReciprocal a b f (e t).val=
      (N:ℝ)*flaggedReciprocal N (fun _ : Unit => row) (fun _ => partialTarget row active e t)
        active p bid 1 false () :=
    (reciprocal_compression a e b f t).symm.trans
      (partial_reciprocal_compression row active p bid e t hN hb)
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [hM,hW,mul_div_cancel_left₀ _ hN0] at hs
  exact hs

end Partial
end FCAppendix.Affine.Tail04.OriginalFlagCompression
