import FCAppendix.Affine.Tail04.CommonEmpiricalError
import FCAppendix.Affine.Tail04.OriginalFlagMeasure

noncomputable section
namespace FCAppendix.Affine.Tail04.CommonFlagCompression
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression NativeTypicalCount EqualPrivateSignal
open scoped BigOperators

variable {X : Type*} {N A : ℕ}
  (row : Fin N→ X×unitInterval) (active : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)

def activePrefix : Fin (N+1)→ Bool := Fin.cons true (fun k => active (row k).1)
def flagsPrefix (f : Bool) : Fin (N+1)→ Bool :=
  Fin.cons f (fun k => Empirical.flag (p (row k).1) (row k).2)
def bidsPrefix (b : ℝ) : Fin (N+1)→ℝ := Fin.cons b (fun k => bid (row k).1)

variable (e : Fin A≃Active (activePrefix row active)) (target : Fin A)

theorem mixed_exact (f : Bool) :
    (targetMixedSet target (compressedFlags (activePrefix row active) e (flagsPrefix row p f))).card=
      flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p f () := by
  rw [mixed_card_compression]
  unfold fullMixedCount flaggedMixedCount boolCount fullMixedBit flaggedMixedBit
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : k=(e target).val
  · simp [ht]
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp only [activePrefix,flagsPrefix,Fin.cons_zero,Fin.cases_zero,if_true]
    · cases ha : active (row l).1 <;>
        cases hf : Empirical.flag (p (row l).1) (row l).2 <;>
        simp [activePrefix,flagsPrefix,ha,hf,activeFlag]

theorem reciprocal_exact (hN : 0< N) (b : ℝ) (_hb : 1≤ b) (f : Bool)
    (_hbid : ∀ k,active (row k).1=true → 1≤ bid (row k).1) :
    mixedReciprocalSum
      (targetMixedSet target (compressedFlags (activePrefix row active) e (flagsPrefix row p f)))
      (compressedBids (activePrefix row active) e (bidsPrefix row bid b))=
      (N:ℝ)*flaggedReciprocal N (fun _ : Unit => row) (fun _ => (e target).val)
        active p bid b f () := by
  rw [reciprocal_compression]
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold flaggedReciprocal forcedMean
  rw [mul_div_cancel₀ _ hn]
  unfold fullReciprocal
  apply Finset.sum_congr rfl
  intro k _
  by_cases ht : k=(e target).val
  · simp [ht]
  · refine Fin.cases ?_ (fun l => ?_) k
    · cases f <;> simp [activePrefix,bidsPrefix,flagsPrefix,prefixWeight]
    · cases ha : active (row l).1 <;>
        cases hf : Empirical.flag (p (row l).1) (row l).2
      all_goals try simp [activePrefix,bidsPrefix,flagsPrefix,prefixWeight,ha,hf,
        Empirical.markedStatistic,reciprocalWeight]
      all_goals rw [max_eq_right (_hbid l ha)]

include e in
theorem active_exact : activeCount N (fun _ : Unit => row) active ()=A :=
  active_card (activePrefix row active) e

theorem phi_exact (hN : 0< N) (private0 private1 : X→ Bool)
    (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1) (reg : Bool)
    (hshareLo : lowerShare reg≤ share)
    (ν0 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private0 ())))
    (ν1 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private1 ())))
    (hmean0 : privateMean _ reg ν0=share*privateCount N (fun _ : Unit => row) private0 ())
    (hmean1 : privateMean _ reg ν1=share*privateCount N (fun _ : Unit => row) private1 ())
    (b : ℝ) (hb : 1≤ b) (f : Bool)
    (hbid : ∀ k,active (row k).1=true → 1≤ bid (row k).1) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi A (privateCount N (fun _ : Unit => row) private0 ())
        (privateCount N (fun _ : Unit => row) private1 ())
        (iidCapacity ρ N) ξ B R Rp width reg ν0 ν1)
      (compressedBids (activePrefix row active) e (bidsPrefix row bid b)) target
      (compressedFlags (activePrefix row active) e (flagsPrefix row p f))=
      flaggedGuardWeight N (fun _ : Unit => row) (fun _ => (e target).val)
        active private0 private1 p bid ξ share ρ B R Rp width b hshare reg f () := by
  rw [targetTypicalWeight,mixed_exact,reciprocal_exact row active p bid e target hN b hb f hbid]
  unfold TypicalGuardStatistics.phi
  simp only [countParameters,TypicalCountParameters.owner0,TypicalCountParameters.owner1,hmean0,hmean1]
  have ha := active_exact row active e
  simpa only [flaggedGuardWeight,ha,clampedOwner] using
    actual_weight_eq_scalarSourceWeight N (activeCount N (fun _ : Unit => row) active ())
      (flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p f ())
      (privateCount N (fun _ : Unit => row) private0 ())
      (privateCount N (fun _ : Unit => row) private1 ()) ξ share ρ B R Rp width hshare reg
      (flaggedReciprocal N (fun _ : Unit => row) (fun _ => (e target).val) active p bid b f ())
      hshareLo ν0 ν1 hmean0 hmean1

theorem mixedCount_exact (hN : 0< N) (private0 private1 : X→ Bool)
    (ξ share ρ : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private0 ())))
    (ν1 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private1 ())))
    (hmean0 : privateMean _ reg ν0=share*privateCount N (fun _ : Unit => row) private0 ())
    (hmean1 : privateMean _ reg ν1=share*privateCount N (fun _ : Unit => row) private1 ())
    (b : ℝ) (hb : 1≤ b) (f : Bool)
    (hbid : ∀ k,active (row k).1=true → 1≤ bid (row k).1) :
    let M := (targetMixedSet target (compressedFlags (activePrefix row active) e (flagsPrefix row p f))).card
    let W := mixedReciprocalSum
      (targetMixedSet target (compressedFlags (activePrefix row active) e (flagsPrefix row p f)))
      (compressedBids (activePrefix row active) e (bidsPrefix row bid b))
    let H0 := privateCount N (fun _ : Unit => row) private0 ()
    let H1 := privateCount N (fun _ : Unit => row) private1 ()
    let Q := clampedOwner (activeCount N (fun _ : Unit => row) active ()-
      flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p f ()) (share*H0) (share*H1)
    (countParameters A H0 H1 (iidCapacity ρ N) ξ reg ν0 ν1).mixedCount M W b=
      meanCountLaw ξ (iidCapacity ρ N) Q
        (activeCount N (fun _ : Unit => row) active ()-
          flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p f ()-Q)
        (share*H0) (share*H1)
        (flaggedMixedCount N (fun _ : Unit => row) (fun _ => (e target).val) active p f ())
        ((N:ℝ)*flaggedReciprocal N (fun _ : Unit => row) (fun _ => (e target).val) active p bid b f ()) b := by
  dsimp only
  rw [mixed_exact,reciprocal_exact row active p bid e target hN b hb f hbid]
  simp only [countParameters,TypicalCountParameters.mixedCount,TypicalCountParameters.owner0,
    TypicalCountParameters.owner1,hmean0,hmean1,clampedOwner,active_exact row active e]

lemma focal_membership (i : Fin A) (hi : (e i).val=0) (f : Bool) :
    i∈targetMixedSet target (compressedFlags (activePrefix row active) e (flagsPrefix row p f)) ↔
      f=true ∧ i≠target := by
  rw [targetMixedSet,flaggedMixedSet_forceExclusive]
  simp only [Finset.mem_erase,flaggedMixedSet,Finset.mem_filter,Finset.mem_univ,true_and,
    compressedFlags,hi,flagsPrefix,Fin.cons_zero]
  tauto

end FCAppendix.Affine.Tail04.CommonFlagCompression
