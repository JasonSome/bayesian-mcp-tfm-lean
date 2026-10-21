import FCAppendix.Affine.Tail04.OriginalFlagCompression

noncomputable section
namespace FCAppendix.Affine.Tail04.TwoFocalCompression
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression NativeTypicalCount EqualPrivateSignal
open scoped BigOperators

variable {X : Type*} {N A : ℕ} (row : Fin N→ X×unitInterval)
  (active : X→ Bool) (p : X→ unitInterval) (bid : X→ℝ)

def fullActive : Fin (N+2)→ Bool :=
  Fin.cases true (Fin.cases true (fun j : Fin N => active (row j).1))

def fullFlags (f0 f1 : Bool) : Fin (N+2)→ Bool :=
  Fin.cases f0 (Fin.cases f1 (fun j : Fin N => Empirical.flag (p (row j).1) (row j).2))

def fullBid (b0 b1 : ℝ) : Fin (N+2)→ℝ :=
  Fin.cases b0 (Fin.cases b1 (fun j : Fin N => bid (row j).1))

lemma full_active_count : boolCount (fullActive row active)=
    twoActiveCount N (fun _ : Unit => row) active () := rfl

lemma full_mixed_count (f0 f1 : Bool) (target : Fin (N+2)) :
    fullMixedCount (fullActive row active) (fullFlags row p f0 f1) target=
      twoMixedCount N (fun _ : Unit => row) active p f0 f1 (fun _ => target) () := by
  unfold fullMixedCount twoMixedCount
  congr 1
  funext j
  by_cases hj : j=target
  · subst j
    simp only [fullMixedBit,twoMixedBit]
    cases fullActive row active target <;> rfl
  · simp only [fullMixedBit,twoMixedBit,if_neg hj]
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [fullActive,fullFlags,Fin.cases_zero,if_true]
    · refine Fin.cases ?_ (fun k => ?_) k
      · simp only [fullActive,fullFlags,Fin.cases_succ,Fin.cases_zero,if_true]
      · cases ha : active (row k).1 <;> cases hf : Empirical.flag (p (row k).1) (row k).2 <;>
          simp [fullActive,fullFlags,activeFlag,ha,hf]

lemma full_reciprocal (hN : 0< N) (b0 b1 : ℝ) (f0 f1 : Bool) (target : Fin (N+2))
    (hb : ∀ j,active (row j).1=true → 1≤ bid (row j).1) :
    fullReciprocal (fullActive row active) (fullBid row bid b0 b1) (fullFlags row p f0 f1) target=
      (N:ℝ)*twoReciprocal N (fun _ : Unit => row) active p bid b0 b1 f0 f1
        (fun _ => target) () := by
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold fullReciprocal twoReciprocal twoForcedMean
  rw [mul_div_cancel₀ _ hN0]
  apply Finset.sum_congr rfl
  intro j _
  refine Fin.cases ?_ (fun k => ?_) j
  · by_cases ht : (0 : Fin (N+2))=target <;> cases f0 <;>
      simp [fullActive,fullBid,fullFlags,twoPrefixWeight,ht]
  · refine Fin.cases ?_ (fun k => ?_) k
    · by_cases ht : (0 : Fin (N+1)).succ=target <;> cases f1 <;>
        simp only [fullActive,fullBid,fullFlags,twoPrefixWeight,
          Fin.cases_succ,Fin.cases_zero]
      all_goals simp_all
    · by_cases ht : k.succ.succ=target <;>
        cases ha : active (row k).1 <;> cases hf : Empirical.flag (p (row k).1) (row k).2
      all_goals try simp [fullActive,fullBid,fullFlags,twoPrefixWeight,ht,ha,hf,
        Empirical.markedStatistic,reciprocalWeight]
      all_goals exact hb k ha

variable (e : Fin A≃Active (fullActive row active)) (target : Fin A)

theorem mixed_compression (f0 f1 : Bool) :
    (targetMixedSet target
      (compressedFlags (fullActive row active) e (fullFlags row p f0 f1))).card=
      twoMixedCount N (fun _ : Unit => row) active p f0 f1 (fun _ => (e target).val) () := by
  rw [mixed_card_compression,full_mixed_count]

theorem reciprocal_compression (hN : 0< N) (b0 b1 : ℝ) (f0 f1 : Bool)
    (hb : ∀ j,active (row j).1=true → 1≤ bid (row j).1) :
    mixedReciprocalSum
      (targetMixedSet target (compressedFlags (fullActive row active) e (fullFlags row p f0 f1)))
      (compressedBids (fullActive row active) e (fullBid row bid b0 b1))=
      (N:ℝ)*twoReciprocal N (fun _ : Unit => row) active p bid b0 b1 f0 f1
        (fun _ => (e target).val) () := by
  rw [OriginalFlagCompression.reciprocal_compression]
  exact full_reciprocal row active p bid hN b0 b1 f0 f1 (e target).val hb

theorem two_phi_exact (hN : 0< N) (private0 private1 : X→ Bool)
    (b0 b1 : ℝ) (f0 f1 : Bool) (ξ share ρ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private0 ())))
    (ν1 : FiniteLaw (Marks (privateCount N (fun _ : Unit => row) private1 ())))
    (hmean0 : privateMean _ reg ν0=share*privateCount N (fun _ : Unit => row) private0 ())
    (hmean1 : privateMean _ reg ν1=share*privateCount N (fun _ : Unit => row) private1 ())
    (hb : ∀ j,active (row j).1=true → 1≤ bid (row j).1) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi A
        (privateCount N (fun _ : Unit => row) private0 ())
        (privateCount N (fun _ : Unit => row) private1 ())
        (twoCapacity ρ N) ξ B R Rp width reg ν0 ν1)
      (compressedBids (fullActive row active) e (fullBid row bid b0 b1)) target
      (compressedFlags (fullActive row active) e (fullFlags row p f0 f1))=
      let A0 := twoActiveCount N (fun _ : Unit => row) active ()
      let M := twoMixedCount N (fun _ : Unit => row) active p f0 f1 (fun _ => (e target).val) ()
      let H0 := privateCount N (fun _ : Unit => row) private0 ()
      let H1 := privateCount N (fun _ : Unit => row) private1 ()
      let q := clampedOwner (A0-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity ρ N) q (A0-M-q) M
        ξ B R Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N (fun _ : Unit => row) active p bid b0 b1 f0 f1
            (fun _ => (e target).val) ()) := by
  have h := actual_phi_compression_capacity (fullActive row active)
    (privateCount N (fun _ : Unit => row) private0 ())
    (privateCount N (fun _ : Unit => row) private1 ())
    (twoCapacity ρ N) ξ share B R Rp width reg ν0 ν1 hmean0 hmean1 e
    (fullBid row bid b0 b1) (fullFlags row p f0 f1) target
  rw [full_active_count,full_mixed_count,
    full_reciprocal row active p bid hN b0 b1 f0 f1 (e target).val hb] at h
  exact h

end FCAppendix.Affine.Tail04.TwoFocalCompression
