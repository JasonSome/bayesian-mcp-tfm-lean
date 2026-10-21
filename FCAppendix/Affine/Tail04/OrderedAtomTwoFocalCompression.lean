import FCAppendix.Affine.Tail04.TwoFocalCompression

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomTwoFocalCompression
open MeasureTheory ProbabilityTheory Set Classical
open MenuError OriginalFlagCompression NativeTypicalCount EqualPrivateSignal TwoFocalCompression
open scoped BigOperators

variable {X : Type*} {N A : ℕ} (row : Fin N→X×unitInterval)
  (active : X→Bool) (p : X→unitInterval) (bid : X→ℝ)
  (e : Fin A≃Active (fullActive row active)) (target : Fin A)

theorem two_phi_exact (hN : 0< N) (private0 private1 : X→ Bool)
    (b0 b1 : ℝ) (f0 f1 : Bool) (ξ share ρ B R Rp width : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks ((min (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))))
    (ν1 : FiniteLaw (Marks ((max (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))))
    (hmean0 : privateMean _ reg ν0=share*(min (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
    (hmean1 : privateMean _ reg ν1=share*(max (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
    (hb : ∀ j,active (row j).1=true → 1≤ bid (row j).1) :
    targetTypicalWeight
      (TypicalGuardStatistics.phi A
        ((min (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
        ((max (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
        (twoCapacity ρ N) ξ B R Rp width reg ν0 ν1)
      (compressedBids (fullActive row active) e (fullBid row bid b0 b1)) target
      (compressedFlags (fullActive row active) e (fullFlags row p f0 f1))=
      let A0 := twoActiveCount N (fun _ : Unit => row) active ()
      let M := twoMixedCount N (fun _ : Unit => row) active p f0 f1 (fun _ => (e target).val) ()
      let H0 := (min (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ()))
      let H1 := (max (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ()))
      let q := clampedOwner (A0-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity ρ N) q (A0-M-q) M
        ξ B R Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N (fun _ : Unit => row) active p bid b0 b1 f0 f1
            (fun _ => (e target).val) ()) := by
  have h := actual_phi_compression_capacity (fullActive row active)
    ((min (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
    ((max (privateCount N (fun _ : Unit => row) private0 ()) (privateCount N (fun _ : Unit => row) private1 ())))
    (twoCapacity ρ N) ξ share B R Rp width reg ν0 ν1 hmean0 hmean1 e
    (fullBid row bid b0 b1) (fullFlags row p f0 f1) target
  rw [full_active_count,full_mixed_count,
    full_reciprocal row active p bid hN b0 b1 f0 f1 (e target).val hb] at h
  exact h

end FCAppendix.Affine.Tail04.OrderedAtomTwoFocalCompression
