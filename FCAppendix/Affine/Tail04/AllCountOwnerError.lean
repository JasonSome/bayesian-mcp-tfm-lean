import FCAppendix.Affine.Tail04.NormalizedMenuError

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open Set MeasureTheory

def clampedOwner (E : ℕ) (mean0 mean1 : ℝ) : ℕ :=
  min E (balancedOwnerQuota E mean0 mean1)

theorem clampedOwner_le (E : ℕ) (mean0 mean1 : ℝ) : clampedOwner E mean0 mean1≤ E :=
  min_le_left _ _

theorem clampedOwner_error (E : ℕ) (mean0 mean1 : ℝ) :
    |(clampedOwner E mean0 mean1:ℝ)-((E:ℝ)+mean1-mean0)/2|≤
      1/2+|mean1-mean0|/2 := by
  let x := ((E:ℝ)+mean1-mean0)/2
  have hE : (0:ℝ)≤ E := Nat.cast_nonneg _
  have hd0 := neg_le_abs (mean1-mean0)
  have hd1 := le_abs_self (mean1-mean0)
  have hd : 0≤|mean1-mean0| := abs_nonneg _
  change |((min E (nearestQuota x):ℕ):ℝ)-x|≤_
  by_cases hx : 0≤ x
  · have hnear := nearestQuota_error hx
    by_cases hquota : nearestQuota x≤ E
    · rw [min_eq_right hquota]
      exact hnear.trans (le_add_of_nonneg_right (by positivity))
    · rw [min_eq_left (le_of_not_ge hquota)]
      have hlt : (E:ℝ)< nearestQuota x := by exact_mod_cast (lt_of_not_ge hquota)
      have hn := abs_le.mp hnear
      apply abs_le.mpr
      dsimp [x] at *
      constructor <;> linarith
  · have hx' : x<0 := lt_of_not_ge hx
    have hz : nearestQuota x=0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hz,min_eq_right (Nat.zero_le _),Nat.cast_zero,zero_sub,abs_neg,abs_of_nonpos hx'.le]
    dsimp [x] at *
    linarith

theorem clampedOwner_complement_error (E : ℕ) (mean0 mean1 : ℝ) :
    ((E-clampedOwner E mean0 mean1:ℕ):ℝ)-((E:ℝ)+mean0-mean1)/2=
      -((clampedOwner E mean0 mean1:ℝ)-((E:ℝ)+mean1-mean0)/2) := by
  rw [Nat.cast_sub (clampedOwner_le E mean0 mean1)]
  ring

def commonNumerator (ξ scale cap active private0 private1 mixed share : ℝ) : ℝ :=
  ((1-ξ/2)*mixed-ξ*cap+(ξ/2)*active+(ξ/2)*share*(private0+private1))/scale

def normalizedOwnerError (A M H0 H1 : ℕ) (share scale : ℝ) : ℝ :=
  ((clampedOwner (A-M) (share*H0) (share*H1):ℝ)-
    (((A-M:ℕ):ℝ)+share*H1-share*H0)/2)/scale

theorem normalizedOwnerError_bound (A M H0 H1 : ℕ) {share scale : ℝ}
    (hshare : 0≤ share) (hscale : 0< scale) :
    |normalizedOwnerError A M H0 H1 share scale|≤
      1/(2*scale)+(share/2)*|(H1:ℝ)/scale-(H0:ℝ)/scale| := by
  unfold normalizedOwnerError
  rw [abs_div,abs_of_pos hscale]
  calc
    _ ≤ (1/2+|share*(H1:ℝ)-share*(H0:ℝ)|/2)/scale :=
      div_le_div_of_nonneg_right (clampedOwner_error (A-M) (share*H0) (share*H1)) hscale.le
    _ = _ := by
      rw [←mul_sub,abs_mul,abs_of_nonneg hshare,←sub_div,abs_div,abs_of_pos hscale]
      field_simp [hscale.ne']

theorem balanced_numerators (A M H0 H1 c : ℕ) (hMA : M≤ A) (ξ share scale : ℝ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    let n := commonNumerator ξ scale c A H0 H1 M share
    let e := normalizedOwnerError A M H0 H1 share scale
    (((M:ℝ)-ξ*((c:ℝ)-share*H0-Q))/scale=n+ξ*e) ∧
      (((M:ℝ)-ξ*((c:ℝ)-share*H1-(A-M-Q:ℕ)))/scale=n-ξ*e) := by
  dsimp only
  have hQ := clampedOwner_le (A-M) (share*H0) (share*H1)
  unfold commonNumerator normalizedOwnerError
  simp only [Nat.cast_sub hMA,Nat.cast_sub hQ]
  constructor <;> simp only [div_eq_mul_inv] <;> ring

theorem meanCountLaw_normalized (ξ b scale : ℝ) (hscale : scale≠0)
    (c ell0 ell1 M : ℕ) (mean0 mean1 W : ℝ) :
    meanCountLaw ξ c ell0 ell1 mean0 mean1 M W b=
      clippedCount ξ b (((M:ℝ)-ξ*((c:ℝ)-mean0-ell0))/scale)
        (((M:ℝ)-ξ*((c:ℝ)-mean1-ell1))/scale) (W/scale) := by
  have he (ell : ℕ) (mu : ℝ) : meanMarginal ξ c ell mu M W b=
      clippedMarginal ξ b (((M:ℝ)-ξ*((c:ℝ)-mu-ell))/scale) (W/scale) := by
    unfold meanMarginal rawMeanMarginal clippedMarginal
    apply congrArg probabilityClip
    apply congrArg (fun x : ℝ => (1-x/b)/ξ)
    by_cases hW : W=0
    · simp [hW]
    · field_simp [hscale,hW]
  apply FiniteLaw.ext_expect
  intro f
  unfold meanCountLaw clippedCount
  rw [twoCoinCountLaw_expect,twoCoinCountLaw_expect,he ell0 mean0,he ell1 mean1]

theorem balanced_meanCountLaw_normalized (A M H0 H1 c : ℕ) (hMA : M≤ A)
    (ξ share scale b W : ℝ) (hscale : scale≠0) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    let n := commonNumerator ξ scale c A H0 H1 M share
    let e := normalizedOwnerError A M H0 H1 share scale
    meanCountLaw ξ c Q (A-M-Q) (share*H0) (share*H1) M W b=
      clippedCount ξ b (n+ξ*e) (n-ξ*e) (W/scale) := by
  dsimp only
  rw [meanCountLaw_normalized ξ b scale hscale]
  obtain ⟨h0,h1⟩ := balanced_numerators A M H0 H1 c hMA ξ share scale
  rw [h0,h1]

theorem abs_four_terms (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d| := by
  calc
    _ ≤ |a+b+c|+|d| := abs_add_le _ _
    _ ≤ (|a+b|+|c|)+|d| := add_le_add (abs_add_le _ _) (le_refl _)
    _ ≤ _ := add_le_add (add_le_add (abs_add_le _ _) (le_refl _)) (le_refl _)

theorem balanced_numerator_error (A M H0 H1 c : ℕ) (hMA : M≤ A)
    {ξ share scale : ℝ} (hξ : 0≤ ξ) (hξ1 : ξ≤1) (hshare : 0≤ share) (hscale : 0< scale)
    (ρ abar mbar hbar : ℝ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
    let E := (1-ξ/2)*|(M:ℝ)/scale-mbar|+ξ*|(c:ℝ)/scale-ρ|+
      (ξ/2)*|(A:ℝ)/scale-abar|+
      ξ*share*(|(H0:ℝ)/scale-hbar|+|(H1:ℝ)/scale-hbar|)+ξ/(2*scale)
    |((M:ℝ)-ξ*((c:ℝ)-share*H0-Q))/scale-nbar|≤ E ∧
      |((M:ℝ)-ξ*((c:ℝ)-share*H1-(A-M-Q:ℕ)))/scale-nbar|≤ E := by
  dsimp only
  let C := commonNumerator ξ scale c A H0 H1 M share
  let e := normalizedOwnerError A M H0 H1 share scale
  let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
  have hcoef : 0≤1-ξ/2 := by linarith
  have hhalf : 0≤ ξ/2 := by positivity
  have hpriv : 0≤ ξ*share/2 := by positivity
  have hcommon : |C-nbar|≤
      (1-ξ/2)*|(M:ℝ)/scale-mbar|+ξ*|(c:ℝ)/scale-ρ|+
      (ξ/2)*|(A:ℝ)/scale-abar|+
      (ξ*share/2)*(|(H0:ℝ)/scale-hbar|+|(H1:ℝ)/scale-hbar|) := by
    have hid : C-nbar=
      (1-ξ/2)*((M:ℝ)/scale-mbar)+(-ξ)*((c:ℝ)/scale-ρ)+
      (ξ/2)*((A:ℝ)/scale-abar)+(ξ*share/2)*
        (((H0:ℝ)/scale-hbar)+((H1:ℝ)/scale-hbar)) := by
      dsimp [C,commonNumerator,nbar]
      simp only [div_eq_mul_inv]
      ring
    rw [hid]
    have ht := abs_four_terms ((1-ξ/2)*((M:ℝ)/scale-mbar))
      ((-ξ)*((c:ℝ)/scale-ρ)) ((ξ/2)*((A:ℝ)/scale-abar))
      ((ξ*share/2)*(((H0:ℝ)/scale-hbar)+((H1:ℝ)/scale-hbar)))
    rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg hcoef,abs_neg,
      abs_of_nonneg hξ,abs_of_nonneg hhalf,abs_of_nonneg hpriv] at ht
    exact ht.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left (abs_add_le _ _) hpriv))
  have himbalance : |(H1:ℝ)/scale-(H0:ℝ)/scale|≤
      |(H0:ℝ)/scale-hbar|+|(H1:ℝ)/scale-hbar| := by
    have hh := abs_sub_le ((H1:ℝ)/scale) hbar ((H0:ℝ)/scale)
    rw [abs_sub_comm hbar] at hh
    linarith
  have he : |e|≤1/(2*scale)+(share/2)*
      (|(H0:ℝ)/scale-hbar|+|(H1:ℝ)/scale-hbar|) :=
    (normalizedOwnerError_bound A M H0 H1 hshare hscale).trans
      (add_le_add (le_refl (1/(2*scale)))
        (mul_le_mul_of_nonneg_left himbalance (show 0 ≤ share/2 from by positivity)))
  obtain ⟨h0,h1⟩ := balanced_numerators A M H0 H1 c hMA ξ share scale
  rw [h0,h1]
  have hplus : |C+ξ*e-nbar|≤|C-nbar|+ξ*|e| := by
    have heq : C+ξ*e-nbar=(C-nbar)+ξ*e := by ring
    rw [heq]
    simpa only [abs_mul,abs_of_nonneg hξ] using abs_add_le (C-nbar) (ξ*e)
  have hminus : |C-ξ*e-nbar|≤|C-nbar|+ξ*|e| := by
    have heq : C-ξ*e-nbar=(C-nbar)-ξ*e := by ring
    rw [heq]
    simpa only [abs_mul,abs_of_nonneg hξ] using abs_sub (C-nbar) (ξ*e)
  have hr := add_le_add hcommon (mul_le_mul_of_nonneg_left he hξ)
  constructor
  · exact hplus.trans (by
      convert! hr using 1
      ring)
  · exact hminus.trans (by
      convert! hr using 1
      ring)

end FCAppendix.Affine.Tail04.MenuError
