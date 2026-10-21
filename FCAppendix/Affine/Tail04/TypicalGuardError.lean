import FCAppendix.Affine.Tail04.IidActualBalancedCount
import FCAppendix.Affine.Tail04.TypicalGuardEndpoints

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory Set Classical
open EqualPrivateSignal NativeTypicalCount TypicalGuardEndpoints

def guardError (N A M H0 H1 : ℕ) (W abar mbar hbar wbar : ℝ) : ℝ :=
  |(A:ℝ)/N-abar|+|(M:ℝ)/N-mbar|+|(H0:ℝ)/N-hbar|+
    |(H1:ℝ)/N-hbar|+|W-wbar|+1/(N:ℝ)

theorem guardError_bounds (N A M H0 H1 : ℕ) (W abar mbar hbar wbar : ℝ) :
    0≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    |(A:ℝ)/N-abar|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    |(M:ℝ)/N-mbar|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    |(H0:ℝ)/N-hbar|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    |(H1:ℝ)/N-hbar|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    |W-wbar|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
    1/(N:ℝ)≤ guardError N A M H0 H1 W abar mbar hbar wbar := by
  have hn : 0≤1/(N:ℝ) := by positivity
  dsimp [guardError]
  have ha := abs_nonneg ((A:ℝ)/N-abar)
  have hm := abs_nonneg ((M:ℝ)/N-mbar)
  have h0 := abs_nonneg ((H0:ℝ)/N-hbar)
  have h1 := abs_nonneg ((H1:ℝ)/N-hbar)
  have hw := abs_nonneg (W-wbar)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith

theorem owners_guardError (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    {share : ℝ} (hshare : share∈Icc (0:ℝ) 1) (W abar mbar hbar wbar : ℝ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    let o := (abar-mbar)/2
    |(Q:ℝ)/N-o|≤ guardError N A M H0 H1 W abar mbar hbar wbar ∧
      |((A-M-Q:ℕ):ℝ)/N-o|≤ guardError N A M H0 H1 W abar mbar hbar wbar := by
  dsimp only
  let Q := clampedOwner (A-M) (share*H0) (share*H1)
  let mid := (((A:ℝ)/N)-((M:ℝ)/N))/2
  let D := |(H0:ℝ)/N-hbar|+|(H1:ℝ)/N-hbar|
  let E := 1/(2*(N:ℝ))+share*D
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hQ := clampedOwner_le (A-M) (share*H0) (share*H1)
  have hd : |(H1:ℝ)/N-(H0:ℝ)/N|≤ D := by
    have hh := abs_sub_le ((H1:ℝ)/N) hbar ((H0:ℝ)/N)
    rw [abs_sub_comm hbar] at hh
    dsimp [D]
    linarith
  have he := normalizedOwnerError_bound A M H0 H1 hshare.1 hn
  have hid : (Q:ℝ)/N-mid=normalizedOwnerError A M H0 H1 share N+
      (share/2)*((H1:ℝ)/N-(H0:ℝ)/N) := by
    dsimp [Q,mid,normalizedOwnerError]
    rw [Nat.cast_sub hMA]
    simp only [div_eq_mul_inv]
    ring
  have h0mid : |(Q:ℝ)/N-mid|≤ E := by
    rw [hid]
    have hh := abs_add_le (normalizedOwnerError A M H0 H1 share N)
      ((share/2)*((H1:ℝ)/N-(H0:ℝ)/N))
    rw [abs_mul,abs_of_nonneg (div_nonneg hshare.1 (by norm_num) : 0≤ share/2)] at hh
    have hmul := mul_le_mul_of_nonneg_left hd (div_nonneg hshare.1 (by norm_num) : 0≤ share/2)
    dsimp [E]
    linarith
  have h1mid : |((A-M-Q:ℕ):ℝ)/N-mid|≤ E := by
    have hid1 : ((A-M-Q:ℕ):ℝ)/N-mid= -((Q:ℝ)/N-mid) := by
      rw [Nat.cast_sub hQ,Nat.cast_sub hMA]
      dsimp [mid]
      simp only [div_eq_mul_inv]
      ring
    rw [hid1,abs_neg]
    exact h0mid
  have hmid : |mid-(abar-mbar)/2|≤
      (|(A:ℝ)/N-abar|+|(M:ℝ)/N-mbar|)/2 := by
    have heq : mid-(abar-mbar)/2=(((A:ℝ)/N-abar)-((M:ℝ)/N-mbar))/2 := by
      dsimp [mid]
      ring
    rw [heq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)
  have hD : 0≤ D := by dsimp [D]; positivity
  have hshareD : share*D≤ D := by nlinarith [hshare.2]
  have hE : E+(|(A:ℝ)/N-abar|+|(M:ℝ)/N-mbar|)/2≤
      guardError N A M H0 H1 W abar mbar hbar wbar := by
    have hAN := abs_nonneg ((A:ℝ)/N-abar)
    have hMN := abs_nonneg ((M:ℝ)/N-mbar)
    have hWN := abs_nonneg (W-wbar)
    have hi : 1/(2*(N:ℝ))=(1/(N:ℝ))/2 := by
      field_simp [hn.ne']
    have hin : 0≤1/(N:ℝ) := by positivity
    dsimp [E,guardError]
    rw [hi]
    dsimp [D] at hshareD
    linarith
  constructor
  · exact (abs_sub_le ((Q:ℝ)/N) mid ((abar-mbar)/2)).trans
      ((add_le_add h0mid hmid).trans hE)
  · exact (abs_sub_le (((A-M-Q:ℕ):ℝ)/N) mid ((abar-mbar)/2)).trans
      ((add_le_add h1mid hmid).trans hE)

def populationNumerator (ξ ρ abar mbar hbar keptShare : ℝ) : ℝ :=
  mbar-ξ*(ρ-(abar-mbar)/2-keptShare*hbar)

def endpointNumerator (N c ell M H : ℕ) (ξ keptShare : ℝ) : ℝ :=
  (M:ℝ)/N-ξ*((c:ℝ)/N-(ell:ℝ)/N-keptShare*((H:ℝ)/N))

def lowerShare (reg : Bool) : ℝ := if reg then 0 else 1

theorem lowerShare_mem (reg : Bool) : lowerShare reg∈Icc (0:ℝ) 1 := by
  cases reg <;> norm_num [lowerShare]

theorem lowerPrivateCount_real (H : ℕ) (reg : Bool) :
    (lowerPrivateCount H reg:ℝ)=lowerShare reg*(H:ℝ) := by
  cases reg <;> simp [lowerPrivateCount,lowerShare]

theorem populationNumerator_mono {ξ ρ abar mbar hbar k l : ℝ}
    (hξ : 0≤ ξ) (hh : 0≤ hbar) (hkl : k≤ l) :
    populationNumerator ξ ρ abar mbar hbar k≤ populationNumerator ξ ρ abar mbar hbar l := by
  have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkl hh) hξ
  unfold populationNumerator
  nlinarith

theorem endpointNumerator_error (N c ell M H : ℕ) (ξ k ρ abar mbar hbar Z : ℝ)
    (hξ : ξ∈Icc (0:ℝ) 1) (hk : k∈Icc (0:ℝ) 1)
    (hM : |(M:ℝ)/N-mbar|≤ Z) (hc : |(c:ℝ)/N-ρ|≤ Z)
    (hell : |(ell:ℝ)/N-(abar-mbar)/2|≤ Z) (hH : |(H:ℝ)/N-hbar|≤ Z) :
    |endpointNumerator N c ell M H ξ k-populationNumerator ξ ρ abar mbar hbar k|≤4*Z := by
  have hZ : 0≤ Z := (abs_nonneg _).trans hM
  have hid : endpointNumerator N c ell M H ξ k-populationNumerator ξ ρ abar mbar hbar k=
      ((M:ℝ)/N-mbar)+(-ξ)*((c:ℝ)/N-ρ)+ξ*((ell:ℝ)/N-(abar-mbar)/2)+
        (ξ*k)*((H:ℝ)/N-hbar) := by
    unfold endpointNumerator populationNumerator
    ring
  have hprod : ξ*k∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg hξ.1 hk.1,(mul_le_mul hξ.2 hk.2 hk.1 (by norm_num)).trans_eq (by norm_num)⟩
  rw [hid]
  have hh := abs_four_terms ((M:ℝ)/N-mbar) ((-ξ)*((c:ℝ)/N-ρ))
    (ξ*((ell:ℝ)/N-(abar-mbar)/2)) ((ξ*k)*((H:ℝ)/N-hbar))
  simp only [abs_mul,abs_neg,abs_of_nonneg hξ.1,abs_of_nonneg hprod.1] at hh
  have hc' : ξ*|(c:ℝ)/N-ρ|≤ Z := by
    exact (mul_le_mul_of_nonneg_left hc hξ.1).trans (by nlinarith [hξ.2])
  have hell' : ξ*|(ell:ℝ)/N-(abar-mbar)/2|≤ Z := by
    exact (mul_le_mul_of_nonneg_left hell hξ.1).trans (by nlinarith [hξ.2])
  have hH' : (ξ*k)*|(H:ℝ)/N-hbar|≤ Z := by
    exact (mul_le_mul_of_nonneg_left hH hprod.1).trans (by nlinarith [hprod.2])
  linarith

theorem lambda_normalized (N c ell M H : ℕ) (hN : 0< N)
    (ξ W k : ℝ) (hW : W≠0) :
    lambda c ell M ξ ((N:ℝ)*W) (k*(H:ℝ))=endpointNumerator N c ell M H ξ k/W := by
  have hn : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold lambda endpointNumerator
  field_simp [hn,hW]

def populationRadius (ρ abar mbar hbar wbar γ : ℝ) : ℝ :=
  min (mbar/2) (min (wbar/2) (min ((ρ-(abar-mbar)/2-hbar)/4) (γ*wbar/10)))

theorem populationRadius_pos {ρ abar mbar hbar wbar γ : ℝ}
    (hm : 0< mbar) (hw : 0< wbar) (hC : 0< ρ-(abar-mbar)/2-hbar) (hγ : 0< γ) :
    0< populationRadius ρ abar mbar hbar wbar γ := by
  unfold populationRadius
  positivity

theorem populationRadius_bounds (ρ abar mbar hbar wbar γ : ℝ) :
    populationRadius ρ abar mbar hbar wbar γ≤ mbar/2 ∧
    populationRadius ρ abar mbar hbar wbar γ≤ wbar/2 ∧
    4*populationRadius ρ abar mbar hbar wbar γ≤ ρ-(abar-mbar)/2-hbar ∧
    10*populationRadius ρ abar mbar hbar wbar γ≤ γ*wbar := by
  have h0 := min_le_left (mbar/2)
    (min (wbar/2) (min ((ρ-(abar-mbar)/2-hbar)/4) (γ*wbar/10)))
  have h1 := (min_le_right (mbar/2)
    (min (wbar/2) (min ((ρ-(abar-mbar)/2-hbar)/4) (γ*wbar/10)))).trans (min_le_left _ _)
  have h2 := ((min_le_right (mbar/2)
    (min (wbar/2) (min ((ρ-(abar-mbar)/2-hbar)/4) (γ*wbar/10)))).trans
      (min_le_right _ _)).trans (min_le_left _ _)
  have h3 := ((min_le_right (mbar/2)
    (min (wbar/2) (min ((ρ-(abar-mbar)/2-hbar)/4) (γ*wbar/10)))).trans
      (min_le_right _ _)).trans (min_le_right _ _)
  dsimp [populationRadius] at *
  exact ⟨h0,h1,by linarith,by linarith⟩

set_option maxHeartbeats 800000 in

theorem source_weight_eq_one_of_guardError_capacity (N A M H0 H1 c : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ B R Rp width γ δ extra W abar mbar hbar wbar : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (_hρ : ρ∈Icc (0:ℝ) 1)
    (hB : 0≤ B) (hhbar : 0≤ hbar) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hδ : 0< δ) (hδm : δ≤ mbar/2) (hδw : δ≤ wbar/2)
    (hδc : 4*δ≤ ρ-(abar-mbar)/2-hbar) (hδγ : 10*δ≤ γ*wbar)
    (hmean0 : privateMean H0 reg ν0=share*H0)
    (hmean1 : privateMean H1 reg ν1=share*H1)
    (hlo : (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar)
    (hhi : populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1)
    (hmean : if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R)
    (hextra : 0≤ extra)
    (hcapacity : |(c:ℝ)/N-ρ|≤ guardError N A M H0 H1 W abar mbar hbar wbar+extra)
    (hgood : guardError N A M H0 H1 W abar mbar hbar wbar+extra< δ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    TypicalGuardStatistics.weight H0 H1 c Q (A-M-Q) M
      ξ B R Rp width reg ν0 ν1 ((N:ℝ)*W)=1 := by
  dsimp only
  let Z := guardError N A M H0 H1 W abar mbar hbar wbar+extra
  let Q := clampedOwner (A-M) (share*H0) (share*H1)
  let o := (abar-mbar)/2
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hg := guardError_bounds N A M H0 H1 W abar mbar hbar wbar
  have hgle : guardError N A M H0 H1 W abar mbar hbar wbar≤ Z :=
    le_add_of_nonneg_right hextra
  have hz0 : 0≤ Z := hg.1.trans hgle
  have hzδ : Z< δ := hgood
  have hmerr : |(M:ℝ)/N-mbar|≤ Z := hg.2.2.1.trans hgle
  have h0err : |(H0:ℝ)/N-hbar|≤ Z := hg.2.2.2.1.trans hgle
  have h1err : |(H1:ℝ)/N-hbar|≤ Z := hg.2.2.2.2.1.trans hgle
  have hwerr : |W-wbar|≤ Z := hg.2.2.2.2.2.1.trans hgle
  have hcerr : |(c:ℝ)/N-ρ|≤ Z := hcapacity
  obtain ⟨ho0,ho1⟩ := owners_guardError N A M H0 H1 hN hMA hshare W abar mbar hbar wbar
  have ho0' : |(Q:ℝ)/N-o|≤ Z := ho0.trans hgle
  have ho1' : |((A-M-Q:ℕ):ℝ)/N-o|≤ Z := ho1.trans hgle
  have hmbar : 0< mbar := by linarith
  have hwbar : 0< wbar := by linarith
  have hγ : 0< γ := hw.trans_le hwγ
  have hWlow : wbar/2≤ W := by
    have he := (abs_le.mp hwerr).1
    linarith
  have hW : 0< W := (half_pos hwbar).trans_le hWlow
  have hfullW : 0<(N:ℝ)*W := mul_pos hn hW
  have hMpos : 0< M := by
    have he := (abs_le.mp hmerr).1
    have hmn : 0<(M:ℝ)/N := by linarith
    have hmr : 0<(M:ℝ) := by simpa using (lt_div_iff₀ hn).mp hmn
    exact_mod_cast hmr
  have cap_of_errors (ell H : ℕ)
      (hell : |(ell:ℝ)/N-o|≤ Z) (hH : |(H:ℝ)/N-hbar|≤ Z) : ell+H≤ c := by
    have hc0 := (abs_le.mp hcerr).1
    have ho := (abs_le.mp hell).2
    have hh := (abs_le.mp hH).2
    have he : ((ell:ℝ)+(H:ℝ))/N≤(c:ℝ)/N := by
      rw [add_div]
      dsimp [o] at ho
      linarith
    have hr := (div_le_div_iff_of_pos_right hn).mp he
    exact_mod_cast hr
  have hcap0 := cap_of_errors Q H0 ho0' h0err
  have hcap1 := cap_of_errors (A-M-Q) H1 ho1' h1err
  have hκB : 0≤(1-ξ)*B := mul_nonneg (by linarith [hξ.2]) hB
  have hnlo : 0≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg) := by
    have hh : 0≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar := by linarith
    simpa using (le_div_iff₀ hwbar).mp hh
  have hnhi : populationNumerator ξ ρ abar mbar hbar 1≤ wbar := by
    have hh : populationNumerator ξ ρ abar mbar hbar 1/wbar≤1 := by linarith
    simpa using (div_le_iff₀ hwbar).mp hh
  have hnbound (k : ℝ) (hklo : lowerShare reg≤ k) (hk1 : k≤1) :
      |populationNumerator ξ ρ abar mbar hbar k|≤ wbar := by
    have hlo' := populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ.1 hhbar hklo
    have hhi' := populationNumerator_mono (ρ:=ρ) (abar:=abar) (mbar:=mbar) hξ.1 hhbar hk1
    rw [abs_of_nonneg (hnlo.trans hlo')]
    exact hhi'.trans hnhi
  have hratio (ell H : ℕ) (hell : |(ell:ℝ)/N-o|≤ Z) (hH : |(H:ℝ)/N-hbar|≤ Z)
      (k : ℝ) (hk : k∈Icc (0:ℝ) 1) (hklo : lowerShare reg≤ k) :
      |lambda c ell M ξ ((N:ℝ)*W) (k*(H:ℝ))-
        populationNumerator ξ ρ abar mbar hbar k/wbar|≤ γ := by
    rw [lambda_normalized N c ell M H hN ξ W k hW.ne']
    have he := endpointNumerator_error N c ell M H ξ k ρ abar mbar hbar Z
      hξ hk hmerr hcerr hell hH
    have hr := Central.ratio_error (half_pos hwbar) hWlow hwbar
      (hnbound k hklo hk.2) he hwerr
    have hc : (4*Z+Z)/(wbar/2)≤ γ := by
      apply (div_le_iff₀ (half_pos hwbar)).mpr
      nlinarith [hzδ.le]
    exact hr.trans hc
  have low0 := hratio Q H0 ho0' h0err (lowerShare reg) (lowerShare_mem reg) le_rfl
  have low1 := hratio (A-M-Q) H1 ho1' h1err (lowerShare reg) (lowerShare_mem reg) le_rfl
  have high0 := hratio Q H0 ho0' h0err 1 (by norm_num) (lowerShare_mem reg).2
  have high1 := hratio (A-M-Q) H1 ho1' h1err 1 (by norm_num) (lowerShare_mem reg).2
  have mean0 := hratio Q H0 ho0' h0err share hshare hshareLo
  have mean1 := hratio (A-M-Q) H1 ho1' h1err share hshare hshareLo
  have hlo0 : (1-ξ)*B+γ≤ lambda c Q M ξ ((N:ℝ)*W) (lowerPrivateCount H0 reg) := by
    rw [lowerPrivateCount_real]
    linarith [(abs_le.mp low0).1]
  have hlo1 : (1-ξ)*B+γ≤ lambda c (A-M-Q) M ξ ((N:ℝ)*W) (lowerPrivateCount H1 reg) := by
    rw [lowerPrivateCount_real]
    linarith [(abs_le.mp low1).1]
  have hhi0 : lambda c Q M ξ ((N:ℝ)*W) H0+γ≤1 := by
    simpa only [one_mul] using (show lambda c Q M ξ ((N:ℝ)*W) (1*(H0:ℝ))+γ≤1 by
      linarith [(abs_le.mp high0).2])
  have hhi1 : lambda c (A-M-Q) M ξ ((N:ℝ)*W) H1+γ≤1 := by
    simpa only [one_mul] using (show lambda c (A-M-Q) M ξ ((N:ℝ)*W) (1*(H1:ℝ))+γ≤1 by
      linarith [(abs_le.mp high1).2])
  have hp : if reg then
      Rp+γ≤ lambda c Q M ξ ((N:ℝ)*W) (privateMean H0 reg ν0) ∧
        Rp+γ≤ lambda c (A-M-Q) M ξ ((N:ℝ)*W) (privateMean H1 reg ν1)
      else lambda c Q M ξ ((N:ℝ)*W) (privateMean H0 reg ν0)+γ≤ R ∧
        lambda c (A-M-Q) M ξ ((N:ℝ)*W) (privateMean H1 reg ν1)+γ≤ R := by
    rw [hmean0,hmean1]
    cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hmean ⊢
    · exact ⟨by linarith [(abs_le.mp mean0).2],by linarith [(abs_le.mp mean1).2]⟩
    · exact ⟨by linarith [(abs_le.mp mean0).1],by linarith [(abs_le.mp mean1).1]⟩
  exact scalar_weight_eq_one H0 H1 c Q (A-M-Q) M reg ν0 ν1 hξ.1 hfullW hcap0 hcap1
    hMpos hw hwγ hγ1 hlo0 hhi0 hlo1 hhi1 hp

theorem source_weight_eq_one_of_guardError (N A M H0 H1 : ℕ) (hN : 0< N) (hMA : M≤ A)
    (ξ share ρ B R Rp width γ δ W abar mbar hbar wbar : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1)
    (hB : 0≤ B) (hhbar : 0≤ hbar) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hδ : 0< δ) (hδm : δ≤ mbar/2) (hδw : δ≤ wbar/2)
    (hδc : 4*δ≤ ρ-(abar-mbar)/2-hbar) (hδγ : 10*δ≤ γ*wbar)
    (hmean0 : privateMean H0 reg ν0=share*H0)
    (hmean1 : privateMean H1 reg ν1=share*H1)
    (hlo : (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar)
    (hhi : populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1)
    (hmean : if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R)
    (hgood : guardError N A M H0 H1 W abar mbar hbar wbar< δ) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    TypicalGuardStatistics.weight H0 H1 (iidCapacity ρ N) Q (A-M-Q) M
      ξ B R Rp width reg ν0 ν1 ((N:ℝ)*W)=1 := by
  apply source_weight_eq_one_of_guardError_capacity N A M H0 H1 (iidCapacity ρ N) hN hMA
    ξ share ρ B R Rp width γ δ 0 W abar mbar hbar wbar reg ν0 ν1
    hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ hδm hδw hδc hδγ
    hmean0 hmean1 hlo hhi hmean (by norm_num)
  · simpa only [add_zero] using (iidCapacity_error hρ N hN).trans
      (guardError_bounds N A M H0 H1 W abar mbar hbar wbar).2.2.2.2.2.2
  · simpa only [add_zero] using hgood

def guardMeanProxy (H : ℕ) (share : ℝ) (hshare : share∈Icc (0:ℝ) 1) : FiniteLaw (Marks H) :=
  FiniteLaw.mixture (FiniteLaw.dirac (fun _ => true))
    (FiniteLaw.dirac (fun _ => false)) share hshare.1 hshare.2

theorem guardMeanProxy_mean (H : ℕ) (share : ℝ) (hshare : share∈Icc (0:ℝ) 1)
    (reg : Bool) (hshareLo : lowerShare reg≤ share) :
    privateMean H reg (guardMeanProxy H share hshare)=share*H := by
  cases reg
  · have he : share=1 := le_antisymm hshare.2 (by simpa [lowerShare] using hshareLo)
    simp [privateMean,he]
  · unfold privateMean guardMeanProxy
    rw [FiniteLaw.expect_mixture,FiniteLaw.expect_dirac,FiniteLaw.expect_dirac]
    simp [upperCount]

def scalarSourceWeight (N A M H0 H1 : ℕ) (ξ share ρ B R Rp width : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (W : ℝ) : ℝ :=
  let Q := clampedOwner (A-M) (share*H0) (share*H1)
  TypicalGuardStatistics.weight H0 H1 (iidCapacity ρ N) Q (A-M-Q) M
    ξ B R Rp width reg (guardMeanProxy H0 share hshare)
      (guardMeanProxy H1 share hshare) ((N:ℝ)*W)

theorem scalarSourceWeight_bounds (N A M H0 H1 : ℕ) (ξ share ρ B R Rp width : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (W : ℝ) :
    scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg W∈Icc (0:ℝ) 1 :=
  TypicalGuardStatistics.weight_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem actual_weight_eq_scalarSourceWeight (N A M H0 H1 : ℕ) (ξ share ρ B R Rp width : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) (W : ℝ)
    (hshareLo : lowerShare reg≤ share)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hmean0 : privateMean H0 reg ν0=share*H0)
    (hmean1 : privateMean H1 reg ν1=share*H1) :
    let Q := clampedOwner (A-M) (share*H0) (share*H1)
    TypicalGuardStatistics.weight H0 H1 (iidCapacity ρ N) Q (A-M-Q) M
      ξ B R Rp width reg ν0 ν1 ((N:ℝ)*W)=
        scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg W := by
  apply scalar_weight_congr_privateMeans
  · rw [hmean0,guardMeanProxy_mean H0 share hshare reg hshareLo]
  · rw [hmean1,guardMeanProxy_mean H1 share hshare reg hshareLo]

section Measurability
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_guard_listMinimum {α : Type*} (as : List α)
    (f : Ω→ α→ℝ) (hf : ∀ a,Measurable (fun x => f x a)) :
    Measurable (fun x => TypicalGuard.listMinimum as (f x)) := by
  induction as with
  | nil => exact measurable_const
  | cons a as ih => exact (hf a).min ih

theorem measurable_guard_finiteMinimum {α : Type*} [Fintype α]
    (f : Ω→ α→ℝ) (hf : ∀ a,Measurable (fun x => f x a)) :
    Measurable (fun x => TypicalGuard.finiteMinimum (f x)) :=
  measurable_guard_listMinimum _ f hf

omit [MeasurableSpace Ω] in
theorem measurable_scalarSourceWeight_fixed (N A M H0 H1 : ℕ) (ξ share ρ B R Rp width : ℝ)
    (hshare : share∈Icc (0:ℝ) 1) (reg : Bool) :
    Measurable (scalarSourceWeight N A M H0 H1 ξ share ρ B R Rp width hshare reg) := by
  let Q := clampedOwner (A-M) (share*H0) (share*H1)
  let c := iidCapacity ρ N
  have hmult (H ell : ℕ) (z : Marks H) : Measurable (fun W : ℝ =>
      TypicalGuardStatistics.multiplier H c ell M ξ reg ((N:ℝ)*W) z) :=
    measurable_const.div (measurable_const.mul measurable_id)
  have hreal (H ell : ℕ) : Measurable (fun W : ℝ =>
      TypicalGuardStatistics.realizationMargin H c ell M ξ B reg ((N:ℝ)*W)) := by
    apply measurable_guard_finiteMinimum
    intro z
    exact ((hmult H ell z).sub measurable_const).min (measurable_const.sub (hmult H ell z))
  have hmean (H ell : ℕ) : Measurable (fun W : ℝ =>
      TypicalGuardStatistics.meanMultiplier H c ell M ξ reg
        (guardMeanProxy H share hshare) ((N:ℝ)*W)) := by
    unfold TypicalGuardStatistics.meanMultiplier FiniteLaw.expect
    apply Finset.measurable_sum
    intro z _
    exact measurable_const.mul (hmult H ell z)
  have hpartial : Measurable (fun W : ℝ => TypicalGuardStatistics.partialMargin
      H0 H1 c Q (A-M-Q) M ξ R Rp reg (guardMeanProxy H0 share hshare)
        (guardMeanProxy H1 share hshare) ((N:ℝ)*W)) := by
    cases reg
    · exact (measurable_const.sub (hmean H0 Q)).min (measurable_const.sub (hmean H1 (A-M-Q)))
    · exact ((hmean H0 Q).sub measurable_const).min ((hmean H1 (A-M-Q)).sub measurable_const)
  have hmargin : Measurable (fun W : ℝ => TypicalGuardStatistics.margin
      H0 H1 c Q (A-M-Q) M ξ B R Rp reg (guardMeanProxy H0 share hshare)
        (guardMeanProxy H1 share hshare) ((N:ℝ)*W)) :=
    ((hreal H0 Q).min (hreal H1 (A-M-Q))).min hpartial
  change Measurable (fun W : ℝ => TypicalGuardStatistics.weight H0 H1 c Q (A-M-Q) M
    ξ B R Rp width reg (guardMeanProxy H0 share hshare) (guardMeanProxy H1 share hshare) ((N:ℝ)*W))
  by_cases hs : TypicalGuardStatistics.Structural H0 H1 c Q (A-M-Q) M
  · simpa only [TypicalGuardStatistics.weight,if_pos hs,Function.comp_def] using
      continuous_probabilityClip.measurable.comp (hmargin.div_const width)
  · simp only [TypicalGuardStatistics.weight,if_neg hs]
    exact measurable_const

theorem measurable_scalarSourceWeight (N : ℕ) (A M H0 H1 : Ω→ℕ)
    (hA : Measurable A) (hM : Measurable M) (hH0 : Measurable H0) (hH1 : Measurable H1)
    (ξ share ρ B R Rp width : ℝ) (hshare : share∈Icc (0:ℝ) 1) (reg : Bool)
    (W : Ω→ℝ) (hW : Measurable W) :
    Measurable (fun x => scalarSourceWeight N (A x) (M x) (H0 x) (H1 x)
      ξ share ρ B R Rp width hshare reg (W x)) := by
  have h : Measurable (fun z : ((ℕ×ℕ)×(ℕ×ℕ))×ℝ =>
      scalarSourceWeight N z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2
        ξ share ρ B R Rp width hshare reg z.2) :=
    measurable_from_prod_countable_right fun q =>
      measurable_scalarSourceWeight_fixed N q.1.1 q.1.2 q.2.1 q.2.2 ξ share ρ B R Rp width hshare reg
  exact h.comp (((hA.prodMk hM).prodMk (hH0.prodMk hH1)).prodMk hW)

end Measurability

end FCAppendix.Affine.Tail04.MenuError
