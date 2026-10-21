import FCAppendix.Affine.Tail04.SourceMenuError
import FCAppendix.Affine.Tail04.GuardReciprocalRobustness
import FCAppendix.Affine.Tail04.TwoFocalCompression
import FCAppendix.Affine.Tail04.OriginalPrivateSource

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomTwoFocalGuardGeneric
open MeasureTheory ProbabilityTheory Set Classical
open MenuError EqualPrivateSignal NativeTypicalCount TypicalGuardEndpoints

theorem guardError_ordered (N A M H0 H1 : ℕ) (W abar mbar hbar wbar : ℝ) :
    guardError N A M (min H0 H1) (max H0 H1) W abar mbar hbar wbar=
      guardError N A M H0 H1 W abar mbar hbar wbar := by
  by_cases h : H0≤H1
  · simp only [min_eq_left h,max_eq_right h]
  · have h' : H1≤H0 := le_of_not_ge h
    simp only [min_eq_right h',max_eq_left h']
    unfold guardError
    ring

section Perturbed
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  (μ : Measure X) [IsProbabilityMeasure μ]
  (N : ℕ) (hN : 0< N) (row : Ω→ Fin N→ X×unitInterval)
  (active private0 private1 : X→ Bool)
  (hactive : Measurable active) (hprivate0 : Measurable private0)
  (hprivate1 : Measurable private1) (p : X→ unitInterval) (hp : Measurable p)
  (bid : X→ℝ) (hbid : Measurable bid)

omit [MeasurableSpace Ω] in
include hN hactive hprivate0 hprivate1 hp hbid in
theorem two_fixed_weight_eq_one_after_perturb
    (ξ share ρ B R Rp width γ δ : ℝ) (reg : Bool)
    (hξ : ξ∈Icc (0:ℝ) 1) (hshare : share∈Icc (0:ℝ) 1)
    (hshareLo : lowerShare reg≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (hB : 0≤ B)
    (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1) (hδ : 0< δ)
    (hroom : 32/(N:ℝ)≤ δ)
    (hfair : (∫ x,indicator private0 x ∂μ)=(∫ x,indicator private1 x ∂μ)) :
    let abar := ∫ y,indicator active y ∂μ
    let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
    let hbar := ∫ y,indicator private0 y ∂μ
    let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
    δ≤ mbar/2 → δ≤ wbar/2 → 4*δ≤ ρ-(abar-mbar)/2-hbar → 10*δ≤ γ*wbar →
    (1-ξ)*B+2*γ≤ populationNumerator ξ ρ abar mbar hbar (lowerShare reg)/wbar →
    populationNumerator ξ ρ abar mbar hbar 1/wbar+2*γ≤1 →
    (if reg then Rp+2*γ≤ populationNumerator ξ ρ abar mbar hbar share/wbar
      else populationNumerator ξ ρ abar mbar hbar share/wbar+2*γ≤ R) →
    ∀ x,x∉sourceFiveBad μ N row active private0 private1 p bid (δ/2) →
      ∀ bid' : X→ℝ,
      (∀ j,active (row x j).1=true → 1≤ bid (row x j).1 ∧ 1≤ bid' (row x j).1) →
      (∀ j,active (row x j).1=true → |bid (row x j).1-bid' (row x j).1|≤ δ/2) →
      ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target : Ω→ Fin (N+2),
      ∀ ν0 : FiniteLaw (Marks ((min (privateCount N row private0 x) (privateCount N row private1 x)))),
      ∀ ν1 : FiniteLaw (Marks ((max (privateCount N row private0 x) (privateCount N row private1 x)))),
      privateMean ((min (privateCount N row private0 x) (privateCount N row private1 x))) reg ν0=share*(min (privateCount N row private0 x) (privateCount N row private1 x)) →
      privateMean ((max (privateCount N row private0 x) (privateCount N row private1 x))) reg ν1=share*(max (privateCount N row private0 x) (privateCount N row private1 x)) →
      let A := twoActiveCount N row active x
      let M := twoMixedCount N row active p f0 f1 target x
      let H0 := (min (privateCount N row private0 x) (privateCount N row private1 x))
      let H1 := (max (privateCount N row private0 x) (privateCount N row private1 x))
      let Q := clampedOwner (A-M) (share*H0) (share*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity ρ N) Q (A-M-Q) M
        ξ B R Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N row active p bid' b0 b1 f0 f1 target x)=1 := by
  dsimp only
  intro hδm hδw hδc hδγ hlo hhi hmean x hx bid' hbox hnear
    b0 b1 hb0 hb1 f0 f1 target ν0 ν1 hmean0 hmean1
  let A := twoActiveCount N row active x
  let M := twoMixedCount N row active p f0 f1 target x
  let H0 := (min (privateCount N row private0 x) (privateCount N row private1 x))
  let H1 := (max (privateCount N row private0 x) (privateCount N row private1 x))
  let W := twoReciprocal N row active p bid' b0 b1 f0 f1 target x
  let abar := ∫ y,indicator active y ∂μ
  let mbar := ∫ y,(p y:ℝ)*indicator active y ∂μ
  let hbar := ∫ y,indicator private0 y ∂μ
  let wbar := ∫ y,(p y:ℝ)*reciprocalWeight active bid y ∂μ
  have hg0 := twoGuardError_lt_of_not_bad μ N hN row active private0 private1
    hactive hprivate0 hprivate1 p hp bid hbid (δ:=δ/2) (by
      calc
        16/(N:ℝ)=(32/(N:ℝ))/2 := by ring
        _≤δ/2 := div_le_div_of_nonneg_right hroom (by norm_num))
    b0 b1 hb0 hb1 f0 f1 target hfair x hx
  have hg := twoGuardError_lt_after_perturb N hN row active private0 private1 p bid bid'
    b0 b1 f0 f1 target abar mbar hbar wbar δ (δ/2) (by linarith) le_rfl
    x hg0 hbox hnear
  have hhbar : 0≤ hbar := integral_nonneg (fun y => (indicator_bounds private0 y).1)
  apply source_weight_eq_one_of_guardError_capacity N A M H0 H1 (twoCapacity ρ N) hN
    (twoMixedCount_le_active N row active p f0 f1 target x)
    ξ share ρ B R Rp width γ δ (1/(N:ℝ)) W abar mbar hbar wbar reg ν0 ν1
    hξ hshare hshareLo hρ hB hhbar hw hwγ hγ1 hδ hδm hδw hδc hδγ
    hmean0 hmean1 hlo hhi hmean (by positivity)
  · have hc := twoCapacity_error hρ N hN
    have hz := (guardError_bounds N A M H0 H1 W abar mbar hbar wbar).2.2.2.2.2.2
    calc
      _≤2/(N:ℝ) := hc
      _=1/(N:ℝ)+1/(N:ℝ) := by ring
      _≤guardError N A M H0 H1 W abar mbar hbar wbar+1/(N:ℝ) :=
        add_le_add hz le_rfl
  · simpa only [A,M,H0,H1,W,twoGuardError,guardError_ordered] using hg

end Perturbed
end FCAppendix.Affine.Tail04.OrderedAtomTwoFocalGuardGeneric

namespace FCAppendix.Affine.Tail04.OrderedAtomTwoFocalGuard
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation OriginalPrivateSource
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open EqualPrivateSignal NativeTypicalCount OriginalFlagCompression TwoFocalCompression
open OrderedAtomTwoFocalGuardGeneric

section Source
variable {m c : ℕ} {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u : ℝ) (hu : 0≤ u) (huE : 1+u≤ E.U)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)

local notation "πA" => ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT
variable (hjoint : Γ.F⊗ₘΓ.σ=(originalJoint P t ht.le E.R E.Rp E.U
  (E.d_nonneg.trans E.d_lt_R.le) πL πP
  (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper : Measure _))
  (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
  (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
  (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (ν : Measure Ω) [IsProbabilityMeasure ν] (N : ℕ) (hN : 0< N)
  (row : Ω→ Fin N→ UserDraw 2×unitInterval)
  (hrow : MeasurePreserving row ν
    (Measure.pi (fun _ : Fin N => (userLaw Γ).prod (volume : Measure unitInterval))))

def originalMarks (H : ℕ) : FiniteLaw (Marks H) :=
  AtypicalOriginalPosterior.markLaw
    (originalPrivateRow E P hd t ht.le πL πP πA upperBid hupper hfloor H :
      Measure (EqualPrivateUpper.Row H E.R E.Rp E.H))

lemma originalMarks_mean (reg : Bool) (H : ℕ) :
    privateMean H reg (originalMarks P E hd t ht u huE πL πP πB πT upperBid hupper hfloor H)=
      keptShare P t reg*H := by
  have hc := originalPrivateRow_countMean E P hd t ht.le πL πP πA upperBid hupper hfloor H
  have hm := privateMean_regime_of_countMean H reg
    (originalMarks P E hd t ht u huE πL πP πB πT upperBid hupper hfloor H)
    (upperMass P t/(partialMass+upperMass P t)) hc
  rw [hm]
  cases reg
  all_goals simp only [keptShare,Bool.false_eq_true,if_false,if_true,one_mul]
  all_goals ring

include hu hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow in
theorem native_robust_guard (width : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (reg : Bool) (hroom : 32/(N:ℝ)≤ radius ξ (centerMoment P reg)) :
    let δ := radius ξ (centerMoment P reg)
    let bad := sourceFiveBad (userLaw Γ) N row (categoryFlag E 1)
      (categoryFlag E 2) (categoryFlag E 3) (nativeFlag P ξ reg) nativeBid (δ/2)
    MeasurableSet bad ∧ ν.real bad≤10*Real.exp (-(N:ℝ)*δ^2/200) ∧
      ∀ x,x∉bad → ∀ bid' : UserDraw 2→ℝ,
      (∀ j,categoryFlag E 1 (row x j).1=true →
        1≤ nativeBid (row x j).1 ∧ 1≤ bid' (row x j).1) →
      (∀ j,categoryFlag E 1 (row x j).1=true →
        |nativeBid (row x j).1-bid' (row x j).1|≤ δ/2) →
      ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target : Ω→ Fin (N+2),
      let A := twoActiveCount N row (categoryFlag E 1) x
      let M := twoMixedCount N row (categoryFlag E 1) (nativeFlag P ξ reg) f0 f1 target x
      let H0 := (min (privateCount N row (categoryFlag E 2) x) (privateCount N row (categoryFlag E 3) x))
      let H1 := (max (privateCount N row (categoryFlag E 2) x) (privateCount N row (categoryFlag E 3) x))
      let Q := clampedOwner (A-M) (keptShare P t reg*H0) (keptShare P t reg*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity (99/200) N) Q (A-M-Q) M
        ξ E.U E.R E.Rp width reg
        (originalMarks P E hd t ht u huE πL πP πB πT upperBid hupper hfloor H0)
        (originalMarks P E hd t ht u huE πL πP πB πT upperBid hupper hfloor H1)
        ((N:ℝ)*twoReciprocal N row (categoryFlag E 1) (nativeFlag P ξ reg)
          bid' b0 b1 f0 f1 target x)=1 := by
  dsimp only
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  refine ⟨measurableSet_sourceFiveBad (userLaw Γ) ν N row hrow
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid _,?_,?_⟩
  · have hh := sourceFiveBad_probability (userLaw Γ) ν N hN row hrow
      (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
      (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
      (show 0≤ radius ξ (centerMoment P reg)/2 by linarith [hg.radius_pos])
    convert! hh using 1
    congr 2
    ring
  · intro x hx bid' hbox hnear b0 b1 hb0 hb1 f0 f1 target
    exact two_fixed_weight_eq_one_after_perturb (userLaw Γ) N hN row
      (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
      (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
      ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
      (radius ξ (centerMoment P reg)) reg ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
      (by norm_num) (zero_le_one.trans E.one_le_U) hw hwγ (by unfold γ;linarith) hg.radius_pos hroom
      (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
      hg.lower_endpoint hg.upper_endpoint hg.private_mean x hx bid' hbox hnear
      b0 b1 hb0 hb1 f0 f1 target _ _
      (originalMarks_mean P E hd t ht u huE πL πP πB πT upperBid hupper hfloor reg _)
      (originalMarks_mean P E hd t ht u huE πL πP πB πT upperBid hupper hfloor reg _)

end Source
end FCAppendix.Affine.Tail04.OrderedAtomTwoFocalGuard
