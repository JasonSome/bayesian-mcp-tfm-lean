import FCAppendix.Affine.Tail04.SourceMenuPopulation
import FCAppendix.Affine.Tail04.IidJoinedMenuError
import FCAppendix.Affine.Tail04.TwoFocalGuard
import FCAppendix.Affine.Tail04.OneFocalFlags
import FCAppendix.Affine.Tail04.PartialFocalGuard
import FCAppendix.Affine.Tail04.PartialUniformGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceMenuError
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation MenuError
open SourceMomentRectangle SourceMenuPopulation Hybrid
open EqualPrivateSignal NativeTypicalCount

def nativeBid (x : UserDraw 2) : ℝ := x.1.2.bid

theorem measurable_nativeBid : Measurable nativeBid :=
  (measurable_bid 2).comp measurable_fst.snd

def nativeFlag (P : ValueParameters) (ξ : ℝ) (reg : Bool) (x : UserDraw 2) : unitInterval :=
  sourceProbability (baseFlag P reg) (Central.B ξ) (nativeBid x)

theorem measurable_nativeFlag (P : ValueParameters) (ξ : ℝ) (reg : Bool) :
    Measurable (nativeFlag P ξ reg) :=
  (measurable_sourceProbability (baseFlag P reg) (Central.B ξ)).comp measurable_nativeBid

def mixedMoment {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
    (ξ : ℝ) (reg : Bool) : ℝ :=
  ∫ x,(nativeFlag P ξ reg x:ℝ)*indicator (categoryFlag E 1) x ∂userLaw Γ

def reciprocalMoment {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
    (ξ : ℝ) (reg : Bool) : ℝ :=
  ∫ x,(nativeFlag P ξ reg x:ℝ)*reciprocalWeight (categoryFlag E 1) nativeBid x ∂userLaw Γ

def meanNumerator (P : ValueParameters) (ξ M : ℝ) (reg : Bool) : ℝ :=
  if reg then (1-ξ/2)*M-ξ*(partialMass+P.theta^2)/2
  else (1-ξ/2)*M-ξ*(P.theta^2)/2

theorem population_mean_eq (P : ValueParameters) (ξ t M : ℝ) (ht : P.M≤ t) (reg : Bool) :
    populationNumerator ξ (99/200) (activeMass P.theta-upperMass P t) M
      ((partialMass+upperMass P t)/2) (keptShare P t reg)=meanNumerator P ξ M reg := by
  cases reg
  · exact population_full_private P ξ M (upperMass P t)
  · exact population_reject_mean P ξ M (upperMass P t) (upperMass_nonnegative P t ht)

section CountDefinition
variable {m c : ℕ} {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]
    (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions)
    (ξ t : ℝ) (ht : P.M≤ t) (ν : Measure Ω) [IsProbabilityMeasure ν]
    (N : ℕ) (row : Ω→ Fin N→ UserDraw 2×unitInterval)
    (hrow : MeasurePreserving row ν
      (Measure.pi (fun _ : Fin N => (userLaw Γ).prod (volume : Measure unitInterval))))
    (target : Ω→ Fin (N+1)) (htarget : Measurable target)

def nativeGuardedCount (width b : ℝ) (reg : Bool) (fallback : Ω→ CountLaw 2)
    (hfallback : ∀ k,Measurable (fun x => (fallback x).mass k)) : CountLaw 2 :=
  originalGuardedBalancedCount (userLaw Γ) ν N row hrow target htarget
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width b (keptShare_bounds P t ht reg).1 reg
    fallback hfallback

end CountDefinition

section Native
variable {m c : ℕ} {Seed Ω : Type*} [MeasurableSpace Seed] [MeasurableSpace Ω]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u : ℝ)
  (hu : 0≤ u) (huE : 1+u≤ E.U)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)

variable (hjoint : Γ.F⊗ₘΓ.σ=((originalJoint P t ht.le E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper) : Measure (ℝ×JointAction 2)))

variable (ξ : ℝ) (hξ : 0< ξ) (hξh : ξ<1/2)
    (huB : 1+u< Central.B ξ) (hEB : E.U≤ Central.B ξ)
    (hR : E.R=Central.R ξ) (hRp : E.Rp≤ Central.R ξ+ξ/1000)
    (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)

variable (ν : Measure Ω) [IsProbabilityMeasure ν] (N : ℕ) (hN : 0< N)
    (row : Ω→ Fin N→ UserDraw 2×unitInterval)
    (hrow : MeasurePreserving row ν
      (Measure.pi (fun _ : Fin N => (userLaw Γ).prod (volume : Measure unitInterval))))
    (target : Ω→ Fin (N+1)) (htarget : Measurable target)

include hd u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN in
theorem native_guarded_count_error (width b : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (hb : 1≤ b) (reg : Bool) (fallback : Ω→ CountLaw 2)
    (hfallback : ∀ k,Measurable (fun x => (fallback x).mass k)) (f : Fin 3→ℝ) :
    let M := mixedMoment Γ P E ξ reg
    let W := reciprocalMoment Γ P E ξ reg
    let n := meanNumerator P ξ M reg
    let δg := radius ξ (centerMoment P reg)
    |(nativeGuardedCount Γ P E ξ t ht.le ν N row hrow target htarget
      width b reg fallback hfallback).expect f-(clippedCount ξ b n n W).expect f|≤
      MenuError.oscillation f*((4/(ξ*b*W))*(numeratorBudget ξ (keptShare P t reg) N+
        1/Real.sqrt N+1/(N:ℝ))+(4/W)*(1/Real.sqrt N+1/(N:ℝ))+
        2*((5/Real.sqrt N+4/(N:ℝ))/δg)) := by
  dsimp only
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  have hf : (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)=
      (∫ x,indicator (categoryFlag E 3) x ∂userLaw Γ) := hp.1.trans hp.2.symm
  have ha := SourceNativeMoments.native_active_mean Γ P E hd t ht u huE πL πP πB πT
    upperBid hupper hfloor hjoint
  have hn : populationNumerator ξ (99/200)
      (∫ x,indicator (categoryFlag E 1) x ∂userLaw Γ) (mixedMoment Γ P E ξ reg)
      (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ) (keptShare P t reg)=
      meanNumerator P ξ (mixedMoment Γ P E ξ reg) reg := by
    rw [ha,hp.1]
    exact population_mean_eq P ξ t (mixedMoment Γ P E ξ reg) ht.le reg
  have h := original_guarded_count_error (userLaw Γ) ν N hN row hrow target htarget
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) b reg hξ (by linarith) hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos hb hf
    fallback hfallback f hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean
  change |(nativeGuardedCount Γ P E ξ t ht.le ν N row hrow target htarget
      width b reg fallback hfallback).expect f-
      (clippedCount ξ b
        (populationNumerator ξ (99/200) (∫ x,indicator (categoryFlag E 1) x ∂userLaw Γ)
          (mixedMoment Γ P E ξ reg) (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)
          (keptShare P t reg))
        (populationNumerator ξ (99/200) (∫ x,indicator (categoryFlag E 1) x ∂userLaw Γ)
          (mixedMoment Γ P E ξ reg) (∫ x,indicator (categoryFlag E 2) x ∂userLaw Γ)
          (keptShare P t reg)) (reciprocalMoment Γ P E ξ reg)).expect f|≤_ at h
  rw [hn] at h
  exact h

include Γ hd u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow htarget in
theorem native_guard_defect (width b : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (hb : 1≤ b) (reg : Bool) :
    (∫ x,1-originalGuardWeight N row target (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (nativeFlag P ξ reg) nativeBid ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width b
      (keptShare_bounds P t ht.le reg).1 reg x ∂ν)≤
        (5/Real.sqrt N+4/(N:ℝ))/radius ξ (centerMoment P reg) := by
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  exact original_guard_defect_L1 (userLaw Γ) ν N hN row hrow target htarget
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) b reg ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos hb
    (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean

include Γ hd u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow htarget in
theorem native_flagged_guard_defect (width b : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (hb : 1≤ b) (reg focal : Bool) :
    (∫ x,1-flaggedGuardWeight N row target (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (nativeFlag P ξ reg) nativeBid ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width b
      (keptShare_bounds P t ht.le reg).1 reg focal x ∂ν)≤
        (5/Real.sqrt N+4/(N:ℝ))/radius ξ (centerMoment P reg) := by
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  exact original_flagged_guard_defect_L1 (userLaw Γ) ν N hN row hrow target htarget
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) b reg focal ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos hb
    (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean

include Γ hd u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow htarget in
theorem native_partial_guard_failure (width : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (reg : Bool) (side : Fin 2) :
    ν.real {x | partialGuardWeight N row target (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (nativeFlag P ξ reg) nativeBid ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width
      (keptShare_bounds P t ht.le reg).1 reg side x≠1}≤
        (5/Real.sqrt N+4/(N:ℝ))/radius ξ (centerMoment P reg) := by
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  exact original_partial_guard_failure (userLaw Γ) ν N hN row hrow target htarget
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) reg ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos
    (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean side

include hd u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow in
theorem native_partial_common_guard (width : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (reg : Bool) (hroom : 8/(N:ℝ)≤ radius ξ (centerMoment P reg)) :
    let bad := sourceFiveBad (userLaw Γ) N row (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (nativeFlag P ξ reg) nativeBid (radius ξ (centerMoment P reg))
    MeasurableSet bad ∧ ν.real bad≤10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P reg))^2/50) ∧
      ∀ x,x∉bad → ∀ target' : Ω→ Fin (N+1),∀ side : Fin 2,
      partialGuardWeight N row target' (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
        (nativeFlag P ξ reg) nativeBid ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width
        (keptShare_bounds P t ht.le reg).1 reg side x=1 := by
  dsimp only
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  refine ⟨measurableSet_sourceFiveBad (userLaw Γ) ν N row hrow
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid _,
    sourceFiveBad_probability (userLaw Γ) ν N hN row hrow
      (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
      (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
      (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid hg.radius_pos.le,?_⟩
  exact partial_weight_eq_one_on_common_good (userLaw Γ) N hN row
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) reg ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos hroom
    (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean

include Γ hd ht u hu huE πL πP πB πT upperBid hupper hfloor hjoint hξ hξh huB hEB hR hRp hsmall hmSmall hN hrow in
theorem native_two_focal_guard (width : ℝ) (hw : 0< width) (hwγ : width≤ γ ξ)
    (reg : Bool) (hroom : 16/(N:ℝ)≤ radius ξ (centerMoment P reg)) :
    ∃ bad : Set Ω,MeasurableSet bad ∧
      ν.real bad≤10*Real.exp (-(N:ℝ)*(radius ξ (centerMoment P reg))^2/50) ∧
      ∀ x,x∉bad → ∀ b0 b1 : ℝ,1≤ b0 → 1≤ b1 → ∀ f0 f1 : Bool,∀ target2 : Ω→ Fin (N+2),
      ∀ ν0 : FiniteLaw (Marks (privateCount N row (categoryFlag E 2) x)),
      ∀ ν1 : FiniteLaw (Marks (privateCount N row (categoryFlag E 3) x)),
      privateMean (privateCount N row (categoryFlag E 2) x) reg ν0=
        keptShare P t reg*privateCount N row (categoryFlag E 2) x →
      privateMean (privateCount N row (categoryFlag E 3) x) reg ν1=
        keptShare P t reg*privateCount N row (categoryFlag E 3) x →
      let A := twoActiveCount N row (categoryFlag E 1) x
      let M := twoMixedCount N row (categoryFlag E 1) (nativeFlag P ξ reg) f0 f1 target2 x
      let H0 := privateCount N row (categoryFlag E 2) x
      let H1 := privateCount N row (categoryFlag E 3) x
      let Q := clampedOwner (A-M) (keptShare P t reg*H0) (keptShare P t reg*H1)
      TypicalGuardStatistics.weight H0 H1 (twoCapacity (99/200) N) Q (A-M-Q) M
        ξ E.U E.R E.Rp width reg ν0 ν1
          ((N:ℝ)*twoReciprocal N row (categoryFlag E 1) (nativeFlag P ξ reg)
            nativeBid b0 b1 f0 f1 target2 x)=1 := by
  have hg := native_guard_interior Γ P E hd t ht u hu huE πL πP πB πT upperBid hupper hfloor
    hjoint ξ hξ hξh huB hEB hR hRp hsmall hmSmall reg
  have hp := native_private_means Γ P E hd t ht u huE πL πP πB πT upperBid hupper hfloor hjoint
  exact two_fixed_common_policy_guard (userLaw Γ) ν N hN row hrow
    (categoryFlag E 1) (categoryFlag E 2) (categoryFlag E 3)
    (measurable_categoryFlag E 1) (measurable_categoryFlag E 2) (measurable_categoryFlag E 3)
    (nativeFlag P ξ reg) (measurable_nativeFlag P ξ reg) nativeBid measurable_nativeBid
    ξ (keptShare P t reg) (99/200) E.U E.R E.Rp width (γ ξ)
    (radius ξ (centerMoment P reg)) reg ⟨hξ.le,by linarith⟩ hg.share_mem hg.share_lower
    (by norm_num) (by linarith : 0≤ E.U) hw hwγ (by unfold γ;linarith) hg.radius_pos hroom
    (hp.1.trans hp.2.symm) hg.radius_mixed hg.radius_reciprocal hg.radius_capacity hg.radius_margin
    hg.lower_endpoint hg.upper_endpoint hg.private_mean

end Native
end FCAppendix.Affine.Tail04.SourceMenuError
