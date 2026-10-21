import FCAppendix.Affine.Tail04.OrderedAtomSourceCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomRestoredGuard
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open NativeNoisySource OrderedAtomActiveCompression OriginalActiveCrossingCarrier
open OrderedAtomTwoPrefix OrderedAtomCountExceptions OrderedAtomRestoredBeta OrderedAtomFiniteGain
open OrderedAtomTwoFocalExpectation OrderedAtomTwoFocalGuard SourceMenuError SourceMenuPopulation
open SourceMomentRectangle MenuError OriginalFlagCompression OrderedAtomSourceCoordinates
open ActualActiveFiniteGain ActualFallbackPromotion ActiveGainUniformModulus CompactPromotionErrors
open EqualPrivateSignal

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v → H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hBH
local notation "decode" => NoisyNativeFiberProduct.commonProjection D P hdR H hBH
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+2) hrare
local notation "μr" => Measure.pi (fun _ : Fin N => userLaw Γ)
variable (hcap : D.c=twoCapacity (99/200) N) (hN : 0< N)
  (hξh : D.ξ<1/2) (hF : D.F=Central.B D.ξ) (hR : D.R=Central.R D.ξ)
  (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
  (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)
  (hroom : ∀ reg,32/(N:ℝ)≤ radius D.ξ (centerMoment P reg))

lemma source_joint : (Γ).F⊗ₘ(Γ).σ=
    (OriginalPopulation.originalJoint P t ht.le (E).R (E).Rp (E).U
      ((E).d_nonneg.trans (E).d_lt_R.le) πL (partialPhysical D P t ht π)
      (activePhysical D P t ht π) upperBid hupperBid : Measure _) :=
  game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+2) hrare

include hcap in
lemma restored_cut_eq (reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (hw : (E).coarseTag w=1) (r : Fin N→ UserDraw 2) :
    effectivePhi (lowPresent E r)
      (actualPhi P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D) πL
        (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
        upperBid hupperBid hfloor D.ξ N D.width reg r
        ((Ds).count (tags (E).coarseTag (restore j w r)) 1+1))=
      effectivePhi (decide (0< (Ds).count (tags (E).coarseTag (restore j w r)) 0))
        (TypicalGuardStatistics.phi ((Ds).count (tags (E).coarseTag (restore j w r)) 1+1)
          (min ((Ds).count (tags (E).coarseTag (restore j w r)) 2) ((Ds).count (tags (E).coarseTag (restore j w r)) 3))
          (max ((Ds).count (tags (E).coarseTag (restore j w r)) 2) ((Ds).count (tags (E).coarseTag (restore j w r)) 3))
          D.c D.ξ D.B D.R D.V D.width reg ((Ds).marksLaw _) ((Ds).marksLaw _)) := by
  rw [OrderedAtomOriginalMarks.actualPhi_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor]
  rw [private_count_unchanged Ds (E).coarseTag j w hw r 0 (by decide),
    private_count_unchanged Ds (E).coarseTag j w hw r 2 (by decide),
    private_count_unchanged Ds (E).coarseTag j w hw r 3 (by decide),
    count_lowPresent Ds E r,count_privateSize Ds E r 2,count_privateSize Ds E r 3,hcap]

private def term (frozen : Bool) (reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (b y : Icc (1:ℝ) D.B) (r : Fin N→ UserDraw 2) : ℝ :=
  let k := tags (E).coarseTag (restore j w r)
  let old := fun l => (focalRow Ds k decode b (restore j w r) l:ℝ)
  let cut := effectivePhi (decide (0< (Ds).count k 0))
    (TypicalGuardStatistics.phi ((Ds).count k 1+1) (min ((Ds).count k 2) ((Ds).count k 3)) (max ((Ds).count k 2) ((Ds).count k 3))
      D.c D.ξ D.B D.R D.V D.width reg ((Ds).marksLaw _) ((Ds).marksLaw _))
  badWeightProbability cut (D.e0 reg) D.F
    (if frozen then freezeFocal old 0 y else Function.update old 0 (y:ℝ))

private lemma term_integrable (frozen reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (b y : Icc (1:ℝ) D.B) : Integrable (term D P t ht hdR H hBH N frozen reg j w b y) μr := by
  have hr : Measurable (fun row : Fin N→ UserDraw 2 => restore j w row) :=
    (measurable_restore j).comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (term D P t ht hdR H hBH N frozen reg j w b y) := by
    apply LocalCoordinates.measurable_finite_eval
      (fun row : Fin N→UserDraw 2 => tags (E).coarseTag (restore j w row))
      (fun row kind => badWeightProbability
        (effectivePhi (decide (0<(Ds).count kind 0))
          (TypicalGuardStatistics.phi ((Ds).count kind 1+1)
            (min ((Ds).count kind 2) ((Ds).count kind 3))
            (max ((Ds).count kind 2) ((Ds).count kind 3)) D.c D.ξ D.B D.R D.V D.width reg
            ((Ds).marksLaw _) ((Ds).marksLaw _))) (D.e0 reg) D.F
        (if frozen then freezeFocal
          (fun l => (focalRow Ds kind decode b (restore j w row) l:ℝ)) 0 y
        else Function.update (fun l => (focalRow Ds kind decode b (restore j w row) l:ℝ)) 0 (y:ℝ)))
      ((measurable_tags (E).coarseTag (E).measurable_coarseTag).comp hr)
    intro kind
    have hb : Measurable (fun row : Fin N→ UserDraw 2 =>
        fun k => (focalRow Ds kind decode b (restore j w row) k:ℝ)) :=
      measurable_pi_lambda _ fun k => measurable_subtype_coe.comp
        ((measurable_pi_apply k).comp
          ((measurable_focalRow Ds kind decode
            (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH)).comp
            (measurable_const.prodMk hr)))
    have hc := IntegratedActiveFiniteGain.measurable_weightFailure (A:=(Ds).count kind 1+1)
      (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) D.c D.ξ D.B D.R D.V D.width
      (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0)) ((Ds).marksLaw _) ((Ds).marksLaw _)
    cases frozen
    · exact hc.comp (Resample.measurable_update_pair 0 |>.comp (measurable_const.prodMk hb))
    · exact hc.comp (IntegratedActiveFiniteGain.measurable_freeze _ hb 0 _ measurable_const)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun r => by
    rw [Real.norm_eq_abs]
    change |FiniteLaw.prob _ _|≤1
    rw [abs_of_nonneg (FiniteLaw.prob_nonneg _ _)]
    exact FiniteLaw.prob_le_one _ _

include hcap hN hξh hF hR hflags huB hRp hsmall hmSmall hwγ hroom in
theorem native_restored_beta_bound (reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (hw : (E).coarseTag w=1) (b y : Icc (1:ℝ) D.B) (hby : (b:ℝ)≤ y)
    (hnear : (y:ℝ)-b≤ radius D.ξ (centerMoment P reg)/2)
    (εflag rflag C : ℝ) (hBC : D.B≤ C) (hrflag : 0< rflag)
    (hsmallFlag : (y:ℝ)-b< rflag)
    (hmod : ∀ kind : Fin (N+1)→ Fin 4,∀ b' d' : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) C,
      (∀ k,|(b' k:ℝ)-(d' k:ℝ)|< rflag) →
        flagVariation (D.e0 reg) D.F (fun k => (b' k:ℝ)) (fun k => (d' k:ℝ))< εflag) :
    (∫ r,nativeRestoredBeta D P t ht hdR H hBH N reg j w b y r ∂μr)≤
      2*(10*Real.exp (-(N:ℝ)*(radius D.ξ (centerMoment P reg))^2/200)+
        Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2))+εflag := by
  let A := fun r : Fin N→ UserDraw 2 => (Ds).count (tags (E).coarseTag (restore j w r)) 1+1
  let e := fun r : Fin N→ UserDraw 2 => activeEnumeration D (E).coarseTag j w hw r
  let fbid : UserDraw 2→ℝ := fun x => freezeScalar b y (nativeBid x)
  let bw : ℝ := freezeScalar b y (decode w)
  have hbw : bw∈Icc (1:ℝ) D.B := freezeScalar_bounds b.2 (decode w).2
  have hE : (E).U≤ Central.B D.ξ := D.hUF.trans_eq hF
  have hm := source_row_menu Γ P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D)
    πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor
    (source_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare) N
  have hf := changed_flag_loss Γ P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_nonneg D) (bulkPhysicalWidth_le D) πL
    (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor
    (source_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    D.ξ D.hξ hξh huB hE hR hRp hsmall hmSmall N hN D.width D.hw hwγ reg (hroom reg)
    A e fbid
    (fun x hx ha => (freezeScalar_bounds b.2 (PartialSortedCompression.menu_active_box E x hx ha)).1)
    (fun x _ _ => by
      rw [abs_sub_comm]
      exact (freezeScalar_close (x:=nativeBid x) hby).trans hnear)
    b bw b.2.1 hbw.1 εflag (by
      filter_upwards [hm] with r hr
      let old := compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E r) (e r)
        (prefixBid r nativeBid b bw)
      let new := compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E r) (e r)
        (prefixBid r fbid b bw)
      have hold (k) : old k∈Icc (1:ℝ) D.B :=
        compressed_prefix_mem D P hdR H hBH r (e r) nativeBid
          (fun l hl => PartialSortedCompression.menu_active_box E (r l) (hr l)
            (by simpa [categoryFlag] using hl)) b.2 hbw k
      have hnew (k) : new k∈Icc (1:ℝ) D.B :=
        compressed_prefix_mem D P hdR H hBH r (e r) fbid
          (fun l hl => freezeScalar_bounds b.2
            (PartialSortedCompression.menu_active_box E (r l) (hr l)
              (by simpa [categoryFlag] using hl))) b.2 hbw k
      let bc : Fin (A r)→ Icc (1:ℝ) C := fun k => ⟨new k,(hnew k).1,(hnew k).2.trans hBC⟩
      let dc : Fin (A r)→ Icc (1:ℝ) C := fun k => ⟨old k,(hold k).1,(hold k).2.trans hBC⟩
      have hc : ∀ k,|(bc k:ℝ)-(dc k:ℝ)|< rflag := by
        intro k
        let i := (e r k).val
        change |prefixBid r fbid b bw i-prefixBid r nativeBid b bw i|< rflag
        refine Fin.cases ?_ (fun l => ?_) i
        · simpa only [prefixBid,TwoFocalCompression.fullBid,Fin.cases_zero,sub_self,abs_zero] using hrflag
        · refine Fin.cases ?_ (fun l => ?_) l
          · simpa only [prefixBid,TwoFocalCompression.fullBid,Fin.cases_zero,Fin.cases_succ,sub_self,abs_zero] using hrflag
          · exact (freezeScalar_close (x:=nativeBid (r l)) hby).trans_lt hsmallFlag
      have hv := hmod (tags (E).coarseTag (restore j w r)) bc dc hc
      rw [hflags reg,hF] at hv
      exact hv.le)
  have hu := actual_two_focal_loss Γ P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_nonneg D) (bulkPhysicalWidth_le D) πL
    (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor
    (source_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare)
    D.ξ D.hξ hξh huB hE hR hRp hsmall hmSmall N hN D.width D.hw hwγ reg (hroom reg)
    A e y (decode w) y.2.1 (decode w).2.1
  have hff : (∫ r,term D P t ht hdR H hBH N true reg j w b y r ∂μr)=
      ∫ r,badWeightProbability
        (effectivePhi (lowPresent E r)
          (actualPhi P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D) πL
            (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
            upperBid hupperBid hfloor D.ξ N D.width reg r (A r)))
        (baseFlag P reg) (Central.B D.ξ)
        (compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E r) (e r) (prefixBid r fbid b bw)) ∂μr := by
    apply integral_congr_ae
    filter_upwards [hm] with r hr
    rw [restored_cut_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hcap reg j w hw r]
    have he := compressed_freeze D P hdR H hBH j w hw r hr b y
    rw [freezeScalar_self hby] at he
    simp only [term,hflags reg,hF,ite_true]
    congr 1
    simpa only [e,fbid,bw] using! he.symm
  have huu : (∫ r,term D P t ht hdR H hBH N false reg j w b y r ∂μr)=
      ∫ r,badWeightProbability
        (effectivePhi (lowPresent E r)
          (actualPhi P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D) πL
            (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
            upperBid hupperBid hfloor D.ξ N D.width reg r (A r)))
        (baseFlag P reg) (Central.B D.ξ)
        (compressedBids (OrderedAtomTwoFocalExpectation.prefixActive E r) (e r)
          (prefixBid r nativeBid y (decode w))) ∂μr := by
    apply integral_congr_ae
    filter_upwards [hm] with r hr
    rw [restored_cut_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hcap reg j w hw r]
    simp only [term,hflags reg,hF,Bool.false_eq_true,ite_false]
    congr 1
    simpa only [e] using! (compressed_raised D P hdR H hBH j w hw r hr b y).symm
  have hf' := hff.le.trans hf
  have hu' := huu.le.trans hu
  have heq : nativeRestoredBeta D P t ht hdR H hBH N reg j w b y=
      (term D P t ht hdR H hBH N true reg j w b y)+
      (term D P t ht hdR H hBH N false reg j w b y) := rfl
  have hadd := integral_add
    (term_integrable D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare true reg j w b y)
    (term_integrable D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare false reg j w b y)
  have hsum : (∫ r,nativeRestoredBeta D P t ht hdR H hBH N reg j w b y r ∂μr)=
      (∫ r,term D P t ht hdR H hBH N true reg j w b y r ∂μr)+
      (∫ r,term D P t ht hdR H hBH N false reg j w b y r ∂μr) := by
    simpa only [heq,Pi.add_apply] using! hadd
  calc
    _ = _ := hsum
    _ ≤ _ := by linarith only [hf',hu']

include hcap hN hξh hF hR hflags huB hRp hsmall hmSmall hwγ hroom in
theorem exists_native_restored_radius (εflag C : ℝ) (hε : 0< εflag) (hBC : D.B≤ C) :
    ∃ r : ℝ,0< r ∧ ∀ reg : Bool,∀ j : Fin (N+1),∀ w : UserDraw 2,
      (E).coarseTag w=1 → ∀ b y : Icc (1:ℝ) D.B,(b:ℝ)≤ y → (y:ℝ)-b< r →
        (∫ row,nativeRestoredBeta D P t ht hdR H hBH N reg j w b y row ∂μr)≤
          2*(10*Real.exp (-(N:ℝ)*(radius D.ξ (centerMoment P reg))^2/200)+
            Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2))+εflag := by
  obtain ⟨rflag,hrflag,hmod⟩ := OrderedAtomFlagVariation.exists_source_pair_modulus D P t ht (N+1) C hε
  have hδ (reg : Bool) : 0< radius D.ξ (centerMoment P reg) := by
    have hM := centerMoment_pos P reg
    have hξ := D.hξ
    unfold radius γ
    positivity
  let r := min rflag (min (radius D.ξ (centerMoment P false)/2)
    (radius D.ξ (centerMoment P true)/2))
  have hr : 0< r := lt_min hrflag (lt_min (half_pos (hδ false)) (half_pos (hδ true)))
  refine ⟨r,hr,?_⟩
  intro reg j w hw b y hby hnear
  have hnear' : (y:ℝ)-b≤ radius D.ξ (centerMoment P reg)/2 := by
    cases reg
    · exact (hnear.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    · exact (hnear.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  exact native_restored_beta_bound D P t ht hdR H hBH πL π upperBid hupperBid hfloor N hrare
    hcap hN hξh hF hR hflags huB hRp hsmall hmSmall hwγ hroom reg j w hw b y hby hnear'
    εflag rflag C hBC hrflag (hnear.trans_le (min_le_left _ _))
    (fun kind b' d' hb => hmod kind reg b' d' hb)

end FCAppendix.Affine.Tail04.OrderedAtomRestoredGuard
