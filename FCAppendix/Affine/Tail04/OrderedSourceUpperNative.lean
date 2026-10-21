import FCAppendix.Affine.Tail04.OrderedNativeUpperRank
import FCAppendix.Affine.Tail04.OrderedNativeZeroNoiseSource
import FCAppendix.Affine.Tail04.OriginalMovingUpperEnvelope
import FCAppendix.Affine.Tail04.ZeroNativeBindings
import FCAppendix.Affine.Hybrid.PopulationUpper
import FCAppendix.Affine.Hybrid.UpperNativeEnvelope

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceUpperNative
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeLocalPolicy Existence.RankEnvelope

private lemma fourJoint_above (s h a z B0 : ℝ)
    (PL PP PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),x.2.bid≤ B0)
    (hP : ∀ᵐ x ∂(PP : Measure (ℝ×JointAction 2)),x.2.bid≤ B0)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid≤ B0)
    (B : Set ℝ) (hB : B⊆Ioi B0) :
    fourJoint s h a z PL PP PA PH {x | x.2.bid∈B}=
      ENNReal.ofReal z*(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid∈B} := by
  have hz (Q : ProbabilityMeasure (ℝ×JointAction 2))
      (hQ : ∀ᵐ x ∂(Q : Measure (ℝ×JointAction 2)),x.2.bid≤ B0) :
      (Q : Measure (ℝ×JointAction 2)) {x | x.2.bid∈B}=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hQ] with x hx hb
    exact not_lt.mpr hx (hB hb)
  simp only [fourJoint,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    hz PL hL,hz PP hP,hz PA hA,mul_zero,zero_add]

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters)
    (t : ℝ) (ht : P.M< t) (hdR : P.d0< D.R)
    (H : ℝ) (hUH : D.U< H) (hHt : H< t)
    (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (π : JointProfile D P t ht) (N : ℕ)
    (hm : 2≤ N+1) (hc : 1≤ D.c) (hcm : D.c< N+1)

local instance movingActive_probability (hle : P.M≤t) :
    IsProbabilityMeasure (P.originalMovingActiveLaw t hle) :=
  P.originalMovingActiveLaw_probability t hle

include hUH in
private lemma positive_floor : (0:ℝ)<H :=
  ((by norm_num : (0:ℝ)<1).trans_le D.hU).trans hUH

local notation "hH" => positive_floor D H hUH
local notation "bH" => OriginalMovingUpperEnvelope.b P t (N+1) D.c H
local notation "qH" => OriginalMovingUpperEnvelope.q P t (N+1) D.c
local notation "muH" => P.movingUpperMeasure t

include ht hUH hHt hm hc hcm in
lemma upper_measurable : Measurable bH :=
  (OriginalMovingUpperEnvelope.continuous_bid P t ht.le (N+1) D.c hm hc hcm H hH hHt).measurable

include D P ht H hUH hHt N hm hc hcm in
lemma upper_floor (v : ℝ) (hv : t< v) : H≤ bH v :=
  (OriginalMovingUpperEnvelope.bid_bounds P t ht.le (N+1) D.c hm hc hcm H hH hHt v hv.le).1

local notation "hb" => upper_measurable D P t ht H hUH hHt N hm hc hcm
local notation "hf" => upper_floor D P t ht H hUH hHt N hm hc hcm
local notation "z" => activeMass P.theta*P.zeta*powerTail P.M 10 t
variable (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
  ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
    (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤ D.R)

def game : FiniteGame (N+1) 2 D.c Seed :=
  OrderedNativeZeroNoiseSource.game D P t ht hdR H hUH πL π bH hb hf (N+1) hrare

local notation "Γ" => game D P t ht hdR H hUH hHt πL π N hm hc hcm hrare
local notation "K" => ZeroNativeBindings.localData D P t ht hdR H hUH πL π bH hb hf N hrare
local notation "PH" => OriginalMovingUpperEnvelope.joint P t ht.le (N+1) D.c hm hc hcm H hH hHt

lemma original_joint : (Γ).F⊗ₘ(Γ).σ=
    (OrderedNativeZeroNoiseSource.joint D P t ht πL π bH hb : Measure (ℝ×JointAction 2)) :=
  OrderedNativeZeroNoiseSource.game_original_joint D P t ht hdR H hUH πL π bH hb hf (N+1) hrare

lemma joint_above (B : Set ℝ) (hB : B⊆Ioi D.U) :
    ((Γ).F⊗ₘ(Γ).σ) {x | x.2.bid∈B}=ENNReal.ofReal z*(PH : Measure (ℝ×JointAction 2)) {x | x.2.bid∈B} := by
  rw [original_joint]
  apply fourJoint_above
  · have hl : ∀ᵐ x ∂(Hybrid.lowJoint P.originalLowLaw πL : Measure (ℝ×JointAction 2)),x.2.bid≤ P.d0 := by
      apply (ae_map_iff (measurable_fst.subtype_val.prodMk
        ((Hybrid.measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
        (measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const)).mpr
      exact ae_of_all _ (fun x=> x.2.2.2)
    filter_upwards [hl] with x hx
    exact hx.trans (hdR.le.trans (D.hRUp.trans
      ((OrderedNativeZeroNoiseSource.base_partial_lt_one D).le.trans D.hU)))
  · exact (bandJoint_support D.hR.le 1 (by norm_num) P.originalPartialLaw
      (OrderedNativeZeroNoiseSource.partialLaw D P t ht π)).mono
      (fun _ hx=> hx.2.1.2.trans ((OrderedNativeZeroNoiseSource.base_partial_lt_one D).le.trans D.hU))
  · exact (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
      (P.originalMovingActiveLaw t ht.le) (OrderedNativeZeroNoiseSource.active D P t ht π)).mono
      (fun _ hx=> hx.2.1.2)
  · exact hB

lemma upper_visible_atomless (j : Fin 2) (y : ℝ) (hy : H≤ y) :
    userLaw Γ {x | j∈firstK x.2 x.1.2.routeCount ∧ x.1.2.bid=y}=0 := by
  have hz : ((Γ).F⊗ₘ(Γ).σ) {x | x.2.bid=y}=0 := by
    have hh := joint_above D P t ht hdR H hUH hHt πL π N hm hc hcm hrare {y}
      (fun x hx=> by rw [mem_singleton_iff.mp hx];exact hUH.trans_le hy)
    simp only [mem_singleton_iff,
      OriginalMovingUpperEnvelope.joint_atomless P t ht.le (N+1) D.c hm hc hcm H hH hHt y,
      mul_zero] at hh
    exact hh
  have hp : userLaw Γ {x : UserDraw 2 | x.1.2.bid=y}=0 := by
    have he : {x : UserDraw 2 | x.1.2.bid=y}=
        {x : ℝ×JointAction 2 | x.2.bid=y}×ˢuniv := by ext x;simp
    rw [he,userLaw,Measure.prod_prod,hz,zero_mul]
  exact measure_mono_null (fun _ hx=> hx.2) hp

lemma upper_alpha (j : Fin 2) (y : ℝ) (hy : H≤ y) :
    alphaGt Γ j y=((muH).map bH).real (Ioi y)/2 := by
  have hr : ∀ᵐ x ∂(Γ).F⊗ₘ(Γ).σ,y< x.2.bid→ x.2.routeCount=1 := by
    rw [original_joint]
    filter_upwards [OrderedNativeZeroNoiseSource.source_bands D P t ht hdR H hUH πL π bH hb hf] with x hx hxy
    rcases hx with hx | hx | hx | hx
    · exact (not_lt.mpr (hx.2.1.trans (by
        have := (OrderedNativeZeroNoiseSource.regions D P hdR H hUH).d_lt_H
        exact this.le.trans hy)) hxy).elim
    · exact hx.2.2
    · exact (not_lt.mpr (hx.2.1.2.trans (hUH.le.trans hy)) hxy).elim
    · exact hx.2.2
  rw [Hybrid.upper_alphaGt Γ j y hr]
  have htJ := joint_above D P t ht hdR H hUH hHt πL π N hm hc hcm hrare (Ioi y)
    (fun _ hx=>(hUH.trans_le hy).trans hx)
  have hw := Hybrid.weighted_upper_bid_tail (OriginalMovingUpperEnvelope.law P t) PH bH
    (OriginalMovingUpperEnvelope.joint_bid P t ht.le (N+1) D.c hm hc hcm H hH hHt)
    z (P.tailMass_nonneg t ht.le) y
  have hlaw := OriginalMovingUpperEnvelope.weighted_law P t ht.le
  change ENNReal.ofReal z • (OriginalMovingUpperEnvelope.law P t : Measure ℝ)=muH at hlaw
  rw [hlaw] at hw
  simp only [Set.mem_Ioi] at htJ
  congr 1
  change (((Γ).F⊗ₘ(Γ).σ) {x | y< x.2.bid}).toReal=_
  rw [htJ,ENNReal.toReal_mul,ENNReal.toReal_ofReal (P.tailMass_nonneg t ht.le)]
  exact hw.symm

lemma policy_feasible (j : Fin 2) (L : LocalList (N+1)) (hL : NonnegativeList L)
    (u : Seed) : (Γ).policy j L u=OrderedNativePolicy.policy K j L u := by
  apply Subtype.ext
  change (OrderedNativePolicy.policy K j (FeasibleListNormalization.cleanList L) u).val=_
  rw [FeasibleListNormalization.cleanList_eq L hL]

lemma source_user_bands :
    ∀ᵐx ∂userLaw Γ,sourceBands P (K).E t x.1 := by
  rw [userLaw,original_joint]
  exact (measurePreserving_fst (ν:=permLaw 2)).quasiMeasurePreserving.ae
    (OrderedNativeZeroNoiseSource.source_bands D P t ht hdR H hUH πL π bH hb hf)

theorem actual_rank (i : Fin (N+1)) (j : Fin 2) (y : ℝ) (hy : H≤ y) :
    ∀ᵐ ω ∂backgroundLaw Γ,Accepts Γ i y j ω↔rivals i (aboveAt j y) ω< D.c :=
  OrderedNativeUpperRank.native_upper_accepts_iff_rank K Γ P t
    (policy_feasible D P t ht hdR H hUH hHt πL π N hm hc hcm hrare)
    (source_user_bands D P t ht hdR H hUH hHt πL π N hm hc hcm hrare)
    (upper_visible_atomless D P t ht hdR H hUH hHt πL π N hm hc hcm hrare) i j y hy

theorem actual_mean (i : Fin (N+1)) (y : ℝ) (hy : H≤ y) :
    meanAcceptProb Γ i y=bidRank muH N D.c 2 bH y := by
  simpa only [Nat.add_sub_cancel] using
    native_upper_mean_of_policy_rank Γ muH bH H (le_of_lt hcm)
      (actual_rank D P t ht hdR H hUH hHt πL π N hm hc hcm hrare)
      (upper_alpha D P t ht hdR H hUH hHt πL π N hm hc hcm hrare) i y hy

theorem actual_attainment (i : Fin (N+1)) (v : ℝ) (hv : t≤ v) :
    (problem Γ i).payoff v (Hybrid.upperAction bH v)=
      OriginalMovingUpperEnvelope.U P t (N+1) D.c H v := by
  exact native_original_upper_attainment Γ rfl muH hm hc hcm
    (OriginalMovingUpperEnvelope.measure_mass_le_one P t) t H hH hHt
    (P.movingUpperMeasure_support t)
    (by intro i y hy;simpa only [OriginalMovingUpperEnvelope.b,OriginalMovingUpperEnvelope.q,
      Nat.add_sub_cancel] using
      actual_mean D P t ht hdR H hUH hHt πL π N hm hc hcm hrare i y hy) i v hv

end FCAppendix.Affine.Tail04.OrderedSourceUpperNative
