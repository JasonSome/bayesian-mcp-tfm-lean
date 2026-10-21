import FCAppendix.Affine.Tail04.OrderedSourceOriginalCountFamily
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedSourceOriginalMoments
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues OriginalPopulation SourceMenuIdentity SourceMenuPopulation SourceMenuError
open SourceMomentRectangle SourceMovingScalarGuards OrderedSourceRestrictedNative
open OrderedSourceActiveCountData OrderedSourceActiveSpecified MenuError

def bidTest (P : ValueParameters) (ξ : ℝ) (rec reg : Bool) (b : ℝ) : ℝ :=
  if rec then sourceReciprocalWeight (baseFlag P reg) (Central.B ξ) b
  else (sourceProbability (baseFlag P reg) (Central.B ξ) b:ℝ)

lemma bidTest_bounds (P : ValueParameters) (ξ : ℝ) (rec reg : Bool) (b : ℝ) :
    bidTest P ξ rec reg b∈Icc (0:ℝ) 1 := by
  cases rec
  · exact (sourceProbability _ _ _).2
  · exact sourceReciprocalWeight_bounds _ _ _

lemma continuous_bidTest (P : ValueParameters) (ξ : ℝ) (rec reg : Bool) :
    Continuous (bidTest P ξ rec reg) := by
  have hp : Continuous (fun b : ℝ=>(sourceProbability (baseFlag P reg) (Central.B ξ) b:ℝ)) :=
    continuous_probabilityClip.comp (continuous_mixedFlagProbability _ _)
  cases rec
  · exact hp
  · exact hp.div (continuous_const.max continuous_id)
      (fun b=> ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 b)))

lemma bidTest_one (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (rec reg : Bool) :
    bidTest P ξ rec reg 1=baseFlag P reg := by
  have hB : Central.B ξ-1≠0 := by unfold Central.B;linarith
  have hp : (sourceProbability (baseFlag P reg) (Central.B ξ) 1:ℝ)=baseFlag P reg := by
    change probabilityClip (baseFlag P reg*((Central.B ξ-1)/(Central.B ξ-1))^2)=_
    rw [div_self hB,one_pow,mul_one,
      probabilityClip_eq ⟨(baseFlag_bounds P reg).1.le,(baseFlag_bounds P reg).2.le⟩]
  cases rec
  · exact hp
  · simpa only [bidTest,Bool.true_eq,ite_true,sourceReciprocalWeight,max_self,div_one] using hp

lemma integrable_bidTest (P : ValueParameters) (ξ : ℝ) (rec reg : Bool)
    (μ : Measure (JointAction 2)) [IsFiniteMeasure μ] :
    Integrable (fun a=> bidTest P ξ rec reg a.bid) μ :=
  Integrable.of_bound ((continuous_bidTest P ξ rec reg).measurable.comp
    (measurable_bid 2)).aestronglyMeasurable 1 (ae_of_all _ fun a=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (bidTest_bounds P ξ rec reg a.bid).1]
      exact (bidTest_bounds P ξ rec reg a.bid).2)

lemma source_tag_active_iff (P : ValueParameters) (E : Observable.Regions)
    (_hd : (E).d=P.d0) (t : ℝ) (_ht : P.M< t) (x : UserDraw 2)
    (hx : sourceBands P E t x.1) :
    (E).coarseTag x=1 ↔ x.1.1∈P.movingActiveValues t := by
  constructor
  · intro htag
    have hb:=SourceNativeMoments.source_active_bid E P t x hx htag
    rcases hx with hx|hx|hx|hx
    · exact (not_le.mpr ((E).d_lt_one.trans_le hb.1) hx.2.1).elim
    · exact (not_le.mpr ((E).Rp_lt_one.trans_le hb.1) hx.2.1.2).elim
    · exact hx.1
    · exact (not_le.mpr (E).U_lt_H (hx.2.1.trans hb.2)).elim
  · intro hv
    rcases hx with hx|hx|hx|hx
    · exfalso
      linarith [hx.1.2,hv.1,P.low_partial_gap,P.partial_active_gap,P.w_pos]
    · exfalso
      linarith [hx.1.2,hv.1,P.partial_active_gap]
    · exact coarseTag_of_active_box E x hx.2.1
    · exact (not_lt.mpr hv.2 hx.1).elim

def valueWeight (P : ValueParameters) (ξ t : ℝ) (rec reg : Bool)
    (x : ℝ×JointAction 2) : ℝ :=
  if x.1∈P.movingActiveValues t then bidTest P ξ rec reg x.2.bid else 0

lemma measurable_valueWeight (P : ValueParameters) (ξ t : ℝ) (rec reg : Bool) :
    Measurable (valueWeight P ξ t rec reg) :=
  Measurable.ite (measurableSet_Icc.preimage measurable_fst)
    ((continuous_bidTest P ξ rec reg).measurable.comp ((measurable_bid 2).comp measurable_snd))
    measurable_const

lemma valueWeight_bounds (P : ValueParameters) (ξ t : ℝ) (rec reg : Bool)
    (x : ℝ×JointAction 2) : valueWeight P ξ t rec reg x∈Icc (0:ℝ) 1 := by
  unfold valueWeight
  split_ifs
  · exact bidTest_bounds _ _ _ _ _
  · norm_num

lemma integrable_valueWeight (P : ValueParameters) (ξ t : ℝ) (rec reg : Bool)
    (μ : Measure (ℝ×JointAction 2)) [IsFiniteMeasure μ] :
    Integrable (valueWeight P ξ t rec reg) μ :=
  Integrable.of_bound (measurable_valueWeight P ξ t rec reg).aestronglyMeasurable 1
    (ae_of_all _ fun x=> by
      rw [Real.norm_eq_abs,abs_of_nonneg (valueWeight_bounds P ξ t rec reg x).1]
      exact (valueWeight_bounds P ξ t rec reg x).2)

variable {P : ValueParameters} {ξ Up u k width : ℝ}
  {hξ : 0< ξ} {hξh : ξ<1/2} {hu : 0≤ u}
  {hRUp : Central.R ξ< Up} {hUp : Up<1} {hw : 0< width}
  {N : ℕ} (A : Market P ξ Up u k width hξ hξh hu hRUp hUp hw N)
  (hlow : P.d0<1-ξ)

local notation "E" => OrderedNativeZeroNoiseSource.regions A.D P (A.forget.low_gap hlow) A.H A.upper_gap

def actualMoment (rec reg : Bool) : ℝ :=
  ∫x,(if (E).coarseTag x=1 then bidTest P ξ rec reg x.1.2.bid else 0) ∂userLaw (A.native hlow)

def conditionalMoment (rec reg : Bool) (v : ℝ) : ℝ :=
  if v∈P.movingActiveValues (cutoff N) then
    ∫a,bidTest P ξ rec reg a.bid ∂(specified A hlow).σ v else 0

lemma actualMoment_false (reg : Bool) :
    actualMoment A hlow false reg=mixedMoment (A.native hlow) P E ξ reg := by
  unfold actualMoment mixedMoment
  apply integral_congr_ae
  exact ae_of_all _ fun x=> SourceNativeMoments.mixedWeight_eq_marked E _ _ x

lemma actualMoment_true (reg : Bool) :
    actualMoment A hlow true reg=reciprocalMoment (A.native hlow) P E ξ reg := by
  unfold actualMoment reciprocalMoment
  apply integral_congr_ae
  exact ae_of_all _ fun x=> originalReciprocalWeight_eq_marked E _ _ x

theorem actualMoment_original (hwγ : width≤ γ ξ) (rec reg : Bool) :
    actualMoment A hlow rec reg=∫v,conditionalMoment A hlow rec reg v ∂valueLaw P := by
  let H:=valueWeight P ξ (cutoff N) rec reg
  have hH : Measurable H :=measurable_valueWeight P ξ (cutoff N) rec reg
  have hs : ∀ᵐx ∂userLaw (A.native hlow),sourceBands P E (cutoff N) x.1 := by
    have hh:=OrderedNativeZeroNoiseSource.source_bands A.D P (cutoff N) A.point.range.cutoff_gt_M
      (A.forget.low_gap hlow) A.H A.upper_gap A.point.low.joint A.sequence.limit
      A.upperBid A.upperBid_measurable A.upper_floor
    rw [←A.original_joint hlow] at hh
    exact (measurePreserving_fst (μ:=(A.native hlow).F⊗ₘ(A.native hlow).σ)
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hh
  have he : actualMoment A hlow rec reg=∫x,H x.1 ∂userLaw (A.native hlow) := by
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    simp only [source_tag_active_iff P E rfl (cutoff N) A.point.range.cutoff_gt_M x hx,H,valueWeight]
  rw [he]
  have hproj := (measurePreserving_fst (μ:=(A.native hlow).F⊗ₘ(A.native hlow).σ)
    (ν:=permLaw 2)).integral_comp_ae_real hH.aestronglyMeasurable
  change (∫x : UserDraw 2,H x.1 ∂((A.native hlow).F⊗ₘ(A.native hlow).σ).prod (permLaw 2))=_
  rw [hproj]
  rw [←specified_joint A hlow hwγ]
  rw [Measure.integral_compProd (integrable_valueWeight P ξ (cutoff N) rec reg _)]
  apply integral_congr_ae
  exact ae_of_all _ fun v=> by
    dsimp only [H,valueWeight,conditionalMoment]
    split_ifs <;> simp

lemma conditionalMoment_bounds (rec reg : Bool) (v : ℝ) :
    conditionalMoment A hlow rec reg v∈Icc (0:ℝ) 1 := by
  unfold conditionalMoment
  split_ifs
  · constructor
    · exact integral_nonneg fun a=>(bidTest_bounds P ξ rec reg a.bid).1
    · have hh:=integral_mono (μ:=(specified A hlow).σ v) (integrable_bidTest P ξ rec reg _) (integrable_const (1:ℝ))
        (fun a=>(bidTest_bounds P ξ rec reg a.bid).2)
      simpa only [integral_const,probReal_univ,one_smul] using hh
  · norm_num

lemma integrable_conditionalMoment (rec reg : Bool) :
    Integrable (conditionalMoment A hlow rec reg) (valueLaw P) := by
  have hi:=integrable_valueWeight P ξ (cutoff N) rec reg
    ((specified A hlow).F⊗ₘ(specified A hlow).σ)
  have hh:=(Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi |>.2
  have he : (fun v=>∫a,‖valueWeight P ξ (cutoff N) rec reg (v,a)‖ ∂(specified A hlow).σ v)=
      conditionalMoment A hlow rec reg := by
    funext v
    simp only [Real.norm_eq_abs,abs_of_nonneg (valueWeight_bounds P ξ (cutoff N) rec reg _).1]
    unfold valueWeight conditionalMoment
    split_ifs <;> simp
  rw [he] at hh
  exact hh

theorem lambda_eq_actualMoments (reg : Bool) :
    (if reg then (lambda A hlow).2 else (lambda A hlow).1)=
      meanNumerator P ξ (actualMoment A hlow false reg) reg/actualMoment A hlow true reg := by
  have hm:=ZeroSourceCommonMoments.mixed_mean A.D P (cutoff N) A.point.range.cutoff_gt_M
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor N A.rare_nat rfl
    (by intro r;cases r <;> rfl) reg
  have hw:=ZeroSourceCommonMoments.reciprocal_mean A.D P (cutoff N) A.point.range.cutoff_gt_M
    A.point.low.joint A.sequence.limit A.upperBid A.upperBid_measurable
    (A.forget.low_gap hlow) A.H A.upper_gap A.upper_floor N A.rare_nat rfl
    (by intro r;cases r <;> rfl) reg
  rw [actualMoment_false,actualMoment_true]
  cases reg <;> simp only [lambda,ZeroSourceCommonMenuError.lambda,Bool.false_eq_true,ite_false,ite_true] <;> rw [hm,hw] <;> rfl

end FCAppendix.Affine.Tail04.OrderedSourceOriginalMoments
