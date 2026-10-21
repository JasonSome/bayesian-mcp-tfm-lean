import FCAppendix.Affine.Tail04.SourceMomentRectangle
import FCAppendix.Affine.Tail04.OriginalLowRow
import FCAppendix.Affine.Tail04.OriginalPopulationSupport

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceNativeMoments
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation MenuError
open SourceMomentRectangle Hybrid

def mixedWeight (E : Observable.Regions) (e0 B0 : ℝ) (x : UserDraw 2) : ℝ :=
  if E.coarseTag x=1 then (sourceProbability e0 B0 x.1.2.bid:ℝ) else 0

lemma mixedWeight_eq_marked (E : Observable.Regions) (e0 B0 : ℝ) (x : UserDraw 2) :
    mixedWeight E e0 B0 x=(sourceProbability e0 B0 x.1.2.bid:ℝ)*MenuError.indicator (categoryFlag E 1) x := by
  by_cases h : E.coarseTag x=1 <;> simp [mixedWeight,categoryFlag,MenuError.indicator,h]

lemma measurable_mixedWeight (E : Observable.Regions) (e0 B0 : ℝ) :
    Measurable (mixedWeight E e0 B0) :=
  Measurable.ite (measurableSet_eq_fun E.measurable_coarseTag measurable_const)
    ((measurable_sourceProbability e0 B0).subtype_val.comp
      ((measurable_bid 2).comp measurable_fst.snd)) measurable_const

lemma mixedWeight_bounds (E : Observable.Regions) (e0 B0 : ℝ) (x : UserDraw 2) :
    mixedWeight E e0 B0 x∈Icc (0:ℝ) 1 := by
  unfold mixedWeight
  split_ifs
  · exact (sourceProbability e0 B0 x.1.2.bid).2
  · norm_num

lemma integrable_mixedWeight (E : Observable.Regions) (e0 B0 : ℝ)
    (μ : Measure (UserDraw 2)) [IsFiniteMeasure μ] : Integrable (mixedWeight E e0 B0) μ :=
  Integrable.of_bound (measurable_mixedWeight E e0 B0).aestronglyMeasurable 1
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mixedWeight_bounds E e0 B0 x).1]
      exact (mixedWeight_bounds E e0 B0 x).2))

lemma reciprocal_le_mixed (E : Observable.Regions) (e0 B0 : ℝ) (x : UserDraw 2) :
    originalReciprocalWeight E e0 B0 x≤ mixedWeight E e0 B0 x := by
  by_cases h : E.coarseTag x=1
  · simp only [originalReciprocalWeight,mixedWeight,if_pos h,sourceReciprocalWeight]
    have hp := (sourceProbability e0 B0 x.1.2.bid).2.1
    have hd : 0< max (1:ℝ) x.1.2.bid := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    apply (div_le_iff₀ hd).mpr
    nlinarith [le_max_left (1:ℝ) x.1.2.bid]
  · simp [originalReciprocalWeight,mixedWeight,h]

lemma sourceProbability_le_base {e0 B0 b : ℝ}
    (he0 : 0≤ e0) (he1 : e0≤1) (hB : 1< B0) (hb : b∈Icc 1 B0) :
    (sourceProbability e0 B0 b:ℝ)≤ e0 := by
  have hD : 0< B0-1 := sub_pos.mpr hB
  have hr : (B0-b)/(B0-1)∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (sub_nonneg.mpr hb.2) hD.le,
      (div_le_one hD).mpr (by linarith [hb.1])⟩
  have hs : ((B0-b)/(B0-1))^2≤1 := by nlinarith [hr.1,hr.2]
  have hraw : mixedFlagProbability e0 B0 b≤ e0 := by
    unfold mixedFlagProbability
    nlinarith
  change probabilityClip (mixedFlagProbability e0 B0 b)≤ e0
  rw [probabilityClip_eq ⟨mixedFlagProbability_nonneg he0,
    mixedFlagProbability_le_one he0 he1 hB hb⟩]
  exact hraw

lemma source_active_bid (E : Observable.Regions) (P : ValueParameters) (t : ℝ)
    (x : UserDraw 2) (hx : sourceBands P E t x.1) (ht : E.coarseTag x=1) :
    x.1.2.bid∈Icc (1:ℝ) E.U := by
  have hnlow : ¬x.1.2.bid≤ E.d := by
    intro h
    simp [Observable.Regions.coarseTag,Observable.Regions.collapse,h] at ht
  have hnprivate : x.1.2.bid∉E.privateBids := by
    intro h
    simp only [Observable.Regions.coarseTag,Observable.Regions.collapse,
      if_neg hnlow,if_pos h,upperRow] at ht
    split_ifs at ht <;> norm_num [Fin.ext_iff] at ht
  rcases hx with hx | hx | hx | hx
  · exact (hnlow hx.2.1).elim
  · exact (hnprivate (Or.inl hx.2.1)).elim
  · exact hx.2.1
  · exact (hnprivate (Or.inr hx.2.1)).elim

section Native
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m 2 c Seed) (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M< t) (u e0 B0 : ℝ)
  (hu : 0≤ u) (huE : 1+u≤ E.U) (huB : 1+u< B0) (hEB : E.U≤ B0)
  (he0 : 0< e0) (he1 : e0≤1)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
  (πB : Law (A:=Icc (1:ℝ) (1+u)) P.originalBulkLaw)
  (πT : Law (A:=Icc (1:ℝ) E.U) (P.originalTruncatedTailLaw t ht))
  (upperBid : ℝ→ℝ) (hupper : Measurable upperBid)
  (hfloor : ∀ v,t< v → E.H≤ upperBid v)

variable (hjoint : Γ.F⊗ₘΓ.σ=((originalJoint P t ht.le E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper) : Measure (ℝ×JointAction 2)))

include hd ht u huE πL πP πB πT upperBid hupper hfloor hjoint in
lemma native_active_mean :
    (∫ x,MenuError.indicator (categoryFlag E 1) x ∂userLaw Γ)=activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t) := by
  have hrow := native_original_exact_low_row E P hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor Γ hjoint
  have hsum : lowMass P.theta+(activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t))+(partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t))=1 := by
    have hh := mass_sum P.theta
    linarith
  simpa using original_category_mean Γ E (lowMass P.theta) (activeMass P.theta-(activeMass P.theta*P.zeta*powerTail P.M 10 t))
    (partialMass+(activeMass P.theta*P.zeta*powerTail P.M 10 t)) P.low_mass_pos.le (P.movingActiveMass_positive t ht.le).le
    (by have := P.tailMass_nonneg t ht.le;norm_num [partialMass];linarith) hsum
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) hrow 1

include P hd t ht u huE hEB πL πP πB πT upperBid hupper hfloor hjoint in
lemma native_active_source :
    ∀ᵐ x ∂userLaw Γ,E.coarseTag x=1 → x.1.2.bid∈Icc (1:ℝ) B0 := by
  have hs := originalJoint_sourceBands P E hd t ht.le πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper hfloor
  rw [userLaw,hjoint]
  filter_upwards [(measurePreserving_fst (μ:=((originalJoint P t ht.le E.R E.Rp E.U (E.d_nonneg.trans E.d_lt_R.le) πL πP (ActiveJointMerge.mergedActiveLaw P t ht u E.U huE πB πT) upperBid hupper) : Measure (ℝ×JointAction 2)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae hs] with x hx
  intro htag
  have hb := source_active_bid E P t x hx htag
  exact ⟨hb.1,hb.2.trans hEB⟩

include hd t ht u hu huE huB hEB he0 he1 πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_mixed_upper :
    (∫ x,mixedWeight E e0 B0 x ∂userLaw Γ)≤ activeMass P.theta*e0 := by
  have hm : ∀ᵐ x ∂userLaw Γ,mixedWeight E e0 B0 x≤ e0*MenuError.indicator (categoryFlag E 1) x := by
    filter_upwards [native_active_source Γ P E hd t ht u B0 huE hEB πL πP πB πT
      upperBid hupper hfloor hjoint] with x hx
    by_cases h : E.coarseTag x=1
    · simpa only [mixedWeight,if_pos h,categoryFlag,if_pos h,MenuError.indicator,ite_true,mul_one] using
        sourceProbability_le_base he0.le he1 (by linarith : 1< B0) (hx h)
    · simp [mixedWeight,categoryFlag,MenuError.indicator,h]
  have hi : Integrable (fun x : UserDraw 2 => MenuError.indicator (categoryFlag E 1) x) (userLaw Γ) :=
    Integrable.of_bound ((measurable_of_countable (fun b : Bool => if b then (1:ℝ) else 0)).comp
      (measurable_categoryFlag E 1)).aestronglyMeasurable 1
      (ae_of_all _ (fun x => by cases hb : categoryFlag E 1 x <;> norm_num [MenuError.indicator,hb]))
  have hh := integral_mono_ae (integrable_mixedWeight E e0 B0 (userLaw Γ)) (hi.const_mul e0) hm
  rw [integral_const_mul,native_active_mean Γ P E hd t ht u huE πL πP πB πT
    upperBid hupper hfloor hjoint] at hh
  have htail := P.tailMass_nonneg t ht.le
  nlinarith

include hd t ht hu huE huB hEB he0 he1 πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_two_moment_error :
    |(∫ x,mixedWeight E e0 B0 x ∂userLaw Γ)-activeMass P.theta*e0|≤
        activeMass P.theta*e0*relativeError P.zeta u B0 ∧
    |(∫ x,originalReciprocalWeight E e0 B0 x ∂userLaw Γ)-activeMass P.theta*e0|≤
        activeMass P.theta*e0*relativeError P.zeta u B0 := by
  have hb := native_original_reciprocal_lower Γ P E t ht u e0 B0
    (by linarith : 1≤1+u) huE huB he0 he1 πL πP πB πT upperBid hupper hjoint
  simp_rw [←originalReciprocalWeight_eq_marked] at hb
  have hWM := integral_mono (integrable_originalReciprocalWeight E e0 B0 (userLaw Γ))
    (integrable_mixedWeight E e0 B0 (userLaw Γ)) (reciprocal_le_mixed E e0 B0)
  exact two_moment_error P.active_mass_pos he0 ⟨P.zeta_pos.le,P.zeta_lt_one.le⟩ hu huB
    hb.2 hWM (native_mixed_upper Γ P E hd t ht u e0 B0 hu huE huB hEB he0 he1
      πL πP πB πT upperBid hupper hfloor hjoint)

include hd t ht hu huE huB hEB he0 he1 πL πP πB πT upperBid hupper hfloor hjoint in
theorem native_two_moment_small {ξ : ℝ}
    (hsmall : relativeError P.zeta u B0≤ ξ/1000) :
    |(∫ x,mixedWeight E e0 B0 x ∂userLaw Γ)-activeMass P.theta*e0|≤
        ξ*(activeMass P.theta*e0)/1000 ∧
    |(∫ x,originalReciprocalWeight E e0 B0 x ∂userLaw Γ)-activeMass P.theta*e0|≤
        ξ*(activeMass P.theta*e0)/1000 := by
  have he := native_two_moment_error Γ P E hd t ht u e0 B0 hu huE huB hEB he0 he1
    πL πP πB πT upperBid hupper hfloor hjoint
  have hm := mul_le_mul_of_nonneg_left hsmall (mul_pos P.active_mass_pos he0).le
  constructor
  · exact he.1.trans (by nlinarith)
  · exact he.2.trans (by nlinarith)

end Native
end FCAppendix.Affine.Tail04.SourceNativeMoments
