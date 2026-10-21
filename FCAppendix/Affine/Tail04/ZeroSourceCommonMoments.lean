import FCAppendix.Affine.Tail04.ZeroCommonMenuCount
import FCAppendix.Affine.Tail04.ZeroNativeFiberProduct
import FCAppendix.Affine.Tail04.ZeroNativeRowLaws
import FCAppendix.Affine.Tail04.SourceTwoFocalGuard
import FCAppendix.Affine.Tail04.OriginalCommonReciprocal

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroSourceCommonMoments
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource
open OriginalActiveCompression ZeroCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open NativeCountGuards EqualPrivateSignal NativeTypicalCount Hybrid LowBody
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => userLaw Γ
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH

lemma tagFlag_eq (k : Fin 4) (x : UserDraw 2) :
    tagFlag tag k x=categoryFlag E k x := by
  simp only [tagFlag,categoryFlag]
  split_ifs <;> simp_all

lemma tagFlag_fun_eq (k : Fin 4) : tagFlag tag k=categoryFlag E k := by
  funext x
  exact tagFlag_eq D P hdR H hUH k x

include D P t ht πL π upperBid hupperBid hdR H hUH hfloor in
lemma decoded_common : ∀ᵐ x ∂μ,tag x=1 → (decode x:ℝ)=nativeBid x := by
  have hsource := source_bands D P t ht hdR H hUH πL π upperBid hupperBid hfloor
  rw [game_original_user]
  filter_upwards [(measurePreserving_fst («μ»:=(ProbabilityMeasure.toMeasure (joint D P t ht πL π upperBid hupperBid)))
    (ν:=permLaw 2)).quasiMeasurePreserving.ae hsource] with x hx htag
  have hb := SourceNativeMoments.source_active_bid E P t x hx htag
  exact OriginalValues.clipToBand_eq 1 (E).U (E).one_le_U hb

include D ht πL π upperBid hupperBid hdR H hUH hfloor N hrare in
lemma active_mean : activeMean tag μ=activeMass P.theta-upperMass P t := by
  simp only [activeMean,tagFlag_fun_eq]
  exact SourceNativeMoments.native_active_mean Γ P E rfl t ht D.u D.huU
    πL («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)

include D ht πL π upperBid hupperBid hdR H hUH hfloor N hrare in
lemma private_means :
    privateMean0 tag μ=(partialMass+upperMass P t)/2 ∧
      (∫x,indicator (tagFlag tag 3) x ∂μ)=(partialMass+upperMass P t)/2 := by
  have hp := native_private_means Γ P E rfl t ht D.u D.huU
    πL («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
  simpa only [privateMean0,tagFlag_fun_eq] using hp

variable (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)

include t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags in
lemma mixed_mean (reg : Bool) :
    mixedMean Ds tag decode μ reg=mixedMoment Γ P E D.ξ reg := by
  change (∫ x,(sourceProbability (D.e0 reg) D.F (decode x):ℝ)*
      MenuError.indicator (tagFlag tag 1) x ∂μ)=
    ∫ x,(sourceProbability (baseFlag P reg) (Central.B D.ξ) (nativeBid x):ℝ)*
      MenuError.indicator (categoryFlag E 1) x ∂μ
  apply integral_congr_ae
  filter_upwards [decoded_common D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare]
    with x hx
  rw [←tagFlag_fun_eq D P hdR H hUH 1]
  by_cases ha : tag x=1
  · rw [hflags reg,hF,hx ha]
  · simp [MenuError.indicator,tagFlag,ha]

include t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags in
lemma reciprocal_mean (reg : Bool) :
    reciprocalMean Ds tag decode μ reg=reciprocalMoment Γ P E D.ξ reg := by
  change (∫ x,(sourceProbability (D.e0 reg) D.F (decode x):ℝ)*
      reciprocalWeight (tagFlag tag 1) (fun y => (decode y:ℝ)) x ∂μ)=
    ∫ x,(sourceProbability (baseFlag P reg) (Central.B D.ξ) (nativeBid x):ℝ)*
      reciprocalWeight (categoryFlag E 1) nativeBid x ∂μ
  apply integral_congr_ae
  filter_upwards [decoded_common D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare]
    with x hx
  rw [←tagFlag_fun_eq D P hdR H hUH 1]
  by_cases ha : tag x=1
  · simp only [reciprocalWeight,tagFlag,ha,decide_true,if_true]
    rw [hflags reg,hF,hx ha]
  · simp [reciprocalWeight,tagFlag,ha]

include hdR hUH in
lemma originalMarks_eq (K : ℕ) :
    SourceTwoFocalGuard.originalMarks P E rfl t ht D.u D.huU πL
      («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor K=(Ds).marksLaw K := by
  apply AtypicalOriginalPosterior.markLaw_eq_of_pushforward
  exact ZeroNativeRowLaws.original_sorted_marks D P t ht hdR H hUH
    πL π upperBid hupperBid hfloor K

include D ht πL π upperBid hupperBid hdR H hUH hfloor in
lemma source_marks (reg : Bool) (K : ℕ) :
    NativeTypicalCount.privateMean K reg ((Ds).marksLaw K)=keptShare P t reg*K := by
  rw [←originalMarks_eq D P t ht πL π upperBid hupperBid hdR H hUH hfloor K]
  exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht D.u D.huU πL
    («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor reg K

variable (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ) (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)

include ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags hξh hR huB hRp hsmall hmSmall in
lemma source_guard (reg : Bool) :
    GuardInterior D.ξ (keptShare P t reg) (99/200) D.U D.R D.Up (γ D.ξ)
      (radius D.ξ (centerMoment P reg))
      (activeMean tag μ) (mixedMean Ds tag decode μ reg) (privateMean0 tag μ)
      (reciprocalMean Ds tag decode μ reg) reg := by
  have hg := native_guard_interior Γ P E rfl t ht D.u D.hu D.huU πL
    («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
    D.ξ D.hξ hξh huB (by change D.U≤Central.B D.ξ;rw [←hF];exact (base_active_le_physical D).trans D.hUF)
    hR hRp hsmall hmSmall reg
  rw [mixed_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags]
  simpa only [activeMean,privateMean0,tagFlag_fun_eq,mixedMoment,reciprocalMoment,nativeFlag,nativeBid] using! hg

include ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags hξh hR huB hRp hsmall hmSmall in
lemma source_nominal_guard (reg : Bool) :
    GuardInterior D.ξ (keptShare P t reg) (99/200) (Central.B D.ξ) D.R D.Up (γ D.ξ)
      (radius D.ξ (centerMoment P reg))
      (activeMean tag μ) (mixedMean Ds tag decode μ reg) (privateMean0 tag μ)
      (reciprocalMean Ds tag decode μ reg) reg := by
  have hg := native_nominal_guard_interior Γ P E rfl t ht D.u D.hu D.huU πL
    («partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare)
    D.ξ D.hξ hξh huB (by change D.U≤Central.B D.ξ;rw [←hF];exact (base_active_le_physical D).trans D.hUF)
    hR hRp hsmall hmSmall reg
  rw [mixed_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags]
  simpa only [activeMean,privateMean0,tagFlag_fun_eq,mixedMoment,reciprocalMoment,nativeFlag,nativeBid] using! hg

include D πL π upperBid hupperBid hdR H hUH hfloor N hrare in
lemma source_category_mass (k : Fin 4) :
    (μ).real (tag ⁻¹' {k})=(originalCategories P t ht).mass k := by
  rw [measureReal_def,ZeroNativeCategories.native_source_category_mass D P t ht hdR H hUH
    πL π upperBid hupperBid hfloor Γ
    (game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare) k,
    ENNReal.toReal_ofReal ((originalCategories P t ht).nonneg k)]

include D t ht πL π upperBid hupperBid hdR H hUH hfloor hrare in
lemma source_reciprocal (hN : 0< N) :
    (∫r,1/(((Ds).count (tags tag r) 1+1:ℕ):ℝ) ∂Measure.pi (fun _ : Fin N=> μ))≤
      2/(P.bulkWeight*N)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2) := by
  have hm : P.bulkWeight≤ (μ).real (tag ⁻¹' {1}) := by
    rw [source_category_mass D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare]
    change P.bulkWeight≤ P.bulkWeight+P.truncatedTailWeight t
    linarith [P.truncatedTailWeight_pos t ht]
  have hh := OriginalCommonReciprocal.iid_reciprocal μ (tag ⁻¹' {1})
    ((E).measurable_coarseTag (measurableSet_singleton 1)) N hN P.bulkWeight_pos hm
  simpa only [Data.count,tags,Probability.sampleCount,Function.comp_apply,
    Set.mem_preimage,Set.mem_singleton_iff] using hh

include D P t ht πL π upperBid hupperBid hdR H hUH hfloor hrare in
lemma source_equal (hN : 0< N) :
    (Measure.pi (fun _ : Fin N=> μ)).real
      {r | (Ds).count (tags tag r) 2=(Ds).count (tags tag r) 3}≤75/(4*Real.sqrt N) := by
  have hc := originalJoint_role_correspondence P E rfl t ht.le πL
    («partial» D P t ht π) (active D P t ht π) upperBid hupperBid hfloor
  have hj := game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
  have he := NativeCountGuards.source_private_tie_bound Γ E P rfl t ht.le
    (by rw [hj];exact hc.mono fun _ h=> h.1)
    (by rw [hj];exact hc.mono fun _ h=> h.2.1) (fun _ : Fin 0=>1) N hN
  convert! he using 1
  all_goals simp only [fullCategoryCount,categoryCount,LowBody.hitCount,Fin.sum_univ_zero,zero_add,
    SourceActiveCountExceptions.count_eq_categoryCount,tags,Function.comp_apply,div_div]
  all_goals congr!

include D t ht πL π upperBid hupperBid hdR H hUH hfloor hrare in
lemma source_noLow (hN : 0< N) :
    (Measure.pi (fun _ : Fin N=> μ)).real {r | (Ds).count (tags tag r) 0=0}≤
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  have hm : (μ).real (tag ⁻¹' {0})=lowMass P.theta :=
    source_category_mass D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare 0
  apply (measureReal_mono («μ»:=Measure.pi (fun _ : Fin N=> μ)) ?_).trans
    (NativeFlag.iid_bulk_count_lower_tail μ (tag ⁻¹' {0})
      ((E).measurable_coarseTag (measurableSet_singleton 0)) N hN P.low_mass_pos hm.ge)
  intro r hr
  have hc : Probability.sampleCount (tag ⁻¹' {0}) r=(Ds).count (tags tag r) 0 := by
    simp only [Data.count,tags,Probability.sampleCount,Function.comp_apply,
      Set.mem_preimage,Set.mem_singleton_iff]
  change (Probability.sampleCount (tag ⁻¹' {0}) r:ℝ)<lowMass P.theta*(N:ℝ)/2
  rw [hc,show (Ds).count (tags tag r) 0=0 from hr,Nat.cast_zero]
  exact div_pos (mul_pos P.low_mass_pos (Nat.cast_pos.mpr hN)) (by norm_num)

end FCAppendix.Affine.Tail04.ZeroSourceCommonMoments
