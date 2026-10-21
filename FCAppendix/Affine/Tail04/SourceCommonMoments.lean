import FCAppendix.Affine.Tail04.OriginalCommonMenuCount
import FCAppendix.Affine.Tail04.NoisyOriginalMarks
import FCAppendix.Affine.Tail04.OriginalCommonReciprocal
import FCAppendix.Affine.Tail04.LatentNoisySupport

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceCommonMoments
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open NativeActiveCompressedLaw OriginalActiveCompression OriginalCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open SourceActiveCountExceptions NativeCountGuards EqualPrivateSignal NativeTypicalCount
open scoped BigOperators

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hBH
local notation "Γ" => game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "tag" => latentTag D P hdR H hBH
local notation "decode" => latentBid D P hdR H hBH

include hfloor hrare in
theorem integral_native (g : UserDraw 2→ℝ) (hg : Measurable g) :
    (∫ z,g (realize D z) ∂μ)=∫ x,g x ∂userLaw Γ := by
  have hh := integral_map («μ»:=μ) (measurable_realize D).aemeasurable hg.aestronglyMeasurable
  rw [realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare] at hh
  exact hh.symm

lemma tagFlag_eq (k : Fin 4) (z : Draw) :
    tagFlag tag k z=categoryFlag E k (realize D z) := by
  simp only [tagFlag,categoryFlag,latentTag]
  split_ifs <;> simp_all

lemma indicator_tagFlag (k : Fin 4) (z : Draw) :
    MenuError.indicator (tagFlag tag k) z=
      MenuError.indicator (categoryFlag E k) (realize D z) := by
  simp only [MenuError.indicator,tagFlag_eq]

include hfloor hrare in
theorem active_mean : activeMean tag μ=activeMass P.theta-upperMass P t := by
  rw [activeMean]
  simp_rw [indicator_tagFlag]
  rw [integral_native D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    (indicator (categoryFlag E 1)) (measurable_indicator _ (measurable_categoryFlag E 1))]
  exact SourceNativeMoments.native_active_mean Γ P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_le D) πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π)
    (tailPhysical D P t ht π) upperBid hupperBid hfloor
      (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare)

include hfloor hrare in
theorem private_means :
    privateMean0 tag μ=(partialMass+upperMass P t)/2 ∧
      (∫ z,indicator (tagFlag tag 3) z ∂μ)=(partialMass+upperMass P t)/2 := by
  have h0 := integral_native D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    (indicator (categoryFlag E 2)) (measurable_indicator _ (measurable_categoryFlag E 2))
  have h1 := integral_native D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    (indicator (categoryFlag E 3)) (measurable_indicator _ (measurable_categoryFlag E 3))
  have hp := native_private_means Γ P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D)
    πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor
    (game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare)
  simpa only [privateMean0,indicator_tagFlag] using And.intro (h0.trans hp.1) (h1.trans hp.2)

include hfloor hrare in
theorem decoded_common : ∀ᵐ z ∂μ,tag z=1 → (decode z:ℝ)=nativeBid (realize D z) := by
  filter_upwards [LatentNoisySupport.original_common_support D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare] with z hz htag
  have hb := SourceNativeMoments.source_active_bid E P t (realize D z) hz.1 htag
  exact OriginalValues.clipToBand_eq 1 (E).U (E).one_le_U hb

variable (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)

include hfloor hrare hF hflags in
theorem mixed_mean (reg : Bool) :
    mixedMean Ds tag decode μ reg=mixedMoment Γ P E D.ξ reg := by
  let g := fun x : UserDraw 2 => (nativeFlag P D.ξ reg x:ℝ)*indicator (categoryFlag E 1) x
  have hm : Measurable g := (measurable_nativeFlag P D.ξ reg).subtype_val.mul
    (measurable_indicator _ (measurable_categoryFlag E 1))
  calc
    _=∫ z,g (realize D z) ∂μ := by
      change (∫ z,(sourceProbability (D.e0 reg) D.F (decode z):ℝ)*
        MenuError.indicator (tagFlag tag 1) z ∂μ)=_
      apply integral_congr_ae
      filter_upwards [decoded_common D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare] with z hz
      change (sourceProbability (D.e0 reg) D.F (decode z):ℝ)*MenuError.indicator (tagFlag tag 1) z=
        (sourceProbability (baseFlag P reg) (Central.B D.ξ) (nativeBid (realize D z)):ℝ)*
          MenuError.indicator (categoryFlag E 1) (realize D z)
      rw [←indicator_tagFlag D P hdR H hBH 1 z]
      by_cases ha : tag z=1
      · rw [hflags reg,hF,hz ha]
      · simp [MenuError.indicator,tagFlag,ha]
    _=_ := integral_native D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare g hm

include hfloor hrare hF hflags in
theorem reciprocal_mean (reg : Bool) :
    reciprocalMean Ds tag decode μ reg=reciprocalMoment Γ P E D.ξ reg := by
  let g := fun x : UserDraw 2 => (nativeFlag P D.ξ reg x:ℝ)*
    reciprocalWeight (categoryFlag E 1) nativeBid x
  have hm : Measurable g := (measurable_nativeFlag P D.ξ reg).subtype_val.mul
    (measurable_reciprocalWeight _ (measurable_categoryFlag E 1) nativeBid measurable_nativeBid)
  calc
    _=∫ z,g (realize D z) ∂μ := by
      change (∫ z,(sourceProbability (D.e0 reg) D.F (decode z):ℝ)*
        reciprocalWeight (tagFlag tag 1) (fun y => (decode y:ℝ)) z ∂μ)=_
      apply integral_congr_ae
      filter_upwards [decoded_common D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare] with z hz
      change (sourceProbability (D.e0 reg) D.F (decode z):ℝ)*
          reciprocalWeight (tagFlag tag 1) (fun y => (decode y:ℝ)) z=
        (sourceProbability (baseFlag P reg) (Central.B D.ξ) (nativeBid (realize D z)):ℝ)*
          reciprocalWeight (categoryFlag E 1) nativeBid (realize D z)
      by_cases ha : tag z=1
      · simp only [reciprocalWeight,←tagFlag_eq D P hdR H hBH 1 z,tagFlag,ha,decide_true,if_true]
        rw [hflags reg,hF,hz ha]
      · simp [reciprocalWeight,←tagFlag_eq D P hdR H hBH 1 z,tagFlag,ha]
    _=_ := integral_native D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare g hm

include πL π upperBid hupperBid hdR H hBH hfloor in
theorem source_marks (reg : Bool) (K : ℕ) :
    NativeTypicalCount.privateMean K reg ((Ds).marksLaw K)=keptShare P t reg*K := by
  rw [←NoisyOriginalMarks.originalMarks_eq D P t ht hdR H hBH πL π upperBid hupperBid hfloor K]
  exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_le D) πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π)
    (tailPhysical D P t ht π) upperBid hupperBid hfloor reg K

variable (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
  (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)

include hfloor N hrare hF hflags hξh hR huB hRp hsmall hmSmall in
theorem source_guard (reg : Bool) :
    GuardInterior D.ξ (keptShare P t reg) (99/200) D.B D.R D.V (γ D.ξ)
      (radius D.ξ (centerMoment P reg))
      (activeMean tag μ) (mixedMean Ds tag decode μ reg) (privateMean0 tag μ)
      (reciprocalMean Ds tag decode μ reg) reg := by
  have hj := game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
  have hg := native_guard_interior Γ P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_nonneg D) (bulkPhysicalWidth_le D) πL (partialPhysical D P t ht π)
    (bulkPhysical D P t ht π) (tailPhysical D P t ht π) upperBid hupperBid hfloor hj
    D.ξ D.hξ hξh huB (by change D.B≤Central.B D.ξ;rw [←hF];exact D.hUF) hR hRp hsmall hmSmall reg
  have ha := SourceNativeMoments.native_active_mean Γ P E rfl t ht (bulkPhysicalWidth D)
    (bulkPhysicalWidth_le D) πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π)
    (tailPhysical D P t ht π) upperBid hupperBid hfloor hj
  have hp := native_private_means Γ P E rfl t ht (bulkPhysicalWidth D) (bulkPhysicalWidth_le D)
    πL (partialPhysical D P t ht π) (bulkPhysical D P t ht π) (tailPhysical D P t ht π)
    upperBid hupperBid hfloor hj
  rw [active_mean D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare,
    (private_means D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare).1,
    mixed_mean D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare hF hflags,
    reciprocal_mean D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare hF hflags]
  simpa only [ha,hp.1,mixedMoment,reciprocalMoment,nativeFlag,nativeBid] using! hg

include hfloor hrare in
theorem source_equal (hN : 0< N) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {r | (Ds).count (tags tag r) 2=(Ds).count (tags tag r) 3}≤75/(4*Real.sqrt N) := by
  have hj := game_original_joint D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
  have hc := originalJoint_role_correspondence P E rfl t ht.le πL
    (partialPhysical D P t ht π) (activePhysical D P t ht π) upperBid hupperBid hfloor
  have he := NativeCountGuards.source_private_tie_bound Γ E P rfl t ht.le
    (by rw [hj];exact hc.mono fun _ h => h.1)
    (by rw [hj];exact hc.mono fun _ h => h.2.1) (fun _ : Fin 0 => 1) N hN
  let f := fun r : Fin N→ Draw => fun j => realize D (r j)
  have hm : Measurable f := measurable_pi_lambda _ fun j => (measurable_realize D).comp (measurable_pi_apply j)
  have hmap : (Measure.pi (fun _ : Fin N => μ)).map f=Measure.pi (fun _ : Fin N => userLaw Γ) := by
    rw [Measure.pi_map_pi (fun _ => (measurable_realize D).aemeasurable)]
    simp only [realize_original_user D P t ht πL π upperBid hupperBid hdR H hBH hfloor (N+1) hrare]
  have hs : MeasurableSet {r : Fin N→ UserDraw 2 | (Ds).count (tags (E).coarseTag r) 2=(Ds).count (tags (E).coarseTag r) 3} :=
    ((Set.to_countable {kind : Fin N→Fin 4 | (Ds).count kind 2=(Ds).count kind 3}).measurableSet).preimage (measurable_tags (E).coarseTag (E).measurable_coarseTag)
  have hm' := congrArg (fun ν : Measure (Fin N→ UserDraw 2) =>
    ν.real {r | (Ds).count (tags (E).coarseTag r) 2=(Ds).count (tags (E).coarseTag r) 3}) hmap
  rw [measureReal_def,Measure.map_apply hm hs] at hm'
  rw [show {r : Fin N→ Draw | (Ds).count (tags tag r) 2=(Ds).count (tags tag r) 3}=
    f ⁻¹' {r | (Ds).count (tags (E).coarseTag r) 2=(Ds).count (tags (E).coarseTag r) 3} from rfl,
    measureReal_def,hm']
  convert! he using 1
  all_goals simp only [Hybrid.fullCategoryCount,Hybrid.categoryCount,LowBody.hitCount,Fin.sum_univ_zero,zero_add,
    count_eq_categoryCount,tags,Function.comp_apply,div_div]
  all_goals congr!

include hfloor hrare in
theorem source_noLow (hN : 0< N) :
    (Measure.pi (fun _ : Fin N => μ)).real {r | (Ds).count (tags tag r) 0=0}≤
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2) := by
  let S : Set Draw := tag ⁻¹' {0}
  have hS : MeasurableSet S := (measurable_latentTag D P hdR H hBH) (measurableSet_singleton 0)
  have hm : (μ).real S=lowMass P.theta := by
    rw [measureReal_def,original_category_mass D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare 0]
    exact ENNReal.toReal_ofReal P.low_mass_pos.le
  apply (measureReal_mono («μ»:=Measure.pi (fun _ : Fin N => μ)) ?_).trans
    (NativeFlag.iid_bulk_count_lower_tail μ S hS N hN P.low_mass_pos hm.ge)
  intro r hr
  have hc : Probability.sampleCount S r=(Ds).count (tags tag r) 0 := by
    simp only [S,Data.count,tags,Probability.sampleCount,Function.comp_apply,
      Set.mem_preimage,Set.mem_singleton_iff]
  change (Probability.sampleCount S r:ℝ)<lowMass P.theta*(N:ℝ)/2
  rw [hc,show (Ds).count (tags tag r) 0=0 from hr,Nat.cast_zero]
  exact div_pos (mul_pos P.low_mass_pos (Nat.cast_pos.mpr hN)) (by norm_num)

end FCAppendix.Affine.Tail04.SourceCommonMoments
