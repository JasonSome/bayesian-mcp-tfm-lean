import FCAppendix.Affine.Tail04.SourceZeroBulkEvent
import FCAppendix.Affine.Tail04.OriginalUnusedCompression
import FCAppendix.Affine.Tail04.SourceUnusedConstants
import FCAppendix.Affine.Tail04.UnusedFiniteCountError
import FCAppendix.Affine.Tail04.UnusedMomentGeometry
import FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle
import FCAppendix.Affine.Tail04.OrderedUnusedEmpirical
import FCAppendix.Affine.Tail04.OrderedZeroNativeBindings
import FCAppendix.Affine.Tail04.OrderedZeroSourceCommonMenuError

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroSourceUnusedPublic
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open OriginalActiveCompression OrderedZeroCommonMenuCount OriginalFlagCompression
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle NativeTypicalCount
open UnusedEmpiricalGuard UnusedFiniteCountError UnusedPublicPrices
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
local notation "originalLaw" => userLaw Γ
local notation "Qsrc" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => mixedMean Ds tag decode originalLaw
local notation "W" => reciprocalMean Ds tag decode originalLaw
local notation "lam" => OrderedZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
local notation "Bnom" => Central.B D.ξ
local notation "rad" => (fun reg=> radius D.ξ (centerMoment P reg))
local notation "bulkE" => SourceZeroBulkEvent.event D P

def bids (r : Fin N→ UserDraw 2) : Fin ((Ds).count (tags tag r) 1)→ℝ :=
  TypicalGuard.bids (SortedAllNoise.sortedBox (baseCommonRow Ds decode (tags tag r) r))

def count (r : Fin N→ UserDraw 2) (y : ℝ) : CountLaw 2 :=
  publicCount Qsrc ((Ds).count (tags tag r) 1)
    (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
    (bids D P t ht hdR H hUH N r) y

def bad (r : Fin N→ UserDraw 2) : ℝ :=
  (PublicScenario.scenarioLaw Qsrc ((Ds).count (tags tag r) 1)
    (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
    (bids D P t ht hdR H hUH N r)).prob
      (fun s=>¬StrongSafe Qsrc ((Ds).count (tags tag r) 1)
        (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
        D.U Bnom D.R D.Up D.width (γ D.ξ) (D.ξ/4)
        (bids D P t ht hdR H hUH N r) s)

def empirical (reg : Bool) (r : Fin N→ UserDraw 2) : ℝ :=
  averageError originalLaw N (tagFlag tag 1) (tagFlag tag 2) (tagFlag tag 3)
    (flag Ds decode reg) (fun x=>(decode x:ℝ)) r

def badBulk : Set (Fin N→ UserDraw 2) :=
  {r | (Probability.sampleCount bulkE r:ℝ)< P.bulkWeight*N/2}

lemma measurable_badBulk : MeasurableSet (badBulk D P N) :=
  measurableSet_lt ((measurable_of_countable (fun n : ℕ=>(n:ℝ))).comp
    (Probability.measurable_sampleCount bulkE (SourceZeroBulkEvent.measurable_event D P) N)) measurable_const

variable (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀reg,D.e0 reg=baseFlag P reg)
  (hθ : (D.regimeShare:ℝ)=P.theta) (hξh : D.ξ<1/2)
  (hR : D.R=Central.R D.ξ) (huB : 1+D.u<Central.B D.ξ)
  (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)
  (hsize : ∀reg,4*D.ξ/((N:ℝ)*centerMoment P reg)≤ γ D.ξ)

include hF hflags huB hsmall hξh in
lemma moments (reg : Bool) :
    |M reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 ∧
    |W reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 ∧
    centerMoment P reg/2≤ W reg := by
  have hh:=ZeroSourceMultiplierRectangle.actual_moment_error D P t ht πL π
    upperBid hupperBid hdR H hUH hfloor N hrare hF hflags huB reg
  have hm:=hh.1.trans (mul_le_mul_of_nonneg_left hsmall (centerMoment_pos P reg).le)
  have hw:=hh.2.trans (mul_le_mul_of_nonneg_left hsmall (centerMoment_pos P reg).le)
  have hm' : |M reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 := by
    have hm0 : |M reg-centerMoment P reg|≤centerMoment P reg*(D.ξ/1000) := hm
    nlinarith only [hm0]
  have hw' : |W reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 := by
    have hw0 : |W reg-centerMoment P reg|≤centerMoment P reg*(D.ξ/1000) := hw
    nlinarith only [hw0]
  refine ⟨hm',hw',?_⟩
  have hc:=(centerMoment_pos P reg)
  nlinarith [(abs_le.mp hw').1]

lemma numerator (reg : Bool) :
    populationNumerator D.ξ (99/200) (activeMean tag originalLaw) (M reg) (privateMean0 tag originalLaw)
      (keptShare P t reg)=meanNumerator P D.ξ (M reg) reg := by
  have ha : activeMean tag originalLaw=activeMass P.theta-upperMass P t :=
    ZeroSourceCommonMoments.active_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
  have hp : privateMean0 tag originalLaw=(partialMass+upperMass P t)/2 :=
    (ZeroSourceCommonMoments.private_means D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare).1
  rw [ha,hp]
  exact population_mean_eq P D.ξ t (M reg) ht.le reg

include hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize in
theorem row_guard (r : Fin N→ UserDraw 2) :
    bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r≤
      (1-(Qsrc).θ)*empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare false r/rad false+
      (Qsrc).θ*empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare true r/rad true := by
  let en:=OriginalUnusedCompression.sortedEnumeration Ds tag decode N r
  have hG:=ZeroSourceCommonMoments.source_nominal_guard D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hF hflags hξh hR huB hRp hsmall hmSmall
  have hp:=ZeroSourceCommonMoments.private_means D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare
  have he:=moments D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags hξh huB hsmall
  have hc2 : privateCount N (CommonFixedRowError.markedRow N r) (tagFlag tag 2) (fun _=>0)=
      (Ds).count (tags tag r) 2 := (OrderedZeroCommonMenuCount.count_privateCount Ds tag N r 2).symm
  have hc3 : privateCount N (CommonFixedRowError.markedRow N r) (tagFlag tag 3) (fun _=>0)=
      (Ds).count (tags tag r) 3 := (OrderedZeroCommonMenuCount.count_privateCount Ds tag N r 3).symm
  have hm0 (reg : Bool) : NativeTypicalCount.privateMean
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) reg ((Qsrc).marksLaw (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)))=
      keptShare P t reg*(min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) := by
    exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht D.u D.huU πL
      (NativeZeroNoiseSource.«partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor reg _
  have hm1 (reg : Bool) : NativeTypicalCount.privateMean
      (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) reg ((Qsrc).marksLaw (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)))=
      keptShare P t reg*(max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) := by
    exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht D.u D.huU πL
      (NativeZeroNoiseSource.«partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor reg _
  have hroom (reg : Bool) : 2*D.ξ/((N:ℝ)*W reg)≤ γ D.ξ := by
    have hc:=(centerMoment_pos P reg)
    have hh:=div_le_div_of_nonneg_left (by linarith [D.hξ] : 0≤2*D.ξ)
      (mul_pos (Nat.cast_pos.mpr hN) (half_pos hc))
      (mul_le_mul_of_nonneg_left (he reg).2.2 (Nat.cast_nonneg N))
    have heq : 2*D.ξ/((N:ℝ)*(centerMoment P reg/2))=4*D.ξ/((N:ℝ)*centerMoment P reg) := by ring
    rw [heq] at hh
    exact hh.trans (hsize reg)
  have hbroom (reg : Bool) : 4*rad reg≤ activeMean tag originalLaw-M reg := by
    have ha : activeMean tag originalLaw=activeMass P.theta-upperMass P t :=
      ZeroSourceCommonMoments.active_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
    rw [ha]
    exact UnusedMomentGeometry.exclusive_room P D.hξ hξh reg hmSmall (he reg).1
  have hceil (reg : Bool) :
      populationNumerator D.ξ (99/200) (activeMean tag originalLaw) (M reg) (privateMean0 tag originalLaw)
        (keptShare P t reg)/W reg+γ D.ξ≤1-D.ξ/2-D.ξ/4 := by
    rw [numerator D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare]
    exact UnusedMomentGeometry.multiplier_ceiling P D.hξ hξh reg (he reg).1 (he reg).2.1
  have hflag (reg : Bool) (j : Fin ((Ds).count (tags tag r) 1)) :
      sourceFlagProb (PublicScenario.e0 Qsrc reg) (Qsrc).B0
        (compressedBids _ en (fun j=>(decode (r j):ℝ))) j=
          (flag Ds decode reg (r (en j).val):ℝ) := rfl
  have hh:=OrderedUnusedEmpirical.probability_bound
    (μ:=originalLaw) (N:=N) (hN:=hN) (active:=tagFlag tag 1) (private0:=tagFlag tag 2) (private1:=tagFlag tag 3)
    (hactive:=measurable_tagFlag tag (E).measurable_coarseTag 1)
    (hprivate0:=measurable_tagFlag tag (E).measurable_coarseTag 2)
    (hprivate1:=measurable_tagFlag tag (E).measurable_coarseTag 3)
    (p:=flag Ds decode) (hp:=measurable_flag Ds decode (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH))
    (bid:=fun x=>(decode x:ℝ)) (hbid:=(ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH).subtype_val)
    (r:=r) (hfair:=hp.1.trans hp.2.symm) (ξ:=D.ξ) (ρ:=99/200)
    (B:=D.U) (B0:=Bnom) (R:=D.R) (Rp:=D.Up) (width:=D.width) (γ:=γ D.ξ)
    (share:=keptShare P t) (δ:=rad) (hξ:=⟨D.hξ.le,D.hξ1.le⟩) (hρ:=by norm_num)
    (hB0:=by unfold Central.B;linarith [D.hξ]) (hBB:=by rw [←hF];exact (base_active_le_physical D).trans D.hUF)
    (hw:=D.hw) (hwγ:=hwγ) (hγ1:=by unfold γ;linarith [D.hξ]) (G:=hG)
    (Q:=Qsrc) (hQc:=hcap) (hQξ:=rfl)
    (hmean0:=by intro reg; erw [hc2,hc3]; exact hm0 reg)
    (hmean1:=by intro reg; erw [hc2,hc3]; exact hm1 reg)
    (hphysical:=fun j _=>(decode (r j)).2.1) (hroom:=hroom) (e:=en) (hflag:=hflag)
    (a:=D.ξ/4) (hbalanceRoom:=hbroom) (hceiling:=hceil)
  simpa only [bad,empirical,bids,hc2,hc3,
    OriginalUnusedCompression.compressed_sorted] using! hh

include hN hF hflags huB in
theorem row_crossing (r : Fin N→ UserDraw 2)
    (hr : r∉badBulk D P N) (y : ℝ) (hy : 0≤ y) :
    (PublicScenario.scenarioLaw Qsrc ((Ds).count (tags tag r) 1)
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) (bids D P t ht hdR H hUH N r)).prob
        (Crossed Qsrc ((Ds).count (tags tag r) 1)
          (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
          D.U Bnom D.R D.Up D.width (γ D.ξ) (D.ξ/4) y (bids D P t ht hdR H hUH N r))≤
      2/(SourceUnusedConstants.epsilon P Bnom D.u*(P.bulkWeight*N/2))+
        (SourceUnusedConstants.cover D.ξ:ℝ)*Real.sqrt
          (2/(SourceUnusedConstants.epsilon P Bnom D.u*(P.bulkWeight*N/2)+1)) := by
  let J:=OriginalUnusedCompression.bulk Ds tag decode N bulkE r
  have hE : ∀x∈bulkE,tag x=1 := fun x hx=>(SourceZeroBulkEvent.member_shape D P hdR H hUH x hx).1
  have hcount : P.bulkWeight*(N:ℝ)/2≤(J.card:ℝ) := by
    rw [OriginalUnusedCompression.bulk_card Ds tag decode N bulkE hE r]
    exact le_of_not_gt hr
  have hJ:=OriginalUnusedCompression.bulk_nonempty Ds tag decode N bulkE hE r P.bulkWeight_pos hN (le_of_not_gt hr)
  have hB : 1< Bnom := by unfold Central.B;linarith [D.hξ]
  have he:=SourceUnusedConstants.epsilon_bounds P hB huB
  have hflagsJ (reg : Bool) (j : Fin ((Ds).count (tags tag r) 1)) (hj : j∈J) :
      SourceUnusedConstants.epsilon P Bnom D.u≤ sourceFlagProb (PublicScenario.e0 Qsrc reg) (Qsrc).B0 (bids D P t ht hdR H hUH N r) j ∧
      sourceFlagProb (PublicScenario.e0 Qsrc reg) (Qsrc).B0 (bids D P t ht hdR H hUH N r) j≤1-SourceUnusedConstants.epsilon P Bnom D.u := by
    have hb:=OriginalUnusedCompression.bulk_bid_bounds Ds tag decode N bulkE
      (fun x hx=>(SourceZeroBulkEvent.member_shape D P hdR H hUH x hx).2.2) r j hj
    have he0 : PublicScenario.e0 Qsrc reg=baseFlag P reg := hflags reg
    have hB0 : (Qsrc).B0=Central.B D.ξ := hF
    simpa only [he0,hB0,bids] using! SourceUnusedConstants.flag_bounds P hB huB _ reg j hb
  have hc:=SourceUnusedConstants.cover_bounds D.hξ
  have hh:=crossed_probability Qsrc ((Ds).count (tags tag r) 1)
    (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),
      max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) D.U Bnom D.R D.Up D.width (γ D.ξ) (D.ξ/4) y
    (bids D P t ht hdR H hUH N r) J hJ he.1 he.2
    (fun reg j hj=>(hflagsJ reg j hj).1) (fun reg j hj=>(hflagsJ reg j hj).2)
    D.hξ.le (by have hh:=D.hξ1;change D.ξ≤2;linarith) hy (by linarith [D.hξ])
    (fun j=>(SortedAllNoise.sortedBox (baseCommonRow Ds decode (tags tag r) r) j).2.1)
    5 (SourceUnusedConstants.cover D.ξ) hc.1 hc.2
  exact hh.trans (WeightedFlagBound.weighted_bound_antitone_card he.1
    (half_pos (mul_pos P.bulkWeight_pos (Nat.cast_pos.mpr hN))) hcount (SourceUnusedConstants.cover D.ξ))

include hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize in
theorem row_count_error (r : Fin N→ UserDraw 2) (hA : 0< (Ds).count (tags tag r) 1)
    (y : ℝ) (hy : y∈Icc (0:ℝ) Bnom) (f : Fin 3→ℝ) :
    |(count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y).expect f-
      (canonicalMixture Qsrc lam y).expect f|≤
      MenuError.oscillation f*((1-(Qsrc).θ)*((80/(D.ξ*W false)+2/rad false)*
          empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare false r+
          16/((N:ℝ)*W false))+
        (Qsrc).θ*((80/(D.ξ*W true)+2/rad true)*
          empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare true r+
          16/((N:ℝ)*W true)))+
      2*MenuError.oscillation f*(PublicScenario.scenarioLaw Qsrc ((Ds).count (tags tag r) 1)
        (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) (bids D P t ht hdR H hUH N r)).prob
        (Crossed Qsrc ((Ds).count (tags tag r) 1)
          (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3),max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3))
          D.U Bnom D.R D.Up D.width (γ D.ξ) (D.ξ/4) y (bids D P t ht hdR H hUH N r)) := by
  let en:=OriginalUnusedCompression.sortedEnumeration Ds tag decode N r
  have hG:=ZeroSourceCommonMoments.source_nominal_guard D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hF hflags hξh hR huB hRp hsmall hmSmall
  have hp:=ZeroSourceCommonMoments.private_means D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare
  have he:=moments D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags hξh huB hsmall
  have hc2 : privateCount N (CommonFixedRowError.markedRow N r) (tagFlag tag 2) (fun _=>0)=
      (Ds).count (tags tag r) 2 := (OrderedZeroCommonMenuCount.count_privateCount Ds tag N r 2).symm
  have hc3 : privateCount N (CommonFixedRowError.markedRow N r) (tagFlag tag 3) (fun _=>0)=
      (Ds).count (tags tag r) 3 := (OrderedZeroCommonMenuCount.count_privateCount Ds tag N r 3).symm
  have hm0 (reg : Bool) : NativeTypicalCount.privateMean
      (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) reg ((Qsrc).marksLaw (min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)))=
      keptShare P t reg*(min ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) := by
    exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht D.u D.huU πL
      (NativeZeroNoiseSource.«partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor reg _
  have hm1 (reg : Bool) : NativeTypicalCount.privateMean
      (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) reg ((Qsrc).marksLaw (max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)))=
      keptShare P t reg*(max ((Ds).count (tags tag r) 2) ((Ds).count (tags tag r) 3)) := by
    exact SourceTwoFocalGuard.originalMarks_mean P E rfl t ht D.u D.huU πL
      (NativeZeroNoiseSource.«partial» D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor reg _
  have hroom (reg : Bool) : 2*D.ξ/((N:ℝ)*W reg)≤ γ D.ξ := by
    have hc:=(centerMoment_pos P reg)
    have hh:=div_le_div_of_nonneg_left (by linarith [D.hξ] : 0≤2*D.ξ)
      (mul_pos (Nat.cast_pos.mpr hN) (half_pos hc))
      (mul_le_mul_of_nonneg_left (he reg).2.2 (Nat.cast_nonneg N))
    have heq : 2*D.ξ/((N:ℝ)*(centerMoment P reg/2))=4*D.ξ/((N:ℝ)*centerMoment P reg) := by ring
    rw [heq] at hh
    exact hh.trans (hsize reg)
  have hbroom (reg : Bool) : 4*rad reg≤ activeMean tag originalLaw-M reg := by
    have ha : activeMean tag originalLaw=activeMass P.theta-upperMass P t :=
      ZeroSourceCommonMoments.active_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
    rw [ha]
    exact UnusedMomentGeometry.exclusive_room P D.hξ hξh reg hmSmall (he reg).1
  have hceil (reg : Bool) :
      populationNumerator D.ξ (99/200) (activeMean tag originalLaw) (M reg) (privateMean0 tag originalLaw)
        (keptShare P t reg)/W reg+γ D.ξ≤1-D.ξ/2-D.ξ/4 := by
    rw [numerator D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare]
    exact UnusedMomentGeometry.multiplier_ceiling P D.hξ hξh reg (he reg).1 (he reg).2.1
  have hflag (reg : Bool) (j : Fin ((Ds).count (tags tag r) 1)) :
      sourceFlagProb (PublicScenario.e0 Qsrc reg) (Qsrc).B0
        (compressedBids _ en (fun j=>(decode (r j):ℝ))) j=
          (flag Ds decode reg (r (en j).val):ℝ) := rfl
  have hh:=OrderedUnusedEmpirical.public_count_error
    (μ:=originalLaw) (N:=N) (hN:=hN) (active:=tagFlag tag 1) (private0:=tagFlag tag 2) (private1:=tagFlag tag 3)
    (hactive:=measurable_tagFlag tag (E).measurable_coarseTag 1)
    (hprivate0:=measurable_tagFlag tag (E).measurable_coarseTag 2)
    (hprivate1:=measurable_tagFlag tag (E).measurable_coarseTag 3)
    (p:=flag Ds decode) (hp:=measurable_flag Ds decode (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH))
    (bid:=fun x=>(decode x:ℝ)) (hbid:=(ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH).subtype_val)
    (r:=r) (hfair:=hp.1.trans hp.2.symm) (ξ:=D.ξ) (ρ:=99/200)
    (B:=D.U) (B0:=Bnom) (R:=D.R) (Rp:=D.Up) (width:=D.width) (γ:=γ D.ξ)
    (share:=keptShare P t) (δ:=rad) (hξ:=⟨D.hξ.le,D.hξ1.le⟩) (hρ:=by norm_num)
    (hB0:=by unfold Central.B;linarith [D.hξ]) (hBB:=by rw [←hF];exact (base_active_le_physical D).trans D.hUF)
    (hw:=D.hw) (hwγ:=hwγ) (hγ1:=by unfold γ;linarith [D.hξ]) (G:=hG)
    (Q:=Qsrc) (hQc:=hcap) (hQξ:=rfl)
    (hmean0:=by intro reg; erw [hc2,hc3]; exact hm0 reg)
    (hmean1:=by intro reg; erw [hc2,hc3]; exact hm1 reg)
    (hphysical:=fun j _=>(decode (r j)).2.1) (hroom:=hroom) (e:=en) (hflag:=hflag)
    (a:=D.ξ/4) (hbalanceRoom:=hbroom) (hceiling:=hceil) (hξpos:=D.hξ) (hξh:=hξh)
    (hB01:=by unfold Central.B;linarith [D.hξ]) hA y hy f
  have hbr : compressedBids (fun j => tagFlag tag 1 (r j)) en (fun j=>(decode (r j):ℝ))=
      bids D P t ht hdR H hUH N r :=
    OriginalUnusedCompression.compressed_sorted Ds tag decode N r
  have hnum (reg : Bool) : populationNumerator D.ξ (99/200)
      (∫x,MenuError.indicator (tagFlag tag 1) x ∂originalLaw)
      (∫x,(flag Ds decode reg x:ℝ)*MenuError.indicator (tagFlag tag 1) x ∂originalLaw)
      (∫x,MenuError.indicator (tagFlag tag 2) x ∂originalLaw) (keptShare P t reg)=
      meanNumerator P D.ξ (M reg) reg :=
    numerator D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare reg
  simpa only [count,empirical,hc2,hc3,hbr,hnum,
    OrderedZeroSourceCommonMenuError.lambda] using! hh

include hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize in
theorem row_total_error (hbulk : 1≤ P.bulkWeight*(N:ℝ)/2)
    (r : Fin N→ UserDraw 2) (y : ℝ) (hy : y∈Icc (0:ℝ) Bnom) (f : Fin 3→ℝ) :
    |(count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y).expect f-
      (canonicalMixture Qsrc lam y).expect f|+
      4*MenuError.oscillation f*bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r≤
      MenuError.oscillation f*(
        SourceUnusedConstants.regimeCoefficient P D.ξ false*
          empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare false r+
        SourceUnusedConstants.regimeCoefficient P D.ξ true*
          empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare true r+
        SourceUnusedConstants.integerCoefficient P/(N:ℝ)+
        2*SourceUnusedConstants.crossingCoefficient P Bnom D.u D.ξ/Real.sqrt N+
        6*(if r∈badBulk D P N then (1:ℝ) else 0)) := by
  let E0:=empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare false r
  let E1:=empirical D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare true r
  have he0 : 0≤ E0 := by
    unfold E0 empirical UnusedEmpiricalGuard.averageError
    exact add_nonneg (CommonFixedRowError.empiricalAverage_nonnegative _ _ _ _ _ _ _ _) (by positivity)
  have he1 : 0≤ E1 := by
    unfold E1 empirical UnusedEmpiricalGuard.averageError
    exact add_nonneg (CommonFixedRowError.empiricalAverage_nonnegative _ _ _ _ _ _ _ _) (by positivity)
  have ho:=oscillation_nonneg f
  have hB : 1< Bnom := by unfold Central.B;linarith [D.hξ]
  have hK0:=SourceUnusedConstants.regimeCoefficient_nonneg P D.hξ false
  have hK1:=SourceUnusedConstants.regimeCoefficient_nonneg P D.hξ true
  have hC:=SourceUnusedConstants.crossingCoefficient_nonneg (ξ:=D.ξ) P hB huB
  have hc0:=centerMoment_pos P false
  have hc1:=centerMoment_pos P true
  have hI0 : 0≤ SourceUnusedConstants.integerCoefficient P/(N:ℝ) := by
    unfold SourceUnusedConstants.integerCoefficient;positivity
  have hrest : 0≤ SourceUnusedConstants.regimeCoefficient P D.ξ false*E0+
      SourceUnusedConstants.regimeCoefficient P D.ξ true*E1+
      SourceUnusedConstants.integerCoefficient P/(N:ℝ)+
      2*SourceUnusedConstants.crossingCoefficient P Bnom D.u D.ξ/Real.sqrt N := by positivity
  by_cases hr : r∈badBulk D P N
  · have hh:=count_expect_difference_bound
      (count D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r y) (canonicalMixture Qsrc lam y) f
    have hb : bad D P t ht πL π upperBid hupperBid hdR H hUH hfloor N r≤1 :=
      FiniteLaw.prob_le_one _ _
    simp only [if_pos hr,mul_one]
    have hh' :=mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num : (0:ℝ)≤4) ho)
    have hrest' :=mul_nonneg ho hrest
    dsimp only [E0,E1] at hrest'
    nlinarith
  · have hE : ∀x∈bulkE,tag x=1 := fun x hx=>(SourceZeroBulkEvent.member_shape D P hdR H hUH x hx).1
    have hJ:=OriginalUnusedCompression.bulk_nonempty Ds tag decode N bulkE hE r
      P.bulkWeight_pos hN (le_of_not_gt hr)
    have hA : 0< (Ds).count (tags tag r) 1 := by
      obtain ⟨j,_⟩:=hJ
      exact Nat.zero_lt_of_lt j.2
    have hh:=row_count_error D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
      hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize r hA y hy f
    have hg:=row_guard D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
      hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ hsize r
    have hx:=row_crossing D P t ht πL π upperBid hupperBid hdR H hUH hfloor N
      hN hF hflags huB r hr y hy.1
    have hx':=hx.trans (SourceUnusedConstants.crossing_rate P hB huB N hbulk)
    have hm:=moments D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
      hF hflags hξh huB hsmall
    have hcoef (reg : Bool) : 80/(D.ξ*W reg)+6/rad reg≤
        SourceUnusedConstants.regimeCoefficient P D.ξ reg := by
      have hcen:=centerMoment_pos P reg
      have hz:=div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤80)
        (mul_pos D.hξ (half_pos hcen))
        (mul_le_mul_of_nonneg_left (hm reg).2.2 D.hξ.le)
      have heq : 80/(D.ξ*(centerMoment P reg/2))=160/(D.ξ*centerMoment P reg) := by ring
      rw [heq] at hz
      change 80/(D.ξ*W reg)+6/rad reg≤160/(D.ξ*centerMoment P reg)+6/rad reg
      linarith only [hz]
    have hint (reg : Bool) : 16/((N:ℝ)*W reg)≤32/((N:ℝ)*centerMoment P reg) := by
      have hcen:=centerMoment_pos P reg
      have hz:=div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤16)
        (mul_pos (Nat.cast_pos.mpr hN) (half_pos hcen))
        (mul_le_mul_of_nonneg_left (hm reg).2.2 (Nat.cast_nonneg N))
      have heq : 16/((N:ℝ)*(centerMoment P reg/2))=32/((N:ℝ)*centerMoment P reg) := by ring
      rwa [heq] at hz
    have hu0:=add_le_add (mul_le_mul_of_nonneg_right (hcoef false) he0) (hint false)
    have hu1:=add_le_add (mul_le_mul_of_nonneg_right (hcoef true) he1) (hint true)
    have hm0 : (1-(Qsrc).θ)*(SourceUnusedConstants.regimeCoefficient P D.ξ false*E0+
        32/((N:ℝ)*centerMoment P false))≤
        SourceUnusedConstants.regimeCoefficient P D.ξ false*E0+32/((N:ℝ)*centerMoment P false) :=
      mul_le_of_le_one_left (by positivity) (by linarith [(Qsrc).θ_nonneg])
    have hm1 : (Qsrc).θ*(SourceUnusedConstants.regimeCoefficient P D.ξ true*E1+
        32/((N:ℝ)*centerMoment P true))≤
        SourceUnusedConstants.regimeCoefficient P D.ξ true*E1+32/((N:ℝ)*centerMoment P true) :=
      mul_le_of_le_one_left (by positivity) (Qsrc).θ_le_one
    have hu0':=mul_le_mul_of_nonneg_left hu0 (show 0≤1-(Qsrc).θ by linarith [(Qsrc).θ_le_one])
    have hu1':=mul_le_mul_of_nonneg_left hu1 (Qsrc).θ_nonneg
    have hguard:=mul_le_mul_of_nonneg_left hg (by positivity : 0≤4*MenuError.oscillation f)
    have hcross:=mul_le_mul_of_nonneg_left hx' (by positivity : 0≤2*MenuError.oscillation f)
    have hcombined:=mul_le_mul_of_nonneg_left (add_le_add (hu0'.trans hm0) (hu1'.trans hm1)) ho
    have hi : 32/((N:ℝ)*centerMoment P false)+32/((N:ℝ)*centerMoment P true)=
        SourceUnusedConstants.integerCoefficient P/(N:ℝ) := by
      unfold SourceUnusedConstants.integerCoefficient
      ring
    rw [if_neg hr,mul_zero,add_zero]
    dsimp only [E0,E1] at *
    rw [div_eq_mul_inv] at hg
    rw [←hi]
    simp only [div_eq_mul_inv] at hh hguard hcross hcombined ⊢
    nlinarith only [hh,hguard,hcross,hcombined]

end FCAppendix.Affine.Tail04.OrderedZeroSourceUnusedPublic
