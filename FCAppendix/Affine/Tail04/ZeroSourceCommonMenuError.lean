import FCAppendix.Affine.Tail04.ZeroSourceCommonMoments
import FCAppendix.Affine.Tail04.SourceCommonMenuError
import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.SourceMovingMenuRates

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroSourceCommonMenuError
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource LatentNoisyPopulation
open NativeActiveCompressedLaw OriginalActiveCompression ZeroCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open CommonFiniteCountError ZeroSourceCommonMoments SourceMenuIdentity
open scoped BigOperators

abbrev regimeCoefficient := SourceCommonMenuError.regimeCoefficient
abbrev commonCoefficient := SourceCommonMenuError.commonCoefficient
export SourceCommonMenuError
  (regimeCoefficient_nonnegative commonCoefficient_nonnegative coefficient_le_regime)

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+D.u< Central.B D.ξ)
  (hRp : D.Up≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (D.u) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => userLaw Γ
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "μP" => CompactSourceBidLaws.bidMarginal (Subtype.val (π 2))

def lambda (reg : Bool) : ℝ := SourceMenuError.meanNumerator P D.ξ (M reg) reg/W reg

include hfloor hrare in
include ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags in
theorem benchmark_source (reg : Bool) (b : Icc (1:ℝ) D.U) :
    benchmark Ds tag decode μ (99/200) (keptShare P t reg) reg b=
      idealRegime P D.ξ (M reg) (W reg) b reg := by
  have hn : populationNumerator D.ξ (99/200) (activeMean tag μ) (M reg) (privateMean0 tag μ)
      (keptShare P t reg)=SourceMenuError.meanNumerator P D.ξ (M reg) reg := by
    have ha : activeMean tag μ=activeMass P.theta-upperMass P t :=
      active_mean D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
    have hp0 : privateMean0 tag μ=(partialMass+upperMass P t)/2 :=
      (private_means D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare).1
    rw [ha,hp0]
    exact population_mean_eq P D.ξ t (M reg) ht.le reg
  unfold benchmark idealRegime
  apply FiniteLaw.ext
  intro k
  simp only [FiniteLaw.mixture]
  erw [hn,hflags reg,hF]
  rfl

include t ht πL π upperBid hupperBid hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ in
theorem original_count_error (reg : Bool) (b : Icc (1:ℝ) D.U) (f : Fin 3→ℝ) :
    |(averageCount Ds tag (E).measurable_coarseTag
        decode (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) μP N μ reg b).expect f-
      (idealRegime P D.ξ (M reg) (W reg) b reg).expect f|≤
      MenuError.oscillation f*SourceMovingMenuRates.rate
        (commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N := by
  have G := source_guard D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
    hF hflags hξh hR huB hRp hsmall hmSmall reg
  have hp := private_means D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare
  have hh := integrated_count_error Ds tag (E).measurable_coarseTag
    decode (ZeroNativeFiberProduct.measurable_commonProjection D P hdR H hUH) μP N μ hN (99/200) (keptShare P t reg)
    (γ D.ξ) (radius D.ξ (centerMoment P reg)) reg hcap (by norm_num) D.hξ1.le hwγ
    (by unfold γ;linarith [D.hξ]) (hp.1.trans hp.2.symm)
    (source_marks D P t ht πL π upperBid hupperBid hdR H hUH hfloor reg) G b f
  rw [benchmark_source D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hF hflags] at hh
  have hr := ZeroSourceCommonMoments.source_reciprocal D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hN
  have he := source_equal D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hN
  have hn := source_noLow D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare hN
  have hrec : radius D.ξ (centerMoment P reg)≤(W reg)/2 := G.radius_reciprocal
  have hk := @coefficient_le_regime D.ξ (b:ℝ) (W reg) (radius D.ξ (centerMoment P reg))
    D.hξ b.2.1 G.radius_pos (by linarith only [hrec])
  have hkc : regimeCoefficient P D.ξ reg≤ commonCoefficient P D.ξ := by
    cases reg <;> simp only [commonCoefficient,SourceCommonMenuError.commonCoefficient] <;>
      linarith [regimeCoefficient_nonnegative P D.hξ false,regimeCoefficient_nonnegative P D.hξ true]
  have hK : coefficient D.ξ b (W reg) (radius D.ξ (centerMoment P reg))≤ commonCoefficient P D.ξ :=
    hk.trans hkc
  have hZ : 0≤5/Real.sqrt (N:ℝ)+4/(N:ℝ) := by positivity
  have hc := mul_le_mul_of_nonneg_right hK hZ
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (oscillation_nonneg f)
  unfold SourceMovingMenuRates.rate
  have he' : 2*(75/(4*Real.sqrt (N:ℝ)))=75/(2*Real.sqrt (N:ℝ)) := by ring
  rw [←he']
  have hc' : coefficient (Ds).ξ (b:ℝ) (W reg) (radius D.ξ (centerMoment P reg))*
      (5/Real.sqrt (N:ℝ)+4/(N:ℝ))≤
      commonCoefficient P D.ξ*(5/Real.sqrt (N:ℝ)+4/(N:ℝ)) := hc
  linarith only [hc',hr,he,hn]

end FCAppendix.Affine.Tail04.ZeroSourceCommonMenuError
