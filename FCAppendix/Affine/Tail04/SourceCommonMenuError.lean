import FCAppendix.Affine.Tail04.SourceCommonMoments
import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.SourceMovingMenuRates

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceCommonMenuError
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open NativeActiveCompressedLaw OriginalActiveCompression OriginalCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle
open CommonFiniteCountError SourceCommonMoments SourceMenuIdentity
open scoped BigOperators

def regimeCoefficient (P : ValueParameters) (ξ : ℝ) (reg : Bool) : ℝ :=
  6/(ξ*radius ξ (centerMoment P reg))+4/radius ξ (centerMoment P reg)

def commonCoefficient (P : ValueParameters) (ξ : ℝ) : ℝ :=
  regimeCoefficient P ξ false+regimeCoefficient P ξ true

lemma regimeCoefficient_nonnegative (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) (reg : Bool) :
    0≤ regimeCoefficient P ξ reg := by
  have hc := centerMoment_pos P reg
  unfold regimeCoefficient radius γ
  positivity

lemma commonCoefficient_nonnegative (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    0≤ commonCoefficient P ξ :=
  add_nonneg (regimeCoefficient_nonnegative P hξ false) (regimeCoefficient_nonnegative P hξ true)

lemma coefficient_le_regime {ξ b W δ : ℝ} (hξ : 0< ξ) (hb : 1≤ b)
    (hδ : 0< δ) (hW : 2*δ≤ W) :
    coefficient ξ b W δ≤6/(ξ*δ)+4/δ := by
  have hw : 0< W := by linarith
  have hden : 2*(ξ*δ)≤ ξ*b*W := by nlinarith [mul_nonneg hξ.le (sub_nonneg.mpr hb)]
  have h0 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤12)
    (by positivity : 0<2*(ξ*δ)) hden
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4)
    (by positivity : 0<2*δ) hW
  unfold coefficient
  have he0 : 12/(2*(ξ*δ))=6/(ξ*δ) := by ring
  have he1 : 4/(2*δ)=2/δ := by ring
  rw [he0] at h0
  rw [he1] at h1
  linarith [show 4/δ=2/δ+2/δ by ring]

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hcap : D.c=iidCapacity (99/200) N) (hN : 0< N)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (hξh : D.ξ<1/2) (hR : D.R=Central.R D.ξ)
  (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
  (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
  (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : D.width≤ γ D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hBH
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "tag" => latentTag D P hdR H hBH
local notation "decode" => latentBid D P hdR H hBH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "μP" => CompactSourceBidLaws.bidMarginal (Subtype.val (π 2))

def lambda (reg : Bool) : ℝ := SourceMenuError.meanNumerator P D.ξ (M reg) reg/W reg

include hfloor hrare hF hflags in
theorem benchmark_source (reg : Bool) (b : Icc (1:ℝ) D.B) :
    benchmark Ds tag decode μ (99/200) (keptShare P t reg) reg b=
      idealRegime P D.ξ (M reg) (W reg) b reg := by
  have hn : populationNumerator D.ξ (99/200) (activeMean tag μ) (M reg) (privateMean0 tag μ)
      (keptShare P t reg)=SourceMenuError.meanNumerator P D.ξ (M reg) reg := by
    rw [active_mean D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare,
      (private_means D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare).1]
    exact population_mean_eq P D.ξ t (M reg) ht.le reg
  unfold benchmark idealRegime
  apply FiniteLaw.ext
  intro k
  simp only [FiniteLaw.mixture]
  erw [hn,hflags reg,hF]
  rfl

include hfloor hrare hcap hN hF hflags hξh hR huB hRp hsmall hmSmall hwγ in
theorem original_count_error (reg : Bool) (b : Icc (1:ℝ) D.B) (f : Fin 3→ℝ) :
    |(averageCount Ds tag (measurable_latentTag D P hdR H hBH)
        decode (measurable_latentBid D P hdR H hBH) μP N μ reg b).expect f-
      (idealRegime P D.ξ (M reg) (W reg) b reg).expect f|≤
      MenuError.oscillation f*SourceMovingMenuRates.rate
        (commonCoefficient P D.ξ) (lowMass P.theta) P.bulkWeight N := by
  have G := source_guard D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    hF hflags hξh hR huB hRp hsmall hmSmall reg
  have hp := private_means D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
  have hh := integrated_count_error Ds tag (measurable_latentTag D P hdR H hBH)
    decode (measurable_latentBid D P hdR H hBH) μP N μ hN (99/200) (keptShare P t reg)
    (γ D.ξ) (radius D.ξ (centerMoment P reg)) reg hcap (by norm_num) D.hξ1.le hwγ
    (by unfold γ;linarith [D.hξ]) (hp.1.trans hp.2.symm)
    (source_marks D P t ht πL π upperBid hupperBid hdR H hBH hfloor reg) G b f
  rw [benchmark_source D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare hF hflags] at hh
  have hr := OriginalCommonReciprocal.original_common_reciprocal D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare hN
  have he := source_equal D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare hN
  have hn := source_noLow D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare hN
  have hk := @coefficient_le_regime D.ξ (b:ℝ) (W reg) (radius D.ξ (centerMoment P reg)) D.hξ b.2.1 G.radius_pos (by linarith [G.radius_reciprocal])
  have hkc : regimeCoefficient P D.ξ reg≤ commonCoefficient P D.ξ := by
    cases reg <;> unfold commonCoefficient <;>
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

end FCAppendix.Affine.Tail04.SourceCommonMenuError
