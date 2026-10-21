import FCAppendix.Affine.Tail04.ZeroSourceMultiplierRectangle
import FCAppendix.Affine.Tail04.SourceGlobalMargins

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourceMultiplierFloor
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open FiniteTailNoisyGame SourceTailNoisyFixedPoint NativeZeroNoiseSource
open OriginalActiveCompression ZeroCommonMenuCount
open MenuError SourceMenuPopulation SourceMenuError SourceMomentRectangle ZeroSourceCommonMoments
open SourceMultiplierRectangle SourceGlobalMargins

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hUH : D.U< H)
  (hfloor : ∀ v,t< v→ H≤ upperBid v) (N : ℕ)
  (hrare : (1-D.ξ)*D.U+D.ξ*D.U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (hF : D.F=Central.B D.ξ) (hflags : ∀ reg,D.e0 reg=baseFlag P reg)
  (huB : 1+D.u< Central.B D.ξ)

local notation "Ds" => installOriginal D P t ht
local notation "E" => regions D P hdR H hUH
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => userLaw Γ
local notation "tag" => Observable.Regions.coarseTag E
local notation "decode" => ZeroNativeFiberProduct.commonProjection D P hdR H hUH
local notation "M" => mixedMean Ds tag decode μ
local notation "W" => reciprocalMean Ds tag decode μ
local notation "lam" => ZeroSourceCommonMenuError.lambda D P t ht πL π upperBid hupperBid hdR H hUH hfloor N hrare

include hF hflags huB in

theorem actual_floor (hξh : D.ξ<1/2)
    (hsmall : relativeError P.zeta D.u (Central.B D.ξ)≤ D.ξ/1000) (reg : Bool) :
    multiplierFloor D.ξ≤ lam reg := by
  have hm:=ZeroSourceMultiplierRectangle.actual_moment_error D P t ht πL π upperBid hupperBid
    hdR H hUH hfloor N hrare hF hflags huB reg
  have hc:=centerMoment_pos P reg
  have hM : |M reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 := by
    exact hm.1.trans (by nlinarith [mul_le_mul_of_nonneg_left hsmall hc.le])
  have hW : |W reg-centerMoment P reg|≤ D.ξ*centerMoment P reg/1000 := by
    exact hm.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hsmall hc.le])
  cases reg
  · have he : ((1-D.ξ/2)*centerMoment P false-D.ξ*P.theta^2/2)/centerMoment P false=
        1-D.ξ*(19/20) := by
      have hh := accept_center P D.ξ
      simp only [Central.lamA] at hh
      simpa only [centerMoment,Bool.false_eq_true,if_false,show 1-D.ξ*(19/20)=1-19*D.ξ/20 by ring] using hh
    have hn:=central_ratio_bounds ⟨D.hξ.le,hξh.le⟩
      (by norm_num : (19/20:ℝ)∈Icc (0:ℝ) 1) hc he
    have hr:=moment_ratio ⟨D.hξ.le,hξh.le⟩ hc hM hW hn
    rw [he] at hr
    change multiplierFloor D.ξ≤ meanNumerator P D.ξ (M false) false/(W false)
    unfold meanNumerator multiplierFloor at *
    simp only [Bool.false_eq_true,if_false] at *
    linarith [(abs_le.mp hr).1]
  · have he : ((1-D.ξ/2)*centerMoment P true-D.ξ*(partialMass+P.theta^2)/2)/centerMoment P true=
        1-D.ξ*(9/10) := by
      have hh := reject_center P D.ξ
      simp only [Central.lamR] at hh
      simpa only [centerMoment,Bool.true_eq,if_true,show 1-D.ξ*(9/10)=1-9*D.ξ/10 by ring] using hh
    have hn:=central_ratio_bounds ⟨D.hξ.le,hξh.le⟩
      (by norm_num : (9/10:ℝ)∈Icc (0:ℝ) 1) hc he
    have hr:=moment_ratio ⟨D.hξ.le,hξh.le⟩ hc hM hW hn
    rw [he] at hr
    change multiplierFloor D.ξ≤ meanNumerator P D.ξ (M true) true/(W true)
    unfold meanNumerator multiplierFloor at *
    simp only [if_true] at *
    linarith [(abs_le.mp hr).1,D.hξ]

end FCAppendix.Affine.Tail04.NativeSourceMultiplierFloor
