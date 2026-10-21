import FCAppendix.Existence.R01Parameterization
import FCAppendix.Existence.R01CompactProduct
import Mathlib.MeasureTheory.Constructions.UnitInterval

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional

abbrev LowValue (d : ℝ) := Icc (0:ℝ) d

def bidRatio (ε : ℝ) (q : unitInterval) : ℝ :=
  ε+(1/(1+ε)-ε)*(q:ℝ)

theorem bidRatio_bounds {ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2) (q : unitInterval) :
    bidRatio ε q∈Icc ε (1/(1+ε)) := by
  have hden : 0<1+ε := by linarith
  have hlu : ε≤1/(1+ε) := (le_div_iff₀ hden).mpr (by nlinarith)
  unfold bidRatio
  constructor
  · nlinarith [q.property.1,mul_nonneg (sub_nonneg.mpr hlu) q.property.1]
  · nlinarith [q.property.2,mul_nonneg (sub_nonneg.mpr hlu) (sub_nonneg.mpr q.property.2)]

theorem noisyBid_bounds {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (w : LowValue d) (q z : unitInterval) :
    w.1*bidRatio ε q*(1+ε*z.1)∈Icc (0:ℝ) w.1 := by
  have hr:=bidRatio_bounds hε hsmall q
  have hr0 : 0≤bidRatio ε q := hε.le.trans hr.1
  have hz0 : 0≤1+ε*z.1 := by nlinarith [mul_nonneg hε.le z.property.1]
  have hnoise : 1+ε*z.1≤1+ε := by nlinarith [z.property.2]
  have hprod : bidRatio ε q*(1+ε*z.1)≤1 := by
    calc
      _≤bidRatio ε q*(1+ε):=mul_le_mul_of_nonneg_left hnoise hr0
      _≤1:=(le_div_iff₀ (by linarith : 0<1+ε)).mp hr.2
  constructor
  · exact mul_nonneg (mul_nonneg w.property.1 hr0) hz0
  · nlinarith [mul_le_mul_of_nonneg_left hprod w.property.1]

def noisyBid (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (x : (LowValue d × unitInterval) × unitInterval) : LowValue d :=
  ⟨x.1.1.1*bidRatio ε x.1.2*(1+ε*x.2.1),
    (noisyBid_bounds hε hsmall x.1.1 x.1.2 x.2).1,
    (noisyBid_bounds hε hsmall x.1.1 x.1.2 x.2).2.trans x.1.1.property.2⟩

theorem continuous_noisyBid (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) :
    Continuous (noisyBid d ε hε hsmall) := by
  apply Continuous.subtype_mk
  unfold bidRatio
  fun_prop

theorem noisyBid_pos {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/2)
    (x : (LowValue d × unitInterval) × unitInterval) (hw : 0<x.1.1.1) :
    0<(noisyBid d ε hε hsmall x).1 := by
  have hr:=hε.trans_le (bidRatio_bounds hε hsmall x.1.2).1
  exact mul_pos (mul_pos hw hr) (by nlinarith [mul_nonneg hε.le x.2.property.1])

def lowNoisyLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) : Law (A:=LowValue d) mu :=
  noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (noisyBid d ε hε hsmall) (continuous_noisyBid d ε hε hsmall) pi

theorem continuous_lowNoisyLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    Continuous (lowNoisyLaw d ε hε hsmall mu) :=
  continuous_noisyLaw mu (⟨volume,inferInstance⟩ : ProbabilityMeasure unitInterval)
    (noisyBid d ε hε hsmall) (continuous_noisyBid d ε hε hsmall)

end FCAppendix.Affine.LowBody
