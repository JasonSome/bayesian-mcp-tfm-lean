import FCAppendix.Affine.LowBody.PhysicalWeakPayoff
import FCAppendix.Affine.LowBody.NoisyDeviations
import Mathlib.MeasureTheory.Measure.DiracProba

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory
open Existence.Distributional

abbrev NoiseBox := Icc (0:ℝ) (1/4)

def deviationBaseBid (B : ℝ) (e : NoiseBox) (w : ℝ) : ℝ :=
  max (e.1*w) (min (w/(1+e.1)) B)

theorem deviationBaseBid_bounds (B : ℝ) (e : NoiseBox) {w : ℝ} (hw : 0≤w) :
    deviationBaseBid B e w∈Icc 0 (w/(1+e.1)) := by
  have hd : 0<1+e.1 := by linarith [e.property.1]
  have he : e.1≤1/(1+e.1) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [e.property.1,e.property.2,sq_nonneg (e.1-1/4)]
  have hmul : e.1*w≤w/(1+e.1) := by
    have hh:=mul_le_mul_of_nonneg_right he hw
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh
  exact ⟨(mul_nonneg e.property.1 hw).trans (le_max_left _ _),
    max_le hmul (min_le_left _ _)⟩

def deviationPhysicalBid (d B : ℝ) (e : NoiseBox) (w : LowValue d) (z : unitInterval) : LowValue d := by
  let x:=deviationBaseBid B e w.1
  have hx:=deviationBaseBid_bounds B e w.property.1
  have hd : 0<1+e.1 := by linarith [e.property.1]
  have hz0 : 0≤1+e.1*z.1 := by nlinarith [mul_nonneg e.property.1 z.property.1]
  have hz1 : 1+e.1*z.1≤1+e.1 := by nlinarith [e.property.1,z.property.2]
  refine ⟨x*(1+e.1*z.1),mul_nonneg hx.1 hz0,?_⟩
  have hh : x*(1+e.1)≤w.1 := (le_div_iff₀ hd).mp hx.2
  exact (mul_le_mul_of_nonneg_left hz1 hx.1).trans (hh.trans w.property.2)

@[fun_prop] theorem continuous_deviationPhysicalBid (d B : ℝ) :
    Continuous (fun t : NoiseBox×LowValue d×unitInterval=>deviationPhysicalBid d B t.1 t.2.1 t.2.2) := by
  apply Continuous.subtype_mk
  unfold deviationBaseBid
  have hd : ∀t : NoiseBox×LowValue d×unitInterval,1+t.1.1≠0 :=
    fun t=>ne_of_gt (by linarith [t.1.property.1])
  have hdiv : Continuous (fun t : NoiseBox×LowValue d×unitInterval=>t.2.1.1/(1+t.1.1)) :=
    continuous_snd.fst.subtype_val.div (continuous_const.add continuous_fst.subtype_val) hd
  exact ((continuous_fst.subtype_val.mul continuous_snd.fst.subtype_val).max
    (hdiv.min continuous_const)).mul
    (continuous_const.add (continuous_fst.subtype_val.mul continuous_snd.snd.subtype_val))

def zeroNoiseBox : NoiseBox := ⟨0,by norm_num⟩

theorem deviationPhysicalBid_zero (d B : ℝ) (hB : 0<B) (w : LowValue d) (z : unitInterval) :
    (deviationPhysicalBid d B zeroNoiseBox w z).1=min w.1 B := by
  change max (0*w.1) (min (w.1/(1+0)) B)*(1+0*z.1)=_
  simp only [zero_mul,add_zero,div_one,mul_one]
  exact max_eq_right (le_min w.property.1 hB.le)

theorem deviationPhysicalBid_choice {d ε : ℝ} (hε : 0<ε) (hsmall : ε≤1/4)
    (B : ℝ) (w : LowValue d) (z : unitInterval) :
    noisyBid d ε hε (hsmall.trans (by norm_num)) ((w,choiceAtRatio ε hε hsmall (B/w.1)),z)=
      deviationPhysicalBid d B ⟨ε,hε.le,hsmall⟩ w z := by
  apply Subtype.ext
  change w.1*bidRatio ε (choiceAtRatio ε hε hsmall (B/w.1))*(1+ε*z.1)=
    deviationBaseBid B ⟨ε,hε.le,hsmall⟩ w.1*(1+ε*z.1)
  congr 1
  rw [bidRatio_choiceAtRatio]
  by_cases hw : w.1=0
  · simp [hw,deviationBaseBid]
  · have hwp : 0<w.1:=lt_of_le_of_ne w.property.1 (Ne.symm hw)
    unfold clippedRatio deviationBaseBid
    rw [mul_max_of_nonneg _ _ w.property.1,mul_min_of_nonneg _ _ w.property.1]
    congr 1
    · ring
    · congr 1
      · ring
      · exact mul_div_cancel₀ B hw

end FCAppendix.Affine.LowBody
