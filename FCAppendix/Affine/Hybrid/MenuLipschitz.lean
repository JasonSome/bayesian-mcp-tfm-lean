import FCAppendix.Affine.Hybrid.HarmonicStability

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set

def broadcastExposureModulus (eta W U : ℝ) : ℝ := 2*W+2*U*(1+|1-eta|)

lemma broadcastExposureModulus_nonneg {eta W U : ℝ} (hW : 0 ≤ W) (hU : 0 ≤ U) :
    0 ≤ broadcastExposureModulus eta W U := by
  unfold broadcastExposureModulus
  positivity

lemma independentTwo_lipschitz {eta v b q q' W U : ℝ}
    (hv : |v| ≤ W) (hb : |b| ≤ U) (hq : q ∈ Icc (0:ℝ) 1) (hq' : q' ∈ Icc (0:ℝ) 1) :
    |independentTwo eta v b q-independentTwo eta v b q'| ≤
      broadcastExposureModulus eta W U*|q-q'| := by
  have hW : 0 ≤ W := (abs_nonneg _).trans hv
  have hU : 0 ≤ U := (abs_nonneg _).trans hb
  have hs : |q+q'| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hq.1,hq.2,hq'.1,hq'.2]
  have ht : |2-q-q'| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hq.1,hq.2,hq'.1,hq'.2]
  have he : independentTwo eta v b q-independentTwo eta v b q' =
      (v*(2-q-q')-b*(2-(1-eta)*(q+q')))*(q-q') := by
    unfold independentTwo
    ring
  have hfactor : |v*(2-q-q')-b*(2-(1-eta)*(q+q'))| ≤ broadcastExposureModulus eta W U := by
    calc
      _ ≤ |v*(2-q-q')|+|b*(2-(1-eta)*(q+q'))| := abs_sub _ _
      _ = |v| *|2-q-q'|+|b| *|2-(1-eta)*(q+q')| := by rw [abs_mul,abs_mul]
      _ ≤ W*2+U*(2+|1-eta| *2) := by
        have hx : |2-(1-eta)*(q+q')| ≤ 2+|1-eta| *2 := by
          calc
            _ ≤ |(2:ℝ)|+|(1-eta)*(q+q')| := abs_sub _ _
            _ = 2+|1-eta| *|q+q'| := by rw [abs_mul]; norm_num
            _ ≤ _ := by gcongr
        gcongr
      _ = _ := by unfold broadcastExposureModulus; ring
  rw [he,abs_mul]
  exact mul_le_mul_of_nonneg_right hfactor (abs_nonneg _)

lemma independentTwo_abs_le {eta v b q W U : ℝ}
    (hv : |v| ≤ W) (hb : |b| ≤ U) (hq : q ∈ Icc (0:ℝ) 1) :
    |independentTwo eta v b q| ≤ broadcastExposureModulus eta W U := by
  have hh := independentTwo_lipschitz (eta := eta) hv hb hq
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hz : independentTwo eta v b 0 = 0 := by simp only [independentTwo,mul_zero,
    zero_pow (by decide : 2 ≠ 0),sub_zero]
  rw [hz,sub_zero,sub_zero,abs_of_nonneg hq.1] at hh
  exact hh.trans (mul_le_of_le_one_right (broadcastExposureModulus_nonneg
    ((abs_nonneg v).trans hv) ((abs_nonneg b).trans hb)) hq.2)

lemma broadcast_owner_difference_bound {eta v b q W U : ℝ}
    (hv : |v| ≤ W) (hb : |b| ≤ U) (hq : q ∈ Icc (0:ℝ) 1) :
    |(v-b)-independentTwo eta v b q| ≤ W+U+broadcastExposureModulus eta W U := by
  exact (abs_sub _ _).trans (add_le_add
    ((abs_sub v b).trans (add_le_add hv hb)) (independentTwo_abs_le hv hb hq))

lemma singleton_exposure_lipschitz {v b q q' W U : ℝ} (hv : |v| ≤ W) (hb : |b| ≤ U) :
    |(v-b)*q-(v-b)*q'| ≤ (W+U)*|q-q'| := by
  rw [←mul_sub,abs_mul]
  exact mul_le_mul_of_nonneg_right ((abs_sub v b).trans (add_le_add hv hb)) (abs_nonneg _)

lemma singleton_owner_difference_bound {v b q W U : ℝ}
    (hv : |v| ≤ W) (hb : |b| ≤ U) (hq : q ∈ Icc (0:ℝ) 1) :
    |(v-b)/2-(v-b)*q| ≤ W+U := by
  have he : (v-b)/2-(v-b)*q = (v-b)*(1/2-q) := by ring
  have hq' : |(1:ℝ)/2-q| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hq.1,hq.2]
  rw [he,abs_mul]
  exact (mul_le_mul_of_nonneg_right ((abs_sub v b).trans (add_le_add hv hb))
    (abs_nonneg _)).trans (mul_le_of_le_one_right
      (add_nonneg ((abs_nonneg v).trans hv) ((abs_nonneg b).trans hb)) hq')

end FCAppendix.Affine.Hybrid
