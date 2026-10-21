import FCAppendix.Probability.FiniteAveraging
import FCAppendix.Affine.Tail04.CentralMargins
import FCAppendix.Affine.Tail04.TypicalMeanCount

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

theorem clip_lipschitz (x y : ℝ) :
    |probabilityClip x-probabilityClip y|≤|x-y| := by
  have hlo := neg_le_abs (x-y)
  have hhi := le_abs_self (x-y)
  have hn := abs_nonneg (x-y)
  unfold probabilityClip
  simp only [min_def,max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

theorem unit_abs_sub_le_one {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    |x-y|≤1 := abs_le.mpr ⟨by linarith [hx.1,hy.2],by linarith [hx.2,hy.1]⟩

def oscillation (f : Fin 3 → ℝ) : ℝ := max |f 1-f 0| |f 2-f 1|

theorem oscillation_nonneg (f : Fin 3 → ℝ) : 0≤ oscillation f :=
  (abs_nonneg _).trans (le_max_left _ _)

def coinMoment (p q : ℝ) (f : Fin 3 → ℝ) : ℝ :=
  (1-p)*(1-q)*f 0+(p*(1-q)+(1-p)*q)*f 1+p*q*f 2

theorem convex_increment_bound (f : Fin 3 → ℝ) {p : ℝ} (hp : p∈Icc (0:ℝ) 1) :
    |(1-p)*(f 1-f 0)+p*(f 2-f 1)|≤ oscillation f := by
  calc
    _ ≤ |(1-p)*(f 1-f 0)|+|p*(f 2-f 1)| := abs_add_le _ _
    _ = (1-p)*|f 1-f 0|+p*|f 2-f 1| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith [hp.2]),abs_of_nonneg hp.1]
    _ ≤ (1-p)*oscillation f+p*oscillation f :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [hp.2]))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hp.1)
    _ = _ := by ring

theorem coinMoment_lipschitz (f : Fin 3 → ℝ) {p q p' q' : ℝ}
    (_hp : p∈Icc (0:ℝ) 1) (hq : q∈Icc (0:ℝ) 1)
    (hp' : p'∈Icc (0:ℝ) 1) (_hq' : q'∈Icc (0:ℝ) 1) :
    |coinMoment p q f-coinMoment p' q' f|≤ oscillation f*(|p-p'|+|q-q'|) := by
  have he : coinMoment p q f-coinMoment p' q' f=
      (p-p')*((1-q)*(f 1-f 0)+q*(f 2-f 1))+
        (q-q')*((1-p')*(f 1-f 0)+p'*(f 2-f 1)) := by
    unfold coinMoment
    ring
  rw [he]
  calc
    _ ≤ |(p-p')*((1-q)*(f 1-f 0)+q*(f 2-f 1))|+
        |(q-q')*((1-p')*(f 1-f 0)+p'*(f 2-f 1))| := abs_add_le _ _
    _ ≤ |p-p'| *oscillation f+|q-q'| *oscillation f := by
      rw [abs_mul,abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (convex_increment_bound f hq) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (convex_increment_bound f hp') (abs_nonneg _))
    _ = _ := by ring

def clippedMarginal (ξ b numerator reciprocal : ℝ) : ℝ :=
  probabilityClip ((1-numerator/reciprocal/b)/ξ)

theorem clippedMarginal_bounds (ξ b n w : ℝ) :
    clippedMarginal ξ b n w∈Icc (0:ℝ) 1 := probabilityClip_bounds _

def clippedCount (ξ b n0 n1 w : ℝ) : CountLaw 2 :=
  twoCoinCountLaw (clippedMarginal ξ b n0 w) (clippedMarginal ξ b n1 w)
    (clippedMarginal_bounds _ _ _ _).1 (clippedMarginal_bounds _ _ _ _).2
    (clippedMarginal_bounds _ _ _ _).1 (clippedMarginal_bounds _ _ _ _).2

theorem clippedCount_expect (ξ b n0 n1 w : ℝ) (f : Fin 3 → ℝ) :
    (clippedCount ξ b n0 n1 w).expect f=
      coinMoment (clippedMarginal ξ b n0 w) (clippedMarginal ξ b n1 w) f :=
  twoCoinCountLaw_expect _ _ _ _ _ _ f

theorem raw_marginal_difference (ξ b n w n' w' : ℝ) :
    (1-n/w/b)/ξ-(1-n'/w'/b)/ξ=-(n/w-n'/w')/(ξ*b) := by
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem clippedMarginal_error {ξ b n w nbar wbar : ℝ}
    (hξ : 0< ξ) (hb : 0< b) (hwbar : 0< wbar) (hnbar : |nbar|≤ wbar) :
    |clippedMarginal ξ b n w-clippedMarginal ξ b nbar wbar|≤
      (2/(ξ*b*wbar))*(|n-nbar|+|w-wbar|)+(2/wbar)*|w-wbar| := by
  by_cases hw : wbar/2≤ w
  · have hratio := Central.ratio_error (half_pos hwbar) hw hwbar hnbar
      (le_rfl : |n-nbar|≤|n-nbar|) (le_rfl : |w-wbar|≤|w-wbar|)
    have hclip := clip_lipschitz ((1-n/w/b)/ξ) ((1-nbar/wbar/b)/ξ)
    rw [raw_marginal_difference,abs_div,abs_neg,abs_of_pos (mul_pos hξ hb)] at hclip
    have hmain : |clippedMarginal ξ b n w-clippedMarginal ξ b nbar wbar|≤
        (2/(ξ*b*wbar))*(|n-nbar|+|w-wbar|) := by
      calc
        _ ≤ |n/w-nbar/wbar|/(ξ*b) := hclip
        _ ≤ ((|n-nbar|+|w-wbar|)/(wbar/2))/(ξ*b) :=
          div_le_div_of_nonneg_right hratio (mul_pos hξ hb).le
        _ = _ := by field_simp [hξ.ne',hb.ne',hwbar.ne']
    exact hmain.trans (le_add_of_nonneg_right (by positivity))
  · have hsmall : w< wbar/2 := lt_of_not_ge hw
    have habs : wbar/2≤|w-wbar| := by
      have hh := neg_le_abs (w-wbar)
      linarith
    have htail : 1≤(2/wbar)*|w-wbar| := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hwbar).mpr (by linarith)
    exact (unit_abs_sub_le_one (clippedMarginal_bounds _ _ _ _)
      (clippedMarginal_bounds _ _ _ _)).trans
        (htail.trans (le_add_of_nonneg_left (by positivity)))

theorem clippedCount_error (f : Fin 3 → ℝ) {ξ b n0 n1 w nbar wbar : ℝ}
    (hξ : 0< ξ) (hb : 0< b) (hwbar : 0< wbar) (hnbar : |nbar|≤ wbar) :
    |(clippedCount ξ b n0 n1 w).expect f-(clippedCount ξ b nbar nbar wbar).expect f|≤
      oscillation f*((2/(ξ*b*wbar))*(|n0-nbar|+|n1-nbar|+2*|w-wbar|)+
        (4/wbar)*|w-wbar|) := by
  rw [clippedCount_expect,clippedCount_expect]
  have hh := coinMoment_lipschitz f (clippedMarginal_bounds ξ b n0 w)
    (clippedMarginal_bounds ξ b n1 w) (clippedMarginal_bounds ξ b nbar wbar)
    (clippedMarginal_bounds ξ b nbar wbar)
  have h0 := clippedMarginal_error (n:=n0) (w:=w) hξ hb hwbar hnbar
  have h1 := clippedMarginal_error (n:=n1) (w:=w) hξ hb hwbar hnbar
  exact hh.trans (by
    have he := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (oscillation_nonneg f)
    convert! he using 1
    ring)

section Integral
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

theorem measurable_clippedCount_expect (ξ b : ℝ) (n0 n1 w : Ω→ℝ)
    (hn0 : Measurable n0) (hn1 : Measurable n1) (hw : Measurable w) (f : Fin 3→ℝ) :
    Measurable (fun x => (clippedCount ξ b (n0 x) (n1 x) (w x)).expect f) := by
  have hm (n : Ω→ℝ) (hn : Measurable n) :
      Measurable (fun x => clippedMarginal ξ b (n x) (w x)) :=
    continuous_probabilityClip.measurable.comp
      ((measurable_const.sub ((hn.div hw).div_const b)).div_const ξ)
  have hm0 := hm n0 hn0
  have hm1 := hm n1 hn1
  simp only [clippedCount_expect,coinMoment]
  fun_prop

theorem integrable_clippedCount_expect (ξ b : ℝ) (n0 n1 w : Ω→ℝ)
    (hn0 : Measurable n0) (hn1 : Measurable n1) (hw : Measurable w) (f : Fin 3→ℝ) :
    Integrable (fun x => (clippedCount ξ b (n0 x) (n1 x) (w x)).expect f) ν := by
  apply Integrable.of_bound (measurable_clippedCount_expect ξ b n0 n1 w hn0 hn1 hw f).aestronglyMeasurable
    (∑ r,‖f r‖)
  exact Eventually.of_forall (fun x => (clippedCount ξ b (n0 x) (n1 x) (w x)).norm_expect_le_sum_norm f)

theorem integrated_clippedCount_error (f : Fin 3→ℝ) (ξ b nbar wbar E0 E1 EW : ℝ)
    (n0 n1 w : Ω→ℝ) (hn0 : Measurable n0) (hn1 : Measurable n1) (hw : Measurable w)
    (hi0 : Integrable n0 ν) (hi1 : Integrable n1 ν) (hiw : Integrable w ν)
    (hξ : 0< ξ) (hb : 0< b) (hwbar : 0< wbar) (hnbar : |nbar|≤ wbar)
    (hE0 : (∫ x,|n0 x-nbar| ∂ν)≤ E0) (hE1 : (∫ x,|n1 x-nbar| ∂ν)≤ E1)
    (hEW : (∫ x,|w x-wbar| ∂ν)≤ EW) :
    (∫ x,|(clippedCount ξ b (n0 x) (n1 x) (w x)).expect f-
        (clippedCount ξ b nbar nbar wbar).expect f| ∂ν)≤
      oscillation f*((2/(ξ*b*wbar))*(E0+E1+2*EW)+(4/wbar)*EW) := by
  let K := 2/(ξ*b*wbar)
  let C := 4/wbar
  have hK : 0≤ K := by dsimp [K];positivity
  have hC : 0≤ C := by dsimp [C];positivity
  have hia0 : Integrable (fun x => |n0 x-nbar|) ν := (hi0.sub (integrable_const nbar)).abs
  have hia1 : Integrable (fun x => |n1 x-nbar|) ν := (hi1.sub (integrable_const nbar)).abs
  have hiaw : Integrable (fun x => |w x-wbar|) ν := (hiw.sub (integrable_const wbar)).abs
  have hia01 : Integrable (fun x => |n0 x-nbar|+|n1 x-nbar|) ν := hia0.add hia1
  have hiaAll : Integrable (fun x => |n0 x-nbar|+|n1 x-nbar|+2*|w x-wbar|) ν :=
    hia01.add (hiaw.const_mul 2)
  have hleft := ((integrable_clippedCount_expect ν ξ b n0 n1 w hn0 hn1 hw f).sub
    (integrable_const ((clippedCount ξ b nbar nbar wbar).expect f))).abs
  have hright := (hiaAll.const_mul K).add (hiaw.const_mul C)
  calc
    _ ≤ ∫ x,oscillation f*(K*(|n0 x-nbar|+|n1 x-nbar|+2*|w x-wbar|)+C*|w x-wbar|) ∂ν :=
      integral_mono_ae hleft (hright.const_mul (oscillation f))
        (Eventually.of_forall (fun x => clippedCount_error f hξ hb hwbar hnbar))
    _ = oscillation f*(K*((∫ x,|n0 x-nbar| ∂ν)+(∫ x,|n1 x-nbar| ∂ν)+
        2*(∫ x,|w x-wbar| ∂ν))+C*(∫ x,|w x-wbar| ∂ν)) := by
      rw [integral_const_mul,integral_add (hiaAll.const_mul K)
        (hiaw.const_mul C),integral_const_mul,integral_const_mul,
        integral_add hia01 (hiaw.const_mul 2),integral_add hia0 hia1,integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add
        (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add hE0 hE1) (mul_le_mul_of_nonneg_left hEW (by norm_num))) hK)
        (mul_le_mul_of_nonneg_left hEW hC)) (oscillation_nonneg f)

end Integral
end FCAppendix.Affine.Tail04.MenuError
