import FCAppendix.Affine.Tail04.SourceTailTaylor
import FCAppendix.Affine.Tail04.CapCompletion

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceTailCapGap
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuIdentity SourceMenuPopulation SourceTailTaylor

def stripWidth (Amax k : ℝ) : ℝ := (1/(2*Amax)-k)/2
def endpointRadius (Amin : ℝ) : ℝ := 1/(2*Amin)
def comparison (B A t : ℝ) : ℝ := B-1/(2*A*t)
def inwardCut (B Amax k t : ℝ) : ℝ := B-(k+stripWidth Amax k)/t

lemma stripWidth_pos {Amax k : ℝ} (hk : k<1/(2*Amax)) : 0< stripWidth Amax k := by
  unfold stripWidth
  linarith

lemma coefficient_distance {Amin A Amax k : ℝ}
    (hmin : 0< Amin) (hA : Amin≤ A) (hmax : A≤ Amax) (hk : k<1/(2*Amax)) :
    0< stripWidth Amax k ∧
      k+2*stripWidth Amax k≤1/(2*A) ∧
      k+stripWidth Amax k≤ endpointRadius Amin ∧
      1/(2*A)≤ endpointRadius Amin := by
  have ha : 0< A := hmin.trans_le hA
  have hamax : 0< Amax := ha.trans_le hmax
  have hlo : 1/(2*Amax)≤1/(2*A) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hhi : 1/(2*A)≤ endpointRadius Amin :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have he : k+2*stripWidth Amax k=1/(2*Amax) := by unfold stripWidth;ring
  have hd := stripWidth_pos hk
  exact ⟨hd,by rwa [he],by linarith,hhi⟩

theorem quadratic_gap {Amin A Amax B k t a b : ℝ}
    (hmin : 0< Amin) (hA : Amin≤ A) (hmax : A≤ Amax)
    (hk : k<1/(2*Amax)) (ht : 0< t)
    (hb : inwardCut B Amax k t≤ b)
    (ha : a∈Icc (comparison B A t) (comparison B A t+stripWidth Amax k/(4*t))) :
    (3/4)*Amin*(stripWidth Amax k)^2/t≤
      endpointCost A B t b-endpointCost A B t a := by
  let d := stripWidth Amax k
  have hd := coefficient_distance hmin hA hmax hk
  have hapos : 0< A := hmin.trans_le hA
  have hstar : (k+2*d)/t≤1/(2*A*t) := by
    have hh := div_le_div_of_nonneg_right hd.2.1 ht.le
    convert! hh using 1; ring
  have hcut : B-b≤(k+d)/t := by change B-(k+d)/t≤ b at hb;linarith
  have hx : d/t≤1/(2*A*t)-(B-b) := by
    have he : (k+2*d)/t-(k+d)/t=d/t := by ring
    linarith
  have hs : 0≤ a-comparison B A t ∧ a-comparison B A t≤(d/t)/4 := by
    have he : d/(4*t)=(d/t)/4 := by ring
    change comparison B A t≤ a ∧ a≤ comparison B A t+d/(4*t) at ha
    rw [he] at ha
    exact ⟨by linarith,by linarith⟩
  have hdt : 0≤ d/t := div_nonneg hd.1.le ht.le
  have hx2 : (d/t)^2≤(1/(2*A*t)-(B-b))^2 := by nlinarith
  have hs2 : (a-comparison B A t)^2≤(d/t)^2/16 := by nlinarith
  have hsq : (3/4)*(d/t)^2≤(B-b-1/(2*A*t))^2-(B-a-1/(2*A*t))^2 := by
    have he : (B-a-1/(2*A*t))^2=(a-comparison B A t)^2 := by unfold comparison;ring
    have he' : (B-b-1/(2*A*t))^2=(1/(2*A*t)-(B-b))^2 := by ring
    rw [he,he']
    nlinarith [sq_nonneg (d/t)]
  have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hapos.le ht.le)
  have hm := mul_le_mul_of_nonneg_right hA (show 0≤(3/4)*t*(d/t)^2 by positivity)
  rw [endpointCost_square A B t b hapos.ne' ht.ne',
    endpointCost_square A B t a hapos.ne' ht.ne']
  have he : (3/4)*Amin*d^2/t=(3/4)*Amin*t*(d/t)^2 := by
    field_simp [ht.ne']
  change (3/4)*Amin*d^2/t≤_
  rw [he]
  nlinarith only [hh,hm]

lemma comparison_order {Amin A Amax B k t a b : ℝ}
    (hmin : 0< Amin) (hA : Amin≤ A) (hmax : A≤ Amax)
    (hk : k<1/(2*Amax)) (ht : 0< t)
    (hb : inwardCut B Amax k t≤ b)
    (ha : a∈Icc (comparison B A t) (comparison B A t+stripWidth Amax k/(4*t))) : a≤ b := by
  have hd := coefficient_distance hmin hA hmax hk
  have hh := div_le_div_of_nonneg_right hd.2.1 ht.le
  have hstar : (k+2*stripWidth Amax k)/t≤1/(2*A*t) := by convert! hh using 1; ring
  have hquarter : stripWidth Amax k/(4*t)≤ stripWidth Amax k/t := by
    apply div_le_div_of_nonneg_left hd.1.le ht
    linarith
  dsimp [inwardCut] at hb
  dsimp [comparison] at ha
  have he : (k+2*stripWidth Amax k)/t=
      (k+stripWidth Amax k)/t+stripWidth Amax k/t := by ring
  linarith [ha.2]

lemma served_monotone (P : ValueParameters) {ξ lamA lamR a b : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2)
    (ha : a∈Icc (1:ℝ) (Central.B ξ)) (hb : b∈Icc (1:ℝ) (Central.B ξ)) (hab : a≤ b)
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    served P ξ lamA lamR a≤ served P ξ lamA lamR b := by
  have hterm (reg : Bool) (lam : ℝ) (hlo : (1-ξ)*Central.B ξ≤ lam) (hhi : lam≤1) :
      mixedProbability P ξ reg b*(1-exposure ξ lam b)^2≤
        mixedProbability P ξ reg a*(1-exposure ξ lam a)^2 := by
    have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
    have hlam0 : 0≤ lam := (mul_nonneg (by linarith) hB).trans hlo
    have hqa := exposure_bounds hξ (by linarith : ξ≤1) ha hlo hhi
    have hqb := exposure_bounds hξ (by linarith : ξ≤1) hb hlo hhi
    have hqord := (exposure_change hξ ⟨hlam0,hhi⟩ (show a∈Icc (1:ℝ) b from ⟨ha.1,hab⟩)).1
    have hf : (1-exposure ξ lam b)^2≤(1-exposure ξ lam a)^2 := by nlinarith [hqa.2,hqb.2]
    have he := baseFlag_bounds P reg
    have hs : (Central.B ξ-b)^2≤(Central.B ξ-a)^2 := by nlinarith [ha.2,hb.2]
    have hprob : mixedProbability P ξ reg b≤ mixedProbability P ξ reg a := by
      unfold mixedProbability
      simp only [div_pow]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs (sq_nonneg _)) he.1.le
    exact mul_le_mul hprob hf (sq_nonneg _) (mixedProbability_bounds P hξ ha reg).1
  have h0 := mul_le_mul_of_nonneg_left (hterm false lamA hlamA0 hlamA1)
    (show 0≤1-P.theta by linarith [P.theta_small])
  have h1 := mul_le_mul_of_nonneg_left (hterm true lamR hlamR0 hlamR1) P.theta_pos.le
  unfold served
  nlinarith only [h0,h1]

theorem analytic_strip_gap (P : ValueParameters) {ξ lamA lamR Amin Amax k t v a b : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (hmin : 0< Amin)
    (hA : Amin≤ leadingA P ξ lamA lamR) (hmax : leadingA P ξ lamA lamR≤ Amax)
    (hk : k<1/(2*Amax)) (ht : 0< t) (hvt : v≤ t)
    (ha : a∈Icc (1:ℝ) (Central.B ξ)) (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hcap : inwardCut (Central.B ξ) Amax k t≤ b)
    (hcompare : a∈Icc (comparison (Central.B ξ) (leadingA P ξ lamA lamR) t)
      (comparison (Central.B ξ) (leadingA P ξ lamA lamR) t+stripWidth Amax k/(4*t)))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1)
    (hbudget : 2*taylorConstant ξ (endpointRadius Amin)/t^2≤
      Amin*(stripWidth Amax k)^2/(4*t)) :
    Amin*(stripWidth Amax k)^2/(2*t)≤ menuUtility P ξ lamA lamR v a-menuUtility P ξ lamA lamR v b := by
  have hd := coefficient_distance hmin hA hmax hk
  have hapos := hmin.trans_le hA
  have hrad : 0≤ endpointRadius Amin := by unfold endpointRadius;positivity
  have hnearB : Central.B ξ-b≤ endpointRadius Amin/t := by
    have hh := div_le_div_of_nonneg_right hd.2.2.1 ht.le
    dsimp [inwardCut] at hcap
    linarith
  have hnearA : Central.B ξ-a≤ endpointRadius Amin/t := by
    have hh := div_le_div_of_nonneg_right hd.2.2.2 ht.le
    have he : (1/(2*leadingA P ξ lamA lamR))/t=1/(2*leadingA P ξ lamA lamR*t) := by ring
    rw [he] at hh
    dsimp [comparison] at hcompare
    linarith [hcompare.1]
  have hEA := scaled_remainder P hξ hξh ht hrad ha hnearA hlamA0 hlamA1 hlamR0 hlamR1
  have hEB := scaled_remainder P hξ hξh ht hrad hb hnearB hlamA0 hlamA1 hlamR0 hlamR1
  have hq := quadratic_gap hmin hA hmax hk ht hcap hcompare
  have hg : Amin*(stripWidth Amax k)^2/(2*t)≤
      menuUtility P ξ lamA lamR t a-menuUtility P ξ lamA lamR t b := by
    have h0 := (abs_le.mp hEA).2
    have h1 := (abs_le.mp hEB).1
    have he : (3/4)*Amin*(stripWidth Amax k)^2/t-
        Amin*(stripWidth Amax k)^2/(4*t)=Amin*(stripWidth Amax k)^2/(2*t) := by ring
    unfold cost at h0 h1
    linear_combination hq+h1+h0+hbudget
  have hab := comparison_order hmin hA hmax hk ht hcap hcompare
  exact cap_gap_transfers_down (served P ξ lamA lamR) (payment P ξ lamA lamR) t v b a _ hvt
    (served_monotone P hξ hξh ha hb hab hlamA0 hlamA1 hlamR0 hlamR1) hg

end FCAppendix.Affine.Tail04.SourceTailCapGap
