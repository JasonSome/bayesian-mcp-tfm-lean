import FCAppendix.Affine.Tail04.SourceMenuIdentity
import FCAppendix.Affine.Tail04.MovingBoundary

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceTailTaylor
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues SourceMenuIdentity SourceMenuPopulation

def leadingA (P : ValueParameters) (ξ lamA lamR : ℝ) : ℝ :=
  ((1-P.theta)*baseFlag P false*(1-exposure ξ lamA (Central.B ξ))^2+
    P.theta*baseFlag P true*(1-exposure ξ lamR (Central.B ξ))^2)/(Central.B ξ-1)^2

def cost (P : ValueParameters) (ξ lamA lamR v b : ℝ) : ℝ :=
  v-menuUtility P ξ lamA lamR v b

def remainder (ξ lam t B b : ℝ) : ℝ :=
  t*((1-exposure ξ lam b)^2-(1-exposure ξ lam B)^2)+
    b*((1-2*ξ)*(exposure ξ lam b)^2-(1-exposure ξ lam b)^2)

lemma exposure_change {ξ lam b B : ℝ} (hξ : 0< ξ) (hlam : lam∈Icc (0:ℝ) 1)
    (hb : b∈Icc (1:ℝ) B) :
    0≤ exposure ξ lam B-exposure ξ lam b ∧
      exposure ξ lam B-exposure ξ lam b≤(B-b)/ξ := by
  have hb0 : 0< b := by linarith [hb.1]
  have hB0 : 0< B := hb0.trans_le hb.2
  have hdiff : exposure ξ lam B-exposure ξ lam b=lam*(B-b)/(ξ*b*B) := by
    unfold exposure
    field_simp [hξ.ne',hb0.ne',hB0.ne']
    ring
  have hd : 0≤ B-b := sub_nonneg.mpr hb.2
  rw [hdiff]
  constructor
  · exact div_nonneg (mul_nonneg hlam.1 hd) (by positivity)
  · calc
      _ ≤ (B-b)/(ξ*b*B) := div_le_div_of_nonneg_right
        (by nlinarith [hlam.2]) (by positivity)
      _ ≤ (B-b)/ξ := div_le_div_of_nonneg_left hd hξ (by
        have hbb : 1≤ b*B := by
          have hh := mul_le_mul hb.1 (hb.1.trans hb.2) (by norm_num : (0:ℝ)≤1)
            (by linarith [hb.1])
          simpa only [one_mul] using hh
        nlinarith)

lemma square_difference {x y : ℝ} (hx : x∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    |x^2-y^2|≤2*|x-y| := by
  have hsum : |x+y|≤2 := by
    rw [abs_of_nonneg (add_nonneg hx.1 hy.1)]
    linarith only [hx.2,hy.2]
  rw [show x^2-y^2=(x-y)*(x+y) by ring,abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (x-y))]

lemma remainder_bound {ξ lam t B b : ℝ} (hξ : 0< ξ) (hξh : ξ≤1/2)
    (ht : 0≤ t) (hb : b∈Icc (1:ℝ) B) (hlam0 : (1-ξ)*B≤ lam) (hlam1 : lam≤1) :
    |remainder ξ lam t B b|≤2*t*(B-b)/ξ+B := by
  have hB : 1≤ B := hb.1.trans hb.2
  have hlamnon : 0≤ lam := (mul_nonneg (by linarith) (by linarith)).trans hlam0
  have hq := exposure_bounds hξ (by linarith : ξ≤1) hb hlam0 hlam1
  have hqB := exposure_bounds hξ (by linarith : ξ≤1) ⟨hB,le_rfl⟩ hlam0 hlam1
  have hchange := exposure_change hξ ⟨hlamnon,hlam1⟩ hb
  have hs := square_difference
    (show 1-exposure ξ lam b∈Icc (0:ℝ) 1 by constructor <;> linarith [hq.1,hq.2])
    (show 1-exposure ξ lam B∈Icc (0:ℝ) 1 by constructor <;> linarith [hqB.1,hqB.2])
  have hfs : |(1-exposure ξ lam b)^2-(1-exposure ξ lam B)^2|≤2*((B-b)/ξ) := by
    have he : (1-exposure ξ lam b)-(1-exposure ξ lam B)=
        exposure ξ lam B-exposure ξ lam b := by ring
    rw [he,abs_of_nonneg hchange.1] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left hchange.2 (by norm_num))
  have hq2 : (exposure ξ lam b)^2≤1 := by nlinarith [hq.1,hq.2]
  have hf2 : (1-exposure ξ lam b)^2≤1 := by nlinarith [hq.1,hq.2]
  have heta : 0≤1-2*ξ ∧ 1-2*ξ≤1 := ⟨by linarith,by linarith⟩
  have heq0 : 0≤(1-2*ξ)*(exposure ξ lam b)^2 := mul_nonneg heta.1 (sq_nonneg _)
  have heq1 : (1-2*ξ)*(exposure ξ lam b)^2≤1 :=
    (mul_le_mul_of_nonneg_right heta.2 (sq_nonneg _)).trans (by simpa only [one_mul] using hq2)
  have hunit : |(1-2*ξ)*(exposure ξ lam b)^2-(1-exposure ξ lam b)^2|≤1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (1-exposure ξ lam b)]
  unfold remainder
  calc
    _ ≤ |t*((1-exposure ξ lam b)^2-(1-exposure ξ lam B)^2)|+
        |b*((1-2*ξ)*(exposure ξ lam b)^2-(1-exposure ξ lam b)^2)| := abs_add_le _ _
    _ ≤ t*(2*((B-b)/ξ))+b*1 := by
      simp only [abs_mul,abs_of_nonneg ht,abs_of_nonneg (show 0≤ b by linarith [hb.1])]
      exact add_le_add (mul_le_mul_of_nonneg_left hfs ht)
        (mul_le_mul_of_nonneg_left hunit (by linarith [hb.1]))
    _ = 2*t*(B-b)/ξ+b := by ring
    _ ≤ 2*t*(B-b)/ξ+B := add_le_add le_rfl hb.2

theorem cost_remainder_identity (P : ValueParameters) (ξ lamA lamR t b : ℝ) :
    cost P ξ lamA lamR t b-endpointCost (leadingA P ξ lamA lamR) (Central.B ξ) t b=
      (Central.B ξ-b)^2/(Central.B ξ-1)^2*
        ((1-P.theta)*baseFlag P false*remainder ξ lamA t (Central.B ξ) b+
          P.theta*baseFlag P true*remainder ξ lamR t (Central.B ξ) b) := by
  unfold cost menuUtility payment served duplicates mixedProbability leadingA endpointCost remainder
  simp only [div_pow]
  ring

theorem uniform_remainder (P : ValueParameters) {ξ lamA lamR t b : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (ht : 0≤ t)
    (hb : b∈Icc (1:ℝ) (Central.B ξ))
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    |cost P ξ lamA lamR t b-endpointCost (leadingA P ξ lamA lamR) (Central.B ξ) t b|≤
      (Central.B ξ-b)^2/(Central.B ξ-1)^2*(2*t*(Central.B ξ-b)/ξ+Central.B ξ) := by
  let K := 2*t*(Central.B ξ-b)/ξ+Central.B ξ
  have hK : 0≤ K := by
    have hd : 0≤ Central.B ξ-b := sub_nonneg.mpr hb.2
    have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
    dsimp [K]
    positivity
  have hA := remainder_bound hξ hξh ht hb hlamA0 hlamA1
  have hR := remainder_bound hξ hξh ht hb hlamR0 hlamR1
  have heA := baseFlag_bounds P false
  have heR := baseFlag_bounds P true
  have hθ0 := P.theta_pos.le
  have hθ1 : P.theta≤1 := by linarith [P.theta_small]
  have ha0 : 0≤(1-P.theta)*baseFlag P false :=
    mul_nonneg (sub_nonneg.mpr hθ1) heA.1.le
  have hr0 : 0≤ P.theta*baseFlag P true := mul_nonneg hθ0 heR.1.le
  have hsum : (1-P.theta)*baseFlag P false+P.theta*baseFlag P true≤1 := by
    nlinarith [mul_le_mul_of_nonneg_left heA.2.le (sub_nonneg.mpr hθ1),
      mul_le_mul_of_nonneg_left heR.2.le hθ0]
  rw [cost_remainder_identity,abs_mul,abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ |(1-P.theta)*baseFlag P false*remainder ξ lamA t (Central.B ξ) b|+
        |P.theta*baseFlag P true*remainder ξ lamR t (Central.B ξ) b| := abs_add_le _ _
    _ ≤ ((1-P.theta)*baseFlag P false+P.theta*baseFlag P true)*K := by
      simp only [abs_mul,abs_of_nonneg (sub_nonneg.mpr hθ1),abs_of_nonneg hθ0,
        abs_of_nonneg heA.1.le,abs_of_nonneg heR.1.le]
      nlinarith [mul_le_mul_of_nonneg_left hA ha0,mul_le_mul_of_nonneg_left hR hr0]
    _ ≤ K := by nlinarith [mul_le_mul_of_nonneg_right hsum hK]

def taylorConstant (ξ L : ℝ) : ℝ :=
  L^2/(Central.B ξ-1)^2*(2*L/ξ+Central.B ξ)

theorem scaled_remainder (P : ValueParameters) {ξ lamA lamR t b L : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (ht : 0< t) (hL : 0≤ L)
    (hb : b∈Icc (1:ℝ) (Central.B ξ)) (hnear : Central.B ξ-b≤ L/t)
    (hlamA0 : (1-ξ)*Central.B ξ≤ lamA) (hlamA1 : lamA≤1)
    (hlamR0 : (1-ξ)*Central.B ξ≤ lamR) (hlamR1 : lamR≤1) :
    |cost P ξ lamA lamR t b-endpointCost (leadingA P ξ lamA lamR) (Central.B ξ) t b|≤
      taylorConstant ξ L/t^2 := by
  have hh := uniform_remainder P hξ hξh ht.le hb hlamA0 hlamA1 hlamR0 hlamR1
  have hd : 0≤ Central.B ξ-b := sub_nonneg.mpr hb.2
  have hLt : 0≤ L/t := div_nonneg hL ht.le
  have hs : (Central.B ξ-b)^2≤(L/t)^2 := by nlinarith
  have htprod : t*(Central.B ξ-b)≤ L := by nlinarith [(le_div_iff₀ ht).mp hnear]
  have hcoef : 2*t*(Central.B ξ-b)/ξ+Central.B ξ≤2*L/ξ+Central.B ξ := by
    have h2 : 2*t*(Central.B ξ-b)≤2*L := by linarith only [htprod]
    exact add_le_add (div_le_div_of_nonneg_right h2 hξ.le) le_rfl
  have hB : 0≤ Central.B ξ := by unfold Central.B;linarith
  have hnon : 0≤2*t*(Central.B ξ-b)/ξ+Central.B ξ := by positivity
  apply hh.trans
  calc
    _ ≤ ((L/t)^2/(Central.B ξ-1)^2)*(2*L/ξ+Central.B ξ) :=
      mul_le_mul (div_le_div_of_nonneg_right hs (sq_nonneg _)) hcoef hnon (by positivity)
    _ = taylorConstant ξ L/t^2 := by
      unfold taylorConstant
      rw [div_pow]
      ring

end FCAppendix.Affine.Tail04.SourceTailTaylor
