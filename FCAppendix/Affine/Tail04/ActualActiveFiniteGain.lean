import FCAppendix.Affine.Tail04.CompactPromotionErrors
import FCAppendix.Affine.Tail04.EqualPrivateFiniteLoss

noncomputable section
namespace FCAppendix.Affine.Tail04.ActualActiveFiniteGain
open MeasureTheory Set Classical
open TypicalFinitePromotion ActualFallbackPromotion CompactPromotionErrors
open EqualPrivateSignal SortedAllNoise AtypicalFittingFiniteLoss
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def marginal0 (P : TypicalCountParameters) (b : ι → ℝ) (i target : ι) (z : ι → Bool) : ℝ :=
  meanMarginal P.xi P.c (P.owner0 (targetMixedSet target z).card) P.privateMean0
    (targetMixedSet target z).card (mixedReciprocalSum (targetMixedSet target z) b) (b i)

def marginal1 (P : TypicalCountParameters) (b : ι → ℝ) (i target : ι) (z : ι → Bool) : ℝ :=
  meanMarginal P.xi P.c (P.owner1 (targetMixedSet target z).card) P.privateMean1
    (targetMixedSet target z).card (mixedReciprocalSum (targetMixedSet target z) b) (b i)

def GoodFlags (P : TypicalCountParameters) (phi : ℕ → ℝ → unitInterval)
    (b : ι → ℝ) (i : ι) (qmin : ℝ) (z : ι → Bool) : Prop :=
  (∀ target,targetTypicalWeight phi b target z=1) ∧
    qmin≤ marginal0 P b i i z ∧ qmin≤ marginal1 P b i i z

def WeightFlags (phi : ℕ → ℝ → unitInterval) (b : ι → ℝ) (z : ι → Bool) : Prop :=
  ∀ target,targetTypicalWeight phi b target z=1

def badProbability (P : TypicalCountParameters) (phi : ℕ → ℝ → unitInterval)
    (e0 F : ℝ) (b : ι → ℝ) (i : ι) (qmin : ℝ) : ℝ :=
  (independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
    (sourceFlagProb_le_one e0 F b)).prob (fun z => ¬GoodFlags P phi b i qmin z)

def badWeightProbability (phi : ℕ → ℝ → unitInterval) (e0 F : ℝ) (b : ι → ℝ) : ℝ :=
  (independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
    (sourceFlagProb_le_one e0 F b)).prob (fun z => ¬WeightFlags phi b z)

omit [Fintype ι] [Nonempty ι] in
lemma rankTransfer_le_one (b : ι → ℝ) (i j : ι) (y : ℝ) : Hybrid.rankTransfer b i y j≤1 := by
  unfold Hybrid.rankTransfer Hybrid.rankScore
  split_ifs <;> norm_num

lemma fallbackWeight_le_badWeightProbability (phi : ℕ → ℝ → unitInterval)
    (e0 F : ℝ) (b : ι → ℝ) :
    fallbackWeight phi b (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
      (sourceFlagProb_le_one e0 F b)≤ badWeightProbability phi e0 F b := by
  apply FiniteLaw.expect_le_const
  intro target
  apply FiniteLaw.expect_mono
  intro z
  by_cases hz : WeightFlags phi b z
  · simp only [if_neg (not_not.mpr hz),hz target,sub_self]
    exact le_rfl
  · simp only [if_pos hz]
    linarith [(targetTypicalWeight_bounds phi b target z).1]

theorem finite_rank_gain_lower (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 F eta v L qmin : ℝ)
    (he0 : 0≤ eta) (he1 : eta≤1) (hL : 0≤ L) (hq : 0≤ qmin)
    (b d : ι → ℝ) (i : ι) (y : ℝ) (hy : b i< y)
    (hd : ∀ j,b j∈Icc (b i) y → d i=d j) (hv : d i≤ v) (hbid : L≤ d i) :
    (eta*L*qmin^2)*((sourceFlagProb e0 F d i)^2/2-badProbability P phi e0 F d i qmin)*
        (crossed b i y).card/Hybrid.rankDenominator ι≤
      (∑ j,Hybrid.rankTransfer b i y j*
        targetExchangeGain P.mixedCount phi d (sourceFlagProb e0 F d)
          (sourceFlagProb_nonneg e0 F d) (sourceFlagProb_le_one e0 F d) i j v eta he0 he1)/
        Hybrid.rankDenominator ι := by
  let p := sourceFlagProb e0 F d
  let g := eta*L*qmin^2
  let β := badProbability P phi e0 F d i qmin
  have hg : 0≤ g := by dsimp [g];positivity
  have hβ : 0≤ β := FiniteLaw.prob_nonneg _ _
  have hp2 : 0≤ g*(p i)^2 := mul_nonneg hg (sq_nonneg _)
  have hb2 : 0≤ g*β := mul_nonneg hg hβ
  have hpoint (j : ι) : (if j∈crossed b i y then g*((p i)^2/2-β) else 0)≤
      Hybrid.rankTransfer b i y j*targetExchangeGain P.mixedCount phi d p
        (sourceFlagProb_nonneg e0 F d) (sourceFlagProb_le_one e0 F d) i j v eta he0 he1 := by
    by_cases hj : j∈crossed b i y
    · have hji := (Finset.mem_filter.mp hj).2.1
      have hjb := (Finset.mem_filter.mp hj).2.2
      have he : p j=p i := by simp only [p,sourceFlagProb,hd j hjb]
      have hx := source_targetExchangeGain_lower P phi d p
        (sourceFlagProb_nonneg e0 F d) (sourceFlagProb_le_one e0 F d) i j hji.symm (hd j hjb)
        (GoodFlags P phi d i qmin) (fun z hz => hz.1 i) hv hL hbid he0 he1 hq
        (fun z _ _ hz => hz.2.1) (fun z _ _ hz => hz.2.2)
      rw [he] at hx
      have hm := mul_le_mul_of_nonneg_left hx (Hybrid.rankTransfer_nonneg b i j y hy.le)
      have hpos := mul_le_mul_of_nonneg_right (Hybrid.rankTransfer_half_le_between b i j y hji hy hjb) hp2
      have hneg := mul_le_mul_of_nonneg_right (rankTransfer_le_one b i j y) hb2
      rw [if_pos hj]
      change g*((p i)^2/2-β)≤_
      change Hybrid.rankTransfer b i y j*(g*(p i*p i-β))≤_ at hm
      rw [←pow_two] at hm
      nlinarith only [hm,hpos,hneg]
    · rw [if_neg hj]
      exact mul_nonneg (Hybrid.rankTransfer_nonneg b i j y hy.le)
        (targetExchangeGain_nonneg P.mixedCount phi d p (sourceFlagProb_nonneg e0 F d)
          (sourceFlagProb_le_one e0 F d) i j hv (hL.trans hbid) he0 he1)
  have hs := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset ι)) => hpoint j)
  have he : (∑ j : ι,if j∈crossed b i y then g*((p i)^2/2-β) else 0)=
      g*((p i)^2/2-β)*(crossed b i y).card := by
    rw [Finset.sum_ite_mem,Finset.univ_inter]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  rw [he] at hs
  exact div_le_div_of_nonneg_right hs Hybrid.rankDenominator_pos.le

lemma crossed_card_eq_crossingCount {N : ℕ} (b : Fin N → ℝ) (i : Fin N) (y : ℝ) :
    ((crossed b i y).card:ℝ)=crossingCount b i y := by
  simp only [crossed,crossingCount,Finset.sum_boole]

variable {N : ℕ} [Nonempty (Fin N)]

theorem actual_raw_finite_gain (H0 H1 c : ℕ) {ξ B R Rp width e0 F v L qmin : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2) (hsep : (1-ξ)*B<1)
    (b d : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (hno : ∀ j k,j≠k → b j≠b k) (i : Fin N) (hiv : b i≤ v)
    (y : ℝ) (hy : b i< y) (hyB : y≤ B)
    (hd : ∀ j,b j∈Icc (b i) y → d i=d j)
    (hL : 0≤ L) (hq : 0≤ qmin) (hdv : d i≤ v) (hdb : L≤ d i) :
    let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
    let phi := effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
    let K := sortedFallback N H0 H1 c ξ ν0 ν1 b i
    let a := Function.update b i y
    (((1-2*ξ)*L*qmin^2)*((sourceFlagProb e0 F d i)^2/2-badProbability P phi e0 F d i qmin)/
        Hybrid.rankDenominator (Fin N)-(v+2*B)*badWeightProbability phi e0 F a)*
      crossingCount b i y-
      variation (conditionalUtility P phi e0 F (1-2*ξ) v (by linarith) (by linarith) i K) b d-
      variation (conditionalUtility P phi e0 F (1-2*ξ) v (by linarith) (by linarith) i K) a d-
      2*(y-b i)≤
      affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 a i) v y (1-2*ξ) (by linarith) (by linarith)-
      affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 b i) v (b i) (1-2*ξ) (by linarith) (by linarith) := by
  dsimp only
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  let cut := effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
  have hmain := actual_joined_finite_transfer H0 H1 c (R:=R) (Rp:=Rp) (width:=width)
    (e0:=e0) (F:=F) reg lowPresent ν0 ν1
    hξ0 hξ1 hsep b d hb hno i hiv y hy hyB hd
  have hgain := finite_rank_gain_lower P cut e0 F (1-2*ξ) v L qmin
    (by linarith) (by linarith) hL hq b d i y hy hd hdv hdb
  rw [crossed_card_eq_crossingCount] at hgain
  have hfall := fallbackWeight_le_badWeightProbability cut e0 F (Function.update b i y)
  have hv0 : 0≤ v := (by norm_num : (0:ℝ)≤1).trans ((hb i).1.trans hiv)
  have hB0 : 0≤ B := (by norm_num : (0:ℝ)≤1).trans ((hb i).1.trans (hb i).2)
  have hm := mul_le_mul_of_nonneg_right hfall
    (mul_nonneg (by positivity : 0≤ v+2*B) (crossingCount_nonneg b i y))
  dsimp only at hmain
  dsimp only [P,cut] at hgain hm
  rw [mul_div_right_comm] at hgain
  nlinarith only [hmain,hgain,hm]

omit [Nonempty (Fin N)] in

theorem frozen_bad_probability_le (P : TypicalCountParameters)
    (phi : ℕ → ℝ → unitInterval) (e0 F : ℝ) (b d : Fin N → ℝ) (i : Fin N) (qmin : ℝ) :
    badProbability P phi e0 F d i qmin≤
      (independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
        (sourceFlagProb_le_one e0 F b)).prob (fun z => ¬GoodFlags P phi d i qmin z)+
      flagVariation e0 F b d := by
  have h := (abs_le.mp (flag_probability_difference e0 F b d
    (fun z => ¬GoodFlags P phi d i qmin z))).1
  change _≤_ at h
  dsimp [badProbability]
  linarith

end FCAppendix.Affine.Tail04.ActualActiveFiniteGain
