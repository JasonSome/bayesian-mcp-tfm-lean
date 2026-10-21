import FCAppendix.Affine.Tail04.SortedFallbackFiniteLoss
import FCAppendix.Affine.Tail04.TypicalFinitePromotion

noncomputable section
namespace FCAppendix.Affine.Tail04.ActualFallbackPromotion
open MeasureTheory Set Classical
open EqualPrivateSignal SortedAllNoise AtypicalFittingFiniteLoss SortedFallbackFiniteLoss
open TypicalFinitePromotion
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def fallbackWeight (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ j,0≤ p j) (hp1 : ∀ j,p j≤1) : ℝ :=
  (Hybrid.rankLaw b).expect (fun t => (independentFlagLaw p hp0 hp1).expect
    (fun z => 1-targetTypicalWeight phi b t z))

lemma fallbackWeight_bounds (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ j,0≤ p j) (hp1 : ∀ j,p j≤1) :
    0≤ fallbackWeight phi b p hp0 hp1 ∧ fallbackWeight phi b p hp0 hp1≤1 := by
  constructor
  · apply FiniteLaw.expect_nonneg
    intro t
    exact FiniteLaw.expect_nonneg _ (fun z => sub_nonneg.mpr (targetTypicalWeight_bounds phi b t z).2)
  · apply FiniteLaw.expect_le_const
    intro t
    apply FiniteLaw.expect_le_const
    intro z
    linarith [(targetTypicalWeight_bounds phi b t z).1]

theorem fallback_change (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (phi : ℕ → ℝ → unitInterval) (b p : ι → ℝ)
    (hp0 : ∀ j,0≤ p j) (hp1 : ∀ j,p j≤1) (i : ι)
    (F G : CountLaw 2) (v eta : ℝ) (he0 : 0≤ eta) (he1 : eta≤1) :
    affineCountUtility (typicalRankCount Q phi b p hp0 hp1 i G) v (b i) eta he0 he1-
      affineCountUtility (typicalRankCount Q phi b p hp0 hp1 i F) v (b i) eta he0 he1=
      fallbackWeight phi b p hp0 hp1*
        (affineCountUtility G v (b i) eta he0 he1-affineCountUtility F v (b i) eta he0 he1) := by
  simp only [affineCountUtility,CountLaw.utility,typicalRankCount,conditionalTargetCount,
    FiniteLaw.expect_finiteMix,FiniteLaw.expect_mixture]
  rw [←FiniteLaw.expect_sub]
  calc
    _=(Hybrid.rankLaw b).expect (fun t => (independentFlagLaw p hp0 hp1).expect
      (fun z => (1-targetTypicalWeight phi b t z)*
        (G.expect (fun r => userPayoff v (b i) 0 (Schedule.affine 2 eta he0 he1).charge
          (Schedule.once 2).charge r.val)-F.expect (fun r => userPayoff v (b i) 0
            (Schedule.affine 2 eta he0 he1).charge (Schedule.once 2).charge r.val)))) := by
      apply FiniteLaw.expect_congr
      intro t
      rw [←FiniteLaw.expect_sub]
      apply FiniteLaw.expect_congr
      intro z
      ring
    _=_ := by simp only [FiniteLaw.expect_mul_const,fallbackWeight]

def effectivePhi (lowPresent : Bool) (phi : ℕ → ℝ → unitInterval) :
    ℕ → ℝ → unitInterval := if lowPresent then phi else fun _ _ => 0

lemma typicalRankCount_zero (Q : ℕ → ℝ → ℝ → CountLaw 2)
    (b p : ι → ℝ) (hp0 : ∀ j,0≤ p j) (hp1 : ∀ j,p j≤1)
    (i : ι) (fallback : CountLaw 2) :
    typicalRankCount Q (fun _ _ => 0) b p hp0 hp1 i fallback=fallback := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [typicalRankCount,conditionalTargetCount,FiniteLaw.expect_finiteMix,
    FiniteLaw.expect_mixture,targetTypicalWeight]
  simp

lemma fixedLaw_utility_antitone (C : CountLaw 2) {eta v b y : ℝ}
    (he0 : 0≤ eta) (he1 : eta≤1) (hy : b≤ y) :
    affineCountUtility C v y eta he0 he1≤ affineCountUtility C v b eta he0 he1 := by
  unfold affineCountUtility CountLaw.utility
  apply FiniteLaw.expect_mono
  intro r
  dsimp only [userPayoff]
  have h := mul_le_mul_of_nonneg_right hy ((Schedule.affine 2 eta he0 he1).nonneg r.val (by omega))
  linarith

variable {N : ℕ} [Nonempty (Fin N)]

lemma rawCount_eq_effective (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (b : Fin N → ℝ) (i : Fin N) :
    UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 b i=
      typicalRankCount (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1).mixedCount
        (effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
        b (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b)
        i (sortedFallback N H0 H1 c ξ ν0 ν1 b i) := by
  cases lowPresent
  · exact (typicalRankCount_zero _ _ _ _ _ _ _).symm
  · rfl

theorem actual_joined_finite_transfer (H0 H1 c : ℕ) {ξ B R Rp width e0 F v : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ0 : 0≤ ξ) (hξ1 : ξ≤1/2) (hsep : (1-ξ)*B<1)
    (b d : Fin N → ℝ) (hb : ∀ j,b j∈Icc (1:ℝ) B)
    (hno : ∀ j k,j≠k → b j≠b k)
    (i : Fin N) (hiv : b i≤ v) (y : ℝ) (hy : b i< y) (hyB : y≤ B)
    (hd : ∀ j,b j∈Icc (b i) y → d i=d j) :
    let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
    let phi := effectivePhi lowPresent
      (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
    let K := sortedFallback N H0 H1 c ξ ν0 ν1 b i
    let a := Function.update b i y
    let w := fallbackWeight phi a (sourceFlagProb e0 F a)
      (sourceFlagProb_nonneg e0 F a) (sourceFlagProb_le_one e0 F a)
    (∑ j,Hybrid.rankTransfer b i y j*
      targetExchangeGain P.mixedCount phi d (sourceFlagProb e0 F d)
        (sourceFlagProb_nonneg e0 F d) (sourceFlagProb_le_one e0 F d)
        i j v (1-2*ξ) (by linarith) (by linarith))/Hybrid.rankDenominator (Fin N)-
      variation (conditionalUtility P phi e0 F (1-2*ξ) v (by linarith) (by linarith) i K) b d-
      variation (conditionalUtility P phi e0 F (1-2*ξ) v (by linarith) (by linarith) i K) a d-
      w*(v+2*B)*crossingCount b i y-2*(y-b i)≤
    affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 a i) v y (1-2*ξ) (by linarith) (by linarith)-
      affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 b i) v (b i) (1-2*ξ) (by linarith) (by linarith) := by
  dsimp only
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  let phi := effectivePhi lowPresent
    (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
  let K := sortedFallback N H0 H1 c ξ ν0 ν1 b i
  let a := Function.update b i y
  let G := sortedFallback N H0 H1 c ξ ν0 ν1 a i
  let w := fallbackWeight phi a (sourceFlagProb e0 F a)
    (sourceFlagProb_nonneg e0 F a) (sourceFlagProb_le_one e0 F a)
  have he0 : 0≤1-2*ξ := by linarith
  have he1 : 1-2*ξ≤1 := by linarith
  have hbase := TypicalFinitePromotion.actual_finite_transfer P phi e0 F (1-2*ξ) v he0 he1
    i K b d y hy.le hd
  have hw := fallbackWeight_bounds phi a (sourceFlagProb e0 F a)
    (sourceFlagProb_nonneg e0 F a) (sourceFlagProb_le_one e0 F a)
  have hfall := sortedFallback_finite_loss N H0 H1 c hξ0 hξ1 hsep ν0 ν1 b hb hno i hiv y hy hyB
  have hprice := fixedLaw_utility_antitone K (v:=v) he0 he1 hy.le
  have hloss : affineCountUtility K v y (1-2*ξ) he0 he1-
      affineCountUtility G v y (1-2*ξ) he0 he1≤(v+2*B)*crossingCount b i y+2*(y-b i) := by
    linarith
  have hweighted := mul_le_mul_of_nonneg_left hloss hw.1
  have hsmooth : w*(2*(y-b i))≤2*(y-b i) :=
    mul_le_of_le_one_left (by linarith : 0≤2*(y-b i)) hw.2
  have hchange := fallback_change P.mixedCount phi a (sourceFlagProb e0 F a)
    (sourceFlagProb_nonneg e0 F a) (sourceFlagProb_le_one e0 F a) i K G v (1-2*ξ) he0 he1
  have ha : a i=y := Function.update_self i y b
  rw [ha] at hchange
  simp only [sourceTypicalJointPayoff, Function.update_self] at hbase
  rw [rawCount_eq_effective,rawCount_eq_effective]
  change _≤ affineCountUtility (typicalRankCount P.mixedCount phi a (sourceFlagProb e0 F a)
      (sourceFlagProb_nonneg e0 F a) (sourceFlagProb_le_one e0 F a) i G) v y (1-2*ξ) he0 he1-
    affineCountUtility (typicalRankCount P.mixedCount phi b (sourceFlagProb e0 F b)
      (sourceFlagProb_nonneg e0 F b) (sourceFlagProb_le_one e0 F b) i K) v (b i) (1-2*ξ) he0 he1
  nlinarith only [hbase,hweighted,hsmooth,hchange]

end FCAppendix.Affine.Tail04.ActualFallbackPromotion
