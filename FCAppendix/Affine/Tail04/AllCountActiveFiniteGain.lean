import FCAppendix.Affine.Tail04.ActiveGainUniformModulus
import FCAppendix.Affine.Tail04.EqualNoisyFiniteLoss

noncomputable section
namespace FCAppendix.Affine.Tail04.AllCountActiveFiniteGain
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal SortedAllNoise ActualFallbackPromotion
open ActiveGainUniformModulus ActualActiveFiniteGain
open EqualPrivateFiniteLoss
open scoped BigOperators

variable {N : ℕ} [Nonempty (Fin N)]

def physicalCount (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (σ : ProbabilityMeasure (Signal H0 R Rp))
    (b : Fin N → Icc (1:ℝ) B) (i : Fin N) : CountLaw 2 :=
  if H0=H1 then
    EqualPrivateCountPayoff.countLaw N H0 c R Rp ξ 1 B (sortedBox b,WeakProbability.mk σ)
      (focalRank (fun j => (b j:ℝ)) i)
  else UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F reg lowPresent
    ν0 ν1 (fun j => (b j:ℝ)) i

def physicalUtility (H0 H1 c : ℕ) (ξ B R Rp width e0 F : ℝ)
    (hη0 : 0≤1-2*ξ) (hη1 : 1-2*ξ≤1)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (σ : ProbabilityMeasure (Signal H0 R Rp))
    (v : ℝ) (b : Fin N → Icc (1:ℝ) B) (i : Fin N) : ℝ :=
  affineCountUtility (physicalCount H0 H1 c ξ B R Rp width e0 F reg lowPresent ν0 ν1 σ b i)
    v (b i) (1-2*ξ) hη0 hη1

def smoothCoefficient (ξ C vhi : ℝ) : ℝ := (2*vhi+2*C)/ξ+2

lemma smoothCoefficient_ge_two {ξ C vhi : ℝ} (hξ : 0< ξ) (hC : 0≤ C) (hv : 0≤ vhi) :
    2≤ smoothCoefficient ξ C vhi := by
  have hh : 0≤(2*vhi+2*C)/ξ := by positivity
  unfold smoothCoefficient
  linarith

theorem exists_finite_gain_radius (H0 H1 c m : ℕ) (hcard : N≤ m)
    {ξ R width e0 F C vlo vhi : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (hw : 0< width) (he0 : 0≤ e0) (he1 : e0≤1)
    (hF : 1< F) (hCF : C≤ F) (hC : 1≤ C) (hvhi : 0≤ vhi)
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (i : Fin N) {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ B∈Icc (1:ℝ) C,∀ Rp∈Icc (0:ℝ) 1,∀ v∈Icc vlo vhi,
      (1-ξ)*B<1 → ∀ σ : ProbabilityMeasure (Signal H0 R Rp),
      ∀ b : Fin N → Icc (1:ℝ) B,
      (∀ j k,j≠k → (b j:ℝ)≠(b k:ℝ)) → (b i:ℝ)≤ v →
      ∀ y : Icc (1:ℝ) B,(b i:ℝ)< y → (y:ℝ)-(b i:ℝ)< δ →
      let old := fun j => (b j:ℝ)
      let new := Function.update old i (y:ℝ)
      let frozen := freezeFocal old i y
      let cut := effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      populationCoefficient m ξ width e0 F C*
          (if H0=H1 then 0 else AtypicalFittingFiniteLoss.crossingCount old i y)-
        (vhi+2*C+1)*(badWeightProbability cut e0 F frozen+badWeightProbability cut e0 F new)*
          AtypicalFittingFiniteLoss.crossingCount old i y-
        2*e-smoothCoefficient ξ C vhi*((y:ℝ)-(b i:ℝ))≤
      physicalUtility H0 H1 c ξ B R Rp width e0 F (by linarith) (by linarith)
          reg lowPresent ν0 ν1 σ v (Function.update b i y) i-
        physicalUtility H0 H1 c ξ B R Rp width e0 F (by linarith) (by linarith)
          reg lowPresent ν0 ν1 σ v b i := by
  obtain ⟨δ,hδ,hd⟩ := exists_actual_finite_gain_radius H0 H1 c m (R:=R) hcard
    hξ hξh hw he0 he1 hF hCF reg lowPresent ν0 ν1 i he
  refine ⟨δ,hδ,?_⟩
  intro B hB Rp hRp v hv hsep σ b hno hiv y hy hsmall
  dsimp only
  have hother (j : Fin N) (hj : j≠i) : Function.update b i y j=b j := by
    simp only [Function.update_of_ne hj]
  have hreal : (fun j => ((Function.update b i y) j:ℝ))=
      Function.update (fun j => (b j:ℝ)) i (y:ℝ) := by
    funext j
    by_cases hj : j=i
    · subst j;simp
    · simp only [Function.update_of_ne hj]
  have hv0 : 0≤ v := (by norm_num : (0:ℝ)≤1).trans ((b i).2.1.trans hiv)
  have hdel : 0≤(y:ℝ)-(b i:ℝ) := sub_nonneg.mpr hy.le
  have hL := smoothCoefficient_ge_two hξ (by linarith : 0≤ C) hvhi
  by_cases heq : H0=H1
  · simp only [physicalUtility,physicalCount,if_pos heq,Function.update_self]
    have hh := sorted_countUtility_finite_loss (c:=c) hξ (by linarith : ξ≤1)
      (by linarith : 0≤1-2*ξ) (by linarith : 1-2*ξ≤1)
      (WeakProbability.mk σ) b (Function.update b i y) i hother v hv0 (by simpa using hy.le)
    simp only [Function.update_self] at hh
    have hscale : (2*v+2*B)/ξ+2≤ smoothCoefficient ξ C vhi := by
      unfold smoothCoefficient
      have hnum : 2*v+2*B≤2*vhi+2*C := by linarith [hv.2,hB.2]
      exact add_le_add (div_le_div_of_nonneg_right hnum hξ.le) le_rfl
    have hs := mul_le_mul_of_nonneg_right hscale hdel
    have hbad : 0≤(vhi+2*C+1)*
        (badWeightProbability (effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
          e0 F (freezeFocal (fun j => (b j:ℝ)) i y)+
        badWeightProbability (effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
          e0 F (Function.update (fun j => (b j:ℝ)) i (y:ℝ)))*
          AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) i y := by
      have hβ0 := FiniteLaw.prob_nonneg
        (independentFlagLaw (sourceFlagProb e0 F (freezeFocal (fun j => (b j:ℝ)) i y))
          (sourceFlagProb_nonneg _ _ _) (sourceFlagProb_le_one _ _ _))
        (fun z => ¬WeightFlags
          (effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
          (freezeFocal (fun j => (b j:ℝ)) i y) z)
      have hβ1 := FiniteLaw.prob_nonneg
        (independentFlagLaw (sourceFlagProb e0 F (Function.update (fun j => (b j:ℝ)) i (y:ℝ)))
          (sourceFlagProb_nonneg _ _ _) (sourceFlagProb_le_one _ _ _))
        (fun z => ¬WeightFlags
          (effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
          (Function.update (fun j => (b j:ℝ)) i (y:ℝ)) z)
      have hx := AtypicalFittingFiniteLoss.crossingCount_nonneg (fun j => (b j:ℝ)) i y
      change 0≤ badWeightProbability _ _ _ _ at hβ0
      change 0≤ badWeightProbability _ _ _ _ at hβ1
      positivity
    nlinarith only [hh,hs,hbad,he]
  · simp only [physicalUtility,physicalCount,if_neg heq,Function.update_self,hreal]
    have hh := hd B hB Rp hRp v hv hsep (fun j => (b j:ℝ)) (fun j => (b j).2)
      hno hiv y hy y.2.2 hsmall
    dsimp only at hh
    have hs := mul_le_mul_of_nonneg_right hL hdel
    linarith

end FCAppendix.Affine.Tail04.AllCountActiveFiniteGain
