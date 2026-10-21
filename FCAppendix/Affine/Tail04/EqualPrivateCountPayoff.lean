import FCAppendix.Affine.Tail04.AllCountHighPolicy
import FCAppendix.Affine.Tail04.OriginalCountSampling
import FCAppendix.Affine.Tail04.TypicalTargetCount
import FCAppendix.Affine.Tail04.TwoCoinContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateCountPayoff
open MeasureTheory Set
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon JoinedHighPolicy

def countLaw (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (p : PolicyParameters N H R Rp lo hi) (i : Fin N) : CountLaw 2 :=
  let q := policyMean N H c R Rp ξ lo hi p i
  twoCoinCountLaw q q (policyMean_bounds N H c R Rp ξ lo hi p i).1
    (policyMean_bounds N H c R Rp ξ lo hi p i).2
    (policyMean_bounds N H c R Rp ξ lo hi p i).1
    (policyMean_bounds N H c R Rp ξ lo hi p i).2

theorem original_countLaw (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0≤ R) (hRpB : Rp≤ B)
    (hBRm : B< Rm) (hRm : 0< Rm)
    (p : Parameters N H R Rp B)
    (θ0 θ1 : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hθ0 : θ0.map signal=WeakProbability.toMeasure p.2.1)
    (hθ1 : θ1.map signal=WeakProbability.toMeasure p.2.1) (i : Fin N) :
    originalIndependentCountLaw
      (AllCountHighPolicy.equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
      (AllCountHighPolicy.equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
      (AllCountHighPolicy.equal_measurable N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
      (AllCountHighPolicy.equal_measurable N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
      p θ0 θ1 (Sum.inl i) (Sum.inl i)=
        countLaw N H c R Rp ξ 1 B (equalParameter p) i := by
  simp only [originalIndependentCountLaw_eq,
    AllCountHighPolicy.equal_mean N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm p θ0 hθ0 i,
    AllCountHighPolicy.equal_mean N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm p θ1 hθ1 i]
  rfl

theorem continuous_countLaw_mass (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (hξ : 0< ξ) (hlo : 0< lo) (i : Fin N) (r : Fin 3) :
    Continuous (fun p : PolicyParameters N H R Rp lo hi =>
      (countLaw N H c R Rp ξ lo hi p i).mass r) := by
  have hq := (continuous_apply i).comp
    (continuous_policyMean N H c R Rp ξ lo hi hξ hlo)
  unfold countLaw
  exact continuous_twoCoinCountLaw_mass _ _ _ _ _ _ hq hq r

def utility (N H c : ℕ) (R Rp ξ lo hi eta : ℝ)
    (heta0 : 0≤ eta) (heta1 : eta≤1) (i : Fin N)
    (p : ℝ×PolicyParameters N H R Rp lo hi) : ℝ :=
  affineCountUtility (countLaw N H c R Rp ξ lo hi p.2 i)
    p.1 (p.2.1 i:ℝ) eta heta0 heta1

theorem continuous_utility (N H c : ℕ) (R Rp ξ lo hi eta : ℝ)
    (hξ : 0< ξ) (hlo : 0< lo) (heta0 : 0≤ eta) (heta1 : eta≤1) (i : Fin N) :
    Continuous (utility N H c R Rp ξ lo hi eta heta0 heta1 i) := by
  unfold utility affineCountUtility CountLaw.utility FiniteLaw.expect
  apply continuous_finsetSum
  intro r _
  apply ((continuous_countLaw_mass N H c R Rp ξ lo hi hξ hlo i r).comp continuous_snd).mul
  unfold userPayoff
  exact ((continuous_fst.mul continuous_const).sub
    ((continuous_subtype_val.comp ((continuous_apply i).comp
      (continuous_fst.comp continuous_snd))).mul continuous_const)).sub continuous_const

end FCAppendix.Affine.Tail04.EqualPrivateCountPayoff
