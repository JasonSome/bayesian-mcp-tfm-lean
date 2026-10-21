import FCAppendix.Affine.Tail04.EqualNoisyFiniteLoss
import FCAppendix.Affine.Tail04.UnequalOriginalCountPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualOriginalCountPayoff
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy
open SortedAllNoise EqualNoisyUtilities

def originalCount (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0≤ R) (hRpB : Rp≤ B)
    (hBRm : B< Rm) (hRm : 0< Rm)
    (reg : Bool) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H R Rp))
    (θ0 θ1 : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1] (i : Fin N) : CountLaw 2 :=
  originalIndependentCountLaw
    (AllCountHighPolicy.equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
    (AllCountHighPolicy.equalSample N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
    (AllCountHighPolicy.equal_measurable N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
    (AllCountHighPolicy.equal_measurable N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm)
    (UnequalOriginalCountPayoff.parameter reg b σ) θ0 θ1
    (Sum.inl (focalRank (fun j => (b j:ℝ)) i))
    (Sum.inl (focalRank (fun j => (b j:ℝ)) i))

theorem originalCount_eq (N H c : ℕ) (ξ B R Rp Rm : ℝ)
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0≤ R) (hRpB : Rp≤ B)
    (hBRm : B< Rm) (hRm : 0< Rm)
    (reg : Bool) (b : Fin N → Icc (1:ℝ) B)
    (σ : WeakProbability.Law (Signal H R Rp))
    (θ0 θ1 : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hθ0 : θ0.map signal=WeakProbability.toMeasure σ)
    (hθ1 : θ1.map signal=WeakProbability.toMeasure σ) (i : Fin N) :
    originalCount N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm reg b σ θ0 θ1 i=
      EqualPrivateCountPayoff.countLaw N H c R Rp ξ 1 B (sortedBox b,σ)
        (focalRank (fun j => (b j:ℝ)) i) :=
  EqualPrivateCountPayoff.original_countLaw N H c ξ B R Rp Rm hξ hR hRpB hBRm hRm
    (UnequalOriginalCountPayoff.parameter reg b σ) θ0 θ1 hθ0 hθ1 _

theorem utility_eq_original_integral (N H c : ℕ) {ξ U R Rp Rm eps eta : ℝ}
    (heps : 0≤ eps) (hξ : 0< ξ) (hξ1 : ξ≤1) (hR : 0≤ R)
    (hRpB : Rp≤ U*(1+eps)) (hBRm : U*(1+eps)< Rm) (hRm : 0< Rm)
    (he0 : 0≤ eta) (he1 : eta≤1)
    (reg : Bool) (b : Fin N → Icc (1:ℝ) U)
    (μ : ProbabilityMeasure (Signal H R Rp))
    (θ0 θ1 : Measure (Row H R Rp Rm))
    [IsProbabilityMeasure θ0] [IsProbabilityMeasure θ1]
    (hθ0 : θ0.map signal=(μ : Measure (Signal H R Rp)))
    (hθ1 : θ1.map signal=(μ : Measure (Signal H R Rp))) (v : ℝ) (i : Fin N) :
    activeUtility (c:=c) heps ξ eta he0 he1 i (v,(b,μ))=
      ∫ z : Fin N → unitInterval,
        affineCountUtility
          (originalCount N H c ξ (U*(1+eps)) R Rp Rm ⟨hξ.le,hξ1⟩ hR hRpB hBRm hRm
            reg (physical heps b z) (WeakProbability.mk μ) θ0 θ1 i)
          v (physicalReal heps b z i) eta he0 he1
          ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)) := by
  rw [EqualNoisyFiniteLoss.activeUtility_eq_integral heps hξ]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    erw [originalCount_eq N H c ξ (U*(1+eps)) R Rp Rm ⟨hξ.le,hξ1⟩ hR hRpB hBRm hRm
      reg (physical heps b z) (WeakProbability.mk μ) θ0 θ1 hθ0 hθ1]
    rfl)

end FCAppendix.Affine.Tail04.EqualOriginalCountPayoff
