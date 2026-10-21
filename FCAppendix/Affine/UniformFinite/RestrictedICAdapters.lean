import FCAppendix.Affine.UniformFinite.FiniteExperiment

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory
open Existence.Distributional

lemma baseBid_bounds (i : Row) (p : Value i×unitInterval) :
    (baseBid i p:ℝ)∈Icc (Uniform05.floorBid i p.1) (hiBid i p.1) := by
  simpa [baseBid,noisyBid] using noisyRealBid_bounds i 0 p.1 p.2 0

theorem expectedUtility_zero (i : Row) (N : ℕ) (pi : Joint i)
    (v : Value i) (q : unitInterval) :
    expectedUtility i N 0 pi v q=
      rawUtility i N (restrictedLaw i (0,pi)) v (baseBid i (v,q)) := by
  unfold expectedUtility rawUtility
  apply FiniteLaw.expect_congr
  intro kind
  apply integral_congr_ae
  exact ae_of_all _ (fun b=> by simp only [noisyBid_zero,integral_const,
    probReal_univ,smul_eq_mul,one_mul])

def RestrictedIC (i : Row) (N : ℕ) (pi : Joint i) : Prop :=
  ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,
    b∈Icc (Uniform05.floorBid i p.1) (hiBid i p.1) →
      rawUtility i N (restrictedLaw i (0,pi)) p.1 b≤
        rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)

theorem noisy_zero_iff_restricted_IC (i : Row) (N : ℕ) (pi : Joint i) :
    NoisyIC i N 0 pi↔RestrictedIC i N pi := by
  constructor
  · intro h
    filter_upwards [h,original_value_positive i pi] with p hp hv
    intro b hb
    have hh:=hp (choiceForBid i p.1 b)
    rw [expectedUtility_zero,expectedUtility_zero,
      choiceForBid_exact i p.1 hv b hb] at hh
    exact hh
  · intro h
    filter_upwards [h] with p hp
    intro q
    rw [expectedUtility_zero,expectedUtility_zero]
    exact hp _ (baseBid_bounds i (p.1,q))

theorem restricted_IC_disintegrated (i : Row) (N : ℕ) (pi : Joint i)
    (sigma : Kernel (Value i) unitInterval) [IsMarkovKernel sigma]
    (hsigma : lowerMeasure i⊗ₘsigma=(pi.1 : Measure (Value i×unitInterval)))
    (hIC : RestrictedIC i N pi) :
    ∀ᵐ(v : Value i) ∂lowerMeasure i,∀ᵐq ∂sigma v,∀b : ℝ,
      b∈Icc (Uniform05.floorBid i v) (hiBid i v) →
        rawUtility i N (restrictedLaw i (0,pi)) v b≤
          rawUtility i N (restrictedLaw i (0,pi)) v (baseBid i (v,q)) := by
  rw [RestrictedIC,← hsigma] at hIC
  exact Measure.ae_ae_of_ae_compProd hIC

end FCAppendix.Affine.UniformFinite
