import FCAppendix.Affine.Hybrid.Finishing01ClusterEndgame
import FCAppendix.Affine.Hybrid.Finishing01ExactIC
import FCAppendix.Affine.Hybrid.Finishing01MenusLocalization

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
namespace Primitives
variable (P : Primitives)

theorem LowSourceState.original_all_bid_IC {M c : ℕ}
    {muLow : Measure P.Low} [IsProbabilityMeasure muLow]
    (A : P.LowSourceState M c muLow) :
    ∀ᵐ x ∂(A.witness.joint.1 : Measure (P.Low×P.Low)), ∀ b : ℝ, 0 ≤ b →
      LowBody.exactExpectedPayoff (M-1) P.d P.xi c P.categories A.bidLaw (x.1.1,b) ≤
        LowBody.exactExpectedPayoff (M-1) P.d P.xi c P.categories A.bidLaw (x.1.1,x.2.1) := by
  exact A.witness.all_bid_IC P.xi_pos P.xi_half.le

theorem exists_eventual_active_numeric_solution (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (hpositive : ∀ᵐ v : P.Low ∂muLow, 0 < (v:ℝ))
    (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ∀ᶠ M in atTop, ∃ A : P.LowSourceState M (c M) muLow,
      ∃ _E : P.FiniteLawSolution M (c M) A.bidLaw mu, True := by
  have hlow := LowBody.eventually_exists_actual_low_bid_equilibrium
    P.d_nonneg P.xi_pos P.xi_half.le P.s P.a P.h P.s_pos P.a_pos.le P.h_pos
      P.mass (Measure.dirac (0:ℝ)) c P.rho
        (by linarith [P.rho_lower,P.h_pos]) P.rho_upper hc P.low_rate_gap muLow hpositive
  have hatom := P.atomless_of_actual_noisyWitness c hc
  have hstrip := Finishing01Menus.eventual_strip_threshold P c hc
  filter_upwards [hlow,hatom,hstrip] with M hL hA hS
  obtain ⟨lowWitness,_hlowIC⟩ := hL
  let A : P.LowSourceState M (c M) muLow := ⟨lowWitness⟩
  let W := Classical.choice (P.exists_noisyWitness M (c M) A.bidLaw mu)
  have hG := hA A.bidLaw mu W
  have hIC := P.exact_IC_of_actual_noisyWitness A.bidLaw lowWitness.compact_atomless mu W hG
  exact ⟨A,⟨W.joint,hG,hS A.bidLaw mu W,hIC⟩,trivial⟩

theorem FiniteLawSolution.exists_original_kernel {M c : ℕ}
    {low : ProbabilityMeasure P.Low} [NullSingletonClass (low : Measure P.Low)]
    {mu : Measure P.Value} [IsProbabilityMeasure mu]
    (E : P.FiniteLawSolution M c low mu) :
    ∃ sigma : Kernel P.Value P.Bid, IsMarkovKernel sigma ∧
      mu⊗ₘsigma=(E.joint.1 : Measure P.Latent) ∧
      (∀ᵐ v ∂mu, ∀ᵐ b ∂sigma v, ∀ b' : P.Bid,
        P.exactUtility (M-1) c low mu E.joint (v,b') ≤
          P.exactUtility (M-1) c low mu E.joint (v,b)) := by
  letI := E.atomless
  exact disintegrate_allAction mu E.joint (P.exactUtility (M-1) c low mu E.joint)
    (P.continuous_exactUtility (M-1) c low mu E.joint) E.all_bid_IC

theorem FiniteLawSolution.any_original_kernel {M c : ℕ}
    {low : ProbabilityMeasure P.Low} [NullSingletonClass (low : Measure P.Low)]
    {mu : Measure P.Value} [IsProbabilityMeasure mu]
    (E : P.FiniteLawSolution M c low mu)
    (sigma : Kernel P.Value P.Bid) [IsMarkovKernel sigma]
    (hdis : mu⊗ₘsigma=(E.joint.1 : Measure P.Latent)) :
    ∀ᵐ v ∂mu, ∀ᵐ b ∂sigma v, ∀ b' : P.Bid,
      P.exactUtility (M-1) c low mu E.joint (v,b') ≤
        P.exactUtility (M-1) c low mu E.joint (v,b) := by
  letI := E.atomless
  exact P.exact_IC_any_disintegration (M-1) c low mu E.joint E.all_bid_IC sigma hdis

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
