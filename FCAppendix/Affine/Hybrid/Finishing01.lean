import FCAppendix.Affine.Hybrid.Finishing01Terminal
import FCAppendix.Affine.Hybrid.Finishing01ClearingNamedCounts

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set Filter Topology MeasureTheory ProbabilityTheory Classical
open Existence.Distributional
namespace Primitives
variable (P : Primitives)

structure PrimitiveActiveEndpoint (c : ℕ → ℕ)
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (mu : Measure P.Value) [IsProbabilityMeasure mu] where
  numeric : P.ActiveNumericFamily c muLow mu
  named_counts : P.AllNamedConditionalCountLimit c numeric.low mu numeric.joint numeric.multiplier
  global_unique : ∀ (nu : ℝ) (q : P.Value → ℝ),
    (∀ v, q v ∈ Ioo (0:ℝ) 1) →
    (∀ v, phi P.xi P.z (q v)=nu/(v:ℝ)) →
    (∫ v : P.Value, q v ∂mu)=P.qbar → nu=(numeric.multiplier:ℝ)

theorem exists_primitive_active (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (hpositive : ∀ᵐ v : P.Low ∂muLow, 0 < (v:ℝ))
    (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    Nonempty (P.PrimitiveActiveEndpoint c muLow mu) := by
  let F := Classical.choice (P.construct_active_numeric_family c hc muLow hpositive mu)
  have hLow : ∀ᶠ M in atTop, NullSingletonClass (F.low M : Measure P.Low) :=
    Filter.eventually_atTop.mpr ⟨F.threshold,F.low_atomless⟩
  have hBid : ∀ᶠ M in atTop,
      NullSingletonClass ((F.joint M).1.map measurable_snd.aemeasurable : Measure P.Bid) :=
    Filter.eventually_atTop.mpr ⟨F.threshold,F.atomless⟩
  exact ⟨⟨F,P.all_named_original_conditional_counts c hc F.low mu F.joint
    F.eventual_IC hLow hBid F.multiplier F.price_tendsto,F.global_unique_clearing⟩⟩

namespace PrimitiveActiveEndpoint
variable {P} {c : ℕ → ℕ} {muLow : Measure P.Low} [IsProbabilityMeasure muLow]
  {mu : Measure P.Value} [IsProbabilityMeasure mu]

theorem common_conull_IC_and_named_counts (E : P.PrimitiveActiveEndpoint c muLow mu)
    (sigma : ℕ → Kernel P.Value P.Bid)
    (hmark : ∀ M, IsMarkovKernel (sigma M))
    (hdis : ∀ M, mu⊗ₘsigma M=((E.numeric.joint M).1 : Measure P.Latent)) :
    ∀ᵐ v ∂mu,
      (∀ M ≥ E.numeric.threshold, ∀ᵐ b ∂sigma M v, ∀ b' : P.Bid,
        P.exactUtility (M-1) (c M) (E.numeric.low M) mu (E.numeric.joint M) (v,b') ≤
          P.exactUtility (M-1) (c M) (E.numeric.low M) mu (E.numeric.joint M) (v,b)) ∧
      (∀ i : (N : ℕ) → Fin (N+1), ∀ j : Fin 3,
        Tendsto (fun N => P.namedConditionalCountMass N (c (N+1)) (E.numeric.low (N+1))
          mu (E.numeric.joint (N+1)) (sigma (N+1)) (i N) v j) atTop
            (𝓝 (limitingCountMass P.z (P.qResponse v E.numeric.multiplier) j))) := by
  exact (E.numeric.common_conull_original_IC sigma hmark hdis).and
    (E.named_counts sigma hmark hdis)

end PrimitiveActiveEndpoint

theorem exists_primitive_active_with_all_conditional_laws (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho))
    (muLow : Measure P.Low) [IsProbabilityMeasure muLow]
    (hpositive : ∀ᵐ v : P.Low ∂muLow, 0 < (v:ℝ))
    (mu : Measure P.Value) [IsProbabilityMeasure mu] :
    ∃ E : P.PrimitiveActiveEndpoint c muLow mu,
      ∀ sigma : ℕ → Kernel P.Value P.Bid,
        (∀ M, IsMarkovKernel (sigma M)) →
        (∀ M, mu⊗ₘsigma M=((E.numeric.joint M).1 : Measure P.Latent)) →
        ∀ᵐ v ∂mu,
          (∀ M ≥ E.numeric.threshold, ∀ᵐ b ∂sigma M v, ∀ b' : P.Bid,
            P.exactUtility (M-1) (c M) (E.numeric.low M) mu (E.numeric.joint M) (v,b') ≤
              P.exactUtility (M-1) (c M) (E.numeric.low M) mu (E.numeric.joint M) (v,b)) ∧
          (∀ i : (N : ℕ) → Fin (N+1), ∀ j : Fin 3,
            Tendsto (fun N => P.namedConditionalCountMass N (c (N+1)) (E.numeric.low (N+1))
              mu (E.numeric.joint (N+1)) (sigma (N+1)) (i N) v j) atTop
                (𝓝 (limitingCountMass P.z (P.qResponse v E.numeric.multiplier) j))) := by
  let E := Classical.choice (P.exists_primitive_active c hc muLow hpositive mu)
  exact ⟨E,E.common_conull_IC_and_named_counts⟩

end Primitives
end FCAppendix.Affine.Hybrid.Finish01
