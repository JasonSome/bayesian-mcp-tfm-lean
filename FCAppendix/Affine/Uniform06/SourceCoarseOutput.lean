import FCAppendix.Affine.Uniform06.SourceUniformAmplification

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceCoarseOutput

open MeasureTheory Set Filter Topology
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open EarlyCoarseUniform SourceUniformAmplification

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

def Bounds (i : Row) : Prop :=
  ∀ d>(0:ℝ),d≤ x i-1/2 →
    ∃ θ : (m : ℕ) → C m → ℝ → ℝ,∃ θlo θhi : ℝ,∃ A : ℕ,
      0 < θlo ∧ 0 < θhi ∧ ∀ᶠ m in atTop,∀ E : C m,∀ z ∈ Icc (1/2:ℝ) (x i-d),
        θ m E z ∈ Icc θlo θhi ∧
        SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i)
          (G m E:Measure (ℝ × ℝ)))) Prod.fst (θ m E z)=
            (capacity m:ℝ)/((m-1:ℕ):ℝ) ∧
        1/((A:ℝ)+1) ≤ normalizedC i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ∧
        normalizedC i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ≤ (A:ℝ)+1 ∧
        normalizedR i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ≤ (A:ℝ)+1 ∧
        0 ≤ normalizedR i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z)

structure Output (i : Row) : Prop where
  bounds : Bounds G g cm i
  positive : ∀ H : ℝ,cutoff i/2≤ H → H< entry i →
    ∀ᶠ m in atTop,∀ E : C m,∀ b∈Icc (cutoff i/2) H,
      0< sourceCanonicalMarginal i m (G m E) (g m E) (cm m E) b
  amplification : ∀ H : ℝ,cutoff i/2≤ H → H< entry i →
    ∀ ε>(0:ℝ),∀ K>(0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ b∈Icc (cutoff i/2) H,b+ε≤ H →
        K*sourceCanonicalMarginal i m (G m E) (g m E) (cm m E) b<
          sourceCanonicalMarginal i m (G m E) (g m E) (cm m E) (b+ε)

theorem from_early_source (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i) :
    Output G g cm i := by
  have hp := eventually_source_prefix G g cm i h05 hfields hpsi
  have hg : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius≤ cutoff i/100 ∧
      0<(g m E).margin ∧ 0<(g m E).population ∧ 0<(g m E).requiredDemand := by
    filter_upwards [hp] with m hm E
    exact ⟨(hm E).1,(hm E).2.1.margin_pos,(hm E).2.1.population_pos,
      (hm E).2.1.requiredDemand_pos⟩
  refine ⟨?_,?_,?_⟩
  · intro d hd hdmax
    exact source_uniform_coarse C G g cm i hd hdmax h05.value_marginal
      (original_box G g cm i h05)
      (fun m E => (h05.permitted m E).mono fun _ h => h.2.trans (min_le_left _ _))
      (source_early_active G g cm i h05) h05.root_limit hg
  · intro H hHlo hH
    exact (source_uniform_amplification G g cm i h05 hfields hpsi hHlo hH).1
  · intro H hHlo hH
    exact (source_uniform_amplification G g cm i h05 hfields hpsi hHlo hH).2

end Family
end FCAppendix.Affine.Uniform06.SourceCoarseOutput
