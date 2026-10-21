import FCAppendix.Affine.Uniform06.SourceEarlyFamily
import FCAppendix.Affine.Uniform06.FullFamilyConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceEarlyLate

open MeasureTheory Set Filter Topology
open Uniform07 SourceEarlyFamily SourcePrefixConstructor LiteralExperiment

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem original_inactive_then_full_law (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (h05atoms : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i) :
    (∀ d > (0:ℝ),d≤ x i-1/2 → ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
        p.1≤(x i-d)*cutoff i → |p.2-p.1|<ε) ∧
    (∀ V ∈ 𝓝 (FullJointLaw.law i),∀ᶠ m in atTop,∀ E : C m,G m E ∈ V) := by
  have hK : entry i< sortEnd i := by
    unfold sortEnd
    have ht := cutoff_pos i
    linarith
  have he := early_source_constructor G g cm i h05 h05atoms hfields hpsi
  have hp : ∀ᶠ m in atTop,∀ E : C m,
      (g m E).radius≤ cutoff i/100 ∧
        LiteralPrefixStieltjes.PrefixConditions (xi i) (g m E) (sortEnd i) := by
    filter_upwards [he.2.2] with m hm E
    exact ⟨(hm E).1,(hm E).2.1⟩
  have hinactive : ∀ d > (0:ℝ),d≤ x i-1/2 → ∀ ε > (0:ℝ),∀ᶠ m in atTop,
      ∀ E : C m,∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
        p.1≤(x i-d)*cutoff i → |p.2-p.1|<ε := by
    intro d hd hdmax ε hε
    exact InactiveFamily.original_common_conull_inactive C G g cm i hK
      h05.value_marginal h05atoms h05.permitted h05.all_action_IC he.1
      h05.root_limit hp hd hdmax hε
  refine ⟨hinactive,?_⟩
  exact FullFamilyConvergence.source_family_weak_limit C G g cm i hK
    h05.value_marginal h05atoms he.2.1 he.1 h05.root_limit hp

theorem every_triangular_source_selection (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (h05atoms : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (E : ∀ n,C (m n)) :
    Tendsto (fun n => G (m n) (E n)) atTop (𝓝 (FullJointLaw.law i)) := by
  have hu := (original_inactive_then_full_law G g cm i h05 h05atoms hfields hpsi).2
  apply tendsto_def.mpr
  intro V hV
  filter_upwards [hm.eventually (hu V hV)] with n hn
  exact hn (E n)

end Family
end FCAppendix.Affine.Uniform06.SourceEarlyLate
