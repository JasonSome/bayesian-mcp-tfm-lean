import FCAppendix.Affine.Uniform06.SourceCanonicalOptimizer
import FCAppendix.Affine.Uniform06.PreciseFamilyFields

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceOptimizerFOC

open MeasureTheory Set Filter Topology
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open CanonicalOptimizer SourceCanonicalOptimizer SourcePreciseFamily

section Family
variable {E : ℕ → Type*}
    (G : ∀ m,E m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,E m → GuardData)
    (cm : ∀ m,E m → (Fin (m-1) → Fin 4) → ℝ)

theorem original_optimizer_FOC (i : Row) (h05 : EarlyMenuFields G g cm i)
    (h05atoms : ∀ m (e : E m) b,((G m e:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i)
    {vmin vmax : ℝ} (hmin : cutoff i/2 < vmin) (hminmax : vmin ≤ vmax)
    (hmax : vmax < entry i) :
    ∀ᶠ m in atTop,∀ e : E m,∀ v ∈ Icc vmin vmax,
      let b := chosen G g cm i vmin m e v
      let C := sourceCanonicalMarginal i m (G m e) (g m e) (cm m e)
      let d := FixedPriceCanonicalIntegral.Cprime i m (G m e) (g m e) (cm m e) b
      Optimal C v b ∧ 0 < b ∧ b < v ∧ 0 < one C v b ∧
        HasDerivAt C d b ∧ C b=(v-b)*d := by
  filter_upwards [original_optimizer G g cm i h05 hfields hpsi hmin hminmax hmax,
    eventually_every_fixed_derivatives G g cm i h05 h05atoms hfields hpsi hK hmax]
    with m hm hd e v hv
  have hs := hm e v hv
  have ha : cutoff i/2 < leftBid i vmin := by unfold leftBid; linarith
  have hb0 : 0 < chosen G g cm i vmin m e v :=
    (half_pos (cutoff_pos i)).trans (ha.trans hs.2.1)
  have hb : chosen G g cm i vmin m e v ∈ Icc (cutoff i/2) vmax :=
    ⟨ha.le.trans hs.2.1.le,hs.1.1.2.trans hv.2⟩
  have hder := (hd e _ hb).1
  exact ⟨hs.1,hb0,hs.2.2.1,hs.2.2.2.1,hder,
    finite_FOC hs.1 hb0 hs.2.2.1 hder⟩

end Family
end FCAppendix.Affine.Uniform06.SourceOptimizerFOC
