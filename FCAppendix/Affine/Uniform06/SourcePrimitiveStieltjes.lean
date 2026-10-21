import FCAppendix.Affine.Uniform06.PrimitiveStieltjesMeasures
import FCAppendix.Affine.Uniform06.SourceEarlyFamily

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePrimitiveStieltjes

open MeasureTheory Set Filter Topology
open FCAppendix.Affine.Uniform07
open LiteralExperiment LiteralPrefixStieltjes LowRankMeasures
open SourcePrefixConstructor SourceEarlyFamily PrimitiveStieltjesMeasures

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem eventually_source_primitive_stieltjes (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) b,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2 ∂(G m E:Measure (ℝ × ℝ)))=
        3*PrefixRoot.requiredDemand i) :
    ∀ᶠ m in atTop,∀ E : C m,∀ lo : ℝ,0 < lo → lo ≤ crossoverEnd i →
      Nonempty (PrimitiveStieltjesBounds i m (G m E:Measure (ℝ × ℝ))
        (g m E) (cm m E) lo (crossoverEnd i)) := by
  have ht := cutoff_pos i
  have ha : 0 < EarlyRankCeiling.ceilingValue i-entry i :=
    sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1
  have hε : 0 < cutoff i/10000 := by positivity
  filter_upwards [eventually_primitive_stieltjes_bounds i,
    eventually_source_prefix G g cm i h05 hfields hpsi,
    source_early_active G g cm i h05 (EarlyRankCeiling.ceilingValue i-entry i) ha
      (cutoff i/10000) hε] with m hb hp ha
  intro E lo hlo hloH
  have hA : ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000 := by
    have he : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=EarlyRankCeiling.ceilingValue i := by ring
    simpa only [he] using ha E
  have hceil := EarlyRankCeiling.source_early_rank_ceiling i (G m E:Measure (ℝ × ℝ))
    (h05.value_marginal m E) hA
  have hHprefix : crossoverEnd i ≤ EarlyRankCeiling.prefixEnd i := by
    unfold crossoverEnd EarlyRankCeiling.prefixEnd
    linarith
  have hHK : crossoverEnd i ≤ sortEnd i := by
    unfold crossoverEnd sortEnd
    linarith
  have hHM : crossoverEnd i ≤ RankCutoff.Mstar i := by
    unfold crossoverEnd RankCutoff.Mstar entry
    nlinarith
  have hg := LowRankMeasures.PrefixConditions.mono (hp E).2.1 hHK
  exact hb (G m E:Measure (ℝ × ℝ)) inferInstance (h05.value_marginal m E)
    (h05.permitted m E) (hatom m E) (g m E) (crossoverEnd i) lo (cm m E)
    hlo hloH hHM hg (hp E).2.2
    (fun b hmem => (hceil b (hmem.2.trans hHprefix)).le)

end Family
end FCAppendix.Affine.Uniform06.SourcePrimitiveStieltjes
