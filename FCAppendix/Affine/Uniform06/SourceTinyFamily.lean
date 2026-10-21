import FCAppendix.Affine.Uniform06.SourceEarlyFamily
import FCAppendix.Affine.Uniform06.NativeSourceLowRoute

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceTinyFamily

open MeasureTheory Set Filter Game Bayes LowBody
open scoped ProbabilityTheory
open Uniform07 LiteralExperiment LiteralPrefixStieltjes
open SourceEarlyFamily SourcePrefixConstructor NativeSourceLowRoute NativeLowRoute

theorem prefix_restrict {ξ B H : ℝ} {g : GuardData}
    (hg : PrefixConditions ξ g H) (hBH : B ≤ H) : PrefixConditions ξ g B :=
  {hg with upper := hBH.trans hg.upper,rejection := hBH.trans hg.rejection}

section Family
variable {E : ℕ → Type*}
    (G : ∀ m,E m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,E m → GuardData)
    (cm : ∀ m,E m → (Fin (m-1) → Fin 4) → ℝ)
variable {Seed : Type*} [MeasurableSpace Seed]

theorem original_source_tiny (i : Row) (h05 : EarlyMenuFields G g cm i)
    (h05atoms : ∀ m (e : E m) b,((G m e:Measure (ℝ × ℝ)).map Prod.snd) {b}=0)
    (hfields : ∀ m (e : E m),LiteralFields i (g m e))
    (hpsi : ∀ m (e : E m),
      (∫ p,PrefixRoot.sourcePsi i (g m e).rejectionRoot p.2
        ∂(G m e:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i) :
    ∀ᶠ m in atTop,∀ e : E m,
      ∀ Γ : FiniteGame m 2 (capacity m) Seed,
      (∀ j,ProposerRationalAtFeasibleLists Γ j) →
      (∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ,1 ≤ p.2.routeCount) →
      (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i →
      Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
        (by cases i <;> norm_num [eta,etaQ]) → Γ.g=0 →
      ∀ focal : Fin m,
      (∀ b ∈ Icc (0:ℝ) (tinyEnd i),duplicates Γ focal b=
        sourceDuplicate i m (G m e) (g m e) (cm m e) b) →
      ∀ v : ℝ,0 < v → v ≤ tinyEnd i →
        ∃ bStar ∈ Ico (0:ℝ) v,
          oneSup Γ focal v < twoUtility Γ focal v bStar ∧
          0 < twoUtility Γ focal v bStar ∧
          ∀ b ≥ 0,oneUtility Γ focal v b < twoUtility Γ focal v bStar := by
  have hp := eventually_source_prefix G g cm i h05 hfields hpsi
  have hh : tinyEnd i ≤ sortEnd i := by
    have hx : (501/1000:ℝ) < x i := by cases i <;> norm_num [x,xQ]
    have ht := cutoff_pos i
    unfold tinyEnd sortEnd entry
    nlinarith
  filter_upwards [hp,eventually_native_source_tiny_route (Seed:=Seed) i] with m hm ht e
  exact ht (G m e:Measure (ℝ × ℝ)) inferInstance (h05.value_marginal m e)
    ((h05.permitted m e).mono fun _ h => h.1) (h05atoms m e) (g m e) (cm m e)
    (prefix_restrict (hm e).2.1 hh)
    (by simpa only [tinyEnd,LowRankMeasures.extensionEnd] using (hm e).2.2)

end Family
end FCAppendix.Affine.Uniform06.SourceTinyFamily
