import FCAppendix.Affine.Uniform06.NativeLowRoute
import FCAppendix.Affine.Uniform06.LiteralWeakRent

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.NativeSourceLowRoute

open MeasureTheory Set Filter Game Bayes
open scoped ProbabilityTheory
open FCAppendix.Affine.Uniform07
open LiteralExperiment LiteralPrefixStieltjes LiteralWeakRent LiteralLowDuplicate
open NativeLowRoute

variable {Seed : Type*} [MeasurableSpace Seed]

def tinyEnd (i : Row) : ℝ := (501/1000:ℝ)*cutoff i

theorem tinyEnd_pos (i : Row) : 0 < tinyEnd i := by
  exact mul_pos (by norm_num) (cutoff_pos i)

theorem tinyEnd_rank (i : Row) : tinyEnd i ≤ RankCutoff.Mstar i := by
  have hh : (501/1000:ℝ) ≤ x i+1/200 := by cases i <;> norm_num [x,xQ]
  exact mul_le_mul_of_nonneg_right hh (cutoff_pos i).le

theorem actual_duplicate_including_zero (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) (hg : PrefixConditions (xi i) g (tinyEnd i))
    (hlower : tinyEnd i ≤ g.multiplier-g.radius)
    (margin : (Fin (m-1) → Fin 4) → ℝ) :
    ∀ b ∈ Icc (0:ℝ) (tinyEnd i), sourceDuplicate i m G g margin b ≤
      pureRare m+equalRare i m := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hd := (source_actual_duplicate_level_and_interval i G hvalue hfloor hatom hm
    g hg hlower (tinyEnd_rank i) le_rfl margin).1
  have hmono := (actual_prefix_monotone (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (G.map Prod.snd) (EqualCanonicalRegularity.source_floor_bid_nonnegative i G hfloor)
    (capacity m) g hg margin).2
  intro b hb
  have hh := hmono hb ⟨(tinyEnd_pos i).le,le_rfl⟩ hb.2
  exact hh.trans (hd (tinyEnd i) (tinyEnd_pos i) le_rfl)

theorem eventually_native_source_tiny_route (i : Row) :
    ∀ᶠ m : ℕ in atTop,
      ∀ (G : Measure (ℝ × ℝ)) (hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g (tinyEnd i) → tinyEnd i ≤ g.multiplier-g.radius →
      ∀ (Γ : FiniteGame m 2 (capacity m) Seed),
      (∀ j, ProposerRationalAtFeasibleLists Γ j) →
      (∀ᵐ p ∂Γ.F ⊗ₘ Γ.σ, 1 ≤ p.2.routeCount) →
      (Γ.F ⊗ₘ Γ.σ).real {p | p.2.routeCount=2}=cutoff i →
      Γ.A=Schedule.affine 2 (eta i) (eta_pos i).le
        (by cases i <;> norm_num [eta,etaQ]) → Γ.g=0 →
      ∀ focal : Fin m,
      (∀ b ∈ Icc (0:ℝ) (tinyEnd i),
        duplicates Γ focal b=sourceDuplicate i m G g margin b) →
      ∀ v : ℝ, 0 < v → v ≤ tinyEnd i →
        ∃ bStar ∈ Ico (0:ℝ) v,
          oneSup Γ focal v < twoUtility Γ focal v bStar ∧
          0 < twoUtility Γ focal v bStar ∧
          ∀ b ≥ 0, oneUtility Γ focal v b < twoUtility Γ focal v bStar := by
  filter_upwards [eventually_source_rare_small i,eventually_ge_atTop (4:ℕ)] with m hrare hm
  intro G hG hvalue hfloor hatom g margin hg hlower Γ hpolicy hroutes hlowerMass hA hg0
    focal htransport v hv hvlow
  letI := hG
  have hd := actual_duplicate_including_zero i hm G hvalue hfloor hatom g hg hlower margin
  apply source_tiny_value_strict_all_singletons i hm Γ hpolicy hroutes hlowerMass hA hg0
    focal hv hvlow
  intro b hb
  rw [htransport b hb]
  exact (hd b hb).trans hrare.1

end FCAppendix.Affine.Uniform06.NativeSourceLowRoute
