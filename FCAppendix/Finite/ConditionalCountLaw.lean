import FCAppendix.Probability.FiniteAveraging
import FCAppendix.Game.RealizedIntegrals
import FCAppendix.PayOnce.FiniteJensen

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma measurable_outcome_mass (Γ : FiniteGame m n c Seed) (i : Fin m) (r : Fin (n + 1)) :
    Measurable (fun act => ((problem Γ i).outcome act).mass r) := by
  simpa only [FiniteLaw.expect_singleton] using
    measurable_outcome_expect Γ i (fun r' => if r' = r then 1 else 0)

def typeOutcome (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ) : CountLaw n :=
  FiniteLaw.average (Γ.σ v) (problem Γ i).outcome (measurable_outcome_mass Γ i)

lemma typeOutcome_expect (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ)
    (f : Fin (n + 1) → ℝ) :
    (typeOutcome Γ i v).expect f = ∫ act, ((problem Γ i).outcome act).expect f ∂Γ.σ v :=
  FiniteLaw.expect_average _ _ _ _

lemma measurable_typeOutcome_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) : Measurable (fun v => (typeOutcome Γ i v).expect f) := by
  simp_rw [typeOutcome_expect]
  exact ((measurable_outcome_expect Γ i f).comp
    (show Measurable (fun x : ℝ × JointAction n => x.2) from measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'.measurable

lemma integrable_typeOutcome_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (f : Fin (n + 1) → ℝ) :
    Integrable (fun v => (typeOutcome Γ i v).expect f) ν :=
  Integrable.of_bound (measurable_typeOutcome_expect Γ i f).aestronglyMeasurable
    (∑ r, ‖f r‖) (Filter.Eventually.of_forall fun v => (typeOutcome Γ i v).norm_expect_le_sum_norm f)

lemma integral_typeOutcome_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) :
    (∫ v, (typeOutcome Γ i v).expect f ∂Γ.F) =
      ∫ x, ((problem Γ i).outcome x.2).expect f ∂(Γ.F ⊗ₘ Γ.σ) := by
  simp_rw [typeOutcome_expect]
  exact (Measure.integral_compProd (FiniteLaw.integrable_expect (Γ.F ⊗ₘ Γ.σ)
    (fun x => (problem Γ i).outcome x.2)
    (fun r => (measurable_outcome_mass Γ i r).comp measurable_snd) f)).symm

def conditionalTypeCountLaw (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v : ℝ) : CountLaw n :=
  FiniteLaw.uniformAverage hm (fun i => typeOutcome Γ i v)

lemma conditionalTypeCountLaw_expect (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (v : ℝ) (f : Fin (n + 1) → ℝ) :
    (conditionalTypeCountLaw Γ hm v).expect f =
      (∑ i, ∫ act, ((problem Γ i).outcome act).expect f ∂Γ.σ v) / m := by
  rw [conditionalTypeCountLaw, FiniteLaw.expect_uniformAverage]
  simp only [typeOutcome_expect]

lemma measurable_conditionalTypeCountLaw_expect (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : Fin (n + 1) → ℝ) : Measurable (fun v => (conditionalTypeCountLaw Γ hm v).expect f) := by
  simp only [conditionalTypeCountLaw, FiniteLaw.expect_uniformAverage]
  exact (Finset.measurable_sum _ (fun i _ => measurable_typeOutcome_expect Γ i f)).div_const m

lemma integrable_conditionalTypeCountLaw_expect (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (ν : Measure ℝ) [IsFiniteMeasure ν] (f : Fin (n + 1) → ℝ) :
    Integrable (fun v => (conditionalTypeCountLaw Γ hm v).expect f) ν :=
  Integrable.of_bound (measurable_conditionalTypeCountLaw_expect Γ hm f).aestronglyMeasurable
    (∑ r, ‖f r‖) (Filter.Eventually.of_forall fun v => (conditionalTypeCountLaw Γ hm v).norm_expect_le_sum_norm f)

lemma integral_conditionalTypeCountLaw_expect (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (f : Fin (n + 1) → ℝ) :
    (∫ v, (conditionalTypeCountLaw Γ hm v).expect f ∂Γ.F) =
      (∑ i, ∫ x, ((problem Γ i).outcome x.2).expect f ∂(Γ.F ⊗ₘ Γ.σ)) / m := by
  simp only [conditionalTypeCountLaw, FiniteLaw.expect_uniformAverage]
  rw [integral_div, integral_finsetSum _ (fun i _ => integrable_typeOutcome_expect Γ i Γ.F f)]
  simp only [integral_typeOutcome_expect]

lemma integral_conditionalTypeCountLaw_expect_eq_actual
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (f : Fin (n + 1) → ℝ) :
    (∫ v, (conditionalTypeCountLaw Γ hm v).expect f ∂Γ.F) =
      (∑ i, ∫ ω, f (playedCount Γ i ω) ∂backgroundLaw Γ) / m := by
  rw [integral_conditionalTypeCountLaw_expect]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  symm
  apply integral_realized_eq_interim Γ i (fun x => f x.2)
    ((measurable_of_countable f).comp measurable_snd) (∑ r, ‖f r‖)
  intro x
  exact Finset.single_le_sum (fun r _ => norm_nonneg (f r)) (Finset.mem_univ x.2)

lemma conditionalTypeCountLaw_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v : ℝ) :
    (conditionalTypeCountLaw Γ hm v).success =
      (∑ i, ∫ act, ((problem Γ i).outcome act).success ∂Γ.σ v) / m :=
  conditionalTypeCountLaw_expect Γ hm v _

lemma conditionalTypeCountLaw_load (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v : ℝ) :
    (conditionalTypeCountLaw Γ hm v).load =
      (∑ i, ∫ act, ((problem Γ i).outcome act).load ∂Γ.σ v) / m :=
  conditionalTypeCountLaw_expect Γ hm v _

lemma conditionalTypeCountLaw_duplicates (Γ : FiniteGame m n c Seed) (hm : 0 < m) (v : ℝ) :
    (conditionalTypeCountLaw Γ hm v).duplicates =
      (∑ i, ∫ act, ((problem Γ i).outcome act).duplicates ∂Γ.σ v) / m := by
  simp_rw [CountLaw.duplicates_eq_expect]
  exact conditionalTypeCountLaw_expect Γ hm v _

lemma measurable_conditionalTypeCountLaw_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Measurable (fun v => (conditionalTypeCountLaw Γ hm v).success) :=
  measurable_conditionalTypeCountLaw_expect Γ hm _

lemma measurable_conditionalTypeCountLaw_load (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Measurable (fun v => (conditionalTypeCountLaw Γ hm v).load) :=
  measurable_conditionalTypeCountLaw_expect Γ hm _

lemma measurable_conditionalTypeCountLaw_duplicates (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Measurable (fun v => (conditionalTypeCountLaw Γ hm v).duplicates) :=
  (measurable_conditionalTypeCountLaw_load Γ hm).sub (measurable_conditionalTypeCountLaw_success Γ hm)

lemma integrable_conditionalTypeCountLaw_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Integrable (fun v => (conditionalTypeCountLaw Γ hm v).success) Γ.F :=
  integrable_conditionalTypeCountLaw_expect Γ hm Γ.F _

lemma integrable_conditionalTypeCountLaw_load (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Integrable (fun v => (conditionalTypeCountLaw Γ hm v).load) Γ.F :=
  integrable_conditionalTypeCountLaw_expect Γ hm Γ.F _

lemma integrable_conditionalTypeCountLaw_duplicates (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    Integrable (fun v => (conditionalTypeCountLaw Γ hm v).duplicates) Γ.F :=
  (integrable_conditionalTypeCountLaw_load Γ hm).sub (integrable_conditionalTypeCountLaw_success Γ hm)

theorem integral_conditionalTypeCountLaw_success (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (∫ v, (conditionalTypeCountLaw Γ hm v).success ∂Γ.F) = finiteCoverage Γ := by
  rw [finiteCoverage_eq_actual]
  exact integral_conditionalTypeCountLaw_expect_eq_actual Γ hm _

theorem integral_conditionalTypeCountLaw_load (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (∫ v, (conditionalTypeCountLaw Γ hm v).load ∂Γ.F) = finiteLoad Γ := by
  rw [finiteLoad_eq_actual]
  exact integral_conditionalTypeCountLaw_expect_eq_actual Γ hm _

theorem integral_conditionalTypeCountLaw_duplicates (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    (∫ v, (conditionalTypeCountLaw Γ hm v).duplicates ∂Γ.F) = finiteLoad Γ - finiteCoverage Γ := by
  unfold CountLaw.duplicates
  rw [integral_sub (integrable_conditionalTypeCountLaw_load Γ hm)
    (integrable_conditionalTypeCountLaw_success Γ hm),
    integral_conditionalTypeCountLaw_load, integral_conditionalTypeCountLaw_success]

end FCAppendix.Bayes
