import FCAppendix.Game.RealizedPlay

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_interim_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : (ℝ × JointAction n) × Fin (n + 1) → ℝ) (hf : Measurable f) :
    Measurable (fun x : ℝ × JointAction n =>
      ((problem Γ i).outcome x.2).expect (fun r => f (x, r))) := by
  classical
  unfold FiniteLaw.expect
  apply Finset.measurable_sum
  intro r _
  have hm := measurable_outcome_expect Γ i (fun r' => if r' = r then 1 else 0)
  simp only [FiniteLaw.expect_singleton] at hm
  exact (hm.comp measurable_snd).mul (hf.comp (measurable_id.prodMk measurable_const))

theorem integrable_interim_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : (ℝ × JointAction n) × Fin (n + 1) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun x : ℝ × JointAction n =>
      ((problem Γ i).outcome x.2).expect (fun r => f (x, r))) (Γ.F ⊗ₘ Γ.σ) := by
  apply Integrable.of_bound (measurable_interim_expect Γ i f hf).aestronglyMeasurable B
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_le]
  have hbound (r : Fin (n + 1)) : -B ≤ f (x, r) ∧ f (x, r) ≤ B := by
    have hh := hB (x, r)
    rwa [Real.norm_eq_abs, abs_le] at hh
  constructor
  · have hh := ((problem Γ i).outcome x.2).expect_mono (fun r => (hbound r).1)
    simpa only [FiniteLaw.expect_const] using hh
  · have hh := ((problem Γ i).outcome x.2).expect_mono (fun r => (hbound r).2)
    simpa only [FiniteLaw.expect_const] using hh

theorem integrable_realized_statistic (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : (ℝ × JointAction n) × Fin (n + 1) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    Integrable (fun ω => f ((ω.1 i).1, playedCount Γ i ω)) (backgroundLaw Γ) := by
  have hactual := hf.comp
    ((measurable_fst.comp ((measurable_pi_apply i).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst))).prodMk
      (measurable_playedCount Γ i))
  exact Integrable.of_bound hactual.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => hB _)

theorem integral_realized_eq_interim (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : (ℝ × JointAction n) × Fin (n + 1) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) :
    (∫ ω, f ((ω.1 i).1, playedCount Γ i ω) ∂backgroundLaw Γ) =
      ∫ x, ((problem Γ i).outcome x.2).expect (fun r => f (x, r)) ∂(Γ.F ⊗ₘ Γ.σ) := by
  have hactual := hf.comp
    ((measurable_fst.comp ((measurable_pi_apply i).comp
      (show Measurable (fun ω : Background m n Seed => ω.1) from measurable_fst))).prodMk
      (measurable_playedCount Γ i))
  let T := playFromDeviation (n := n) (Seed := Seed) i
  have hpres := playFromDeviation_measurePreserving Γ i
  have heq (z : (ℝ × JointAction n) × Sample m n Seed) :
      f (((T z).1 i).1, playedCount Γ i (T z)) = f (z.1, focalCount Γ i z.1.2 z.2) := by
    have hv : ((T z).1 i).1 = z.1 := by
      simp only [T, playFromDeviation, insertDraw, Function.update_self]
    have hk := playedCount_insertDraw Γ i ((z.1, z.2.2), z.2.1)
    rw [hv]
    change f (z.1, playedCount Γ i (insertDraw i ((z.1, z.2.2), z.2.1))) = _
    rw [hk]
  have hj := (measurable_focalCount_joint Γ i).comp
    ((measurable_snd.comp (show Measurable (fun z : (ℝ × JointAction n) × Sample m n Seed => z.1)
      from measurable_fst)).prodMk measurable_snd)
  have htest := hf.comp (measurable_fst.prodMk hj)
  have hi : Integrable (fun z : (ℝ × JointAction n) × Sample m n Seed =>
      f (z.1, focalCount Γ i z.1.2 z.2)) ((Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ)) :=
    Integrable.of_bound htest.aestronglyMeasurable B (Filter.Eventually.of_forall fun z => hB _)
  calc
    _ = ∫ z : (ℝ × JointAction n) × Sample m n Seed,
        f (((T z).1 i).1, playedCount Γ i (T z)) ∂((Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ)) := by
      rw [← hpres.map_eq]
      exact integral_map_of_stronglyMeasurable hpres.measurable hactual.stronglyMeasurable
    _ = ∫ z : (ℝ × JointAction n) × Sample m n Seed,
        f (z.1, focalCount Γ i z.1.2 z.2) ∂((Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ)) :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = _ := by
      rw [integral_prod _ hi]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      rw [problem_outcome, CountLaw.expect_ofMeasure]

theorem integral_realized_success_eq_interim (Γ : FiniteGame m n c Seed) (i : Fin m) :
    (∫ ω, successIndicator (playedCount Γ i ω).val ∂backgroundLaw Γ) =
      ∫ x, ((problem Γ i).outcome x.2).success ∂(Γ.F ⊗ₘ Γ.σ) := by
  apply integral_realized_eq_interim Γ i
    (fun x => successIndicator x.2.val)
    ((measurable_of_countable (fun r : Fin (n + 1) => successIndicator r.val)).comp measurable_snd) 1
  intro x
  unfold successIndicator
  split <;> norm_num

end FCAppendix.Bayes
