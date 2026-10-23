import FCAppendix.CommonReserve.ActualEstimates
import FCAppendix.Probability.Resample

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

namespace FiniteGame

def actualProfile (ω : Sample m n r Seed) : Profile m n r := fun l => (ω.1 l).2

def playedCount (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ω : Sample m n r Seed) : Fin (n + 1) :=
  ⟨count (actualProfile ω) Γ.policy ω.2 i, Nat.lt_succ_of_le (count_le _ _ _ _)⟩

def insertDraw (i : Fin m) (p : UserDraw n r × Sample m n r Seed) : Sample m n r Seed :=
  (Function.update p.2.1 i p.1, p.2.2)

theorem insertDraw_measurePreserving (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    MeasurePreserving (insertDraw (Seed := Seed) i)
      (Γ.userLaw.prod Γ.sampleLaw) Γ.sampleLaw := by
  have hu : MeasurePreserving (fun p : UserDraw n r × (Fin m → UserDraw n r) =>
      Function.update p.2 i p.1)
      (Γ.userLaw.prod (Measure.pi fun _ : Fin m => Γ.userLaw))
      (Measure.pi fun _ : Fin m => Γ.userLaw) :=
    ⟨Resample.measurable_update_pair i, Resample.map_update_eq Γ.userLaw i⟩
  exact (hu.prod (MeasurePreserving.id (Measure.pi fun _ : Fin n => Γ.seedLaw))).comp
    (measurePreserving_prodAssoc Γ.userLaw (Measure.pi fun _ : Fin m => Γ.userLaw)
      (Measure.pi fun _ : Fin n => Γ.seedLaw)).symm

omit [MeasurableSpace Seed] in
theorem actualProfile_insertDraw (i : Fin m) (d : UserDraw n r)
    (ω : Sample m n r Seed) : actualProfile (insertDraw i (d, ω)) = deviated i d.2 ω := by
  classical
  funext l
  by_cases hl : l = i
  · subst l
    simp [actualProfile, insertDraw, deviated]
  · simp [actualProfile, insertDraw, deviated, Function.update_of_ne hl]

omit [MeasurableSpace Seed] in
@[simp] theorem deviated_actual (i : Fin m) (ω : Sample m n r Seed) :
    deviated i (ω.1 i).2 ω = actualProfile ω := by
  classical
  change Function.update (fun l => (ω.1 l).2) i (ω.1 i).2 = (fun l => (ω.1 l).2)
  exact Function.update_eq_self i _

theorem playedCount_insertDraw (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (d : UserDraw n r) (ω : Sample m n r Seed) :
    Γ.playedCount i (insertDraw i (d, ω)) = Γ.focalCount i d.2 ω := by
  apply Fin.ext
  change count (actualProfile (insertDraw i (d, ω))) Γ.policy ω.2 i =
    count (deviated i d.2 ω) Γ.policy ω.2 i
  rw [actualProfile_insertDraw]

theorem playedCount_eq_focalCount (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (ω : Sample m n r Seed) :
    Γ.playedCount i ω = Γ.focalCount i (ω.1 i).2 ω := by
  apply Fin.ext
  simp only [playedCount, focalCount, deviated_actual]

theorem measurable_actual_action (i : Fin m) :
    Measurable (fun ω : Sample m n r Seed => (ω.1 i).2) :=
  measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst)

theorem measurable_playedCount (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (Γ.playedCount i) := by
  have he : Γ.playedCount i =
      (fun p : Action n r × Sample m n r Seed => Γ.focalCount i p.1 p.2) ∘
        (fun ω : Sample m n r Seed => ((ω.1 i).2, ω)) := by
    funext ω
    exact Γ.playedCount_eq_focalCount i ω
  rw [he]
  exact (Γ.measurable_focalCount_joint i).comp
    ((measurable_actual_action i).prodMk measurable_id)

theorem joint_draw_count_source_law (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Γ.sampleLaw.map (fun ω => (ω.1 i, Γ.playedCount i ω)) =
      (Γ.userLaw.prod Γ.sampleLaw).map
        (fun p : UserDraw n r × Sample m n r Seed =>
          (p.1, Γ.focalCount i p.1.2 p.2)) := by
  have hpres := Γ.insertDraw_measurePreserving i
  have hm : Measurable (fun ω : Sample m n r Seed => (ω.1 i, Γ.playedCount i ω)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk (Γ.measurable_playedCount i)
  calc
    _ = ((Γ.userLaw.prod Γ.sampleLaw).map (insertDraw i)).map
        (fun ω => (ω.1 i, Γ.playedCount i ω)) := by rw [hpres.map_eq]
    _ = (Γ.userLaw.prod Γ.sampleLaw).map
        ((fun ω : Sample m n r Seed => (ω.1 i, Γ.playedCount i ω)) ∘ insertDraw i) :=
      Measure.map_map hm hpres.measurable
    _ = _ := by
      congr 1
      funext p
      rcases p with ⟨d, ω⟩
      change ((insertDraw i (d, ω)).1 i, Γ.playedCount i (insertDraw i (d, ω))) =
        (d, Γ.focalCount i d.2 ω)
      apply Prod.ext
      · simp only [insertDraw, Function.update_self]
      · exact Γ.playedCount_insertDraw i d ω

theorem joint_value_count_source_law (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Γ.sampleLaw.map (fun ω => ((ω.1 i).1, Γ.playedCount i ω)) =
      (Γ.userLaw.prod Γ.sampleLaw).map
        (fun p : UserDraw n r × Sample m n r Seed =>
          (p.1.1, Γ.focalCount i p.1.2 p.2)) := by
  have hpres := Γ.insertDraw_measurePreserving i
  have hm : Measurable (fun ω : Sample m n r Seed => ((ω.1 i).1, Γ.playedCount i ω)) :=
    (measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (Γ.measurable_playedCount i)
  calc
    _ = ((Γ.userLaw.prod Γ.sampleLaw).map (insertDraw i)).map
        (fun ω => ((ω.1 i).1, Γ.playedCount i ω)) := by rw [hpres.map_eq]
    _ = (Γ.userLaw.prod Γ.sampleLaw).map
        ((fun ω : Sample m n r Seed => ((ω.1 i).1, Γ.playedCount i ω)) ∘ insertDraw i) :=
      Measure.map_map hm hpres.measurable
    _ = _ := by
      congr 1
      funext p
      rcases p with ⟨d, ω⟩
      change (((insertDraw i (d, ω)).1 i).1, Γ.playedCount i (insertDraw i (d, ω))) =
        (d.1, Γ.focalCount i d.2 ω)
      apply Prod.ext
      · simp only [insertDraw, Function.update_self]
      · exact Γ.playedCount_insertDraw i d ω

theorem integrable_playedCount_test (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    Integrable (fun ω => f (Γ.playedCount i ω)) Γ.sampleLaw :=
  CountLaw.integrable_comp Γ.sampleLaw _ (Γ.measurable_playedCount i) f

theorem integral_actual_resample (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (f : Sample m n r Seed → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ ω, ‖f ω‖ ≤ B) :
    (∫ ω, f ω ∂Γ.sampleLaw) =
      ∫ d, ∫ ω, f (insertDraw i (d, ω)) ∂Γ.sampleLaw ∂Γ.userLaw := by
  have hpres := Γ.insertDraw_measurePreserving i
  have hi : Integrable (fun p : UserDraw n r × Sample m n r Seed =>
      f (insertDraw i p)) (Γ.userLaw.prod Γ.sampleLaw) :=
    Integrable.of_bound (hf.comp hpres.measurable).aestronglyMeasurable B
      (Eventually.of_forall fun p => hB _)
  calc
    _ = ∫ p : UserDraw n r × Sample m n r Seed, f (insertDraw i p)
        ∂Γ.userLaw.prod Γ.sampleLaw := by
      have hmap := integral_map_of_stronglyMeasurable (μ := Γ.userLaw.prod Γ.sampleLaw)
        hpres.measurable hf.stronglyMeasurable
      rw [hpres.map_eq] at hmap
      exact hmap
    _ = _ := integral_prod _ hi

theorem integral_playedCount_eq_interim (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) :
    (∫ ω, f (Γ.playedCount i ω) ∂Γ.sampleLaw) =
      ∫ d, (Γ.outcome i d.2).expect f ∂Γ.userLaw := by
  have hm : Measurable (fun ω => f (Γ.playedCount i ω)) :=
    (measurable_of_countable f).comp (Γ.measurable_playedCount i)
  have hh := Γ.integral_actual_resample i (fun ω => f (Γ.playedCount i ω)) hm
    (∑ k, ‖f k‖)
    (fun ω => Finset.single_le_sum (fun k _ => norm_nonneg (f k)) (Finset.mem_univ _))
  simpa only [Γ.playedCount_insertDraw, Γ.outcome_expect] using hh

theorem integral_typeOutcome_expect (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) :
    (∫ v, (Γ.typeOutcome i v).expect f ∂Γ.F) =
      ∫ d, (Γ.outcome i d.2).expect f ∂Γ.userLaw := by
  simp_rw [Γ.typeOutcome_expect]
  exact (Measure.integral_compProd (FiniteLaw.integrable_expect (Γ.F ⊗ₘ Γ.σ)
    (fun d => Γ.outcome i d.2)
    (fun k => (Γ.measurable_outcome_mass i k).comp measurable_snd) f)).symm

theorem integral_typeOutcome_expect_eq_actual (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ v, (Γ.typeOutcome i v).expect f ∂Γ.F) =
      ∫ ω, f (Γ.playedCount i ω) ∂Γ.sampleLaw := by
  rw [Γ.integral_typeOutcome_expect, Γ.integral_playedCount_eq_interim]

theorem coverage_eq_type_integrals (Γ : FiniteGame m n c r Seed) :
    Γ.coverage = (∑ i, ∫ v, (Γ.typeOutcome i v).success ∂Γ.F) / m := by
  unfold coverage
  have he : (fun ω : Sample m n r Seed =>
      ∑ i, successIndicator (count (fun l => (ω.1 l).2) Γ.policy ω.2 i)) =
      fun ω => ∑ i, successIndicator (Γ.playedCount i ω).val := rfl
  rw [he, integral_finsetSum Finset.univ
    (fun i _ => Γ.integrable_playedCount_test i (fun k => successIndicator k.val))]
  simp only [CountLaw.success, Γ.integral_typeOutcome_expect_eq_actual]

theorem load_eq_type_integrals (Γ : FiniteGame m n c r Seed) :
    Γ.load = (∑ i, ∫ v, (Γ.typeOutcome i v).load ∂Γ.F) / m := by
  unfold load
  have he : (fun ω : Sample m n r Seed =>
      ∑ i, (count (fun l => (ω.1 l).2) Γ.policy ω.2 i : ℝ)) =
      fun ω => ∑ i, ((Γ.playedCount i ω).val : ℝ) := rfl
  rw [he, integral_finsetSum Finset.univ
    (fun i _ => Γ.integrable_playedCount_test i (fun k => (k.val : ℝ)))]
  simp only [CountLaw.load, Γ.integral_typeOutcome_expect_eq_actual]

theorem measurable_actual_shortfall (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) :
    Measurable (fun ω : Sample m n r Seed =>
      shortfall p (actualProfile ω) Γ.policy ω.2 i) := by
  have he : (fun ω : Sample m n r Seed => shortfall p (actualProfile ω) Γ.policy ω.2 i) =
      (fun q : Action n r × Sample m n r Seed =>
        shortfall p (deviated i q.1 q.2) Γ.policy q.2.2 i) ∘
        (fun ω : Sample m n r Seed => ((ω.1 i).2, ω)) := by
    funext ω
    dsimp only [Function.comp_apply]
    rw [deviated_actual]
  rw [he]
  exact (Γ.measurable_shortfall_joint i p).comp
    ((measurable_actual_action i).prodMk measurable_id)

theorem actual_shortfall_le (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ)
    (ω : Sample m n r Seed) :
    shortfall p (actualProfile ω) Γ.policy ω.2 i ≤ (n : ℝ) * max p 0 := by
  simpa only [deviated_actual] using Γ.shortfall_deviated_le i p (ω.1 i).2 ω

theorem integrable_actual_shortfall (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) :
    Integrable (fun ω => shortfall p (actualProfile ω) Γ.policy ω.2 i) Γ.sampleLaw := by
  apply Integrable.of_bound (Γ.measurable_actual_shortfall i p).aestronglyMeasurable
    ((n : ℝ) * max p 0)
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (shortfall_nonneg p _ _ _ _)]
    exact Γ.actual_shortfall_le i p ω

theorem integral_actual_shortfall_eq_interim (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) :
    (∫ ω, shortfall p (actualProfile ω) Γ.policy ω.2 i ∂Γ.sampleLaw) =
      ∫ d, Γ.paymentError i p d.2 ∂Γ.userLaw := by
  have he (d : UserDraw n r) (ω : Sample m n r Seed) :
      shortfall p (actualProfile (insertDraw i (d, ω))) Γ.policy
        (insertDraw i (d, ω)).2 i = shortfall p (deviated i d.2 ω) Γ.policy ω.2 i := by
    change shortfall p (actualProfile (insertDraw i (d, ω))) Γ.policy ω.2 i = _
    rw [actualProfile_insertDraw]
  rw [Γ.integral_actual_resample i _ (Γ.measurable_actual_shortfall i p)
    ((n : ℝ) * max p 0) (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (shortfall_nonneg p _ _ _ _)]
      exact Γ.actual_shortfall_le i p ω)]
  simp only [he, paymentError]

theorem integral_typePaymentError_eq_actual (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (p : ℝ) :
    (∫ v, Γ.typePaymentError i p v ∂Γ.F) =
      ∫ ω, shortfall p (actualProfile ω) Γ.policy ω.2 i ∂Γ.sampleLaw := by
  rw [Γ.integral_actual_shortfall_eq_interim]
  have hi : Integrable (fun d : UserDraw n r => Γ.paymentError i p d.2) Γ.userLaw := by
    apply Integrable.of_bound
      ((Γ.measurable_paymentError i p).comp measurable_snd).aestronglyMeasurable
      ((n : ℝ) * max p 0)
    exact Eventually.of_forall fun d => by
      change ‖Γ.paymentError i p d.2‖ ≤ (n : ℝ) * max p 0
      rw [Real.norm_eq_abs, abs_of_nonneg (Γ.paymentError_nonneg i p d.2)]
      exact Γ.paymentError_le i p d.2
  exact (Measure.integral_compProd hi).symm

theorem load_nonneg (Γ : FiniteGame m n c r Seed) : 0 ≤ Γ.load := by
  unfold load
  positivity

theorem coverage_nonneg (Γ : FiniteGame m n c r Seed) : 0 ≤ Γ.coverage := by
  unfold coverage
  exact div_nonneg (integral_nonneg fun ω =>
    Finset.sum_nonneg fun i _ => successIndicator_nonneg _) (Nat.cast_nonneg _)

theorem coverage_le_load (Γ : FiniteGame m n c r Seed) : Γ.coverage ≤ Γ.load := by
  rw [Γ.coverage_eq_type_integrals, Γ.load_eq_type_integrals]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact integral_mono (Γ.integrable_typeOutcome_expect i Γ.F _)
    (Γ.integrable_typeOutcome_expect i Γ.F _) (fun v => (Γ.typeOutcome i v).success_le_load)

theorem load_le_capacity (Γ : FiniteGame m n c r Seed) :
    Γ.load ≤ (n : ℝ) * ((c : ℝ) / m) := by
  have hi : Integrable (fun ω : Sample m n r Seed =>
      ∑ i, ((Γ.playedCount i ω).val : ℝ)) Γ.sampleLaw :=
    integrable_finsetSum _ (fun i _ => Γ.integrable_playedCount_test i (fun k => (k.val : ℝ)))
  have hh := integral_mono hi (integrable_const ((n : ℝ) * c)) (fun ω => by
    have h := total_capacity (actualProfile ω) Γ.policy ω.2
    exact_mod_cast h)
  have hh' : (∫ ω, ∑ i, ((Γ.playedCount i ω).val : ℝ) ∂Γ.sampleLaw) ≤ (n : ℝ) * c := by
    simpa only [integral_const, probReal_univ, one_smul] using hh
  exact (div_le_div_of_nonneg_right hh' (Nat.cast_nonneg m)).trans_eq (by ring)

end FiniteGame
end FCAppendix.CommonReserve
