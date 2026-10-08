import FCAppendix.Finite.ConditionalCountLaw
import FCAppendix.Finite.InterimUtilityBounds

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def PolicyLawEquivariant (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ (e : Equiv.Perm (Fin m)) (j : Fin n) (ℓ : LocalList m),
    FeasibleObservedList j ℓ →
    Γ.seedLaw.map (fun s => (Γ.policy j (ℓ ∘ e.symm) s).val) =
      Γ.seedLaw.map (fun s => (Γ.policy j ℓ s).val.map e.toEmbedding)

def selectionVector (Γ : FiniteGame m n c Seed) (ℓ : Fin n → LocalList m)
    (s : Fin n → Seed) : Fin n → Finset (Fin m) := fun j => (Γ.policy j (ℓ j) (s j)).val

def selectionCount (S : Fin n → Finset (Fin m)) (i : Fin m) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (fun j => i ∈ S j)).card, by have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun j => i ∈ S j); simpa using Nat.lt_succ_of_le this⟩

lemma selectionCount_relabel (e : Equiv.Perm (Fin m)) (S : Fin n → Finset (Fin m)) (i : Fin m) :
    selectionCount (fun j => (S j).map e.toEmbedding) (e i) = selectionCount S i := by
  apply Fin.ext
  simp [selectionCount]

lemma measurable_selectionVector (Γ : FiniteGame m n c Seed) (ℓ : Fin n → LocalList m) :
    Measurable (selectionVector Γ ℓ) := by
  apply measurable_pi_lambda
  intro j
  exact (Γ.policy_measurable j).comp (measurable_const.prodMk (measurable_pi_apply j))

lemma selectionVector_map_relabel (Γ : FiniteGame m n c Seed) (hΓ : PolicyLawEquivariant Γ)
    (e : Equiv.Perm (Fin m)) (ℓ : Fin n → LocalList m)
    (hℓ : ∀ j, FeasibleObservedList j (ℓ j)) :
    (Measure.pi fun _ : Fin n => Γ.seedLaw).map (selectionVector Γ (fun j => ℓ j ∘ e.symm)) =
      (Measure.pi fun _ : Fin n => Γ.seedLaw).map
        (fun s j => (selectionVector Γ ℓ s j).map e.toEmbedding) := by
  have hpol (j : Fin n) (L : LocalList m) : Measurable (fun s => (Γ.policy j L s).val) :=
    (Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id)
  calc
    _ = Measure.pi (fun j => Γ.seedLaw.map (fun s => (Γ.policy j (ℓ j ∘ e.symm) s).val)) :=
      Measure.pi_map_pi (fun j => (hpol j _).aemeasurable)
    _ = Measure.pi (fun j => Γ.seedLaw.map (fun s => (Γ.policy j (ℓ j) s).val.map e.toEmbedding)) := by
      congr 1
      funext j
      exact hΓ e j (ℓ j) (hℓ j)
    _ = _ := (Measure.pi_map_pi (fun j =>
      ((measurable_of_countable (fun S : Finset (Fin m) => S.map e.toEmbedding)).comp
        (hpol j (ℓ j))).aemeasurable)).symm

lemma integral_selectionCount_relabel (Γ : FiniteGame m n c Seed) (hΓ : PolicyLawEquivariant Γ)
    (e : Equiv.Perm (Fin m)) (ℓ : Fin n → LocalList m)
    (hℓ : ∀ j, FeasibleObservedList j (ℓ j)) (i : Fin m) (f : Fin (n + 1) → ℝ) :
    (∫ s, f (selectionCount (selectionVector Γ (fun j => ℓ j ∘ e.symm) s) (e i))
      ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
    ∫ s, f (selectionCount (selectionVector Γ ℓ s) i) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  let F := fun S : Fin n → Finset (Fin m) => f (selectionCount S (e i))
  have hF : Measurable F := measurable_of_countable _
  have hvec := measurable_selectionVector Γ (fun j => ℓ j ∘ e.symm)
  have hmapvec : Measurable (fun s j => (selectionVector Γ ℓ s j).map e.toEmbedding) := by
    exact (measurable_of_countable (fun S : Fin n → Finset (Fin m) => fun j => (S j).map e.toEmbedding)).comp
      (measurable_selectionVector Γ ℓ)
  calc
    _ = ∫ S, F S ∂((Measure.pi fun _ : Fin n => Γ.seedLaw).map (selectionVector Γ (fun j => ℓ j ∘ e.symm))) :=
      (integral_map_of_stronglyMeasurable hvec hF.stronglyMeasurable).symm
    _ = ∫ S, F S ∂((Measure.pi fun _ : Fin n => Γ.seedLaw).map (fun s j => (selectionVector Γ ℓ s j).map e.toEmbedding)) := by
      rw [selectionVector_map_relabel Γ hΓ e ℓ hℓ]
    _ = ∫ s, F (fun j => (selectionVector Γ ℓ s j).map e.toEmbedding) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) :=
      integral_map_of_stronglyMeasurable hmapvec hF.stronglyMeasurable
    _ = _ := by simp only [F, selectionCount_relabel]

def inputsToSample (x : ((Fin m → UserDraw n) × Equiv.Perm (Fin n)) × (Fin n → Seed)) :
    Sample m n Seed := ((x.1.1, x.2), x.1.2)

lemma inputsToSample_measurePreserving (Γ : FiniteGame m n c Seed) :
    MeasurePreserving (inputsToSample (m := m) (n := n) (Seed := Seed))
      (((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)).prod
        (Measure.pi fun _ : Fin n => Γ.seedLaw)) (sampleLaw Γ) := by
  let U := Measure.pi fun _ : Fin m => userLaw Γ
  let R := permLaw n
  let S := Measure.pi fun _ : Fin n => Γ.seedLaw
  exact (measurePreserving_prodAssoc U S R).symm.comp
    (((MeasurePreserving.id U).prod (Measure.measurePreserving_swap (μ := R) (ν := S))).comp
      (measurePreserving_prodAssoc U R S))

lemma integral_focalCount_eq_inputs (Γ : FiniteGame m n c Seed) (i : Fin m)
    (act : JointAction n) (f : Fin (n + 1) → ℝ) :
    (∫ ω, f (focalCount Γ i act ω) ∂sampleLaw Γ) =
      ∫ x : (Fin m → UserDraw n) × Equiv.Perm (Fin n),
        (∫ s, f (focalCount Γ i act ((x.1, s), x.2)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw))
      ∂((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)) := by
  have hpres := inputsToSample_measurePreserving Γ
  have hm := (measurable_focalCount Γ i act).comp hpres.measurable
  have hi := CountLaw.integrable_comp
    (((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)).prod
      (Measure.pi fun _ : Fin n => Γ.seedLaw)) _ hm f
  calc
    _ = ∫ x, f (focalCount Γ i act (inputsToSample x)) ∂
        (((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)).prod
          (Measure.pi fun _ : Fin n => Γ.seedLaw)) := by
      rw [← hpres.map_eq]
      exact integral_map_of_stronglyMeasurable hpres.measurable
        ((measurable_of_countable f).comp (measurable_focalCount Γ i act)).stronglyMeasurable
    _ = _ := integral_prod _ hi

lemma measurable_integral_focalCount_inputs (Γ : FiniteGame m n c Seed) (i : Fin m)
    (act : JointAction n) (f : Fin (n + 1) → ℝ) :
    Measurable (fun x : (Fin m → UserDraw n) × Equiv.Perm (Fin n) =>
      ∫ s, f (focalCount Γ i act ((x.1, s), x.2)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) := by
  have hm := ((measurable_of_countable f).comp (measurable_focalCount Γ i act)).comp
    (inputsToSample_measurePreserving Γ).measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace Seed] in
lemma observe_deviated_relabel (e : Equiv.Perm (Fin m)) (i : Fin m)
    (act : JointAction n) (d : Fin m → UserDraw n) (s : Fin n → Seed)
    (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    observe (deviated (e i) act ((d ∘ e.symm, s), τ)) j =
      observe (deviated i act ((d, s), τ)) j ∘ e.symm := by
  classical
  funext l
  by_cases hl : l = e i
  · subst l
    simp only [Function.comp_apply, Equiv.symm_apply_apply, observe,
      deviated_recipients_self, deviated_bid_self]
  · have hl' : e.symm l ≠ i := fun he => hl (by rw [← he, Equiv.apply_symm_apply])
    simp only [Function.comp_apply, observe, deviated_recipients_other _ _ hl,
      deviated_bid_other _ _ hl, deviated_recipients_other _ _ hl', deviated_bid_other _ _ hl']

lemma focalCount_eq_selectionCount (Γ : FiniteGame m n c Seed) (i : Fin m)
    (act : JointAction n) (d : Fin m → UserDraw n) (s : Fin n → Seed)
    (τ : Equiv.Perm (Fin n)) :
    focalCount Γ i act ((d, s), τ) =
      selectionCount (selectionVector Γ (fun j => observe (deviated i act ((d, s), τ)) j) s) i := rfl

lemma integral_focalCount_relabel_seeds (Γ : FiniteGame m n c Seed) (hΓ : PolicyLawEquivariant Γ)
    (e : Equiv.Perm (Fin m)) (i : Fin m) (act : JointAction n)
    (d : Fin m → UserDraw n) (τ : Equiv.Perm (Fin n)) (f : Fin (n + 1) → ℝ) :
    (∫ s, f (focalCount Γ (e i) act ((d ∘ e.symm, s), τ)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)) =
      ∫ s, f (focalCount Γ i act ((d, s), τ)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw) := by
  let ℓ : Fin n → LocalList m := fun j => observe
    (deviate (drawsRealization d) i act.bid act.bid_nonneg (firstK τ act.routeCount)) j
  have he (s : Fin n → Seed) : (fun j => observe (deviated i act ((d, s), τ)) j) = ℓ := rfl
  have he' (s : Fin n → Seed) : (fun j => observe (deviated (e i) act ((d ∘ e.symm, s), τ)) j) =
      fun j => ℓ j ∘ e.symm := by
    funext j
    exact observe_deviated_relabel e i act d s τ j
  simp_rw [focalCount_eq_selectionCount, he, he']
  have hℓ : ∀ j, FeasibleObservedList j (ℓ j) := by
    intro j
    refine ⟨Function.update d i ((0, act), τ), ?_⟩
    funext l
    by_cases hl : l = i
    · subst l
      simp [ℓ, observe, drawsRealization, deviate]
    · simp [ℓ, observe, drawsRealization, deviate, hl]
  exact integral_selectionCount_relabel Γ hΓ e ℓ hℓ i f

lemma relabelInputs_measurePreserving (Γ : FiniteGame m n c Seed) (e : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun x : (Fin m → UserDraw n) × Equiv.Perm (Fin n) => (x.1 ∘ e.symm, x.2))
      ((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n))
      ((Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)) := by
  have hh := (measurePreserving_piCongrLeft (fun _ : Fin m => userLaw Γ) e).prod
    (MeasurePreserving.id (permLaw n))
  convert hh using 1
  funext x
  congr 1
  funext j
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem outcome_eq_of_policyLawEquivariant (Γ : FiniteGame m n c Seed)
    (hΓ : PolicyLawEquivariant Γ) (i l : Fin m) (act : JointAction n) :
    (problem Γ i).outcome act = (problem Γ l).outcome act := by
  let e := Equiv.swap i l
  have he : e i = l := Equiv.swap_apply_left _ _
  apply FiniteLaw.ext_expect
  intro f
  simp only [problem_outcome, CountLaw.expect_ofMeasure, integral_focalCount_eq_inputs]
  let U := (Measure.pi fun _ : Fin m => userLaw Γ).prod (permLaw n)
  let F := fun x : (Fin m → UserDraw n) × Equiv.Perm (Fin n) =>
    ∫ s, f (focalCount Γ l act ((x.1, s), x.2)) ∂(Measure.pi fun _ : Fin n => Γ.seedLaw)
  have hF : Measurable F := measurable_integral_focalCount_inputs Γ l act f
  have hpres := relabelInputs_measurePreserving Γ e
  have hh : (∫ x, F (x.1 ∘ e.symm, x.2) ∂U) = ∫ x, F x ∂U := by
    calc
      _ = ∫ x, F x ∂U.map (fun x => (x.1 ∘ e.symm, x.2)) :=
        (integral_map_of_stronglyMeasurable hpres.measurable hF.stronglyMeasurable).symm
      _ = _ := by rw [hpres.map_eq]
  calc
    _ = ∫ x, F (x.1 ∘ e.symm, x.2) ∂U := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      dsimp only [F]
      rw [← he]
      exact (integral_focalCount_relabel_seeds Γ hΓ e i act x.1 x.2 f).symm
    _ = _ := hh

theorem policyLawEquivariant_of_seedRelabeling (Γ : FiniteGame m n c Seed)
    (T : Equiv.Perm (Fin m) → Fin n → LocalList m → Seed → Seed)
    (hT : ∀ e j ℓ, FeasibleObservedList j ℓ → MeasurePreserving (T e j ℓ) Γ.seedLaw Γ.seedLaw)
    (hpolicy : ∀ e j ℓ, FeasibleObservedList j ℓ → ∀ᵐ s ∂Γ.seedLaw,
      (Γ.policy j (ℓ ∘ e.symm) (T e j ℓ s)).val = (Γ.policy j ℓ s).val.map e.toEmbedding) :
    PolicyLawEquivariant Γ := by
  intro e j ℓ hℓ
  have hm : Measurable (fun s => (Γ.policy j (ℓ ∘ e.symm) s).val) :=
    (Γ.policy_measurable j).comp (measurable_const.prodMk measurable_id)
  calc
    _ = (Γ.seedLaw.map (T e j ℓ)).map (fun s => (Γ.policy j (ℓ ∘ e.symm) s).val) := by
      rw [(hT e j ℓ hℓ).map_eq]
    _ = Γ.seedLaw.map (fun s => (Γ.policy j (ℓ ∘ e.symm) (T e j ℓ s)).val) :=
      Measure.map_map hm (hT e j ℓ hℓ).measurable
    _ = _ := Measure.map_congr (hpolicy e j ℓ hℓ)

lemma payoff_eq_of_policyLawEquivariant (Γ : FiniteGame m n c Seed)
    (hΓ : PolicyLawEquivariant Γ) (i l : Fin m) (v : ℝ) (act : JointAction n) :
    (problem Γ i).payoff v act = (problem Γ l).payoff v act := by
  unfold Interim.Problem.payoff
  rw [outcome_eq_of_policyLawEquivariant Γ hΓ i l act]
  rfl

theorem envelope_eq_of_policyLawEquivariant (Γ : FiniteGame m n c Seed)
    (hΓ : PolicyLawEquivariant Γ) (i l : Fin m) (v : ℝ) :
    (problem Γ i).envelope v = (problem Γ l).envelope v := by
  unfold Interim.Problem.envelope
  have he : (problem Γ i).payoff v = (problem Γ l).payoff v :=
    funext (fun act => payoff_eq_of_policyLawEquivariant Γ hΓ i l v act)
  rw [he]

theorem typeUtility_eq_envelope (Γ : FiniteGame m n c Seed)
    (hΓ : PolicyLawEquivariant Γ) (i : Fin m) (v : ℝ) :
    typeUtility Γ v = (problem Γ i).envelope v := by
  unfold typeUtility
  simp_rw [envelope_eq_of_policyLawEquivariant Γ hΓ _ i v]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  simp [hm]

lemma typeOutcome_eq_of_policyLawEquivariant (Γ : FiniteGame m n c Seed)
    (hΓ : PolicyLawEquivariant Γ) (i l : Fin m) (v : ℝ) :
    typeOutcome Γ i v = typeOutcome Γ l v := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [typeOutcome_expect]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro act
  dsimp only
  rw [outcome_eq_of_policyLawEquivariant Γ hΓ i l act]

theorem conditionalTypeCountLaw_eq_typeOutcome (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hΓ : PolicyLawEquivariant Γ) (i : Fin m) (v : ℝ) :
    conditionalTypeCountLaw Γ hm v = typeOutcome Γ i v := by
  unfold conditionalTypeCountLaw
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_uniformAverage]
  simp_rw [typeOutcome_eq_of_policyLawEquivariant Γ hΓ _ i v]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp [hmR]

theorem envelope_tendsto_of_typeUtility
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r) n (C r) Seed)
    (hΓ : ∀ r, PolicyLawEquivariant (Γ r)) (i : (r : ℕ) → Fin (M r))
    (v L : ℝ) (hU : Filter.Tendsto (fun r => typeUtility (Γ r) v) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun r => (problem (Γ r) (i r)).envelope v) Filter.atTop (nhds L) := by
  apply hU.congr'
  exact Filter.Eventually.of_forall (fun r => typeUtility_eq_envelope (Γ r) (hΓ r) (i r) v)

end FCAppendix.Bayes
