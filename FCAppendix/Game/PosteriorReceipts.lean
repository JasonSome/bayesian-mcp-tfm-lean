import FCAppendix.Game.PosteriorBeliefs
import FCAppendix.Probability.ConditionalAveraging

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem otherInclusionCount_update_seed (Γ : FiniteGame m n c Seed)
    (j : Fin n) (i : Fin m) (d : UserProfile m n) (s : Fin n → Seed) (u : Seed) :
    otherInclusionCount Γ j i (d, Function.update s j u) = otherInclusionCount Γ j i (d, s) := by
  classical
  apply Fin.ext
  rw [otherInclusionCount_eq_sum, otherInclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hlj := Finset.ne_of_mem_erase hl
  simp only [allocation, Function.update_of_ne hlj]
  rfl

theorem receiptRatio_unit (A : Schedule n) (r : Fin n) :
    0 ≤ A.receiptRatio (r.val + 1) ∧ A.receiptRatio (r.val + 1) ≤ 1 :=
  ⟨(A.receiptRatio_pos _ (by omega) (by omega)).le,
    A.receiptRatio_le_one _ (by omega) (by omega)⟩

theorem integral_weighted_receipt_eq_posterior
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m)
    (w : LocalList m → ℝ) (hw : Measurable w) (R : ℝ) (hR : ∀ ℓ, ‖w ℓ‖ ≤ R) :
    (∫ ω : Background m n Seed,
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        w (observe (drawsRealization ω.1) j) else 0) *
          Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val + 1) ∂backgroundLaw Γ) =
    ∫ ℓ, ∫ s, (if i ∈ (Γ.policy j ℓ s).val then w ℓ else 0) *
      (posteriorCountBelief Γ B j ℓ i).expect (fun r => Γ.A.receiptRatio (r.val + 1))
        ∂Γ.seedLaw ∂observedListLaw Γ j := by
  classical
  let f : LocalList m × Seed → ℝ := fun p => if i ∈ (Γ.policy j p.1 p.2).val then w p.1 else 0
  let g : (LocalList m × UserProfile m n) × (Fin n → Seed) → ℝ :=
    fun z => Γ.A.receiptRatio ((otherInclusionCount Γ j i (z.1.2, z.2)).val + 1)
  have hf : Measurable f := Measurable.ite
    ((Γ.policy_measurable j) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
    (hw.comp measurable_fst) measurable_const
  have hg : Measurable g := ((measurable_of_countable
    (fun r : Fin n => Γ.A.receiptRatio (r.val + 1))).comp (measurable_otherInclusionCount Γ j i)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hfb : ∀ z, ‖f z‖ ≤ R := by
    intro z
    dsimp [f]
    split
    · exact hR z.1
    · simpa only [norm_zero, Real.norm_eq_abs, abs_zero] using (norm_nonneg (w z.1)).trans (hR z.1)
  have hgb : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    have hh := receiptRatio_unit Γ.A (otherInclusionCount Γ j i (z.1.2, z.2))
    simpa only [g, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  have heq := ConditionalAveraging.integral_observation_private_seed
    (userProfileLaw Γ) (observedListLaw Γ j) Γ.seedLaw
    (fun d => observe (drawsRealization d) j) (measurable_observe_draws j)
    (B.posterior j) (B.on_path j) j f g hf hg R 1 hfb hgb
    (fun _ d s u => by dsimp only [g]; rw [otherInclusionCount_update_seed])
  change _ = _ at heq
  calc
    _ = ∫ ℓ, (∫ s, f (ℓ, s) ∂Γ.seedLaw) *
        ∫ ω : Background m n Seed,
          Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val + 1)
            ∂posteriorBackground Γ B j ℓ ∂observedListLaw Γ j := heq
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ℓ
      dsimp only
      rw [posteriorCountBelief, FiniteLaw.expect_ofMeasure]
      exact (integral_mul_const _ _).symm

noncomputable def posteriorReceiptFactor
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) : ℝ :=
  (posteriorCountBelief Γ B j ℓ i).expect
    (fun r => Γ.A.receiptRatio (r.val + 1))

theorem posteriorReceiptFactor_bounds
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (ℓ : LocalList m) (i : Fin m) :
    0 ≤ posteriorReceiptFactor Γ B j ℓ i ∧
      posteriorReceiptFactor Γ B j ℓ i ≤ 1 :=
  ⟨FiniteLaw.expect_nonneg _ (fun r => (receiptRatio_unit Γ.A r).1),
    FiniteLaw.expect_le_const _ (fun r => (receiptRatio_unit Γ.A r).2)⟩

theorem conditionalReceipt_eq_mul_ratio_expect
    (A : Schedule n) (ν : FiniteLaw (Fin n)) (b : ℝ) :
    Finite.conditionalReceipt A ν b =
      b * ν.expect (fun r => A.receiptRatio (r.val + 1)) := by
  rw [← ν.expect_const_mul]
  apply ν.expect_congr
  intro r
  simp only [Schedule.receiptRatio, Nat.cast_add, Nat.cast_one]
  ring

theorem measurable_posteriorReceiptFactor
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (i : Fin m) :
    Measurable (fun ℓ => posteriorReceiptFactor Γ B j ℓ i) := by
  let f : Background m n Seed → ℝ := fun ω =>
    Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val + 1)
  have hf : Measurable f :=
    (measurable_of_countable (fun r : Fin n => Γ.A.receiptRatio (r.val + 1))).comp
      (measurable_otherInclusionCount Γ j i)
  have hb : ∀ ω, ‖f ω‖ ≤ 1 := by
    intro ω
    have h := receiptRatio_unit Γ.A (otherInclusionCount Γ j i ω)
    simpa only [f, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  have he (ℓ : LocalList m) : posteriorReceiptFactor Γ B j ℓ i =
      ∫ d, ∫ s, f (d, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)
        ∂B.posterior j ℓ := by
    rw [posteriorReceiptFactor, posteriorCountBelief, FiniteLaw.expect_ofMeasure]
    exact integral_prod _
      (Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hb))
  have hm : Measurable (fun d : UserProfile m n =>
      ∫ s, f (d, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmk : Measurable (fun z : LocalList m × UserProfile m n =>
      ∫ s, f (z.2, s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) :=
    hm.comp measurable_snd
  simp_rw [he]
  exact hmk.stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem measurePreserving_observation_seed
    (Γ : FiniteGame m n c Seed) (j : Fin n) :
    MeasurePreserving
      (fun ω : Background m n Seed => (observe (drawsRealization ω.1) j, ω.2 j))
      (backgroundLaw Γ) ((observedListLaw Γ j).prod Γ.seedLaw) := by
  have hobs : MeasurePreserving (fun d : UserProfile m n => observe (drawsRealization d) j)
      (userProfileLaw Γ) (observedListLaw Γ j) :=
    ⟨measurable_observe_draws j, rfl⟩
  exact hobs.prod (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j)

theorem integral_weighted_receipt_eq_actual_posterior
    (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n) (i : Fin m)
    (w : LocalList m → ℝ) (hw : Measurable w) (R : ℝ) (hR : ∀ ℓ, ‖w ℓ‖ ≤ R) :
    (∫ ω : Background m n Seed,
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        w (observe (drawsRealization ω.1) j) else 0) *
          Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val + 1) ∂backgroundLaw Γ) =
    ∫ ω : Background m n Seed,
      (if i ∈ allocation (drawsRealization ω.1) Γ.policy ω.2 j then
        w (observe (drawsRealization ω.1) j) else 0) *
          posteriorReceiptFactor Γ B j (observe (drawsRealization ω.1) j) i
            ∂backgroundLaw Γ := by
  classical
  let f : LocalList m × Seed → ℝ := fun z =>
    (if i ∈ (Γ.policy j z.1 z.2).val then w z.1 else 0) *
      posteriorReceiptFactor Γ B j z.1 i
  have hf : Measurable f :=
    (Measurable.ite
      ((Γ.policy_measurable j)
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S}))
      (hw.comp measurable_fst) measurable_const).mul
      ((measurable_posteriorReceiptFactor Γ B j i).comp measurable_fst)
  have hb : ∀ z, ‖f z‖ ≤ R := by
    intro z
    have hfac := posteriorReceiptFactor_bounds Γ B j z.1 i
    by_cases hi : i ∈ (Γ.policy j z.1 z.2).val
    · simp only [f, if_pos hi, norm_mul, Real.norm_eq_abs, abs_of_nonneg hfac.1]
      exact (mul_le_mul_of_nonneg_left hfac.2 (abs_nonneg _)).trans
        (by simpa using hR z.1)
    · simp only [f, if_neg hi, zero_mul, norm_zero]
      exact (norm_nonneg (w z.1)).trans (hR z.1)
  have hi : Integrable f ((observedListLaw Γ j).prod Γ.seedLaw) :=
    Integrable.of_bound hf.aestronglyMeasurable R (Eventually.of_forall hb)
  have hmap := measurePreserving_observation_seed Γ j
  calc
    _ = ∫ ℓ, ∫ s, f (ℓ, s) ∂Γ.seedLaw ∂observedListLaw Γ j :=
      integral_weighted_receipt_eq_posterior Γ B j i w hw R hR
    _ = ∫ z, f z ∂(observedListLaw Γ j).prod Γ.seedLaw := (integral_prod _ hi).symm
    _ = _ := by
      rw [← hmap.map_eq]
      exact integral_map_of_stronglyMeasurable hmap.measurable hf.stronglyMeasurable

end FCAppendix.Bayes
