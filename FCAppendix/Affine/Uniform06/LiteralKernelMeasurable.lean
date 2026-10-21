import FCAppendix.Affine.Uniform06.GuardPrefix
import FCAppendix.Affine.WeightedSampler

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralKernelMeasurable

open MeasureTheory Set Filter LowBody
open LiteralExperiment FiniteGuards GuardPrefix
open FCAppendix.Affine.WeightedSampling FCAppendix.Affine.ClippedResidual
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [Nonempty ι] in
theorem measurable_weights (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) :
    Measurable (weights ξ g T) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ T.support
  · simp only [if_pos hj]
    unfold eligibility clip01 exposure
    fun_prop
  · simp only [if_neg hj]
    exact measurable_const

omit [Fintype ι] [Nonempty ι] in
theorem measurable_maskedBids (T : PureTemplate ι) (E : Finset ι) :
    Measurable (fun b => maskedBids T b E) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ T.support\E
  · simpa only [maskedBids,if_pos hj] using (measurable_pi_apply j : Measurable (fun b : ι → ℝ => b j))
  · simpa only [maskedBids,if_neg hj] using (measurable_const : Measurable (fun _b : ι → ℝ => (0:ℝ)))

omit [Nonempty ι] in
theorem measurable_complementMarginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (E : Finset ι) (j : ι) :
    Measurable (fun b => complementMarginal ξ T b E j) :=
  (measurable_pi_apply j).comp
    ((EqualCapacity.measurable_positiveMarginal ξ (small T) hξ hξ1).comp
      (measurable_maskedBids T E))

omit [Nonempty ι] in
theorem measurable_guardAlpha (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) :
    Measurable (guardAlpha ξ g T) := by
  classical
  have hseed : MeasurableSet {b : ι → ℝ | seeded g T b} := by
    have he : {b : ι → ℝ | seeded g T b}=⋃ j ∈ T.support, {b | b j ≤ g.seedCutoff} := by
      ext b
      simp [seeded]
    rw [he]
    exact MeasurableSet.biUnion (Set.to_countable _) fun j _ =>
      measurableSet_le (measurable_pi_apply j) measurable_const
  have hslack (k : Fin 5) : Measurable (fun b : ι → ℝ => slackVector ξ g T b k) := by
    fin_cases k
    · change Measurable (fun b : ι → ℝ => demand ξ T b (g.multiplier-g.radius)-(small T:ℝ)-imbalance T)
      unfold demand exposure
      fun_prop
    · change Measurable (fun b : ι → ℝ => (small T:ℝ)-demand ξ T b (g.multiplier+g.radius))
      unfold demand exposure
      fun_prop
    · change Measurable (fun b : ι → ℝ => totalWeight (weights ξ g T b)-(imbalance T:ℝ))
      exact ((continuous_totalWeight.measurable.comp (measurable_weights ξ g T)).sub_const _)
    · change Measurable (fun b : ι → ℝ =>
        (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (b j)) -
          (T.residual₀:ℝ)-T.residual₁)
      unfold PrefixRoot.psi
      fun_prop
    · exact measurable_const
  unfold guardAlpha alpha
  apply Measurable.ite hseed
  · apply Finset.measurable_prod
    intro k _
    unfold ramp clip01
    fun_prop
  · exact measurable_const

theorem measurable_canonical_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (j : ι) :
    Measurable (fun b => (canonicalLaw ξ g T b).expect (first j)) := by
  simp_rw [canonical_path_first hξ hξ1,FiniteLaw.expect]
  apply Finset.measurable_sum
  intro path _
  apply ((measurable_pathLaw_mass (imbalance T) ∅ path).comp (measurable_weights ξ g T)).mul
  by_cases hj : j ∈ finalSet (imbalance T) ∅ path
  · simp only [if_pos hj]
    exact measurable_const
  · simp only [if_neg hj]
    exact (measurable_const.mul (measurable_complementMarginal hξ hξ1 T _ j)).sub
      ((measurable_complementMarginal hξ hξ1 T _ j).pow_const 2)

theorem measurable_canonical_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (j : ι) :
    Measurable (fun b => (canonicalLaw ξ g T b).expect (duplicate j)) := by
  simp_rw [canonical_path_duplicate hξ hξ1,FiniteLaw.expect]
  apply Finset.measurable_sum
  intro path _
  exact ((measurable_pathLaw_mass (imbalance T) ∅ path).comp (measurable_weights ξ g T)).mul
    ((measurable_complementMarginal hξ hξ1 T _ j).pow_const 2)

omit [Nonempty ι] in
theorem empty_completion_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) :
    ((complementLaw ξ T b ∅).prod (complementLaw ξ T b ∅)).expect (first j)=
      2*complementMarginal ξ T b ∅ j-(complementMarginal ξ T b ∅ j)^2 := by
  simpa [attachExclusive] using completion_pair_first hξ hξ1 T b ∅ j

omit [Nonempty ι] in
theorem empty_completion_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) :
    ((complementLaw ξ T b ∅).prod (complementLaw ξ T b ∅)).expect (duplicate j)=
      (complementMarginal ξ T b ∅ j)^2 := by
  simpa [attachExclusive] using completion_pair_duplicate hξ hξ1 T b ∅ j

theorem measurable_continuation_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (g : GuardData) (T : PureTemplate ι) (j : ι) :
    Measurable (fun b => (continuationLaw ξ κ g T b).expect (first j)) := by
  by_cases hEq : T.residual₀=T.residual₁
  · simp only [continuationLaw,if_pos hEq,empty_completion_first hξ hξ1]
    exact (measurable_const.mul (measurable_complementMarginal hξ hξ1 T ∅ j)).sub
      ((measurable_complementMarginal hξ hξ1 T ∅ j).pow_const 2)
  · simp only [continuationLaw,if_neg hEq,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
    exact ((measurable_guardAlpha ξ g T).mul (measurable_canonical_first hξ hξ1 g T j)).add
      ((measurable_const.sub (measurable_guardAlpha ξ g T)).mul
        ((measurable_of_countable (first j)).comp (T.measurable_selection κ)))

theorem measurable_continuation_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (g : GuardData) (T : PureTemplate ι) (j : ι) :
    Measurable (fun b => (continuationLaw ξ κ g T b).expect (duplicate j)) := by
  by_cases hEq : T.residual₀=T.residual₁
  · simp only [continuationLaw,if_pos hEq,empty_completion_duplicate hξ hξ1]
    exact (measurable_complementMarginal hξ hξ1 T ∅ j).pow_const 2
  · simp only [continuationLaw,if_neg hEq,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
    exact ((measurable_guardAlpha ξ g T).mul (measurable_canonical_duplicate hξ hξ1 g T j)).add
      ((measurable_const.sub (measurable_guardAlpha ξ g T)).mul
        ((measurable_of_countable (duplicate j)).comp (T.measurable_selection κ)))

theorem continuation_first_bounds (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) :
    (continuationLaw ξ κ g T b).expect (first j) ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact FiniteLaw.expect_nonneg _ (first_nonneg j)
  · apply FiniteLaw.expect_le_const
    intro AB
    rw [first_eq_indicator]
    split_ifs <;> norm_num

theorem continuation_duplicate_bounds (ξ κ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (j : ι) :
    (continuationLaw ξ κ g T b).expect (duplicate j) ∈ Icc (0:ℝ) 1 := by
  constructor
  · exact FiniteLaw.expect_nonneg _ (duplicate_nonneg j)
  · apply FiniteLaw.expect_le_const
    intro AB
    rw [duplicate_eq_indicator]
    split_ifs <;> norm_num

attribute [local irreducible] FiniteLaw.expect continuationLaw

section Row
variable {N : ℕ}

private theorem measurable_original_row_test
    (f : (Fin N → Fin 4) → (Fin (N+1) → ℝ) → ℝ)
    (hf : ∀ k, Measurable (f k)) :
    Measurable (fun p : ℝ × (Fin N → RowRival) =>
      f (fun j => (p.2 j).1) (rowBids p.1 p.2)) := by
  have hk : Measurable (fun p : ℝ × (Fin N → RowRival) => fun j => (p.2 j).1) :=
    measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp measurable_snd).fst
  have hh : Measurable (fun q : (Fin N → Fin 4) × (Fin (N+1) → ℝ) => f q.1 q.2) :=
    measurable_from_prod_countable_right hf
  exact hh.comp (hk.prodMk (measurable_rowBids (N := N)))

theorem measurable_joint_row_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) :
    Measurable (fun p : ℝ × (Fin N → RowRival) =>
      (rowLaw ξ κ c g margin p.1 p.2).expect (first 0)) := by
  unfold rowLaw
  apply measurable_original_row_test (fun k B =>
    (continuationLaw ξ κ {g with countMargin := margin k} (patternTemplate c k) B).expect (first 0))
  intro k
  exact measurable_continuation_first (ι := Fin (N+1)) hξ hξ1 κ
    {g with countMargin := margin k} (patternTemplate c k) 0

theorem measurable_joint_row_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) :
    Measurable (fun p : ℝ × (Fin N → RowRival) =>
      (rowLaw ξ κ c g margin p.1 p.2).expect (duplicate 0)) := by
  unfold rowLaw
  apply measurable_original_row_test (fun k B =>
    (continuationLaw ξ κ {g with countMargin := margin k} (patternTemplate c k) B).expect (duplicate 0))
  intro k
  exact measurable_continuation_duplicate (ι := Fin (N+1)) hξ hξ1 κ
    {g with countMargin := margin k} (patternTemplate c k) 0

theorem measurable_actualSuccess {t ξ : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (κ : ℝ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c : ℕ)
    (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) :
    Measurable (actualSuccess t ξ κ G c N g margin) := by
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) :=
    PureRankCounts.sourceRivalLaw_probability ht G
  exact (measurable_joint_row_first hξ hξ1 κ c g margin).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_actualDuplicate {t ξ : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (κ : ℝ)
    (G : Measure ℝ) [IsProbabilityMeasure G] (c : ℕ)
    (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) :
    Measurable (actualDuplicate t ξ κ G c N g margin) := by
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) :=
    PureRankCounts.sourceRivalLaw_probability ht G
  exact (measurable_joint_row_duplicate hξ hξ1 κ c g margin).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_row_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) :
    Measurable (fun ω : Fin N → RowRival => (rowLaw ξ κ c g margin b ω).expect (first 0)) := by
  exact (measurable_joint_row_first hξ hξ1 κ c g margin).comp
    (measurable_const.prodMk measurable_id)

theorem measurable_row_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) :
    Measurable (fun ω : Fin N → RowRival => (rowLaw ξ κ c g margin b ω).expect (duplicate 0)) := by
  exact (measurable_joint_row_duplicate hξ hξ1 κ c g margin).comp
    (measurable_const.prodMk measurable_id)

theorem integrable_row_first {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (fun ω => (rowLaw ξ κ c g margin b ω).expect (first 0)) P := by
  apply Integrable.of_bound (C := 1) (measurable_row_first hξ hξ1 κ c g margin b).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have hb := continuation_first_bounds ξ κ {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0
    change ‖(continuationLaw ξ κ _ _ _).expect (first 0)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2

theorem integrable_row_duplicate {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (κ : ℝ) (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (fun ω => (rowLaw ξ κ c g margin b ω).expect (duplicate 0)) P := by
  apply Integrable.of_bound (C := 1) (measurable_row_duplicate hξ hξ1 κ c g margin b).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have hb := continuation_duplicate_bounds ξ κ {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) 0
    change ‖(continuationLaw ξ κ _ _ _).expect (duplicate 0)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg hb.1]
    exact hb.2

end Row

open FCAppendix.Affine.Uniform07

theorem measurable_source_kernels (i : FCAppendix.Affine.Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ) :
    Measurable (sourceSuccess i m G g margin) ∧
      Measurable (sourceDuplicate i m G g margin) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact ⟨measurable_actualSuccess (cutoff_mem i) (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) (kappa i) (G.map Prod.snd) (capacity m) g margin,
    measurable_actualDuplicate (cutoff_mem i) (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ]) (kappa i) (G.map Prod.snd) (capacity m) g margin⟩
end FCAppendix.Affine.Uniform06.LiteralKernelMeasurable
