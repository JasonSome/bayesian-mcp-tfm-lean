import FCAppendix.Affine.Uniform06.LiteralLowDuplicate
import FCAppendix.Affine.Uniform06.LiteralSuccessLower

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralPureComponents

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition
open LiteralPrefixStieltjes LiteralLowDuplicate LiteralSuccessLower GuardPrefix
open PureRankCounts PureRankProbability PurePivotalSource PureDuplicateIntervals PureDuplicateRare
open FCAppendix.Affine.Uniform07

variable {N : ℕ}

def rowUnequalPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  if rowResidual c 0 ω=rowResidual c 1 ω then 0 else rowPureDuplicate κ c b ω

theorem measurable_rowUnequalPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ) :
    Measurable (rowUnequalPureDuplicate (N := N) κ c b) :=
  Measurable.ite (EqualCanonicalRegularity.measurableSet_equalResidual c)
    measurable_const (measurable_rowPureDuplicate κ c b)

theorem row_unequal_duplicate_bounds (κ : ℝ) (c : ℕ) (b : ℝ)
    (ω : Fin N → RowRival) :
    0 ≤ rowUnequalPureDuplicate κ c b ω ∧
      rowUnequalPureDuplicate κ c b ω ≤ rowPureDuplicate κ c b ω := by
  unfold rowUnequalPureDuplicate
  split_ifs
  · exact ⟨le_rfl,(rowPureDuplicate_bounds κ c b ω).1⟩
  · exact ⟨(rowPureDuplicate_bounds κ c b ω).1,le_rfl⟩

theorem integrable_rowUnequalPureDuplicate (κ : ℝ) (c : ℕ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (rowUnequalPureDuplicate κ c b) P := by
  apply Integrable.of_bound (C := 1) (measurable_rowUnequalPureDuplicate κ c b).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (row_unequal_duplicate_bounds κ c b ω).1]
    exact (row_unequal_duplicate_bounds κ c b ω).2.trans (rowPureDuplicate_bounds κ c b ω).2

theorem row_duplicate_decomposition
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) B)
    (ω : Fin N → RowRival) :
    (rowLaw ξ κ c g margin b ω).expect (duplicate 0)=
      rowUnequalPureDuplicate κ c b ω+rowCanonicalDuplicate ξ c g margin b ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  by_cases he : T.residual₀=T.residual₁
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have heR : rowResidual c 0 ω=rowResidual c 1 ω := he
    simp only [rowLaw,continuationLaw,rowUnequalPureDuplicate,rowCanonicalDuplicate,
      if_pos heT,if_pos heR,empty_completion_duplicate hξ hξ1,zero_add]
  · have heT : ¬(patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have heR : ¬rowResidual c 0 ω=rowResidual c 1 ω := he
    have hh := (unequal_prefix_add (ξ := ξ) hκ1
      {g with countMargin := margin (fun j => (ω j).1)} T (rowBids b ω)
      hg.margin_pos hg.population_pos hg.rejectionScale_pos (rowBids_outside c b ω)
      0 (by simpa [rowBids] using hb.1) (by simpa [rowBids] using hb.2.trans hg.rejection) he).2
    simpa only [rowLaw,rowUnequalPureDuplicate,rowPureDuplicate,rowPureSelection,
      literal_duplicate_eq_pureDuplicate,rowCanonicalDuplicate,
      if_neg heT,if_neg heR,canonicalLaw_update_countMargin,T] using! hh

def expectedUnequalPureDuplicate (N c : ℕ) (κ t : ℝ) (G : Measure ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, rowUnequalPureDuplicate κ c b ω
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

theorem expected_unequal_duplicate_bounds {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) (κ b : ℝ) :
    0 ≤ expectedUnequalPureDuplicate N c κ t G b ∧
      expectedUnequalPureDuplicate N c κ t G b ≤
        expectedPureDuplicate (N := N) t 0 (1-t) κ G c b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  refine ⟨integral_nonneg (fun ω => (row_unequal_duplicate_bounds κ c b ω).1),?_⟩
  exact integral_mono_ae (integrable_rowUnequalPureDuplicate κ c b P)
    (integrable_rowPureDuplicate κ c b P)
    (Eventually.of_forall fun ω => (row_unequal_duplicate_bounds κ c b ω).2)

theorem actual_duplicate_decomposition
    {t ξ κ B : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) B) :
    actualDuplicate t ξ κ G c N g margin b=
      expectedUnequalPureDuplicate N c κ t G b+actualCanonicalDuplicate t ξ G c N g margin b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  unfold actualDuplicate
  simp_rw [row_duplicate_decomposition hξ hξ1 hκ1 c g hg margin hb]
  change (∫ ω, rowUnequalPureDuplicate κ c b ω+rowCanonicalDuplicate ξ c g margin b ω ∂P)=_
  rw [integral_add (integrable_rowUnequalPureDuplicate κ c b P)
    (integrable_rowCanonical hξ hξ1 c g margin b P).2.2]
  rfl

def sourcePureSuccess (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b

def sourcePureDuplicate (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (b : ℝ) : ℝ :=
  expectedUnequalPureDuplicate (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b

theorem source_both_decompositions (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) B) :
    sourceSuccess i m G g margin b=sourcePureSuccess i m G b+
      2*sourceCanonicalMarginal i m G g margin b-sourceCanonicalDuplicate i m G g margin b ∧
    sourceDuplicate i m G g margin b=sourcePureDuplicate i m G b+
      sourceCanonicalDuplicate i m G g margin b := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  refine ⟨source_first_decomposition i m G g hg margin hb,?_⟩
  exact actual_duplicate_decomposition (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ])
    (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) (G.map Prod.snd) (capacity m) g hg margin hb

theorem source_pure_success_ge_qPure (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (b : ℝ) :
    qPure (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b ≤ sourcePureSuccess i m G b := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact qPure_le_unequal_first (κ := kappa i) (cutoff_mem i) (G.map Prod.snd) (m-1) (capacity m) b

theorem source_pure_duplicate_nonnegative_le_rare (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {b : ℝ} (hb : 0 < b) (hbM : b ≤ RankCutoff.Mstar i) :
    0 ≤ sourcePureDuplicate i m G b ∧ sourcePureDuplicate i m G b ≤ pureRare m := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hh := expected_unequal_duplicate_bounds (cutoff_mem i) (G.map Prod.snd)
    (m-1) (capacity m) (kappa i) b
  exact ⟨hh.1,hh.2.trans (source_pure_duplicate_exponential i G hvalue hfloor hm b hb hbM)⟩

end FCAppendix.Affine.Uniform06.LiteralPureComponents
