import FCAppendix.Affine.Uniform06.LiteralPrefixStieltjes

set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralKernelDecomposition

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelMeasurable GuardPrefix LiteralPrefixStieltjes
open PureRankCounts PurePivotalSource PureDuplicateIntervals
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.Uniform07

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem expect_first_add_duplicate (P : FiniteLaw (Finset ι × Finset ι)) (j : ι) :
    P.expect (first j)+P.expect (duplicate j)=2*P.expect (fairMarginal j) := by
  rw [← FiniteLaw.expect_add,← FiniteLaw.expect_const_mul]
  exact FiniteLaw.expect_congr P (first_add_duplicate j)

omit [Nonempty ι] in
theorem expect_first_bounds (P : FiniteLaw (Finset ι × Finset ι)) (j : ι) :
    P.expect (first j) ∈ Icc (0:ℝ) 1 := by
  refine ⟨FiniteLaw.expect_nonneg _ (first_nonneg j),?_⟩
  apply FiniteLaw.expect_le_const
  intro AB
  rw [first_eq_indicator]
  split_ifs <;> norm_num

omit [Nonempty ι] in
theorem expect_duplicate_bounds (P : FiniteLaw (Finset ι × Finset ι)) (j : ι) :
    P.expect (duplicate j) ∈ Icc (0:ℝ) 1 := by
  refine ⟨FiniteLaw.expect_nonneg _ (duplicate_nonneg j),?_⟩
  apply FiniteLaw.expect_le_const
  intro AB
  rw [duplicate_eq_indicator]
  split_ifs <;> norm_num

omit [Nonempty ι] in
theorem expect_fair_bounds (P : FiniteLaw (Finset ι × Finset ι)) (j : ι) :
    P.expect (fairMarginal j) ∈ Icc (0:ℝ) 1 := by
  have he := expect_first_add_duplicate P j
  have hS := expect_first_bounds P j
  have hD := expect_duplicate_bounds P j
  constructor <;> linarith [hS.1,hS.2,hD.1,hD.2]

theorem measurable_canonical_fair {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (j : ι) :
    Measurable (fun b => (canonicalLaw ξ g T b).expect (fairMarginal j)) := by
  have he : (fun b => (canonicalLaw ξ g T b).expect (fairMarginal j))=
      (fun b => ((canonicalLaw ξ g T b).expect (first j)+
        (canonicalLaw ξ g T b).expect (duplicate j))/2) := by
    funext b
    have hh := expect_first_add_duplicate (canonicalLaw ξ g T b) j
    linarith
  rw [he]
  exact ((measurable_canonical_first hξ hξ1 g T j).add
    (measurable_canonical_duplicate hξ hξ1 g T j)).div_const 2

@[simp] theorem canonicalLaw_update_countMargin (ξ : ℝ) (g : GuardData)
    (T : PureTemplate ι) (b : ι → ℝ) (s : ℝ) :
    canonicalLaw ξ {g with countMargin := s} T b=canonicalLaw ξ g T b := rfl

attribute [local irreducible] FiniteLaw.expect canonicalLaw complementMarginal continuationLaw guardAlpha

section Row
variable {N : ℕ}

def rowCanonicalFirst (ξ : ℝ) (c : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  if T.residual₀=T.residual₁ then 2*complementMarginal ξ T B ∅ 0-(complementMarginal ξ T B ∅ 0)^2
  else guardAlpha ξ {g with countMargin := margin (fun j => (ω j).1)} T B*
    (canonicalLaw ξ g T B).expect (first 0)

def rowCanonicalFair (ξ : ℝ) (c : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  if T.residual₀=T.residual₁ then complementMarginal ξ T B ∅ 0
  else guardAlpha ξ {g with countMargin := margin (fun j => (ω j).1)} T B*
    (canonicalLaw ξ g T B).expect (fairMarginal 0)

def rowCanonicalDuplicate (ξ : ℝ) (c : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  if T.residual₀=T.residual₁ then (complementMarginal ξ T B ∅ 0)^2
  else guardAlpha ξ {g with countMargin := margin (fun j => (ω j).1)} T B*
    (canonicalLaw ξ g T B).expect (duplicate 0)

theorem row_canonical_first_eq (ξ : ℝ) (c : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) (ω : Fin N → RowRival) :
    rowCanonicalFirst ξ c g margin b ω=
      2*rowCanonicalFair ξ c g margin b ω-rowCanonicalDuplicate ξ c g margin b ω := by
  dsimp only [rowCanonicalFirst,rowCanonicalFair,rowCanonicalDuplicate]
  split_ifs
  · rfl
  · have hh := expect_first_add_duplicate
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) (0:Fin (N+1))
    linear_combination
      guardAlpha ξ {g with countMargin := margin (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)*hh

theorem row_canonical_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ)
    (b : ℝ) (ω : Fin N → RowRival) :
    rowCanonicalFirst ξ c g margin b ω ∈ Icc (0:ℝ) 1 ∧
    rowCanonicalFair ξ c g margin b ω ∈ Icc (0:ℝ) 1 ∧
    rowCanonicalDuplicate ξ c g margin b ω ∈ Icc (0:ℝ) 1 := by
  dsimp only [rowCanonicalFirst,rowCanonicalFair,rowCanonicalDuplicate]
  have hp := complement_bounds hξ hξ1 (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) ∅ 0
  have hα := guardAlpha_bounds ξ {g with countMargin := margin (fun j => (ω j).1)}
    (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
  split_ifs
  · refine ⟨⟨?_,?_⟩,hp,⟨sq_nonneg _,?_⟩⟩ <;> nlinarith [hp.1,hp.2]
  · have hS := expect_first_bounds
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) 0
    have hC := expect_fair_bounds
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) 0
    have hD := expect_duplicate_bounds
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) 0
    refine ⟨⟨mul_nonneg hα.1 hS.1,?_⟩,
      ⟨mul_nonneg hα.1 hC.1,?_⟩,⟨mul_nonneg hα.1 hD.1,?_⟩⟩
    · exact (mul_le_mul_of_nonneg_right hα.2 hS.1).trans (by simpa only [one_mul] using hS.2)
    · exact (mul_le_mul_of_nonneg_right hα.2 hC.1).trans (by simpa only [one_mul] using hC.2)
    · exact (mul_le_mul_of_nonneg_right hα.2 hD.1).trans (by simpa only [one_mul] using hD.2)

private theorem measurable_canonical_row_test
    (b : ℝ) (f : (Fin N → Fin 4) → (Fin (N+1) → ℝ) → ℝ)
    (hf : ∀ k, Measurable (f k)) :
    Measurable (fun ω : Fin N → RowRival => f (fun j => (ω j).1) (rowBids b ω)) := by
  have hk : Measurable (fun ω : Fin N → RowRival => fun j => (ω j).1) :=
    measurable_pi_lambda _ fun j => (measurable_pi_apply j).fst
  have hb : Measurable (fun ω : Fin N → RowRival => rowBids b ω) :=
    measurable_rowBids.comp (measurable_const.prodMk measurable_id)
  have hh : Measurable (fun p : (Fin N → Fin 4) × (Fin (N+1) → ℝ) => f p.1 p.2) :=
    measurable_from_prod_countable_right hf
  exact hh.comp (hk.prodMk hb)

theorem measurable_rowCanonical (ξ : ℝ) (c : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    Measurable (rowCanonicalFirst ξ c g margin b) ∧
    Measurable (rowCanonicalFair ξ c g margin b) ∧
    Measurable (rowCanonicalDuplicate ξ c g margin b) := by
  have hp : Measurable (fun ω : Fin N → RowRival =>
      complementMarginal ξ (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) ∅ 0) := by
    apply measurable_canonical_row_test b (fun k B => complementMarginal ξ (patternTemplate c k) B ∅ 0)
    intro k
    exact measurable_complementMarginal hξ hξ1 (patternTemplate c k) ∅ 0
  have hα : Measurable (fun ω : Fin N → RowRival =>
      guardAlpha ξ {g with countMargin := margin (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)) := by
    apply measurable_canonical_row_test b (fun k B =>
      guardAlpha ξ {g with countMargin := margin k} (patternTemplate c k) B)
    intro k
    exact measurable_guardAlpha ξ {g with countMargin := margin k} (patternTemplate c k)
  have hS : Measurable (fun ω : Fin N → RowRival =>
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)).expect (first 0)) := by
    apply measurable_canonical_row_test b (fun k B => (canonicalLaw ξ g (patternTemplate c k) B).expect (first 0))
    intro k
    exact measurable_canonical_first hξ hξ1 g (patternTemplate c k) 0
  have hC : Measurable (fun ω : Fin N → RowRival =>
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)).expect (fairMarginal 0)) := by
    apply measurable_canonical_row_test b (fun k B => (canonicalLaw ξ g (patternTemplate c k) B).expect (fairMarginal 0))
    intro k
    exact measurable_canonical_fair hξ hξ1 g (patternTemplate c k) 0
  have hD : Measurable (fun ω : Fin N → RowRival =>
      (canonicalLaw ξ g (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)).expect (duplicate 0)) := by
    apply measurable_canonical_row_test b (fun k B => (canonicalLaw ξ g (patternTemplate c k) B).expect (duplicate 0))
    intro k
    exact measurable_canonical_duplicate hξ hξ1 g (patternTemplate c k) 0
  have he := EqualCanonicalRegularity.measurableSet_equalResidual (N := N) c
  exact ⟨Measurable.ite he ((measurable_const.mul hp).sub (hp.pow_const 2)) (hα.mul hS),
    Measurable.ite he hp (hα.mul hC),Measurable.ite he (hp.pow_const 2) (hα.mul hD)⟩

theorem integrable_rowCanonical {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ)
    (P : Measure (Fin N → RowRival)) [IsFiniteMeasure P] :
    Integrable (rowCanonicalFirst ξ c g margin b) P ∧
    Integrable (rowCanonicalFair ξ c g margin b) P ∧
    Integrable (rowCanonicalDuplicate ξ c g margin b) P := by
  have hm := measurable_rowCanonical ξ c g margin b hξ hξ1
  have hb := row_canonical_bounds hξ hξ1 c g margin b
  exact ⟨Integrable.of_mem_Icc 0 1 hm.1.aemeasurable (Eventually.of_forall fun ω => (hb ω).1),
    Integrable.of_mem_Icc 0 1 hm.2.1.aemeasurable (Eventually.of_forall fun ω => (hb ω).2.1),
    Integrable.of_mem_Icc 0 1 hm.2.2.aemeasurable (Eventually.of_forall fun ω => (hb ω).2.2)⟩

theorem row_first_decomposition
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc 0 B)
    (ω : Fin N → RowRival) :
    (rowLaw ξ κ c g margin b ω).expect (first 0)=
      rowUnequalPureFirst κ c b ω+rowCanonicalFirst ξ c g margin b ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  by_cases he : T.residual₀=T.residual₁
  · have heRow : rowResidual c 0 ω=rowResidual c 1 ω := he
    dsimp only [T] at he
    simp only [rowLaw,continuationLaw,if_pos he,empty_completion_first hξ hξ1,
      rowUnequalPureFirst,if_pos heRow,rowCanonicalFirst,zero_add]
  · have hh := (unequal_prefix_add (ξ := ξ) hκ1
      {g with countMargin := margin (fun j => (ω j).1)} T (rowBids b ω)
      hg.margin_pos hg.population_pos hg.rejectionScale_pos (rowBids_outside c b ω)
      0 (by simpa [rowBids] using hb.1) (by simpa [rowBids] using hb.2.trans hg.rejection) he).1
    have heRow : ¬ rowResidual c 0 ω=rowResidual c 1 ω := he
    dsimp only [T] at he hh
    simpa only [rowLaw,rowUnequalPureFirst,rowPureSelection,rowCanonicalFirst,
      if_neg he,if_neg heRow,canonicalLaw_update_countMargin] using hh

theorem row_canonical_first_monotone
    {ξ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) (ω : Fin N → RowRival)
    (hω : ∀ j, (ω j).1=0 → 0 ≤ (ω j).2) :
    MonotoneOn (fun b => rowCanonicalFirst ξ c g margin b ω) (Icc 0 B) := by
  let T := patternTemplate c (fun j => (ω j).1)
  by_cases he : T.residual₀=T.residual₁
  · dsimp only [T] at he
    intro x hx y hy hxy
    simp only [rowCanonicalFirst,if_pos he]
    have hm := complement_marginal_update_monotone hξ hξ1 T (rowBids 0 ω) 0
      (fun j _ => rowBids_nonneg 0 ω le_rfl hω j) ∅ hx.1 hxy
    simp only [rowBids_update] at hm
    have hpx := complement_bounds hξ hξ1 T (rowBids x ω) ∅ 0
    have hpy := complement_bounds hξ hξ1 T (rowBids y ω) ∅ 0
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) (show 0 ≤
      2-complementMarginal ξ T (rowBids x ω) ∅ 0-complementMarginal ξ T (rowBids y ω) ∅ 0 by linarith [hpx.2,hpy.2])]
  · have hh := (guarded_canonical_prefix_monotone hξ hξ1
      {g with countMargin := margin (fun j => (ω j).1)} T (rowBids 0 ω) 0
      (focal_mem_patternTemplate c _) (fun j _ => rowBids_nonneg 0 ω le_rfl hω j)
      (rowBids_outside c 0 ω) hg.margin_pos hg.population_pos hg.radius_nonneg
      hg.requiredDemand_pos hg.lower_pos hg.seed_below_lower hg.upper hg.rejection
      (PrefixConditions.zero_eligibility hξ (hg.update_countMargin _))).1
    dsimp only [T] at he hh
    simpa only [rowCanonicalFirst,if_neg he,rowBids_update,canonicalLaw_update_countMargin] using hh

def actualCanonicalFirst (t ξ : ℝ) (G : Measure ℝ) (c N : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  ∫ ω : Fin N → RowRival, rowCanonicalFirst ξ c g margin b ω
    ∂Measure.pi (fun _ : Fin N => sourceRivalLaw t G)

theorem actual_first_bounds {t ξ κ : ℝ} (ht : t ∈ Icc 0 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) :
    actualSuccess t ξ κ G c N g margin b ∈ Icc (0:ℝ) 1 ∧
      actualDuplicate t ξ κ G c N g margin b ∈ Icc (0:ℝ) 1 := by
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hs := integrable_row_first hξ hξ1 κ c g margin b P
  have hd := integrable_row_duplicate hξ hξ1 κ c g margin b P
  refine ⟨⟨integral_nonneg fun ω => (continuation_first_bounds ξ κ _ _ _ _).1,?_⟩,
    ⟨integral_nonneg fun ω => (continuation_duplicate_bounds ξ κ _ _ _ _).1,?_⟩⟩
  · have hh := integral_mono_ae hs (integrable_const (1:ℝ))
      (Eventually.of_forall fun ω => (continuation_first_bounds ξ κ _ _ _ _).2)
    convert! hh using 1
    simp only [integral_const,probReal_univ,one_smul]
  · have hh := integral_mono_ae hd (integrable_const (1:ℝ))
      (Eventually.of_forall fun ω => (continuation_duplicate_bounds ξ κ _ _ _ _).2)
    convert! hh using 1
    simp only [integral_const,probReal_univ,one_smul]

theorem actual_canonical_first_eq {t ξ : ℝ} (ht : t ∈ Icc 0 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ) (b : ℝ) :
    actualCanonicalFirst t ξ G c N g margin b=
      2*actualCanonicalMarginal t ξ G c N g margin b-
        actualCanonicalDuplicate t ξ G c N g margin b := by
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hi := integrable_rowCanonical hξ hξ1 c g margin b P
  rw [actualCanonicalFirst]
  simp_rw [row_canonical_first_eq]
  rw [integral_sub (hi.2.1.const_mul 2) hi.2.2,integral_const_mul]
  rfl

theorem actual_first_decomposition
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc 0 B) :
    actualSuccess t ξ κ G c N g margin b=
      expectedUnequalPureFirst N c κ t G b+
        2*actualCanonicalMarginal t ξ G c N g margin b-
          actualCanonicalDuplicate t ξ G c N g margin b := by
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hi := integrable_rowCanonical hξ hξ1 c g margin b P
  have he : actualSuccess t ξ κ G c N g margin b=
      expectedUnequalPureFirst N c κ t G b+actualCanonicalFirst t ξ G c N g margin b := by
    unfold actualSuccess
    simp_rw [row_first_decomposition hξ hξ1 hκ1 c g hg margin hb]
    exact integral_add (integrable_rowUnequalPureFirst κ c b P) hi.1
  rw [he,actual_canonical_first_eq ht hξ hξ1]
  ring

theorem actual_canonical_first_monotone
    {t ξ B : ℝ} (ht : t ∈ Icc 0 1) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    MonotoneOn (fun b => 2*actualCanonicalMarginal t ξ G c N g margin b-
      actualCanonicalDuplicate t ξ G c N g margin b) (Icc 0 B) := by
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hn := iid_rows_ae_bid_nonnegative (N := N) (sourceRivalLaw t G)
    (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  intro x hx y hy hxy
  dsimp only
  rw [← actual_canonical_first_eq ht hξ hξ1,← actual_canonical_first_eq ht hξ hξ1]
  apply integral_mono_ae (integrable_rowCanonical hξ hξ1 c g margin x P).1
    (integrable_rowCanonical hξ hξ1 c g margin y P).1
  filter_upwards [hn] with ω hω
  exact row_canonical_first_monotone hξ hξ1 c g hg margin ω (fun j _ => hω j) hx hy hxy

end Row

theorem source_first_duplicate_bounds (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (g : GuardData)
    (margin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) :
    sourceSuccess i m G g margin b ∈ Icc (0:ℝ) 1 ∧
      sourceDuplicate i m G g margin b ∈ Icc (0:ℝ) 1 := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact actual_first_bounds (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) (G.map Prod.snd) (capacity m) g margin b

theorem source_first_decomposition (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc 0 B) :
    sourceSuccess i m G g margin b=
      expectedUnequalPureFirst (m-1) (capacity m) (kappa i) (cutoff i) (G.map Prod.snd) b+
        2*sourceCanonicalMarginal i m G g margin b-sourceCanonicalDuplicate i m G g margin b := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact actual_first_decomposition (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ])
    (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) (G.map Prod.snd) (capacity m) g hg margin hb

theorem source_canonical_first_monotone (i : Row) (m : ℕ)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (margin : (Fin (m-1) → Fin 4) → ℝ) :
    MonotoneOn (fun b => 2*sourceCanonicalMarginal i m G g margin b-
      sourceCanonicalDuplicate i m G g margin b) (Icc 0 B) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact actual_canonical_first_monotone (cutoff_mem i) (xi_pos i)
    (by cases i <;> norm_num [xi,xiQ,etaQ]) (G.map Prod.snd)
    (EqualCanonicalRegularity.source_floor_bid_nonnegative i G hfloor) (capacity m) g hg margin

end FCAppendix.Affine.Uniform06.LiteralKernelDecomposition
