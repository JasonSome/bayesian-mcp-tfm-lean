import FCAppendix.Affine.Uniform06.LiteralKernelMeasurable
import FCAppendix.Affine.Uniform06.SourcePivotalRates
import FCAppendix.Affine.Uniform06.SourcePureDuplicate

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralPrefixStieltjes

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelMeasurable GuardPrefix
open PureRankCounts PureDuplicateIntervals PurePivotalSource
open FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.Uniform07

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure PrefixConditions (ξ : ℝ) (g : GuardData) (B : ℝ) : Prop where
  margin_pos : 0 < g.margin
  population_pos : 0 < g.population
  radius_nonneg : 0 ≤ g.radius
  requiredDemand_pos : 0 < g.requiredDemand
  rejectionScale_pos : 0 < g.rejectionScale
  lower_pos : 0 < g.multiplier-g.radius
  seed_below_lower : g.seedCutoff < g.multiplier-g.radius
  upper : B ≤ g.multiplier+g.radius
  rejection : B ≤ g.rejectionRoot
  radius_small : g.radius ≤ ξ*g.requiredDemand*g.multiplier/4

theorem PrefixConditions.zero_eligibility {ξ B : ℝ} {g : GuardData}
    (hξ : 0 < ξ) (hg : PrefixConditions ξ g B) :
    ∀ x, x ≤ B → FiniteGuards.eligibility ξ g.multiplier g.requiredDemand x=0 :=
  eligibility_zero_on_small_prefix hξ (by linarith [hg.lower_pos,hg.radius_nonneg])
    hg.requiredDemand_pos hg.radius_nonneg hg.radius_small hg.upper

theorem PrefixConditions.update_countMargin {ξ B : ℝ} {g : GuardData}
    (hg : PrefixConditions ξ g B) (s : ℝ) :
    PrefixConditions ξ {g with countMargin := s} B := by
  exact ⟨hg.margin_pos,hg.population_pos,hg.radius_nonneg,hg.requiredDemand_pos,
    hg.rejectionScale_pos,hg.lower_pos,hg.seed_below_lower,hg.upper,hg.rejection,hg.radius_small⟩

omit [Nonempty ι] in
theorem complement_bounds {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (T : PureTemplate ι) (b : ι → ℝ) (E : Finset ι) (j : ι) :
    complementMarginal ξ T b E j ∈ Icc (0:ℝ) 1 := by
  have hh := EqualCapacity.positiveMarginal_spec ξ (small T) hξ hξ1 (maskedBids T b E)
  exact ⟨hh.1 j,hh.2.1 j⟩

theorem continuation_first_increment_ge_unequal
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (g : GuardData) (hg : PrefixConditions ξ g B)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hout : ∀ k, k ∉ T.support → b k=0)
    {x y : ℝ} (hx : x ∈ Icc 0 B) (hy : y ∈ Icc 0 B) (hxy : x ≤ y) :
    (if T.residual₀=T.residual₁ then 0 else
      first j (T.selection κ (Function.update b j y))-
        first j (T.selection κ (Function.update b j x))) ≤
      (continuationLaw ξ κ g T (Function.update b j y)).expect (first j)-
        (continuationLaw ξ κ g T (Function.update b j x)).expect (first j) := by
  by_cases he : T.residual₀=T.residual₁
  · simp only [if_pos he,continuationLaw,empty_completion_first hξ hξ1]
    have hp := complement_marginal_update_monotone hξ hξ1 T b j hb ∅ hx.1 hxy
    have hpx := complement_bounds hξ hξ1 T (Function.update b j x) ∅ j
    have hpy := complement_bounds hξ hξ1 T (Function.update b j y) ∅ j
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show 0 ≤
      2-complementMarginal ξ T (Function.update b j x) ∅ j-
        complementMarginal ξ T (Function.update b j y) ∅ j by linarith [hpx.2,hpy.2])]
  · have hm := (guarded_canonical_prefix_monotone hξ hξ1 g T b j hj hb hout
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.lower_pos hg.seed_below_lower hg.upper hg.rejection
      (PrefixConditions.zero_eligibility hξ hg)).1 hx hy hxy
    have hout' (z : ℝ) : ∀ k, k ∉ T.support → Function.update b j z k=0 := by
      intro k hk
      have hkj : k ≠ j := fun hh => hk (hh ▸ hj)
      rw [Function.update_of_ne hkj,hout k hk]
    have hxe := (unequal_prefix_add (ξ := ξ) hκ1 g T (Function.update b j x)
      hg.margin_pos hg.population_pos hg.rejectionScale_pos (hout' x) j
      (by simpa using hx.1) (by simpa using hx.2.trans hg.rejection) he).1
    have hye := (unequal_prefix_add (ξ := ξ) hκ1 g T (Function.update b j y)
      hg.margin_pos hg.population_pos hg.rejectionScale_pos (hout' y) j
      (by simpa using hy.1) (by simpa using hy.2.trans hg.rejection) he).1
    rw [if_neg he,hxe,hye]
    linarith

theorem continuation_prefix_monotone
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (g : GuardData) (hg : PrefixConditions ξ g B)
    (T : PureTemplate ι) (b : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (hb : ∀ k, k ≠ j → 0 ≤ b k) (hout : ∀ k, k ∉ T.support → b k=0) :
    MonotoneOn (fun x => (continuationLaw ξ κ g T (Function.update b j x)).expect (first j)) (Icc 0 B) ∧
    MonotoneOn (fun x => (continuationLaw ξ κ g T (Function.update b j x)).expect (duplicate j)) (Icc 0 B) := by
  by_cases he : T.residual₀=T.residual₁
  · constructor
    · intro x hx y hy hxy
      have hh := continuation_first_increment_ge_unequal hξ hξ1 hκ1 g hg T b j hj hb hout hx hy hxy
      rw [if_pos he] at hh
      linarith
    · intro x hx y hy hxy
      simp only [continuationLaw,if_pos he,empty_completion_duplicate hξ hξ1]
      have hm := complement_marginal_update_monotone hξ hξ1 T b j hb ∅ hx.1 hxy
      have hp := complement_bounds hξ hξ1 T (Function.update b j x) ∅ j
      have hq := complement_bounds hξ hξ1 T (Function.update b j y) ∅ j
      nlinarith [hp.1,hq.1]
  · exact actual_unequal_prefix_monotone hξ hξ1 hκ hκ1 g T b j hj hb hout
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.rejectionScale_pos hg.lower_pos hg.seed_below_lower hg.upper hg.rejection
      (PrefixConditions.zero_eligibility hξ hg) he

section Row
variable {N : ℕ}

theorem row_first_increment_ge_unequal
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) (ω : Fin N → RowRival)
    (hω : ∀ k, (ω k).1=0 → 0 ≤ (ω k).2)
    {x y : ℝ} (hx : x ∈ Icc 0 B) (hy : y ∈ Icc 0 B) (hxy : x ≤ y) :
    rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω ≤
      (rowLaw ξ κ c g margin y ω).expect (first 0)-
        (rowLaw ξ κ c g margin x ω).expect (first 0) := by
  have hh := continuation_first_increment_ge_unequal hξ hξ1 hκ1
    {g with countMargin := margin (fun k => (ω k).1)} (hg.update_countMargin _)
    (patternTemplate c (fun k => (ω k).1)) (rowBids 0 ω) 0
    (focal_mem_patternTemplate c _) (fun k _ => rowBids_nonneg 0 ω le_rfl hω k)
    (rowBids_outside c 0 ω) hx hy hxy
  simp only [rowBids_update] at hh
  unfold rowUnequalPureFirst
  split_ifs with he
  · change (patternTemplate c (fun k => (ω k).1)).residual₀ =
      (patternTemplate c (fun k => (ω k).1)).residual₁ at he
    simpa only [rowLaw,if_pos he,sub_self] using hh
  · change ¬ (patternTemplate c (fun k => (ω k).1)).residual₀ =
      (patternTemplate c (fun k => (ω k).1)).residual₁ at he
    simpa only [rowLaw,rowPureSelection,if_neg he] using hh

theorem row_prefix_monotone
    {ξ κ B : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) (ω : Fin N → RowRival)
    (hω : ∀ k, (ω k).1=0 → 0 ≤ (ω k).2) :
    MonotoneOn (fun x => (rowLaw ξ κ c g margin x ω).expect (first 0)) (Icc 0 B) ∧
    MonotoneOn (fun x => (rowLaw ξ κ c g margin x ω).expect (duplicate 0)) (Icc 0 B) := by
  have hh := continuation_prefix_monotone hξ hξ1 hκ hκ1
    {g with countMargin := margin (fun k => (ω k).1)} (hg.update_countMargin _)
    (patternTemplate c (fun k => (ω k).1)) (rowBids 0 ω) 0
    (focal_mem_patternTemplate c _) (fun k _ => rowBids_nonneg 0 ω le_rfl hω k)
    (rowBids_outside c 0 ω)
  simpa only [rowLaw,rowBids_update] using hh

theorem original_common_conull_prefix
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => sourceRivalLaw t G),
      (MonotoneOn (fun x => (rowLaw ξ κ c g margin x ω).expect (first 0)) (Icc 0 B) ∧
       MonotoneOn (fun x => (rowLaw ξ κ c g margin x ω).expect (duplicate 0)) (Icc 0 B)) ∧
      ∀ x ∈ Icc 0 B, ∀ y ∈ Icc 0 B, x ≤ y →
        rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω ≤
          (rowLaw ξ κ c g margin y ω).expect (first 0)-
            (rowLaw ξ κ c g margin x ω).expect (first 0) := by
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  have hn := iid_rows_ae_bid_nonnegative (N := N) (sourceRivalLaw t G)
    (rivalLaw_ae_bid_nonnegative t 0 (1-t) G hG)
  filter_upwards [hn] with ω hω
  refine ⟨row_prefix_monotone hξ hξ1 hκ hκ1 c g hg margin ω (fun j _ => hω j),?_⟩
  intro x hx y hy hxy
  exact row_first_increment_ge_unequal hξ hξ1 hκ1 c g hg margin ω (fun j _ => hω j) hx hy hxy

theorem actual_prefix_monotone
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) :
    MonotoneOn (actualSuccess t ξ κ G c N g margin) (Icc 0 B) ∧
    MonotoneOn (actualDuplicate t ξ κ G c N g margin) (Icc 0 B) := by
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  have hrows := original_common_conull_prefix ht hξ hξ1 hκ hκ1 G hG c g hg margin
  constructor
  · intro x hx y hy hxy
    apply integral_mono_ae (integrable_row_first hξ hξ1 κ c g margin x _)
      (integrable_row_first hξ hξ1 κ c g margin y _)
    filter_upwards [hrows] with ω hω
    exact hω.1.1 hx hy hxy
  · intro x hx y hy hxy
    apply integral_mono_ae (integrable_row_duplicate hξ hξ1 κ c g margin x _)
      (integrable_row_duplicate hξ hξ1 κ c g margin y _)
    filter_upwards [hrows] with ω hω
    exact hω.1.2 hx hy hxy

theorem actual_first_increment_ge_unequal
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hG : ∀ᵐ b ∂G, 0 ≤ b)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ)
    {x y : ℝ} (hx : x ∈ Icc 0 B) (hy : y ∈ Icc 0 B) (hxy : x ≤ y) :
    expectedUnequalPureFirst N c κ t G y-expectedUnequalPureFirst N c κ t G x ≤
      actualSuccess t ξ κ G c N g margin y-actualSuccess t ξ κ G c N g margin x := by
  letI : IsProbabilityMeasure (rivalLaw t 0 (1-t) G) := sourceRivalLaw_probability ht G
  letI : IsProbabilityMeasure (sourceRivalLaw t G) := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hrows := original_common_conull_prefix ht hξ hξ1 hκ hκ1 G hG c g hg margin
  have hh := integral_mono_ae
    ((integrable_rowUnequalPureFirst κ c y P).sub (integrable_rowUnequalPureFirst κ c x P))
    ((integrable_row_first hξ hξ1 κ c g margin y P).sub (integrable_row_first hξ hξ1 κ c g margin x P))
    (by filter_upwards [hrows] with ω hω; exact hω.2 x hx y hy hxy)
  change (∫ ω, rowUnequalPureFirst κ c y ω-rowUnequalPureFirst κ c x ω ∂P) ≤
    (∫ ω, (rowLaw ξ κ c g margin y ω).expect (first 0)-
      (rowLaw ξ κ c g margin x ω).expect (first 0) ∂P) at hh
  rw [integral_sub (integrable_rowUnequalPureFirst κ c y P) (integrable_rowUnequalPureFirst κ c x P),
    integral_sub (integrable_row_first hξ hξ1 κ c g margin y P) (integrable_row_first hξ hξ1 κ c g margin x P)] at hh
  exact hh

end Row

theorem source_actual_first_pivotal_interval (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      (∀ᵐ p ∂G, 0 ≤ p.2) → (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (B : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g B →
      (∀ b, b ∈ Ioc 0 B → sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, 0 < x → x < y → y ≤ B → y-x ≤ δ →
        ((m:ℝ)/80000)*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
          (sourceRank (cutoff i) (G.map Prod.snd) y)*
          (cutoff i*(G.map Prod.snd).real (Ioc x y)) ≤
          sourceSuccess i m G g margin y-sourceSuccess i m G g margin x := by
  filter_upwards [SourcePivotalRates.eventually_first_pivotal_short_bid_interval i] with m hm
  intro G hG hnon hatom g B margin hg hM
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hb : ∀ᵐ b ∂Gb, 0 ≤ b := (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr hnon
  obtain ⟨δ,hδ,hfirst⟩ := hm Gb inferInstance hatom B hM
  refine ⟨δ,hδ,?_⟩
  intro x y hx hxy hy hδxy
  exact (hfirst x y hx hxy hy hδxy).trans
    (actual_first_increment_ge_unequal (cutoff_mem i) (xi_pos i)
      (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
      (show 0 < kappa i by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
      (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
      Gb hb (capacity m) g hg margin ⟨hx.le,hxy.le.trans hy⟩ ⟨(hx.trans hxy).le,hy⟩ hxy.le)

end FCAppendix.Affine.Uniform06.LiteralPrefixStieltjes
