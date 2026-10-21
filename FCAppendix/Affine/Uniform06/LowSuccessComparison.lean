import FCAppendix.Affine.Uniform06.LowRankMeasures
import FCAppendix.Affine.Uniform06.PureUnionUpper

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowSuccessComparison

open MeasureTheory Set Filter Topology LowBody
open Rank LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition
open LiteralPrefixStieltjes LiteralLowDuplicate LiteralSuccessLower LiteralWeakRent
open SourceGuardGeometry EqualCanonicalRegularity PureRankCounts PurePivotalSource
open PureRankProbability PureUnionUpper SourceRankRates LowRankMeasures
open FCAppendix.Affine.Uniform07

variable {N : ℕ}

theorem row_low_first_le_rank_and_equal_tail
    {ξ κ B z : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1) (hz : 0 < z)
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hBL : B ≤ g.multiplier-g.radius) (hBz : B ≤ z)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B)
    (ω : Fin N → RowRival) (hno : ∀ j, (ω j).1 ≠ 1) :
    (rowLaw ξ κ c g margin b ω).expect (first 0) ≤
      rowUnequalPureFirst κ c b ω+(scalarTailEvent ξ z c).indicator (fun _ => (1:ℝ)) ω := by
  by_cases he : rowResidual c 0 ω=rowResidual c 1 ω
  · have heT : (patternTemplate c (fun j => (ω j).1)).residual₀=
        (patternTemplate c (fun j => (ω j).1)).residual₁ := he
    have hs : (rowLaw ξ κ c g margin b ω).expect (first 0)=
        2*equalMarginal ξ c b ω-(equalMarginal ξ c b ω)^2 := by
      simp only [rowLaw,continuationLaw,if_pos heT,empty_completion_first hξ hξ1,
        row_complement_eq_equal ξ c b ω he]
    rw [hs]
    simp only [rowUnequalPureFirst,if_pos he,zero_add]
    by_cases ht : ω ∈ scalarTailEvent ξ z c
    · rw [indicator_of_mem ht]
      have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids b ω)
      have hsq := sq_nonneg (equalMarginal ξ c b ω-1)
      nlinarith
    · rw [indicator_of_notMem ht]
      have hp := EqualCapacity.positiveMarginal_spec ξ (rowResidual c 0 ω) hξ hξ1 (rowBids b ω)
      have hz' : equalMarginal ξ c b ω=0 := by
        apply le_antisymm _ (hp.1 0)
        apply le_of_not_gt
        intro hpos
        exact ht (equal_positive_implies_scalar_tail hξ hξ1 hz c ω hb (hbB.trans hBz) hno he hpos)
      rw [hz']
      norm_num
  · have hs := (unequal_low_full_eq_pure hξ hξ1 hκ1
      {g with countMargin := margin (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
      hg.margin_pos hg.population_pos hg.radius_nonneg hg.requiredDemand_pos
      hg.rejectionScale_pos hg.lower_pos (rowBids_outside c b ω) 0
      (by simpa only [rowBids,Fin.cons_zero] using hb.le)
      (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hBL)
      (by simpa only [rowBids,Fin.cons_zero] using hbB.trans hg.rejection) he).1
    change (rowLaw ξ κ c g margin b ω).expect (first 0)=_ at hs
    rw [hs]
    simp only [rowUnequalPureFirst,if_neg he]
    exact le_add_of_nonneg_right (by unfold Set.indicator; split_ifs <;> norm_num)

theorem actual_low_first_le_rank_and_equal_tail
    {t ξ κ B z : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1) (hz : 0 < z)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (hBL : B ≤ g.multiplier-g.radius) (hBz : B ≤ z)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B) :
    actualSuccess t ξ κ G c N g margin b ≤ expectedUnequalPureFirst N c κ t G b+
      (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real (scalarTailEvent ξ z c) := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have hE := measurableSet_scalarTailEvent (N := N) hξ hz c
  have hiE := (integrable_const (1:ℝ) (μ := P)).indicator hE
  have hpoint : ∀ᵐ ω ∂P, (rowLaw ξ κ c g margin b ω).expect (first 0) ≤
      rowUnequalPureFirst κ c b ω+(scalarTailEvent ξ z c).indicator (fun _ => (1:ℝ)) ω := by
    filter_upwards [source_iid_row_no_active ht G] with ω hω
    exact row_low_first_le_rank_and_equal_tail hξ hξ1 hκ1 hz c g hg hBL hBz margin hb hbB ω hω
  have hh := integral_mono_ae (integrable_row_first hξ hξ1 κ c g margin b P)
    ((integrable_rowUnequalPureFirst κ c b P).add hiE) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_rowUnequalPureFirst κ c b P) hiE,integral_indicator_const (1:ℝ) hE] at hh
  simpa only [smul_eq_mul,mul_one] using! hh

theorem source_low_first_upper (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (hBL : B ≤ g.multiplier-g.radius) (hBZ : B ≤ extensionEnd i)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ} (hb : 0 < b) (hbB : b ≤ B)
    (hatom : (G.map Prod.snd) {b}=0)
    (hM : sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i) :
    sourceSuccess i m G g margin b ≤
      2*pureRank (m-1) (capacity m) ((1+cutoff i)/2)
        (sourceRank (cutoff i) (G.map Prod.snd) b)+pureRare m+equalRare i m := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hs := actual_low_first_le_rank_and_equal_tail (cutoff_mem i) (xi_pos i)
    (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
    (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
    (show 0 < extensionEnd i from mul_pos (by norm_num) (cutoff_pos i))
    Gb (capacity m) g hg hBL hBZ margin hb hbB
  have hp := source_pure_union_upper i hm Gb hb hatom hM
  have he := source_equal_tail_chernoff i G hvalue hfloor (show 2 ≤ m by omega)
  have hh := hs.trans (add_le_add hp he)
  convert! hh using 1

theorem eventually_source_low_success_comparable (i : Row) :
    ∀ᶠ m : ℕ in atTop, ∀ (G : Measure (ℝ × ℝ)) (_hG : IsProbabilityMeasure G),
      G.map Prod.fst=LowChernoff.conditionalValueLaw i →
      (∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2) →
      (∀ b : ℝ, (G.map Prod.snd) {b}=0) →
      ∀ (g : GuardData) (B : ℝ) (margin : (Fin (m-1) → Fin 4) → ℝ),
      PrefixConditions (xi i) g B → B ≤ g.multiplier-g.radius → B ≤ extensionEnd i →
      ∀ b : ℝ, 0 < b → b ≤ B →
      sourceRank (cutoff i) (G.map Prod.snd) b ≤ RankCutoff.Mstar i →
      let Q := pureRank (m-1) (capacity m) ((1+cutoff i)/2)
        (sourceRank (cutoff i) (G.map Prod.snd) b)
      Q/2 ≤ sourceSuccess i m G g margin b ∧
        sourceSuccess i m G g margin b ≤ 3*Q ∧
        sourceSuccess i m G g margin b+eta i*sourceDuplicate i m G g margin b ≤ 4*Q := by
  obtain ⟨γ,hγ,hrel⟩ := eventually_source_pure_relative i
  have ht₁ := tendsto_exp_affine_nat hγ 0
  have ht₂ := tendsto_exp_affine_nat (by norm_num : (0:ℝ) < 6/1000000) 0
  have ht : Tendsto (fun m : ℕ => Real.exp (-γ*m)+Real.exp (-(6/1000000:ℝ)*m)) atTop (𝓝 0) := by
    convert! ht₁.add ht₂ using 1
    · funext m
      congr 1 <;> congr 1 <;> ring
    · simp
  filter_upwards [hrel,eventually_source_rare_small i,eventually_ge_atTop (4:ℕ),
    ht.eventually_lt_const (by norm_num : (0:ℝ) < 1/2)] with m hrel hrare hm herror
  intro G hG hv hf ha g B margin hg hBL hBZ b hb hbB hM
  letI := hG
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let Q := pureRank (m-1) (capacity m) ((1+cutoff i)/2) (sourceRank (cutoff i) Gb b)
  have hLQ : Lm i m ≤ Q :=
    unilateral_le_pureRank (cutoff_pos i).le (cutoff_lt_one i) Gb b (m-1) (capacity m)
  have hQ : 0 < Q := (Lm_mem_Ioc i hm).1.trans_le hLQ
  have hqrel := (abs_le.mp (hrel Gb inferInstance b hb (ha b) hM)).1
  have hq : Q/2 ≤ qPure (m-1) (capacity m) (kappa i) (cutoff i) Gb b := by
    have hr : (1/2:ℝ) ≤ qPure (m-1) (capacity m) (kappa i) (cutoff i) Gb b/Q := by linarith
    have hh := (le_div_iff₀ hQ).mp hr
    linarith
  have hslo := hq.trans ((qPure_le_unequal_first (κ := kappa i) (cutoff_mem i) Gb
    (m-1) (capacity m) b).trans
      (unequal_first_le_actual (cutoff_mem i) (xi_pos i)
        (show xi i < 1 by cases i <;> norm_num [xi,xiQ,etaQ])
        (show kappa i ≤ 1 by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ])
        Gb (m-1) (capacity m) g hg margin ⟨hb.le,hbB⟩))
  have hshi := source_low_first_upper i hm G hv hf g hg hBL hBZ margin hb hbB (ha b) hM
  have hD := (source_actual_duplicate_level_and_interval i G hv hf ha hm g hg hBL
    (hBZ.trans (lowEnd_bounds i).2.2.2.le) hBZ margin).1 b hb hbB
  have hη : eta i ∈ Icc (0:ℝ) 1 := by cases i <;> norm_num [eta,etaQ]
  have hR : pureRare m+equalRare i m ≤ Q/10 := hrare.1.trans (by linarith)
  have hηD := mul_le_mul_of_nonneg_left hD hη.1
  have hηR := mul_le_mul_of_nonneg_right hη.2
    (show 0 ≤ pureRare m+equalRare i m by unfold pureRare equalRare; positivity)
  change sourceSuccess i m G g margin b ≤ 2*Q+pureRare m+equalRare i m at hshi
  refine ⟨hslo,?_,?_⟩ <;> nlinarith

end FCAppendix.Affine.Uniform06.LowSuccessComparison
