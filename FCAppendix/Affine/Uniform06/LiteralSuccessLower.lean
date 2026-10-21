import FCAppendix.Affine.Uniform06.LiteralLowDuplicate

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralSuccessLower

open MeasureTheory Set Filter LowBody
open LiteralExperiment LiteralKernelMeasurable LiteralKernelDecomposition LiteralPrefixStieltjes
open PureRankCounts PureRankSelector PureRankProbability PurePivotalSource SourceRankRates
open FCAppendix.Affine.Uniform07
open scoped BigOperators

variable {N : ℕ}

theorem count_add_complement {Ω : Type*} (E : Set Ω) (ω : Fin N → Ω) :
    PiBinomial.count E Finset.univ ω+PiBinomial.count Eᶜ Finset.univ ω=N := by
  classical
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum,← Finset.sum_add_distrib]
  have he : (∑ j : Fin N, ((if ω j ∈ E then 1 else 0)+(if ω j ∈ Eᶜ then 1 else 0)))=
      ∑ _j : Fin N, (1:ℕ) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ω j ∈ E <;> simp [hj]
  simpa using! he

theorem unilateral_event_in_main (c : ℕ) (hcap : 2*c ≤ N+1) (b : ℝ)
    (ω : Fin N → RowRival)
    (hω : PiBinomial.count otherUpperᶜ Finset.univ ω< c) :
    PiBinomial.count (higherAtSet b) Finset.univ ω< c ∧
      c ≤ PiBinomial.count otherUpper Finset.univ ω := by
  have hsub : higherAtSet b ⊆ otherUpperᶜ := by
    intro r hr ho
    exact Set.disjoint_left.mp (disjoint_higher_other b) hr ho
  refine ⟨(count_mono_of_subset hsub ω).trans_lt hω,?_⟩
  have hh := count_add_complement otherUpper ω
  omega

theorem unilateral_le_qPure {t κ b : ℝ} (ht : t ∈ Icc 0 1) (hb : 0 < b)
    (G : Measure ℝ) [IsProbabilityMeasure G] (hatom : G {b}=0)
    (N c : ℕ) (hcap : 2*c ≤ N+1) :
    Bayes.binomBelow N ((1+t)/2) c ≤ qPure N c κ t G b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  let E : Set (Fin N → RowRival) := {ω | PiBinomial.count otherUpperᶜ Finset.univ ω< c}
  have hprob : P.real E=Bayes.binomBelow N ((1+t)/2) c := by
    have hp : (sourceRivalLaw t G).real otherUpperᶜ=(1+t)/2 := by
      rw [probReal_compl_eq_one_sub measurableSet_otherUpper,source_other_probability ht.2 G b]
      ring
    simpa only [P,E,Finset.card_univ,Fintype.card_fin,hp] using
      iid_count_lt_eq_binomBelow (sourceRivalLaw t G) otherUpperᶜ
        measurableSet_otherUpper.compl (Finset.univ : Finset (Fin N)) c
  rw [← hprob]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [source_iid_row_no_tie ht G hatom] with ω hω hE
  have hh := unilateral_event_in_main c hcap b ω hE
  exact main_event_in_unequal_pure c κ hb ω hω.2 hh.1 hh.2

theorem qPure_le_unequal_first {t κ : ℝ} (ht : t ∈ Icc 0 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N c : ℕ) (b : ℝ) :
    qPure N c κ t G b ≤ expectedUnequalPureFirst N c κ t G b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  have he := measurableSet_unequalPureLeftEvent (N := N) κ c b
  have hh := integral_mono_ae ((integrable_const (1:ℝ)).indicator he)
    (integrable_rowUnequalPureFirst κ c b P) (Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ unequalPureLeftEvent κ c b
      · rw [indicator_of_mem hω]
        simp only [rowUnequalPureFirst,if_neg hω.1,first_eq_indicator,
          if_pos (Finset.mem_union_left _ hω.2)]
        exact le_rfl
      · rw [indicator_of_notMem hω]
        exact (rowUnequalPureFirst_bounds κ c b ω).1)
  rw [integral_indicator_const (1:ℝ) he] at hh
  simp only [smul_eq_mul,mul_one] at hh
  exact hh

theorem unequal_first_le_actual
    {t ξ κ B : ℝ} (ht : t ∈ Icc 0 1) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ1 : κ ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (N c : ℕ) (g : GuardData) (hg : PrefixConditions ξ g B)
    (margin : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b ∈ Icc 0 B) :
    expectedUnequalPureFirst N c κ t G b ≤ actualSuccess t ξ κ G c N g margin b := by
  letI := sourceRivalLaw_probability ht G
  let P := Measure.pi fun _ : Fin N => sourceRivalLaw t G
  apply integral_mono_ae (integrable_rowUnequalPureFirst κ c b P)
    (integrable_row_first hξ hξ1 κ c g margin b P)
  exact Eventually.of_forall fun ω => by
    change rowUnequalPureFirst κ c b ω ≤ (rowLaw ξ κ c g margin b ω).expect (first 0)
    rw [row_first_decomposition hξ hξ1 hκ1 c g hg margin hb ω]
    exact le_add_of_nonneg_right (row_canonical_bounds hξ hξ1 c g margin b ω).1.1

theorem source_actual_success_ge_Lm (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) {B : ℝ} (hg : PrefixConditions (xi i) g B)
    (margin : (Fin (m-1) → Fin 4) → ℝ) {b : ℝ}
    (hb : 0 < b) (hbB : b ≤ B) (hatom : (G.map Prod.snd) {b}=0) :
    Lm i m ≤ sourceSuccess i m G g margin b := by
  let Gb := G.map Prod.snd
  letI : IsProbabilityMeasure Gb := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hcap : 2*capacity m ≤ m-1+1 := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega)] using source_capacity_twice m
  have hh := unilateral_le_qPure (κ := kappa i) (cutoff_mem i) hb Gb hatom (m-1) (capacity m) hcap
  exact hh.trans ((qPure_le_unequal_first (κ := kappa i) (cutoff_mem i) Gb (m-1) (capacity m) b).trans
    (unequal_first_le_actual (cutoff_mem i) (xi_pos i)
      (by cases i <;> norm_num [xi,xiQ,etaQ])
      (by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]) Gb (m-1) (capacity m) g hg margin ⟨hb.le,hbB⟩))

theorem Lm_mem_Ioc (i : Row) {m : ℕ} (hm : 4 ≤ m) : Lm i m ∈ Ioc (0:ℝ) 1 := by
  have hp := source_rank_parameter i
  refine ⟨Bayes.binomBelow_pos (m-1) (capacity m)
    (PhysicalRates.capacity_positive (show 3 ≤ m by omega)) _ hp,?_⟩
  unfold Lm
  rw [Bayes.binomBelow_eq_prob (m-1) (capacity m) (by
    have hh := PhysicalRates.capacity_strictly_below_rivals hm
    omega) _ hp.1.le hp.2.le]
  exact FiniteLaw.prob_le_one _ _

end FCAppendix.Affine.Uniform06.LiteralSuccessLower
