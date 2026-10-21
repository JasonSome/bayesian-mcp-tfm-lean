import FCAppendix.Affine.Uniform06.SourceCanonicalOptimizer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.CanonicalPureTransfer

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment LiteralPureComponents LiteralKernelDecomposition
open PurePivotalSource PureDuplicateIntervals CanonicalOptimizer LiteralPrefixStieltjes PureRankCounts

def single (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) (v b : ℝ) : ℝ :=
  (v-b)*(sourceSuccess i m G g cm b+sourceDuplicate i m G g cm b)/2

def broadcast (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) (v b : ℝ) : ℝ :=
  Rank.payoff (eta i) v b (sourceSuccess i m G g cm b) (sourceDuplicate i m G g cm b)

def excess (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (v b : ℝ) : ℝ :=
  (v-b)*(sourcePureSuccess i m G b+sourcePureDuplicate i m G b)/2

def budget (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (v : ℝ) : ℝ :=
  sSup ((excess i m G v) '' Icc (0:ℝ) v)

theorem pure_bounds (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (b : ℝ) :
    sourcePureSuccess i m G b ∈ Icc (0:ℝ) 1 ∧
      sourcePureDuplicate i m G b ∈ Icc (0:ℝ) 1 := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI := sourceRivalLaw_probability (cutoff_mem i) (G.map Prod.snd)
  let P := Measure.pi (fun _ : Fin (m-1) => sourceRivalLaw (cutoff i) (G.map Prod.snd))
  have hS := integrable_rowUnequalPureFirst (kappa i) (capacity m) b P
  have hD := integrable_rowUnequalPureDuplicate (kappa i) (capacity m) b P
  have huS := integral_mono_ae hS (integrable_const (1:ℝ))
    (ae_of_all _ fun ω => (rowUnequalPureFirst_bounds (kappa i) (capacity m) b ω).2)
  have huD := integral_mono_ae hD (integrable_const (1:ℝ))
    (ae_of_all _ fun ω => (row_unequal_duplicate_bounds (kappa i) (capacity m) b ω).2.trans
      (rowPureDuplicate_bounds (kappa i) (capacity m) b ω).2)
  refine ⟨⟨integral_nonneg (fun ω => (rowUnequalPureFirst_bounds (kappa i) (capacity m) b ω).1),?_⟩,
    ⟨integral_nonneg (fun ω => (row_unequal_duplicate_bounds (kappa i) (capacity m) b ω).1),?_⟩⟩
  · simpa only [integral_const,probReal_univ,one_smul] using! huS
  · simpa only [integral_const,probReal_univ,one_smul] using! huD

theorem excess_bounds (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {v b : ℝ} (hb : b ∈ Icc (0:ℝ) v) :
    excess i m G v b ∈ Icc (0:ℝ) v := by
  have hp := pure_bounds i m G b
  unfold excess
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr hb.2) (add_nonneg hp.1.1 hp.2.1)) (by norm_num)
  · have hh := mul_le_mul_of_nonneg_left (show sourcePureSuccess i m G b+
        sourcePureDuplicate i m G b ≤ 2 by linarith [hp.1.2,hp.2.2]) (sub_nonneg.mpr hb.2)
    nlinarith [hb.1]

theorem budget_bddAbove (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (v : ℝ) : BddAbove ((excess i m G v) '' Icc (0:ℝ) v) := by
  refine ⟨v,?_⟩
  rintro _ ⟨b,hb,rfl⟩
  exact (excess_bounds i m G hb).2

theorem excess_le_budget (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {v b : ℝ} (hb : b ∈ Icc (0:ℝ) v) :
    excess i m G v b ≤ budget i m G v :=
  le_csSup (budget_bddAbove i m G v) ⟨b,hb,rfl⟩

theorem budget_nonnegative (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] {v : ℝ} (hv : 0 ≤ v) : 0 ≤ budget i m G v := by
  have hh := excess_le_budget i m G (show v ∈ Icc (0:ℝ) v from ⟨hv,le_rfl⟩)
  simpa only [excess,sub_self,zero_mul,zero_div] using hh

theorem exact_payoff_decomposition (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (g : GuardData) {H : ℝ}
    (hg : PrefixConditions (xi i) g H) (cm : (Fin (m-1) → Fin 4) → ℝ)
    (v : ℝ) {b : ℝ} (hb : b ∈ Icc (0:ℝ) H) :
    single i m G g cm v b=
      one (sourceCanonicalMarginal i m G g cm) v b+excess i m G v b ∧
    broadcast i m G g cm v b=
      two (eta i) (sourceCanonicalMarginal i m G g cm) (sourceCanonicalDuplicate i m G g cm) v b+
        (v-b)*sourcePureSuccess i m G b-eta i*b*sourcePureDuplicate i m G b := by
  have hh := source_both_decompositions i m G g hg cm hb
  unfold single broadcast one two excess Rank.payoff
  rw [hh.1,hh.2]
  constructor <;> ring

theorem original_full_menu_gap (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (g : GuardData) {H v b : ℝ}
    (hg : PrefixConditions (xi i) g H) (cm : (Fin (m-1) → Fin 4) → ℝ)
    (hvH : v ≤ H)
    (hopt : Optimal (sourceCanonicalMarginal i m G g cm) v b)
    (hdom : budget i m G v+eta i*b*sourcePureDuplicate i m G b <
      two (eta i) (sourceCanonicalMarginal i m G g cm) (sourceCanonicalDuplicate i m G g cm) v b-
        one (sourceCanonicalMarginal i m G g cm) v b) :
    0 < broadcast i m G g cm v b ∧
      ∀ a : ℝ,0 ≤ a → single i m G g cm v a < broadcast i m G g cm v b := by
  have hbH : b ∈ Icc (0:ℝ) H := ⟨hopt.1.1,hopt.1.2.trans hvH⟩
  have hmain := exact_payoff_decomposition i m G g hg cm v hbH
  have hS0 := (pure_bounds i m G b).1.1
  have hbroadcast : two (eta i) (sourceCanonicalMarginal i m G g cm)
      (sourceCanonicalDuplicate i m G g cm) v b-eta i*b*sourcePureDuplicate i m G b ≤
        broadcast i m G g cm v b := by
    rw [hmain.2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hopt.1.2) hS0]
  have hsingle : ∀ a ∈ Icc (0:ℝ) v,single i m G g cm v a ≤
      one (sourceCanonicalMarginal i m G g cm) v a+budget i m G v := by
    intro a ha
    rw [(exact_payoff_decomposition i m G g hg cm v ⟨ha.1,ha.2.trans hvH⟩).1]
    exact add_le_add le_rfl (excess_le_budget i m G ha)
  have ht := full_menu_transfer _ _ (single i m G g cm v) (broadcast i m G g cm v)
    hopt hsingle hbroadcast hdom
  have hv0 : 0 ≤ v := hopt.1.1.trans hopt.1.2
  have hpositive := ht v ⟨hv0,le_rfl⟩
  simp only [single,sub_self,zero_mul,zero_div] at hpositive
  refine ⟨hpositive,?_⟩
  intro a ha
  by_cases hav : a ≤ v
  · exact ht a ⟨ha,hav⟩
  · have hk := source_first_duplicate_bounds i m G g cm a
    have hs : single i m G g cm v a ≤ 0 := by
      unfold single
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by linarith) (add_nonneg hk.1.1 hk.2.1))
        (by norm_num)
    exact hs.trans_lt hpositive

end FCAppendix.Affine.Uniform06.CanonicalPureTransfer
