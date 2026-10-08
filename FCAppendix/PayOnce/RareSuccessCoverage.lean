import FCAppendix.PayOnce.KernelTailEvent
import FCAppendix.Probability.StrictCramerComparison
import FCAppendix.Probability.UnitInterval

namespace FCAppendix.PayOnce.RareSuccessCoverage
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open FCAppendix.CommonList FCAppendix.PayOnce.KernelTailEvent

theorem transformed_cgf_lt {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ℝ) [IsProbabilityMeasure G] {x δ ε u : ℝ}
    (hx : 0 < x) (hδ : 0 ≤ δ) (hδε : δ < ε) (hε : ε ≤ 1)
    (hsupport : x ∈ G.support) (hu : u < 0) :
    cgf (fun b => kernel n b (x * H n ε)) G u <
      cgf (fun b => kernel n b (x * H n δ)) G u := by
  have hLδ : 0 < x * H n δ := mul_pos hx (H_pos n (by omega) δ hδ (hδε.le.trans hε))
  have hLε : 0 < x * H n ε := mul_pos hx (H_pos n (by omega) ε (hδ.trans hδε.le) hε)
  apply StrictCramerComparison.cgf_lt_of_order G
    (continuous_kernel_bid hn hLδ).measurable.aemeasurable
    (continuous_kernel_bid hn hLε).measurable.aemeasurable
    (.of_forall (kernel_bounds hn hLδ)) (.of_forall (kernel_bounds hn hLε))
    (.of_forall fun b => transformed_kernel_mono hn hx hδ hδε.le hε)
    (transformed_kernel_strict_mass hn G hx hδ hδε hε hsupport).ne' hu

theorem transformed_essInf_le {n : ℕ} (hn : 2 ≤ n)
    (G : Measure ℝ) {x δ : ℝ} (hx : 0 < x) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hsupport : x ∈ G.support) :
    essInf (fun b => kernel n b (x * H n δ)) G ≤ δ := by
  have hL : 0 < x * H n δ := mul_pos hx (H_pos n (by omega) δ hδ hδ1)
  by_contra hh
  obtain ⟨a, hδa, ha⟩ := exists_between (lt_of_not_ge hh)
  have hxval : kernel n x (x * H n δ) < a := by
    rw [kernel_at_score hn hx hδ hδ1]
    exact hδa
  have hnear := (continuousAt_kernel_bid hn hx hL).eventually_lt_const hxval
  have hmass : 0 < G {b | kernel n b (x * H n δ) < a} :=
    (Measure.mem_support_iff_forall x).mp hsupport _ hnear
  have hfreq : ∃ᵐ b ∂G, kernel n b (x * H n δ) ≤ a := by
    apply frequently_ae_iff.mpr
    exact ne_of_gt (hmass.trans_le (measure_mono fun b hb => (show kernel n b (x * H n δ) < a from hb).le))
  have hbdd : IsBoundedUnder (· ≥ ·) (ae G) (fun b => kernel n b (x * H n δ)) :=
    ⟨0, by
      change ∀ᵐ b ∂G, 0 ≤ kernel n b (x * H n δ)
      exact Filter.Eventually.of_forall fun b => (kernel_bounds hn hL b).1⟩
  exact ha.not_ge (liminf_le_of_frequently_le hfreq hbdd)

theorem integral_success_ge_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : Ω → ℝ} (hp : Measurable p)
    (hbound : ∀ ω, p ω ∈ Icc (0 : ℝ) 1) (δ : ℝ) :
    success n δ * P.real {ω | δ ≤ p ω} ≤ ∫ ω, success n (p ω) ∂P := by
  let E := {ω | δ ≤ p ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hp
  have hint := UnitInterval.integrable_success P p hp (fun ω => (hbound ω).1)
    (fun ω => (hbound ω).2) n
  have hi : Integrable (E.indicator (fun _ => success n δ)) P :=
    (integrable_const _).indicator hE
  have hle : ∀ ω, E.indicator (fun _ => success n δ) ω ≤ success n (p ω) := by
    intro ω
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      have hpow : (1 - p ω) ^ n ≤ (1 - δ) ^ n :=
        pow_le_pow_left₀ (sub_nonneg.mpr (hbound ω).2) (by change δ ≤ p ω at he; linarith) n
      unfold success
      linarith
    · rw [indicator_of_notMem he, ← H_mul n hn]
      have hh := H_pos n hn (p ω) (hbound ω).1 (hbound ω).2
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (hbound ω).1) hh.le
  have hh := integral_mono hi hint hle
  rw [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_comm] at hh
  exact hh

theorem ratio_coverage_le_ratio_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {p : Ω → ℝ} (hp : Measurable p)
    (hbound : ∀ ω, p ω ∈ Icc (0 : ℝ) 1) {δ a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (htail : 0 < P.real {ω | δ ≤ p ω}) :
    0 < (∫ ω, success n (p ω) ∂P) ∧
      a / (∫ ω, success n (p ω) ∂P) ≤
        (a / P.real {ω | δ ≤ p ω}) / success n δ := by
  have hS := success_pos n hn δ hδ hδ1
  have hl := integral_success_ge_tail P hn hp hbound δ
  have hpos := (mul_pos hS htail).trans_le hl
  refine ⟨hpos, ?_⟩
  have hd := div_le_div_of_nonneg_left ha (mul_pos hS htail) hl
  simpa only [div_div, mul_comm] using hd

theorem tail_ratio_to_coverage
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    {n : ℕ} (hn : 0 < n) (p : ∀ m, Ω m → ℝ)
    (hp : ∀ m, Measurable (p m)) (hbound : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1)
    {δ ε c : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c)
    (hpos : ∀ᶠ m in atTop, 0 < (P m).real {ω | δ ≤ p m ω})
    (hratio : ∀ᶠ m in atTop,
      (P m).real {ω | ε ≤ p m ω} / (P m).real {ω | δ ≤ p m ω} ≤ exp (-c * m)) :
    (∀ᶠ m in atTop, 0 < (∫ ω, success n (p m ω) ∂P m) ∧
      (P m).real {ω | ε ≤ p m ω} / (∫ ω, success n (p m ω) ∂P m) ≤
        exp (-c * m) / success n δ) ∧
    Tendsto (fun m => (P m).real {ω | ε ≤ p m ω} /
      (∫ ω, success n (p m ω) ∂P m)) atTop (𝓝 0) := by
  have hS := success_pos n hn δ hδ hδ1
  have hevent : ∀ᶠ m in atTop, 0 < (∫ ω, success n (p m ω) ∂P m) ∧
      (P m).real {ω | ε ≤ p m ω} / (∫ ω, success n (p m ω) ∂P m) ≤
        exp (-c * m) / success n δ := by
    filter_upwards [hpos, hratio] with m ht hr
    have hh := ratio_coverage_le_ratio_tail (a := (P m).real {ω | ε ≤ p m ω}) (P m) hn (hp m) (hbound m) hδ hδ1 measureReal_nonneg ht
    exact ⟨hh.1, hh.2.trans (div_le_div_of_nonneg_right hr hS.le)⟩
  refine ⟨hevent, ?_⟩
  have hexp : Tendsto (fun m : ℕ => exp (-c * m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hc)
  have hlim : Tendsto (fun m : ℕ => exp (-c * m) / success n δ) atTop (𝓝 0) := by
    simpa only [zero_div] using hexp.div_const (success n δ)
  apply squeeze_zero' ?_ (hevent.mono fun _ hh => hh.2) hlim
  exact hevent.mono fun _ hh => div_nonneg measureReal_nonneg hh.1.le

end FCAppendix.PayOnce.RareSuccessCoverage
