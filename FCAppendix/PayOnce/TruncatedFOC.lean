import FCAppendix.PayOnce.CovarianceConcentration
import FCAppendix.PayOnce.ProfileWeights

namespace FCAppendix.PayOnce.TruncatedFOC
open MeasureTheory Filter Topology Set OwnImpact RareSuccessSlope
open scoped BigOperators

noncomputable def baseSlope (n : ℕ) (p : ℝ) : ℝ := weightedSlope n p 0

theorem baseSlope_bounds {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    baseSlope n p ∈ Icc (0 : ℝ) ((n : ℝ)^2) := by
  unfold baseSlope weightedSlope
  split_ifs
  · simpa only [sub_zero, mul_one] using ⟨phi_nonneg hn hp, phi_le_sq hn hp⟩
  · exact ⟨le_rfl, sq_nonneg _⟩

theorem measurable_baseSlope (n : ℕ) : Measurable (baseSlope n) :=
  (measurable_weightedSlope n).comp (measurable_id.prodMk measurable_const)

theorem continuousAt_baseSlope {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt (baseSlope n) ρ := by
  have he : baseSlope n =ᶠ[𝓝 ρ] phi n := by
    filter_upwards [Ioo_mem_nhds hρ.1 hρ.2] with p hp
    simp only [baseSlope, weightedSlope, if_pos (show 0 < p ∧ p < 1 from hp), sub_zero, mul_one]
  have hh := (continuousOn_phi hn ρ ⟨hρ.1.le, hρ.2.le⟩).continuousAt
    (Icc_mem_nhds hρ.1 hρ.2)
  exact hh.congr_of_eventuallyEq he

theorem baseSlope_pos {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    0 < baseSlope n ρ := by
  simpa only [baseSlope, weightedSlope, if_pos (show 0 < ρ ∧ ρ < 1 from hρ), sub_zero, mul_one]
    using AnalyticalKernel.phi_pos_interior hn hρ

theorem sum_truncated_correction_le {ι : Type*} [Fintype ι]
    {n : ℕ} (hn : 2 ≤ n) (p T weight : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1) (hT : ∀ i, T i ∈ Icc (0 : ℝ) M)
    (hw : ∀ i, 0 ≤ weight i)
    (hsum : ∑ i ∈ interiorSet p, weight i ≤ 1) :
    (∑ i, T i*baseSlope n (p i)) - (∑ i, T i*weightedSlope n (p i) (weight i)) ≤ M*(n : ℝ)^2 := by
  classical
  have he : (∑ i, T i*baseSlope n (p i)) - (∑ i, T i*weightedSlope n (p i) (weight i)) =
      ∑ i ∈ interiorSet p, T i*phi n (p i)*weight i := by
    rw [← Finset.sum_sub_distrib, interiorSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    unfold baseSlope weightedSlope
    split_ifs <;> ring
  rw [he]
  have hh : (∑ i ∈ interiorSet p, T i*phi n (p i)*weight i) ≤
      ∑ i ∈ interiorSet p, (M*(n : ℝ)^2)*weight i := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (hw i)
    exact mul_le_mul (hT i).2 (phi_le_sq hn (hp i)) (phi_nonneg hn (hp i)) hM
  rw [← Finset.mul_sum] at hh
  exact hh.trans (mul_le_of_le_one_right (mul_nonneg hM (sq_nonneg _)) hsum)

theorem mean_abs_comp_tendsto_zero
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    (p : ∀ m, Ω m → ℝ) (hp : ∀ m, Measurable (p m))
    (hpb : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Measurable f) {ρ C : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (hcont : ContinuousAt f ρ) (hbound : ∀ q ∈ Icc (0 : ℝ) 1, |f q| ≤ C)
    (hgap : Tendsto (fun m => ∫ ω, |p m ω-ρ| ∂P m) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, |f (p m ω)-f ρ| ∂P m) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbound ρ hρ)
  have hdiff (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) : |f q-f ρ| ≤ 2*C := by
    have hh := (abs_sub (f q) (f ρ)).trans (add_le_add (hbound q hq) (hbound ρ hρ))
    linarith
  have hI (m : ℕ) : Integrable (fun ω => |f (p m ω)-f ρ|) (P m) := by
    apply (integrable_const (2*C)).mono' ((hf.comp (hp m)).sub measurable_const).abs.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_abs, Pi.sub_apply, Function.comp_def] using hdiff _ (hpb m ω)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun m => ha.trans_le (integral_nonneg fun _ => abs_nonneg _)
  · intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont (ε/2) (half_pos hε)
    have hlocal (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
        |f q-f ρ| ≤ ε/2 + (2*C/δ)*|q-ρ| := by
      by_cases hnear : |q-ρ| < δ
      · have hh := hδf (by simpa only [Real.dist_eq] using hnear)
        have hn : 0 ≤ (2*C/δ)*|q-ρ| := by positivity
        have hh' : |f q-f ρ| < ε/2 := by simpa only [Real.dist_eq] using hh
        linarith
      · have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hnear) (by positivity : 0 ≤ 2*C/δ)
        have he : (2*C/δ)*δ = 2*C := div_mul_cancel₀ _ hδ.ne'
        rw [he] at hh
        linarith [hdiff q hq]
    have hsmall : ∀ᶠ m in atTop, (2*C/δ)*(∫ ω, |p m ω-ρ| ∂P m) < ε/2 := by
      apply Filter.Tendsto.eventually_lt_const (half_pos hε)
      simpa only [mul_zero] using hgap.const_mul (2*C/δ)
    filter_upwards [hsmall] with m hm
    have hgapI := CovarianceConcentration.integrable_abs_gap (P m) (hp m) measurable_const
      (hpb m) (fun _ => hρ)
    have hh := integral_mono (hI m)
      ((integrable_const (ε/2)).add (hgapI.const_mul (2*C/δ)))
      (fun ω => hlocal _ (hpb m ω))
    simp only [Pi.add_apply] at hh
    rw [integral_add (integrable_const _) (hgapI.const_mul _), integral_const,
      probReal_univ, one_smul, integral_const_mul] at hh
    linarith

theorem weightedSlope_bounds {n : ℕ} (hn : 2 ≤ n) {p w : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    weightedSlope n p w ∈ Icc (0 : ℝ) ((n : ℝ)^2) := by
  refine ⟨weightedSlope_nonneg hn hp (fun _ => hw.2), ?_⟩
  unfold weightedSlope
  split_ifs
  · exact (mul_le_of_le_one_right (phi_nonneg hn hp) (by linarith [hw.1])).trans (phi_le_sq hn hp)
  · exact sq_nonneg _

theorem not_all_bids_vanish
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (P : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (P m)]
    {n : ℕ} (hn : 2 ≤ n) (p T B weight : ∀ m, Ω m → ℝ)
    (hp : ∀ m, Measurable (p m)) (hT : ∀ m, Measurable (T m))
    (hB : ∀ m, Measurable (B m)) (hw : ∀ m, Measurable (weight m))
    {M ρ t : ℝ} (hM : 0 ≤ M) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (ht : 0 < t)
    (hpb : ∀ m ω, p m ω ∈ Icc (0 : ℝ) 1)
    (hTb : ∀ m ω, T m ω ∈ Icc (0 : ℝ) M) (hBb : ∀ m ω, B m ω ∈ Icc (0 : ℝ) M)
    (hwb : ∀ m ω, weight m ω ∈ Icc (0 : ℝ) 1)
    (hpmean : Tendsto (fun m => ∫ ω, |p m ω-ρ| ∂P m) atTop (𝓝 0))
    (hTmean : Tendsto (fun m => ∫ ω, T m ω ∂P m) atTop (𝓝 t))
    (hBmean : Tendsto (fun m => ∫ ω, B m ω ∂P m) atTop (𝓝 0))
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0))
    (hcorrection : ∀ m,
      (∫ ω, T m ω*baseSlope n (p m ω) ∂P m) ≤
      (∫ ω, T m ω*weightedSlope n (p m ω) (weight m ω) ∂P m) + r m)
    (hfirst : ∀ m,
      (∫ ω, T m ω*weightedSlope n (p m ω) (weight m ω) ∂P m) =
      (∫ ω, B m ω*(success n (p m ω)+weightedSlope n (p m ω) (weight m ω)) ∂P m)) : False := by
  let f := baseSlope n
  have hf : Measurable f := measurable_baseSlope n
  have hfbound : ∀ q ∈ Icc (0 : ℝ) 1, |f q| ≤ (n : ℝ)^2 := fun q hq => by
    rw [abs_of_nonneg (baseSlope_bounds hn hq).1]
    exact (baseSlope_bounds hn hq).2
  have herr := mean_abs_comp_tendsto_zero P p hp hpb hf ⟨hρ.1.le, hρ.2.le⟩
    (continuousAt_baseSlope hn hρ) hfbound hpmean
  have hTI (m : ℕ) : Integrable (T m) (P m) := by
    apply (integrable_const M).mono' (hT m).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hTb m ω).1]
      exact (hTb m ω).2
  have hBI (m : ℕ) : Integrable (B m) (P m) := by
    apply (integrable_const M).mono' (hB m).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hBb m ω).1]
      exact (hBb m ω).2
  have hI (m : ℕ) : Integrable (fun ω => |f (p m ω)-f ρ|) (P m) := by
    apply (integrable_const (2*(n : ℝ)^2)).mono'
      ((hf.comp (hp m)).sub measurable_const).abs.aestronglyMeasurable
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, abs_abs, Pi.sub_apply, Function.comp_def]
    have hh := (abs_sub (f (p m ω)) (f ρ)).trans
      (add_le_add (hfbound _ (hpb m ω)) (hfbound _ ⟨hρ.1.le, hρ.2.le⟩))
    linarith
  have hTF (m : ℕ) : Integrable (fun ω => T m ω*f (p m ω)) (P m) := by
    apply (integrable_const (M*(n : ℝ)^2)).mono' ((hT m).mul (hf.comp (hp m))).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖T m ω*f (p m ω)‖ ≤ M*(n : ℝ)^2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hTb m ω).1]
    exact mul_le_mul (hTb m ω).2 (hfbound _ (hpb m ω)) (abs_nonneg _) hM
  have hR (m : ℕ) : Integrable
      (fun ω => B m ω*(success n (p m ω)+weightedSlope n (p m ω) (weight m ω))) (P m) := by
    apply (integrable_const (M*(1+(n : ℝ)^2))).mono'
      ((hB m).mul (((continuous_success n).measurable.comp (hp m)).add
        ((measurable_weightedSlope n).comp ((hp m).prodMk (hw m))))).aestronglyMeasurable
    filter_upwards [] with ω
    have hs := CovarianceConcentration.success_mem_unit (n := n) (hpb m ω)
    have hd := weightedSlope_bounds hn (hpb m ω) (hwb m ω)
    change ‖B m ω*(success n (p m ω)+weightedSlope n (p m ω) (weight m ω))‖ ≤ M*(1+(n : ℝ)^2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hBb m ω).1,
      abs_of_nonneg (add_nonneg hs.1 hd.1)]
    exact mul_le_mul (hBb m ω).2 (add_le_add hs.2 hd.2) (add_nonneg hs.1 hd.1) hM
  have hineq (m : ℕ) : (∫ ω, T m ω ∂P m)*f ρ ≤
      (1+(n : ℝ)^2)*(∫ ω, B m ω ∂P m) + r m + M*(∫ ω, |f (p m ω)-f ρ| ∂P m) := by
    have hl := integral_mono ((hTI m).mul_const (f ρ)) ((hTF m).add ((hI m).const_mul M))
      (fun ω => by
        have hh := mul_le_mul_of_nonneg_left (le_abs_self (f ρ-f (p m ω))) (hTb m ω).1
        rw [abs_sub_comm (f ρ)] at hh
        have hh' := mul_le_mul_of_nonneg_right (hTb m ω).2 (abs_nonneg (f (p m ω)-f ρ))
        change T m ω*f ρ ≤ T m ω*f (p m ω) + M*|f (p m ω)-f ρ|
        nlinarith)
    simp only [Pi.add_apply] at hl
    rw [integral_mul_const, integral_add (hTF m) ((hI m).const_mul M), integral_const_mul] at hl
    have hrb := integral_mono (hR m) ((hBI m).const_mul (1+(n : ℝ)^2)) (fun ω => by
      have hs := CovarianceConcentration.success_mem_unit (n := n) (hpb m ω)
      have hd := weightedSlope_bounds hn (hpb m ω) (hwb m ω)
      have hh := mul_le_mul_of_nonneg_left (add_le_add hs.2 hd.2) (hBb m ω).1
      exact hh.trans_eq (mul_comm _ _))
    rw [integral_const_mul] at hrb
    have hc := hcorrection m
    rw [hfirst m] at hc
    linarith
  have hright : Tendsto (fun m => (1+(n : ℝ)^2)*(∫ ω, B m ω ∂P m) + r m +
      M*(∫ ω, |f (p m ω)-f ρ| ∂P m)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using ((hBmean.const_mul (1+(n : ℝ)^2)).add hr).add (herr.const_mul M)
  have hle := le_of_tendsto_of_tendsto (hTmean.mul_const (f ρ)) hright (Filter.Eventually.of_forall hineq)
  exact (mul_pos ht (baseSlope_pos hn hρ)).not_ge hle

end FCAppendix.PayOnce.TruncatedFOC
