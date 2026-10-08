import FCAppendix.PayOnce.DummyInterimKernel
import FCAppendix.PayOnce.AnalyticalScaling

namespace FCAppendix.PayOnce.DummyKernel
open MeasureTheory Filter Topology Set CommonList
open CompactifiedBidLaws
open AnalyticalKernel (rescaledRealLaw)
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem allocation_div_scale {n c : ℕ} (hn : 2 ≤ n) (r : ι → ℝ) (b : ℝ)
    {a : ℝ} (ha : 0 < a) :
    allocation n c hn (fun j => r j/a) (b/a) = allocation n c hn r b := by
  have hcard : Fintype.card (Active (fun j => r j/a)) = Fintype.card (Active r) :=
    Fintype.card_congr ((Equiv.refl ι).subtypeEquiv (fun _ => div_pos_iff_of_pos_right ha))
  by_cases hb : 0 < b
  · obtain ⟨L,hL,he,hcap⟩ := allocation_root (c := c) hn r hb
    rw [he]
    calc
      _ = kernel n (b/a) (L/a) := allocation_eq_kernel hn _ (div_pos hb ha) (div_pos hL ha)
        (by simpa only [AnalyticalKernel.kernel_div_scale _ _ _ ha,hcard] using hcap)
      _ = _ := AnalyticalKernel.kernel_div_scale n b L ha
  · rw [allocation_eq_zero_of_nonpos hn _ (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) ha.le),
      allocation_eq_zero_of_nonpos hn _ (le_of_not_gt hb)]

theorem coverage_rescaledRealLaw {n c : ℕ} (hn : 2 ≤ n)
    (G : ProbabilityMeasure ℝ) {a : ℝ} (b : ℝ) (ha : 0 < a) :
    coverage n c hn (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (b/a) =
      coverage n c hn (Measure.pi (fun _ : ι => (G : Measure ℝ))) b := by
  let T : (ι → ℝ) → (ι → ℝ) := fun d j => d j/a
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro j
    exact (show Measurable (fun d : ι → ℝ => d j) from measurable_pi_apply j).div_const a
  have hmap : (Measure.pi (fun _ : ι => (G : Measure ℝ))).map T =
      Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ)) :=
    Measure.pi_map_pi (fun _ : ι => (measurable_id.div_const a).aemeasurable)
  have hm : Measurable (fun r : ι → ℝ => success n (allocation n c hn r (b/a))) :=
    (continuous_success n).measurable.comp (measurable_allocation_fixed_bid hn (b/a))
  rw [coverage,← hmap,integral_map hT.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun d => by
    simp only [T,allocation_div_scale hn d b ha]

theorem ae_nonneg_rescaledRealLaw (G : ProbabilityMeasure ℝ) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ᵐ b ∂(G : Measure ℝ), 0 ≤ b) :
    ∀ᵐ b ∂(rescaledRealLaw G a : Measure ℝ), 0 ≤ b := by
  exact (ae_map_iff (measurable_id.div_const a).aemeasurable (by measurability)).mpr
    (hpos.mono fun b hb => div_nonneg hb ha.le)

theorem positive_atomless_rescaledRealLaw (G : ProbabilityMeasure ℝ)
    (hatom : ∀ b : ℝ, 0 < b → (G : Measure ℝ) {b} = 0) {a : ℝ} (ha : 0 < a)
    {b : ℝ} (hb : 0 < b) : (rescaledRealLaw G a : Measure ℝ) {b} = 0 := by
  change ((G : Measure ℝ).map (fun x => x/a)) {b} = 0
  rw [Measure.map_apply (show Measurable (fun x : ℝ => x/a) from measurable_id.div_const a)
    (measurableSet_singleton b)]
  have he : (fun x : ℝ => x/a) ⁻¹' {b} = {b*a} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,div_eq_iff ha.ne']
  rw [he,hatom _ (mul_pos hb ha)]

theorem scaled_coverage_IC {n c : ℕ} (hn : 2 ≤ n)
    (G : ProbabilityMeasure ℝ) {a b y w : ℝ} (ha : 0 < a)
    (hIC : (w-y)*coverage n c hn (Measure.pi (fun _ : ι => (G : Measure ℝ))) y ≤
      (w-b)*coverage n c hn (Measure.pi (fun _ : ι => (G : Measure ℝ))) b) :
    (w/a-y/a)*coverage n c hn (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (y/a) ≤
      (w/a-b/a)*coverage n c hn (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (b/a) := by
  rw [coverage_rescaledRealLaw hn G y ha,coverage_rescaledRealLaw hn G b ha]
  rw [← sub_div,← sub_div,div_mul_eq_mul_div,div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hIC ha.le

end FCAppendix.PayOnce.DummyKernel
