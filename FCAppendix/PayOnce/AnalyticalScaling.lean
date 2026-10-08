import FCAppendix.PayOnce.AnalyticalRareSuccess

namespace FCAppendix.PayOnce.AnalyticalKernel
open MeasureTheory Filter Topology Set CommonList
open CompactifiedBidLaws
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem kernel_div_scale (n : ℕ) (b L : ℝ) {a : ℝ} (ha : 0 < a) :
    kernel n (b/a) (L/a) = kernel n b L := by
  have h1 : b/a ≤ L/a ↔ b ≤ L := div_le_div_iff_of_pos_right ha
  have h2 : b/a < (n:ℝ)*(L/a) ↔ b < (n:ℝ)*L := by
    rw [← mul_div_assoc, div_lt_div_iff_of_pos_right ha]
  have h3 : (L/a)/(b/a) = L/b := by field_simp
  simp only [kernel,h1,h2,h3]

theorem allocation_div_scale {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι+1)
    (rivals : ι → ℝ) (b : ℝ) {a : ℝ} (ha : 0 < a) :
    allocation n c hn hc (fun j => rivals j/a) (b/a) = allocation n c hn hc rivals b := by
  by_cases h : 0 < b ∧ ∀ j, 0 < rivals j
  · obtain ⟨L,hL,he,hcap⟩ := allocation_root hn hc rivals h.2 h.1
    rw [he]
    calc
      _ = kernel n (b/a) (L/a) := allocation_eq_kernel hn hc _ (fun j => div_pos (h.2 j) ha)
        (div_pos h.1 ha) (div_pos hL ha) (by simpa only [kernel_div_scale _ _ _ ha] using hcap)
      _ = _ := kernel_div_scale n b L ha
  · have hh : ¬ (0 < b/a ∧ ∀ j, 0 < rivals j/a) := by
      simpa only [div_pos_iff_of_pos_right ha] using h
    simp only [allocation,dif_neg h,dif_neg hh]

noncomputable def rescaledRealLaw (G : ProbabilityMeasure ℝ) (a : ℝ) : ProbabilityMeasure ℝ :=
  G.map (measurable_id.div_const a).aemeasurable

@[simp] theorem rescaledRealLaw_one (G : ProbabilityMeasure ℝ) : rescaledRealLaw G 1 = G := by
  apply Subtype.ext
  change Measure.map (fun b : ℝ => b/1) (G : Measure ℝ) = (G : Measure ℝ)
  simp only [div_one]
  exact Measure.map_id

theorem compactified_rescaledRealLaw (G : ProbabilityMeasure ℝ) (a : ℝ) :
    scaledLaw (rescaledRealLaw G a) 1 = scaledLaw G a := by
  apply Subtype.ext
  change Measure.map (fun b : ℝ => ENNReal.ofReal (b/1))
    (Measure.map (fun b : ℝ => b/a) (G : Measure ℝ)) =
      Measure.map (fun b : ℝ => ENNReal.ofReal (b/a)) (G : Measure ℝ)
  have hm : Measurable (fun b : ℝ => ENNReal.ofReal (b/1)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.div_const 1)
  rw [Measure.map_map hm (show Measurable (fun b : ℝ => b/a) from measurable_id.div_const a)]
  simp only [Function.comp_def,div_one]

theorem ae_pos_rescaledRealLaw (G : ProbabilityMeasure ℝ) {a : ℝ} (ha : 0 < a)
    (hpos : ∀ᵐ b ∂(G : Measure ℝ), 0 < b) :
    ∀ᵐ b ∂(rescaledRealLaw G a : Measure ℝ), 0 < b := by
  exact (ae_map_iff (measurable_id.div_const a).aemeasurable (by measurability)).mpr
    (hpos.mono fun b hb => div_pos hb ha)

theorem coverage_rescaledRealLaw {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι+1)
    (G : ProbabilityMeasure ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    coverage n c hn hc (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (b/a) =
      coverage n c hn hc (Measure.pi (fun _ : ι => (G : Measure ℝ))) b := by
  let T : (ι → ℝ) → (ι → ℝ) := fun d j => d j/a
  have hT : Measurable T := by
    apply measurable_pi_lambda
    intro j
    change Measurable (fun d : ι → ℝ => d j/a)
    exact (show Measurable (fun d : ι → ℝ => d j) from measurable_pi_apply j).div_const a
  have hmap : (Measure.pi (fun _ : ι => (G : Measure ℝ))).map T =
      Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ)) := by
    exact Measure.pi_map_pi (fun _ : ι => (measurable_id.div_const a).aemeasurable)
  rw [coverage, ← hmap, integral_map hT.aemeasurable
    (measurable_success_allocation hn hc (div_pos hb ha)).aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun d => by
    simp only [T, allocation_div_scale hn hc d b ha]

theorem nullSingleton_rescaledRealLaw (G : ProbabilityMeasure ℝ)
    [NullSingletonClass (G : Measure ℝ)] {a : ℝ} (ha : 0 < a) :
    NullSingletonClass (rescaledRealLaw G a : Measure ℝ) := by
  constructor
  intro b
  change ((G : Measure ℝ).map (fun x => x/a)) {b} = 0
  rw [Measure.map_apply (show Measurable (fun x : ℝ => x/a) from measurable_id.div_const a) (measurableSet_singleton b)]
  have he : (fun x : ℝ => x/a) ⁻¹' {b} = {b*a} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,div_eq_iff ha.ne']
  rw [he,measure_singleton]

theorem scaled_coverage_IC {n c : ℕ} (hn : 2 ≤ n) (hc : c ≤ Fintype.card ι+1)
    (G : ProbabilityMeasure ℝ) {a b y w : ℝ} (ha : 0 < a) (hb : 0 < b) (hy : 0 < y)
    (hIC : (w-y)*coverage n c hn hc (Measure.pi (fun _ : ι => (G : Measure ℝ))) y ≤
      (w-b)*coverage n c hn hc (Measure.pi (fun _ : ι => (G : Measure ℝ))) b) :
    (w/a-y/a)*coverage n c hn hc (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (y/a) ≤
      (w/a-b/a)*coverage n c hn hc (Measure.pi (fun _ : ι => (rescaledRealLaw G a : Measure ℝ))) (b/a) := by
  rw [coverage_rescaledRealLaw hn hc G ha hy,coverage_rescaledRealLaw hn hc G ha hb]
  rw [← sub_div, ← sub_div, div_mul_eq_mul_div, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hIC ha.le

end FCAppendix.PayOnce.AnalyticalKernel
