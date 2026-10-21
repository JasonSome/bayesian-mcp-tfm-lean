import FCAppendix.Affine.LowBody.BoundedNullWeakIntegral

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology Metric

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

theorem ae_nonpos_outside_closed_of_tests (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X→ℝ) (hf : Measurable f) (s : Set X) (hs : IsClosed s)
    (hcont : ∀x∉s,ContinuousAt f x) {C : ℝ} (hC : 0≤C) (hbound : ∀x,|f x|≤C)
    (htest : ∀a : C(X,ℝ),(∀x,0≤a x)→(∀x∈s,a x=0)→∫x,a x*f x ∂mu≤0) :
    ∀ᵐx ∂mu,x∉s→f x≤0 := by
  have hmax (x : X) : |max 0 (f x)|≤C := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hC ((le_abs_self _).trans (hbound x))
  have hex : ∃a : C(X,ℝ),(∀x,0≤a x) ∧ (∀x∈s,a x=0) ∧
      (∀x,f x≤0→a x=0) ∧ (∀x,x∉s→0<f x→0<a x) := by
    by_cases hsne : s.Nonempty
    · let a : C(X,ℝ):=⟨nullCutoff (fun x=>max 0 (f x)) s 1,
        continuous_nullCutoff _ s zero_lt_one hC hmax
          (fun x hx=>continuousAt_const.max (hcont x hx))⟩
      refine ⟨a,?_,?_,?_,?_⟩
      · intro x
        exact mul_nonneg (le_min zero_le_one (div_nonneg infDist_nonneg zero_le_one)) (le_max_left _ _)
      · intro x hx
        simp [a,nullCutoff,infDist_zero_of_mem hx]
      · intro x hx
        simp [a,nullCutoff,max_eq_left hx]
      · intro x hx hfpos
        have hd : 0 < infDist x s := (hs.notMem_iff_infDist_pos hsne).mp hx
        exact mul_pos (lt_min zero_lt_one (div_pos hd zero_lt_one)) (lt_max_of_lt_right hfpos)
    · have he : s=∅:=not_nonempty_iff_eq_empty.mp hsne
      have hc : Continuous f:=continuous_iff_continuousAt.mpr (fun x=>hcont x (by simp [he]))
      refine ⟨⟨fun x=>max 0 (f x),continuous_const.max hc⟩,fun _=>le_max_left _ _,?_,?_,?_⟩
      · intro x hx
        simp only [he,Set.mem_empty_iff_false] at hx
      · exact fun x hx=>max_eq_left hx
      · exact fun x _ hx=>lt_max_of_lt_right hx
  obtain ⟨a,ha,has,haz,hapos⟩:=hex
  have hi : Integrable (fun x=>a x*f x) mu := by
    apply (integrable_const (‖a‖*C)).mono' (a.continuous.measurable.mul hf).aestronglyMeasurable
    exact ae_of_all _ (fun x=>by
      rw [Real.norm_eq_abs]
      change |a x*f x|≤‖a‖*C
      rw [abs_mul]
      exact mul_le_mul (by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm x)
        (hbound x) (abs_nonneg _) (norm_nonneg _))
  have hnonneg (x : X) : 0≤a x*f x := by
    by_cases hx : f x≤0
    · rw [haz x hx,zero_mul]
    · exact mul_nonneg (ha x) (le_of_not_ge hx)
  have hz : ∫x,a x*f x ∂mu=0 := le_antisymm (htest a ha has) (integral_nonneg hnonneg)
  filter_upwards [(integral_eq_zero_iff_of_nonneg hnonneg hi).mp hz] with x hx hsx
  apply le_of_not_gt
  intro hfx
  exact (mul_pos (hapos x hsx hfx) hfx).ne' hx

end FCAppendix.Affine.LowBody
