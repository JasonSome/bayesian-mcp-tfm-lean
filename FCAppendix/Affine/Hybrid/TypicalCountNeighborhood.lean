import FCAppendix.Affine.Hybrid.SourceTypicalGuardedData

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology Classical

theorem eventually_typical_count_point_mem (a h ρ z : ℝ)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hlower : h/2 < ρ) (hupper : ρ < a+h/2)
    (c : ℕ → ℕ) (hc : Tendsto (fun M => (c M : ℝ)/(M : ℝ)) atTop (𝓝 ρ))
    (S : Set (Fin 4 → ℝ)) (hS : S ∈ 𝓝 (sourceCountPoint a h ρ z)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ M : ℕ in atTop, ∀ A H₀ H₁ : ℕ,
      |(A : ℝ)-(M : ℝ)*a| ≤ M*δ →
      |(H₀ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      |(H₁ : ℝ)-(M : ℝ)*(h/2)| ≤ M*δ →
      finiteCountPoint M A (min (activeResidual (c M) A H₀) (activeResidual (c M) A H₁))
        (exclusiveQuota z A)
        (residualDifference (activeResidual (c M) A H₀) (activeResidual (c M) A H₁)) ∈ S := by
  obtain ⟨η,hη,hηS⟩ := Metric.mem_nhds_iff.mp hS
  let δ := min (η/16) (min ((ρ-h/2)/4) ((a+h/2-ρ)/6))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hδη : δ ≤ η/16 := min_le_left _ _
  have hδlo : δ ≤ (ρ-h/2)/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδhi : δ ≤ (a+h/2-ρ)/6 := (min_le_right _ _).trans (min_le_right _ _)
  have hδlower : 2*δ < ρ-h/2 := by linarith
  have hδupper : 3*δ < a+h/2-ρ := by linarith
  have hcapClose : ∀ᶠ M : ℕ in atTop, |(c M : ℝ)/(M : ℝ)-ρ| < δ := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hc) δ hδ
  have hroundClose : ∀ᶠ M : ℕ in atTop, 1/(M : ℝ) < η/4 :=
    (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).eventually (Iio_mem_nhds (by positivity))
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcapClose,hroundClose,eventually_gt_atTop (0:ℕ)] with M hcapM hroundM hM
  intro A H₀ H₁ hA hH₀ hH₁
  have hm : (0:ℝ) < M := Nat.cast_pos.mpr hM
  have hcap : |(c M : ℝ)-(M : ℝ)*ρ| ≤ M*δ := by
    have he : (c M : ℝ)/(M : ℝ)-ρ=((c M : ℝ)-(M : ℝ)*ρ)/(M : ℝ) := by field_simp
    rw [he,abs_div,abs_of_pos hm] at hcapM
    have hh := (div_lt_iff₀ hm).mp hcapM
    nlinarith
  have he := typical_count_point_errors hM hδ.le hz0 hz1 hcap hA hH₀ hH₁ hδlower hδupper
  apply hηS
  apply (dist_pi_lt_iff hη).mpr
  intro i
  fin_cases i
  · exact he.1.trans_lt (by linarith)
  · exact he.2.1.trans_lt (by linarith)
  · exact he.2.2.1.trans_lt (by linarith)
  · exact he.2.2.2.trans_lt (by linarith)

end FCAppendix.Affine.Hybrid
