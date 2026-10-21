import FCAppendix.Affine.LowBody.ClusterMassLimits

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem atom_real_zero_of_strict_contraction {p A D : ℝ}
    (hp : 0 ≤ p) (hDA : D < A) (hcontract : p * A ≤ p * D) : p = 0 := by
  by_contra hn
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hn)
  have hstrict := mul_lt_mul_of_pos_left hDA hp'
  exact (not_lt_of_ge hcontract) hstrict

theorem atom_zero_of_ordinary_cluster_estimates
    (H G : ℕ → ProbabilityMeasure ℝ) (G₀ : ProbabilityMeasure ℝ)
    (hH : Tendsto H atTop (𝓝 G₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (b A D : ℝ) (hA : 0 < A) (hD : 0 ≤ D) (hDA : D < A)
    (r err : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hranti : Antitone r)
    (hrzero : Tendsto r atTop (𝓝 0))
    (herr : ∀ n, 0 ≤ err n) (herrzero : Tendsto err atTop (𝓝 0))
    (hfinite : ∀ n, ∀ᶠ j : ℕ in atTop,
      (H j : Measure ℝ).real (Ioo (b - r n) (b + r n)) ^ 2 * A ≤
        (H j : Measure ℝ).real (Ioo (b - r n) (b + r n)) *
          (D * (G j : Measure ℝ).real (Icc (b - 3 * r n) (b + 3 * r n)) + err n)) :
    (G₀ : Measure ℝ) {b} = 0 := by
  have hbound (n : ℕ) :
      (G₀ : Measure ℝ).real {b} * A ≤
        D * (G₀ : Measure ℝ).real (Icc (b - 3 * r n) (b + 3 * r n)) + err n := by
    have hh := LowBody.atom_bound_of_finite_cluster_estimates H G G₀ hH hG
      (Ioo (b - r n) (b + r n)) (Icc (b - 3 * r n) (b + 3 * r n)) ∅
      isOpen_Ioo isClosed_Icc isClosed_empty
      b A D (err n) ⟨by linarith [hr n], by linarith [hr n]⟩ hA hD (herr n)
      (by simpa only [measureReal_empty, add_zero] using hfinite n)
    simpa only [measureReal_empty, add_zero] using hh
  have hmass := LowBody.shrinking_closedInterval_mass (G₀ : Measure ℝ) b
    (fun n => 3 * r n) (fun n => mul_nonneg (by norm_num) (hr n).le)
    (fun n k hnk => mul_le_mul_of_nonneg_left (hranti hnk) (by norm_num))
    (by simpa only [mul_zero] using hrzero.const_mul 3)
  have hlimit : (G₀ : Measure ℝ).real {b} * A ≤
      D * (G₀ : Measure ℝ).real {b} := by
    have hh := le_of_tendsto_of_tendsto
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => (G₀ : Measure ℝ).real {b} * A) atTop
        (𝓝 ((G₀ : Measure ℝ).real {b} * A)))
      ((hmass.const_mul D).add herrzero) (Eventually.of_forall hbound)
    simpa only [add_zero] using hh
  have hreal := atom_real_zero_of_strict_contraction
    (show 0 ≤ (G₀ : Measure ℝ).real {b} from measureReal_nonneg)
    hDA (by simpa only [mul_comm D] using hlimit)
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right (measure_ne_top _ _)

end FCAppendix.Affine.Tail04
