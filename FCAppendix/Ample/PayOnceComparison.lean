import FCAppendix.PayOnce.InactiveEndpoint

namespace FCAppendix
namespace PayOnce
namespace Limit

open MeasureTheory Set

variable (μW : Measure ℝ) [IsProbabilityMeasure μW] {n : ℕ}

theorem coverage_lt_tail (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) (htail : 0 < μW.real (Ioi t)) :
    coverage μW n t < μW.real (Ioi t) := by
  have hsint := integrable_success_pStar (n := n) μW ht.le
  have hind : Integrable ((Ioi t).indicator (1 : ℝ → ℝ)) μW :=
    (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hpt : ∀ w, success n (pStar n t w) ≤ (Ioi t).indicator (1 : ℝ → ℝ) w ∧
      (w ∈ Ioi t → success n (pStar n t w) < (Ioi t).indicator (1 : ℝ → ℝ) w) := by
    intro w
    by_cases hw : t < w
    · rw [indicator_of_mem (show w ∈ Ioi t from hw)]
      have hf := failure_pos hn ht hw
      have hs : success n (pStar n t w) < 1 := by
        unfold success
        linarith
      exact ⟨hs.le, fun _ => hs⟩
    · rw [indicator_of_notMem (show w ∉ Ioi t from hw),
        success_pStar_of_le hn ht.le (not_lt.mp hw)]
      exact ⟨le_rfl, fun h => absurd h hw⟩
  have hnn : 0 ≤ᵐ[μW] (fun w => (Ioi t).indicator (1 : ℝ → ℝ) w - success n (pStar n t w)) :=
    Filter.Eventually.of_forall fun w => sub_nonneg.mpr (hpt w).1
  have hsupp : Ioi t ⊆ Function.support
      (fun w => (Ioi t).indicator (1 : ℝ → ℝ) w - success n (pStar n t w)) := by
    intro w hw
    exact (sub_pos.mpr ((hpt w).2 hw)).ne'
  have hpos : 0 < μW (Ioi t) := pos_iff_ne_zero.mpr ((measureReal_ne_zero_iff).mp htail.ne')
  have h := (integral_pos_iff_support_of_nonneg_ae hnn (hind.sub hsint)).mpr
    (lt_of_lt_of_le hpos (measure_mono hsupp))
  rw [integral_sub hind hsint, integral_indicator_one measurableSet_Ioi] at h
  unfold coverage
  linarith

theorem coverage_lt_positive_mass (hn : 2 ≤ n) {t ρ : ℝ} (ht : 0 < t) (hρ0 : 0 < ρ)
    (hd : demand μW n t = ρ) : coverage μW n t < μW.real (Ioi 0) := by
  have htail := tail_pos_of_demand_pos μW hn ht.le (hd ▸ hρ0)
  exact (coverage_lt_tail μW hn ht htail).trans_le
    (measureReal_mono (Ioi_subset_Ioi ht.le))

end Limit
end PayOnce

namespace Bayes

open MeasureTheory ProbabilityTheory Game Set Filter Topology
variable {M C : ℕ → ℕ} {k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem netValue_positive_mass (F : Measure ℝ) (g : ℝ) :
    (F.map (fun v => max (v-g) 0)).real (Ioi 0) = F.real (Ioi g) := by
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  rw [measureReal_def, Measure.map_apply hnet measurableSet_Ioi, ← measureReal_def]
  congr 1
  ext v
  simp

theorem payOnce_ample_comparison
    (Γ : ∀ t, FiniteGame (M t) (k+1) (C t) Seed)
    (B : ∀ t, PosteriorSystem (Γ t)) (F : Measure ℝ) [IsProbabilityMeasure F] (g ρ : ℝ)
    (h : InactiveSequenceAssumptions M C Γ B F g ρ) :
    let μW := F.map (fun v => max (v-g) 0)
    let Q := PayOnce.Limit.coverage μW (k+1) (PayOnce.Limit.capRoot μW (k+1) ρ)
    Tendsto (fun t => finiteCoverage (Γ t)) atTop (𝓝 Q) ∧ 0 < Q ∧ Q < F.real (Ioi g) ∧
      Tendsto (fun t => finiteLoad (Γ t)) atTop (𝓝 (((k+1:ℕ):ℝ)*ρ)) ∧
      Tendsto (fun t => finiteMultiplicity (Γ t)) atTop (𝓝 (((k+1:ℕ):ℝ)*ρ/Q)) ∧
      ((k+1:ℕ):ℝ)*ρ / F.real (Ioi g) < ((k+1:ℕ):ℝ)*ρ/Q := by
  intro μW Q
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  letI : IsProbabilityMeasure μW := Measure.isProbabilityMeasure_map hnet.aemeasurable
  obtain ⟨hL, hd, hQpos, hQ, hload, hmult, -, -⟩ :=
    payOnce_inactive_population_limits Γ B F g ρ h
  have hlt : Q < F.real (Ioi g) := by
    have hk := h.proposers_two
    have h' := PayOnce.Limit.coverage_lt_positive_mass μW (n := k+1) (by omega) hL
      h.capacity_bounds.1 hd
    rwa [netValue_positive_mass F g] at h'
  have hβ : 0 < ((k+1:ℕ):ℝ)*ρ := mul_pos (by positivity) h.capacity_bounds.1
  exact ⟨hQ, hQpos, hlt, hload, hmult, div_lt_div_of_pos_left hβ hQpos hlt⟩

theorem ample_regime_capacity_bounds {n : ℕ} {ρ h : ℝ}
    (hρ : 0 < ρ) (hlo : h < (n : ℝ) * ρ)
    (hhi : (n : ℝ) * ρ < (n : ℝ) * h) :
    0 < h ∧ ρ < h ∧ 1 < (n : ℝ) * ρ / h := by
  have hn : (0 : ℝ) < n := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg n)
    rw [hn0, zero_mul, zero_mul] at hhi
    exact (lt_irrefl _ hhi)
  have hrh : ρ < h := by
    by_contra hr
    exact (not_lt_of_ge (mul_le_mul_of_nonneg_left (le_of_not_gt hr) hn.le)) hhi
  have hp : 0 < h := hρ.trans hrh
  exact ⟨hp, hrh, (lt_div_iff₀ hp).mpr (by simpa only [one_mul] using hlo)⟩

end Bayes
end FCAppendix
