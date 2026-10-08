import FCAppendix.Finite.NearPPIAggregate

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem tail_strict_of_interval_mass (F : Measure ℝ) [IsFiniteMeasure F]
    (x y : ℝ) (hxy : x < y) (hpos : 0 < F.real (Ioo x y)) :
    F.real (Ioi y) < F.real (Ioi x) := by
  have hdisj : Disjoint (Ioi y) (Ioo x y) := disjoint_left.mpr (by
    intro v hv1 hv2
    exact (not_lt_of_gt hv1) hv2.2)
  have hsub : Ioi y ∪ Ioo x y ⊆ Ioi x := by
    intro v hv
    rcases hv with hv | hv
    · exact hxy.trans hv
    · exact hv.1
  have hh := measureReal_mono (μ := F) hsub
  rw [measureReal_union hdisj measurableSet_Ioo] at hh
  linarith

theorem eq_cutoff_of_tail_eq (F : Measure ℝ) [IsFiniteMeasure F] (c x : ℝ)
    (hleft : ∀ v < c, 0 < F.real (Ioo v c))
    (hright : ∀ v > c, 0 < F.real (Ioo c v))
    (htail : F.real (Ioi x) = F.real (Ioi c)) : x = c := by
  rcases lt_trichotomy x c with hx | hx | hx
  · have hh := tail_strict_of_interval_mass F x c hx (hleft x hx)
    rw [htail] at hh
    exact (lt_irrefl _ hh).elim
  · exact hx
  · have hh := tail_strict_of_interval_mass F c x hx (hright x hx)
    rw [htail] at hh
    exact (lt_irrefl _ hh).elim

theorem density_positive_interval_mass (F : Measure ℝ) [IsFiniteMeasure F]
    (f : ℝ → ℝ) (hf : Measurable f)
    (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (a b : ℝ) (hab : a < b) (hpos : ∀ x ∈ Ioo a b, 0 < f x) :
    0 < F.real (Ioo a b) := by
  have hm : 0 < F (Ioo a b) := by
    rw [hF, withDensity_apply _ measurableSet_Ioo]
    apply (setLIntegral_pos_iff hf.ennreal_ofReal).mpr
    have he : Function.support (fun x => ENNReal.ofReal (f x)) ∩ Ioo a b = Ioo a b := by
      apply inter_eq_right.mpr
      intro x hx
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (hpos x hx))
    rw [he, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top _ _)

theorem cutoff_interval_mass_of_density (F : Measure ℝ) [IsFiniteMeasure F]
    (f : ℝ → ℝ) (hf : Measurable f)
    (hF : F = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (c : ℝ) (hc : ContinuousAt f c) (hfc : 0 < f c) :
    (∀ v < c, 0 < F.real (Ioo v c)) ∧ (∀ v > c, 0 < F.real (Ioo c v)) := by
  have he := hc (lt_mem_nhds hfc)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  constructor
  · intro v hv
    let l := max v (c - r / 2)
    have hl : l < c := max_lt hv (by linarith)
    have hm := density_positive_interval_mass F f hf hF l c hl (by
      intro x hx
      apply hball
      rw [Real.dist_eq, abs_lt]
      have hh := le_max_right v (c - r / 2)
      dsimp only [l] at hx
      constructor <;> linarith [hx.1, hx.2])
    exact hm.trans_le (measureReal_mono (fun x hx =>
      ⟨lt_of_le_of_lt (le_max_left v (c - r / 2)) hx.1, hx.2⟩))
  · intro v hv
    let u := min v (c + r / 2)
    have hu : c < u := lt_min hv (by linarith)
    have hm := density_positive_interval_mass F f hf hF c u hu (by
      intro x hx
      apply hball
      rw [Real.dist_eq, abs_lt]
      have hh := min_le_right v (c + r / 2)
      dsimp only [u] at hx
      constructor <;> linarith [hx.1, hx.2])
    exact hm.trans_le (measureReal_mono (fun x hx =>
      ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left v (c + r / 2))⟩))

theorem cutoff_interval_mass_of_local_density (F : Measure ℝ) [IsFiniteMeasure F]
    (f : ℝ → ℝ) (hf : Measurable f) (c : ℝ)
    (U : Set ℝ) (hU : MeasurableSet U) (hUn : U ∈ 𝓝 c)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f c) (hfc : 0 < f c) :
    (∀ v < c, 0 < F.real (Ioo v c)) ∧ (∀ v > c, 0 < F.real (Ioo c v)) := by
  classical
  let f' := U.indicator f
  have hmeas : Measurable f' := hf.indicator hU
  have heq : f' =ᶠ[𝓝 c] f := by
    filter_upwards [hUn] with x hx
    exact indicator_of_mem hx f
  have hcont : ContinuousAt f' c := hc.congr_of_eventuallyEq heq
  have hpositive : 0 < f' c := by simpa only [f', indicator_of_mem (mem_of_mem_nhds hUn)] using hfc
  have hmeasure : F.restrict U = volume.withDensity (fun x => ENNReal.ofReal (f' x)) := by
    rw [hF, restrict_withDensity hU, ← withDensity_indicator hU]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · simp only [f', indicator_of_mem hx]
    · simp only [f', indicator_of_notMem hx, ENNReal.ofReal_zero]
  obtain ⟨hl, hr⟩ := cutoff_interval_mass_of_density (F.restrict U) f' hmeas hmeasure c hcont hpositive
  constructor
  · intro v hv
    have hh := hl v hv
    rw [measureReal_restrict_apply measurableSet_Ioo] at hh
    exact hh.trans_le (measureReal_mono inter_subset_left)
  · intro v hv
    have hh := hr v hv
    rw [measureReal_restrict_apply measurableSet_Ioo] at hh
    exact hh.trans_le (measureReal_mono inter_subset_left)

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem nearPPI_visible_quantile_limit
    (M C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (M k) n (C k) Seed) (j : Fin n)
    (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    (hF : ∀ k, (Γ k).F = F) (g : ℝ) (hg : ∀ k, (Γ k).g = g)
    (a : ℕ → ℝ) (ρ vstar : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (hM : Tendsto M atTop atTop)
    (hcap : Tendsto (fun k => (C k : ℝ) / M k) atTop (𝓝 ρ))
    (ha : Tendsto a atTop (𝓝 1))
    (hΓ : ∀ k, IsAEEquilibrium (Γ k))
    (hp : ∀ k j, ProposerRationalAtFeasibleLists (Γ k) j)
    (hatom : ∀ k, PositiveVisibleAtomless (Γ k))
    (hA : ∀ k r, 0 < r → r ≤ n → a k * (r : ℝ) ≤ (Γ k).A.charge r)
    (hscarce : (n : ℝ) * ρ < F.real (Ioi g))
    (hcutoff : F.real (Ioi vstar) = (n : ℝ) * ρ)
    (hleft : ∀ v < vstar, 0 < F.real (Ioo v vstar))
    (hright : ∀ v > vstar, 0 < F.real (Ioo vstar v))
    (q : ℝ) (hq : 0 < q) (hqr : q < ρ) :
    Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 (vstar - g)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨p, hp0, φ, hφ, hquant, _, _⟩ := exists_positive_price_subsequence
    (M ∘ ns) (C ∘ ns) (fun k => Γ (ns k)) j F (fun k => hF (ns k)) g (fun k => hg (ns k))
    (a ∘ ns) ρ hρ0 hρ (hM.comp hns) (hcap.comp hns) (ha.comp hns)
    (fun k => hΓ (ns k)) (fun k => hp (ns k)) (fun k => hatom (ns k)) (fun k => hA (ns k)) hscarce
  have hs := hns.comp hφ.tendsto_atTop
  have hprice := tail_eq_capacity_of_positive_quantiles
    (fun k => M (ns (φ k))) (fun k => C (ns (φ k))) (fun k => Γ (ns (φ k))) j
    F (fun k => hF (ns (φ k))) g (fun k => hg (ns (φ k))) (fun k => a (ns (φ k)))
    ρ p hρ0 hρ hp0 (hM.comp hs) (hcap.comp hs) (ha.comp hs)
    (fun k => hΓ (ns (φ k))) (fun k => hp (ns (φ k))) (fun k => hatom (ns (φ k)))
    (fun k => hA (ns (φ k))) hquant (measure_singleton _)
  have heq := eq_cutoff_of_tail_eq F vstar (g + p) hleft hright (hprice.trans hcutoff.symm)
  have hp' : p = vstar - g := by linarith
  rw [← hp']
  exact ⟨φ, hquant q hq hqr⟩

end FCAppendix.Bayes
