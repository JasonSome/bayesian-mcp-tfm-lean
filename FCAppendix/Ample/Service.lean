import FCAppendix.Finite.FixedReceiptLimits
import FCAppendix.Ample.ServiceBounds

namespace FCAppendix.Bayes.ReceiptSequenceAssumptions

open MeasureTheory ProbabilityTheory Game Filter Set Topology

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

theorem ample_quantile_limit_eq_zero
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (j : Fin n) (ε p : ℝ) (hε : 0 < ε) (hερ : ε < ρ)
    (hample : F.real (Ioi g) < a ^ 2 * ((n : ℝ) * ρ - 2 * n * ε))
    (hp : 0 ≤ p)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) (ρ - ε)) atTop (𝓝 p)) :
    p = 0 := by
  by_contra hpz
  have hp0 : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hb : ∀ᶠ k in atTop, finiteCoverage (Γ k) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteCoverage_unit_bounds (Γ k) hk
  obtain ⟨Q, _, φ, hφ, hQ⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq' hb.frequently
  have h' := h.along φ hφ.tendsto_atTop
  have hlo := h'.coverage_lower_one_quantile j ε p Q hε hερ hp0
    (hu.comp hφ.tendsto_atTop) hQ
  have hhi : Q ≤ F.real (Ioi g) := by
    apply le_of_tendsto hQ
    filter_upwards [h'.population_grows.eventually_gt_atTop 0] with k hk
    have hgz : (Γ (φ k)).F {(Γ (φ k)).g} = 0 := by
      rw [h'.common_values k, h'.common_fee k]
      exact hg
    have hh := finiteCoverage_le_positive_population (Γ (φ k)) hk (h'.users k) hgz
    simpa only [Function.comp_def, h'.common_values k, h'.common_fee k] using hh
  linarith

theorem ample_exists_zero_quantile
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2) (j : Fin n) :
    ∃ q : ℝ, 0 < q ∧ q < ρ ∧
      Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) q) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k => a ^ 2 * ((n : ℝ) * ρ - 2 * n * e k))
      atTop (𝓝 ((n : ℝ) * ρ * a ^ 2)) := by
    have hh := ((he.const_mul (2 * (n : ℝ))).const_sub ((n : ℝ) * ρ)).const_mul (a ^ 2)
    simpa [mul_comm] using hh
  obtain ⟨r, hr, hr'⟩ := (((tendsto_order.mp he).2 ρ h.ratio_pos).and
    ((tendsto_order.mp hlim).1 _ hample)).exists
  have her : 0 < e r := by dsimp [e]; positivity
  refine ⟨ρ - e r, sub_pos.mpr hr, by linarith, ?_⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h' := h.along ns hns
  obtain ⟨D, _, hb⟩ := eventually_bounded_visible_quantile (M ∘ ns) (C ∘ ns)
    (fun k => Γ (ns k)) j F h'.common_values h'.population_grows
    h'.eventually_capacity_pos h'.equilibria (ρ - e r) (sub_pos.mpr hr)
  obtain ⟨p, hpD, φ, hφ, hu⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) D)).tendsto_subseq' hb.frequently
  have hpz := (h'.along φ hφ.tendsto_atTop).ample_quantile_limit_eq_zero hg j
    (e r) p her hr hr' hpD.1 hu
  exact ⟨φ, by simpa only [Function.comp_def, hpz] using hu⟩

theorem ample_envelope_uniform
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2) (H : ℝ) :
    ∀ δ > 0, ∀ᶠ k in atTop, ∀ (i : Fin (M k)) v, v ≤ H →
      |(problem (Γ k) i).envelope v - max (v - g) 0| < δ := by
  let j : Fin n := ⟨0, h.proposers_pos⟩
  obtain ⟨q, hq, hqr, hu⟩ := h.ample_exists_zero_quantile hg hample j
  obtain ⟨e, _, he0, henv⟩ := exists_uniform_singleton_error_fixed_factor h j q 0 H hq hqr hu
  intro δ hδ
  filter_upwards [henv, (tendsto_order.mp he0).2 δ hδ] with k hk he
  intro i v hv
  have hlo := hk i v hv
  have hup := (problem (Γ k) i).envelope_upper v
  change (problem (Γ k) i).envelope v ≤ max (v - (Γ k).g) 0 at hup
  rw [h.common_fee k] at hup
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  simp only [zero_div, sub_zero] at hlo
  linarith

theorem ample_envelope_tendsto
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (i : ∀ k, Fin (M k)) (v : ℝ) :
    Tendsto (fun k => (problem (Γ k) (i k)).envelope v) atTop (𝓝 (max (v - g) 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h.ample_envelope_uniform hg hample v ε hε] with k hk
  simpa only [Real.dist_eq] using hk (i k) v le_rfl

theorem ample_bestResponses
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2)
    (i : ∀ k, Fin (M k)) (v : ℝ) (hv : g < v) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse v act →
      1 - ((problem (Γ k) (i k)).outcome act).success < ε ∧ act.bid < ε ∧
      g * (((problem (Γ k) (i k)).outcome act).charge (Γ k).G -
        ((problem (Γ k) (i k)).outcome act).success) < ε := by
  have hU := h.ample_envelope_tendsto hg hample i v
  have hdef : Tendsto (fun k => Ample.deficit (problem (Γ k) (i k)) (v - g))
      atTop (𝓝 0) := by
    have he (k : ℕ) : (v - g) + (problem (Γ k) (i k)).g = v := by
      change (v - g) + (Γ k).g = v
      rw [h.common_fee k]
      ring
    simpa only [Ample.deficit, he, max_eq_left (sub_pos.mpr hv).le, sub_self] using
      hU.const_sub (v - g)
  have hh := Ample.all_bestResponses_full_service_of_deficit
    (fun k => problem (Γ k) (i k)) (v - g) (sub_pos.mpr hv) hdef
  have he (k : ℕ) : (problem (Γ k) (i k)).g = g := h.common_fee k
  have hG (k : ℕ) : (problem (Γ k) (i k)).G = (Γ k).G := rfl
  simpa only [he, hG, sub_add_cancel] using hh

theorem ample_coverage_limit_eq
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2) (Q : ℝ)
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    Q = F.real (Ioi g) := by
  let j : Fin n := ⟨0, h.proposers_pos⟩
  obtain ⟨q, hq, hqr, hu⟩ := h.ample_exists_zero_quantile hg hample j
  have hfinite (η d : ℝ) (hη : 0 < η) (hd : 0 < d) :
      F.real (Ioi (g + η)) * (1 - d / η) ≤ Q := by
    let t : ℕ → ℝ := fun k => TailQuantile.quantile (alphaGt (Γ k) j) q / a + d
    let r : ℕ → ℝ := fun k => (M k - 1 : ℕ) / (4 * ((M k : ℝ) * (ρ - q) / 2) ^ 2)
    have ht : Tendsto t atTop (𝓝 d) := by simpa [t] using (hu.div_const a).add_const d
    have hr : Tendsto r atTop (𝓝 0) :=
      singleton_failure_tendsto_zero M h.population_grows (ρ - q) (sub_pos.mpr hqr)
    have hlo : Tendsto (fun k => F.real (Ioi (g + η)) * (1 - r k - t k / η))
        atTop (𝓝 (F.real (Ioi (g + η)) * (1 - d / η))) := by
      simpa only [sub_zero] using ((hr.const_sub 1).sub (ht.div_const η)).const_mul
        (F.real (Ioi (g + η)))
    apply le_of_tendsto_of_tendsto hlo hQ
    filter_upwards [h.population_grows.eventually_gt_atTop 0,
      eventually_singleton_success_varying_increment_of_positive M C Γ j
        (fun _ => a) (fun _ => d) ρ q h.ratio_lt_one hq hqr
        (Eventually.of_forall fun _ => hd) h.population_grows h.capacity_ratio
        (Eventually.of_forall fun _ => h.factor_pos) h.equilibria
        h.feasible_continuations h.visible_atomless h.receipt_lower] with k hmk hk
    let act : JointAction n := ⟨t k, hk.1.le, 1, h.proposers_pos⟩
    have hh := finiteCoverage_lower_singleton (Γ k) hmk h.proposers_pos (h.users k)
      act rfl (r k) η (by dsimp [r]; positivity) hη (hk.2)
    simpa only [h.common_values k, h.common_fee k, act] using hh
  have htail (η : ℝ) (hη : 0 < η) : F.real (Ioi (g + η)) ≤ Q := by
    have hd : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hh : Tendsto (fun k : ℕ => F.real (Ioi (g + η)) *
        (1 - (1 / ((k : ℝ) + 1)) / η)) atTop (𝓝 (F.real (Ioi (g + η)))) := by
      simpa using ((hd.div_const η).const_sub 1).const_mul (F.real (Ioi (g + η)))
    exact le_of_tendsto hh (Eventually.of_forall fun k => hfinite η _ hη (by positivity))
  have hlo : F.real (Ioi g) ≤ Q := by
    by_contra hnot
    obtain ⟨η, hη, hηQ⟩ := exists_positive_tail_margin F g Q (lt_of_not_ge hnot)
    exact (not_le_of_gt hηQ) (htail η hη)
  have hhi : Q ≤ F.real (Ioi g) := by
    apply le_of_tendsto hQ
    filter_upwards [h.population_grows.eventually_gt_atTop 0] with k hk
    have hgz : (Γ k).F {(Γ k).g} = 0 := by rw [h.common_values k, h.common_fee k]; exact hg
    simpa only [h.common_values k, h.common_fee k] using
      finiteCoverage_le_positive_population (Γ k) hk (h.users k) hgz
  exact le_antisymm hhi hlo

theorem ample_coverage_tendsto
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ) (hg : F {g} = 0)
    (hample : F.real (Ioi g) < (n : ℝ) * ρ * a ^ 2) :
    Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 (F.real (Ioi g))) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h' := h.along ns hns
  have hb : ∀ᶠ k in atTop, finiteCoverage (Γ (ns k)) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [h'.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteCoverage_unit_bounds (Γ (ns k)) hk
  obtain ⟨Q, _, φ, hφ, hQ⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq' hb.frequently
  have he := (h'.along φ hφ.tendsto_atTop).ample_coverage_limit_eq hg hample Q hQ
  exact ⟨φ, by simpa only [Function.comp_def, he] using hQ⟩

end FCAppendix.Bayes.ReceiptSequenceAssumptions
