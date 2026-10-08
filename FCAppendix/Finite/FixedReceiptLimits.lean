import FCAppendix.Finite.TruncatedValueTail
import FCAppendix.PayOnce.FiniteJensen
import FCAppendix.Finite.FixedQuantile

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Set Topology
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem finiteTruncatedPayment_lower_two_shortfalls
    (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (B : PosteriorSystem Γ) (hu : UsersOptimal Γ) (hB : BayesReceiptOptimalOnPath Γ B)
    (j : Fin n) (a t R ρ ε : ℝ) (ha : 0 < a) (ht : 0 < t) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hA : ∀ r, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (htail : ρ - ε ≤ alphaGt Γ j t) :
    (a * t) * ((n : ℝ) * ((c : ℝ) / m) - n * Γ.F.real (Ioi (Γ.g + R)) -
      2 * n * (ε + (|(c : ℝ) / m - ρ| + 1 / (2 * Real.sqrt m)))) ≤
        finiteTruncatedPayment Γ R := by
  have hΓ := posterior_isAEEquilibrium_onPath Γ B hu hB
  have hgap := capacity_gap_le_visible_shortfall Γ hm hΓ.proposers j a ha hA
    t ρ ε ht hε htail
  have hlow := finiteTruncatedPayment_lower_quantitative Γ hm hc B hu hB j
    a t R ρ ε ha.le ht.le hR hε hA htail
  apply le_trans _ hlow
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg ha.le ht.le)
  linarith

theorem finiteCoverage_unit_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    0 ≤ finiteCoverage Γ ∧ finiteCoverage Γ ≤ 1 := by
  refine ⟨integral_nonneg (fun d => (profileCoverage_bounds Γ hm d).1), ?_⟩
  have hh := integral_mono (integrable_profileCoverage Γ hm) (integrable_const (1 : ℝ))
    (fun d => (profileCoverage_bounds Γ hm d).2)
  simpa only [finiteCoverage, integral_const, probReal_univ, one_smul] using hh

theorem finiteLoad_interval_bounds (Γ : FiniteGame m n c Seed) (hm : 0 < m) :
    0 ≤ finiteLoad Γ ∧ finiteLoad Γ ≤ n := by
  refine ⟨integral_nonneg (fun d => (profileLoad_bounds Γ hm d).1), ?_⟩
  have hh := integral_mono (integrable_profileLoad Γ hm) (integrable_const (n : ℝ))
    (fun d => (profileLoad_bounds Γ hm d).2)
  simpa only [finiteLoad, integral_const, probReal_univ, one_smul] using hh

namespace ReceiptSequenceAssumptions

variable {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

omit [IsProbabilityMeasure F] in

theorem payment_comparison_of_one_quantile
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (j : Fin n) (ε p t R H Q : ℝ)
    (hε : 0 < ε) (hερ : ε < ρ) (hp : 0 < p)
    (ht : 0 < t) (htp : t < p) (hR : 0 ≤ R)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) (ρ - ε)) atTop (𝓝 p))
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    (a * t) * ((n : ℝ) * ρ - n * F.real (Ioi (g + R)) - 2 * n * ε) ≤
      (p / a) * Q + (n * R) * F.real (Ioi H) := by
  obtain ⟨e, he, he0, henv⟩ := exists_uniform_singleton_error_fixed_factor h j
    (ρ - ε) p H (sub_pos.mpr hερ) (by linarith) hu
  have htail := eventually_visible_tail_of_one_quantile M C Γ j (ρ - ε) p t ht.le htp hu
  have hE := marketShortageError_tendsto_zero M C ρ h.population_grows h.capacity_ratio
  have hlo : Tendsto (fun k => (a * t) * ((n : ℝ) * ((C k : ℝ) / M k) -
      n * F.real (Ioi (g + R)) - 2 * n * (ε + marketShortageError M C ρ k)))
      atTop (𝓝 ((a * t) * ((n : ℝ) * ρ - n * F.real (Ioi (g + R)) - 2 * n * ε))) := by
    simpa only [add_zero] using
      ((((h.capacity_ratio.const_mul (n : ℝ)).sub_const (n * F.real (Ioi (g + R)))).sub
        ((hE.const_add ε).const_mul (2 * (n : ℝ)))).const_mul (a * t))
  have hhi : Tendsto (fun k => (p / a) * finiteCoverage (Γ k) + e k +
      (n * R) * F.real (Ioi H)) atTop (𝓝 ((p / a) * Q + (n * R) * F.real (Ioi H))) := by
    simpa only [add_zero] using ((hQ.const_mul (p / a)).add he0).add_const
      ((n * R) * F.real (Ioi H))
  apply le_of_tendsto_of_tendsto hlo hhi
  filter_upwards [h.population_grows.eventually_gt_atTop 0, h.eventually_capacity_pos,
    htail, henv] with k hmk hck htk hek
  have hl := finiteTruncatedPayment_lower_two_shortfalls (Γ k) hmk hck (B k)
    (h.users k) (h.bayes_receipts k) j a t R ρ ε h.factor_pos ht hR hε.le
    (h.receipt_lower k) htk
  have hupp := finiteTruncatedPayment_upper_value_cutoff (Γ k) hmk (h.users k)
    (p / a) R H (e k) (div_nonneg hp.le h.factor_pos.le) hR (he k)
      (fun i v hv => by simpa only [h.common_fee k] using hek i v hv)
  simpa only [marketShortageError, h.common_values k, h.common_fee k] using hl.trans hupp

theorem payment_comparison_without_value_cutoff
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (j : Fin n) (ε p t R Q : ℝ)
    (hε : 0 < ε) (hερ : ε < ρ) (hp : 0 < p)
    (ht : 0 < t) (htp : t < p) (hR : 0 ≤ R)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) (ρ - ε)) atTop (𝓝 p))
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    (a * t) * ((n : ℝ) * ρ - n * F.real (Ioi (g + R)) - 2 * n * ε) ≤ (p / a) * Q := by
  have hh : Tendsto (fun H : ℝ => (p / a) * Q + (n * R) * F.real (Ioi H))
      atTop (𝓝 ((p / a) * Q)) := by
    simpa using ((TailQuantile.tail_tendsto_zero F).const_mul (n * R)).const_add ((p / a) * Q)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hh
  exact Eventually.of_forall (fun H => h.payment_comparison_of_one_quantile j ε p t R H Q
    hε hερ hp ht htp hR hu hQ)

theorem payment_comparison_without_cutoffs
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (j : Fin n) (ε p t Q : ℝ)
    (hε : 0 < ε) (hερ : ε < ρ) (hp : 0 < p) (ht : 0 < t) (htp : t < p)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) (ρ - ε)) atTop (𝓝 p))
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    (a * t) * ((n : ℝ) * ρ - 2 * n * ε) ≤ (p / a) * Q := by
  have htail := (TailQuantile.tail_tendsto_zero F).comp
    (tendsto_atTop_add_const_left atTop g tendsto_id)
  have hh : Tendsto (fun R : ℝ => (a * t) * ((n : ℝ) * ρ -
      n * F.real (Ioi (g + R)) - 2 * n * ε))
      atTop (𝓝 ((a * t) * ((n : ℝ) * ρ - 2 * n * ε))) := by
    simpa using (((htail.const_mul (n : ℝ)).const_sub ((n : ℝ) * ρ)).sub_const
      (2 * n * ε)).const_mul (a * t)
  apply le_of_tendsto_of_tendsto hh tendsto_const_nhds
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  exact h.payment_comparison_without_value_cutoff j ε p t R Q hε hερ hp ht htp hR hu hQ

theorem coverage_lower_one_quantile
    (h : ReceiptSequenceAssumptions M C Γ B F g a ρ)
    (j : Fin n) (ε p Q : ℝ) (hε : 0 < ε) (hερ : ε < ρ) (hp : 0 < p)
    (hu : Tendsto (fun k => TailQuantile.quantile (alphaGt (Γ k) j) (ρ - ε)) atTop (𝓝 p))
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    a ^ 2 * ((n : ℝ) * ρ - 2 * n * ε) ≤ Q := by
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k => (a * (p - d k)) * ((n : ℝ) * ρ - 2 * n * ε))
      atTop (𝓝 ((a * p) * ((n : ℝ) * ρ - 2 * n * ε))) := by
    simpa using ((hd.const_sub p).const_mul a).mul_const ((n : ℝ) * ρ - 2 * n * ε)
  have hh : (a * p) * ((n : ℝ) * ρ - 2 * n * ε) ≤ (p / a) * Q := by
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [(tendsto_order.mp hd).2 p hp] with k hk
    have hdk : 0 < d k := by dsimp [d]; positivity
    exact h.payment_comparison_without_cutoffs j ε p (p - d k) Q hε hερ hp
      (by linarith) (by linarith) hu hQ
  have hmul := mul_le_mul_of_nonneg_left hh h.factor_pos.le
  have hne : a ≠ 0 := h.factor_pos.ne'
  have hright : a * ((p / a) * Q) = p * Q := by field_simp [hne]
  rw [hright] at hmul
  have he : a * ((a * p) * ((n : ℝ) * ρ - 2 * n * ε)) =
      p * (a ^ 2 * ((n : ℝ) * ρ - 2 * n * ε)) := by ring
  rw [he] at hmul
  exact le_of_mul_le_mul_left hmul hp

end ReceiptSequenceAssumptions

namespace FixedReceiptAssumptions

variable {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
  {B : ∀ k, PosteriorSystem (Γ k)} {F : Measure ℝ} [IsProbabilityMeasure F]
  {g a ρ : ℝ}

theorem coverage_limit_lower
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) (Q : ℝ)
    (hQ : Tendsto (fun k => finiteCoverage (Γ k)) atTop (𝓝 Q)) :
    (n : ℝ) * ρ * a ^ 2 ≤ Q := by
  let j : Fin n := ⟨0, h.proposers_pos⟩
  have hrank (ε : ℝ) (hε : 0 < ε) (hερ : ε < ρ) :
      a ^ 2 * ((n : ℝ) * ρ - 2 * n * ε) ≤ Q := by
    obtain ⟨p, hp, φ, hφ, hu⟩ := h.exists_positive_quantile_subsequence j
      (ρ - ε) (sub_pos.mpr hερ) (by linarith)
    exact (h.along φ hφ.tendsto_atTop).toReceiptSequenceAssumptions.coverage_lower_one_quantile j ε p Q
      hε hερ hp hu (hQ.comp hφ.tendsto_atTop)
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun k => a ^ 2 * ((n : ℝ) * ρ - 2 * n * e k))
      atTop (𝓝 (a ^ 2 * ((n : ℝ) * ρ))) := by
    simpa using ((he.const_mul (2 * (n : ℝ))).const_sub ((n : ℝ) * ρ)).const_mul (a ^ 2)
  have hh : a ^ 2 * ((n : ℝ) * ρ) ≤ Q := by
    apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
    filter_upwards [(tendsto_order.mp he).2 ρ h.ratio_pos] with k hk
    exact hrank (e k) (by dsimp [e]; positivity) hk
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hh

theorem coverage_deficit_tendsto_zero
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) :
    Tendsto (fun k => max ((n : ℝ) * ρ * a ^ 2 - finiteCoverage (Γ k)) 0)
      atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h' := h.along ns hns
  have hb : ∀ᶠ k in atTop, finiteCoverage (Γ (ns k)) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [h'.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteCoverage_unit_bounds (Γ (ns k)) hk
  obtain ⟨Q, _, φ, hφ, hQ⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).tendsto_subseq' hb.frequently
  have hlo := (h'.along φ hφ.tendsto_atTop).coverage_limit_lower Q hQ
  have hlim := (hQ.const_sub ((n : ℝ) * ρ * a ^ 2)).max (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
  refine ⟨φ, ?_⟩
  simpa only [Function.comp_def, max_eq_right (sub_nonpos.mpr hlo)] using hlim

theorem eventually_coverage_lower
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, (n : ℝ) * ρ * a ^ 2 - δ < finiteCoverage (Γ k) := by
  filter_upwards [(tendsto_order.mp h.coverage_deficit_tendsto_zero).2 δ hδ] with k hk
  have hm := le_max_left ((n : ℝ) * ρ * a ^ 2 - finiteCoverage (Γ k)) 0
  linarith

theorem load_limit_eq_capacity
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) (L : ℝ)
    (hL : Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 L)) : L = (n : ℝ) * ρ := by
  have hupper : L ≤ (n : ℝ) * ρ := le_of_tendsto_of_tendsto hL
    (h.capacity_ratio.const_mul (n : ℝ)) (Eventually.of_forall fun k => finiteLoad_le_capacity (Γ k))
  let j : Fin n := ⟨0, h.proposers_pos⟩
  have hrank (ε : ℝ) (hε : 0 < ε) (hερ : ε < ρ) : (n : ℝ) * ρ - n * ε ≤ L := by
    obtain ⟨p, hp, φ, hφ, hu⟩ := h.exists_positive_quantile_subsequence j
      (ρ - ε) (sub_pos.mpr hερ) (by linarith)
    have h' := h.along φ hφ.tendsto_atTop
    have htail := eventually_visible_tail_of_one_quantile (M ∘ φ) (C ∘ φ)
      (fun k => Γ (φ k)) j (ρ - ε) p (p / 2) (by positivity) (by linarith) hu
    have hE := marketShortageError_tendsto_zero (M ∘ φ) (C ∘ φ) ρ
      h'.population_grows h'.capacity_ratio
    have hlo : Tendsto (fun k => (n : ℝ) * ((C (φ k) : ℝ) / M (φ k)) -
        n * (ε + marketShortageError (M ∘ φ) (C ∘ φ) ρ k))
        atTop (𝓝 ((n : ℝ) * ρ - n * ε)) := by
      simpa using (h'.capacity_ratio.const_mul (n : ℝ)).sub ((hE.const_add ε).const_mul (n : ℝ))
    apply le_of_tendsto_of_tendsto hlo (hL.comp hφ.tendsto_atTop)
    filter_upwards [h'.population_grows.eventually_gt_atTop 0, htail] with k hmk htk
    have hh := capacity_gap_le_visible_shortfall (Γ (φ k)) hmk
      (h'.equilibria k).proposers j a h.factor_pos (h'.receipt_lower k)
      (p / 2) ρ ε (by positivity) hε.le htk
    dsimp only [marketShortageError, Function.comp_apply]
    linarith
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlo : Tendsto (fun k => (n : ℝ) * ρ - n * e k) atTop (𝓝 ((n : ℝ) * ρ)) := by
    simpa using (he.const_mul (n : ℝ)).const_sub ((n : ℝ) * ρ)
  have hlower : (n : ℝ) * ρ ≤ L := by
    apply le_of_tendsto_of_tendsto hlo tendsto_const_nhds
    filter_upwards [(tendsto_order.mp he).2 ρ h.ratio_pos] with k hk
    exact hrank (e k) (by dsimp [e]; positivity) hk
  exact le_antisymm hupper hlower

theorem load_tendsto_capacity
    (h : FixedReceiptAssumptions M C Γ B F g a ρ) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 ((n : ℝ) * ρ)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have h' := h.along ns hns
  have hb : ∀ᶠ k in atTop, finiteLoad (Γ (ns k)) ∈ Icc (0 : ℝ) (n : ℝ) := by
    filter_upwards [h'.population_grows.eventually_gt_atTop 0] with k hk
    exact finiteLoad_interval_bounds (Γ (ns k)) hk
  obtain ⟨L, _, φ, hφ, hL⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (n : ℝ))).tendsto_subseq' hb.frequently
  have hident := (h'.along φ hφ.tendsto_atTop).load_limit_eq_capacity L hL
  exact ⟨φ, by simpa only [hident, Function.comp_def] using hL⟩

end FixedReceiptAssumptions
end FCAppendix.Bayes
