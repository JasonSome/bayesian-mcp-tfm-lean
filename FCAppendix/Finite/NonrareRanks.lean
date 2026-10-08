import FCAppendix.Finite.PairRanks
import FCAppendix.Finite.RankConcentration

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped BigOperators

theorem binomBelow_upper_of_gap (N c : ℕ) (hc : c ≤ N + 1) (p δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hgap : δ ≤ N * p - (c : ℝ)) :
    binomBelow N p c ≤ N / (4 * δ ^ 2) := by
  rw [binomBelow_eq_prob N c hc p hp0 hp1]
  let μ := IndependentCounts.binomial N p hp0 hp1
  have hsub : μ.prob (fun r => r.val < c) ≤
      μ.prob (fun r => δ ≤ |(r.val : ℝ) - μ.expect (fun s => (s.val : ℝ))|) := by
    apply μ.prob_mono
    intro r hr
    have hrR : (r.val : ℝ) < c := by exact_mod_cast hr
    change _ ≤ |(r.val : ℝ) - μ.load|
    rw [IndependentCounts.binomial_load]
    have habs := neg_abs_le ((r.val : ℝ) - N * p)
    linarith
  have h := μ.chebyshev (fun r => (r.val : ℝ)) δ hδ
  rw [IndependentCounts.binomial_variance] at h
  have hvar : (N : ℝ) * p * (1 - p) ≤ N / 4 := by
    have hp : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  calc
    _ ≤ N * p * (1 - p) / δ ^ 2 := hsub.trans h
    _ ≤ (N / 4) / δ ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = _ := by ring

lemma rank_error_tendsto_zero (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (η : ℝ) :
    Tendsto (fun r => 1 / (4 * (M r : ℝ) * η ^ 2)) atTop (𝓝 0) := by
  have hN : Tendsto (fun r => (M r : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hM)
  have he : (1 : ℝ) / (4 * η ^ 2) = (η ^ 2)⁻¹ * 4⁻¹ := by simp [one_div, mul_inv_rev]
  have hh := hN.mul_const (1 / (4 * η ^ 2))
  rw [he] at hh
  simpa only [one_div, mul_inv_rev, zero_mul, mul_zero, mul_assoc, mul_left_comm, mul_comm] using hh

theorem nonrare_rank_limit_le_capacity (M C : ℕ → ℕ) (p : ℕ → ℝ)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    (hp0 : ∀ r, 0 ≤ p r) (hp1 : ∀ r, p r ≤ 1)
    {p₀ ρ : ℝ} (hp : Tendsto p atTop (𝓝 p₀))
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε) (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r) (p r) (C r)) :
    p₀ ≤ ρ := by
  by_contra hnot
  have hgap : 0 < p₀ - ρ := sub_pos.mpr (lt_of_not_ge hnot)
  let η := (p₀ - ρ) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have he : ∀ᶠ r in atTop, η ≤ p r - (C r : ℝ) / M r :=
    ((hp.sub hc).eventually (eventually_gt_nhds (by dsimp [η]; linarith))).mono (fun _ h => h.le)
  have hsmall := (rank_error_tendsto_zero M hM η).eventually (eventually_lt_nhds hε)
  have hpos := hM.eventually_gt_atTop 0
  obtain ⟨r, hrq, hrgap, hrsmall, hrpos⟩ :=
    Filter.Eventually.exists (hq.and (he.and (hsmall.and hpos)))
  have hMr : (0 : ℝ) < M r := Nat.cast_pos.mpr hrpos
  have hslot : (M r : ℝ) * η ≤ M r * p r - C r := by
    have hh := mul_le_mul_of_nonneg_left hrgap hMr.le
    field_simp at hh
    nlinarith
  have hb := binomBelow_upper_of_gap (M r) (C r) (hC r) (p r) (M r * η)
    (hp0 r) (hp1 r) (mul_pos hMr hη) hslot
  have herr : (M r : ℝ) / (4 * ((M r : ℝ) * η) ^ 2) =
      1 / (4 * (M r : ℝ) * η ^ 2) := by field_simp
  rw [herr] at hb
  linarith

theorem binomBelow_tendsto_one_of_subcritical (M C : ℕ → ℕ) (p : ℕ → ℝ)
    (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    (hp0 : ∀ r, 0 ≤ p r) (hp1 : ∀ r, p r ≤ 1)
    {p₀ ρ : ℝ} (hp : Tendsto p atTop (𝓝 p₀))
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ)) (hgap : p₀ < ρ) :
    Tendsto (fun r => binomBelow (M r) (p r) (C r)) atTop (𝓝 1) := by
  let η := (ρ - p₀) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  have he : ∀ᶠ r in atTop, η ≤ (C r : ℝ) / M r - p r :=
    ((hc.sub hp).eventually (eventually_gt_nhds (by dsimp [η]; linarith))).mono (fun _ h => h.le)
  have hlo : ∀ᶠ r in atTop, 1 - 1 / (4 * (M r : ℝ) * η ^ 2) ≤
      binomBelow (M r) (p r) (C r) := by
    filter_upwards [he, hM.eventually_gt_atTop 0] with r hr hMr
    have hMrR : (0 : ℝ) < M r := Nat.cast_pos.mpr hMr
    have hslot : (M r : ℝ) * η ≤ C r - M r * p r := by
      have hh := mul_le_mul_of_nonneg_left hr hMrR.le
      field_simp at hh
      nlinarith
    have hb := binomBelow_lower_of_gap (M r) (C r) (hC r) (p r) (M r * η)
      (hp0 r) (hp1 r) (mul_pos hMrR hη) hslot
    have herr : (M r : ℝ) / (4 * ((M r : ℝ) * η) ^ 2) =
        1 / (4 * (M r : ℝ) * η ^ 2) := by field_simp
    rwa [herr] at hb
  have hhi : ∀ᶠ r in atTop, binomBelow (M r) (p r) (C r) ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro r
    rw [binomBelow_eq_prob (M r) (C r) (hC r) (p r) (hp0 r) (hp1 r)]
    exact FiniteLaw.prob_le_one _ _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' _ tendsto_const_nhds hlo hhi
  simpa only [sub_zero] using tendsto_const_nhds.sub (rank_error_tendsto_zero M hM η)

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma ppi_acceptProb_eq_binomBelow {N c : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (i : Fin (N + 1)) (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j)
    (b : ℝ) (hb : 0 < b) : acceptProb Γ i b j = binomBelow N (alphaGt Γ j b) c := by
  unfold acceptProb
  have he : (backgroundLaw Γ).real {ω | Accepts Γ i b j ω} =
      (backgroundLaw Γ).real {ω | rivals i (aboveAt j b) ω < c} := by
    apply measureReal_congr
    exact (ae_ppi_accepts_iff_rank Γ hA hatom j hj i b hb).mono (fun _ h => propext h)
  rw [he, prob_rivals_lt Γ i _ (measurableSet_aboveAt j b) c]
  simp only [Nat.add_sub_cancel, alphaGt]

lemma ppi_pair_acceptance_ge_two_rank_sub_one {N c : ℕ} (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (i : Fin (N + 1)) (j : Fin 2 → Fin n) (hj : ∀ k, ProposerRationalAtFeasibleLists Γ (j k))
    (b : ℝ) (hb : 0 < b) :
    2 * binomBelow N (alphaGt Γ (j 0) b) c - 1 ≤
      (backgroundLaw Γ).real {ω | Accepts Γ i b (j 0) ω ∧ Accepts Γ i b (j 1) ω} := by
  have hh := measureReal_union_add_inter (μ := backgroundLaw Γ)
    (s := {ω | Accepts Γ i b (j 0) ω}) (t := {ω | Accepts Γ i b (j 1) ω})
    (measurableSet_accepts Γ i b (j 1)) (measure_ne_top _ _) (measure_ne_top _ _)
  have hu : (backgroundLaw Γ).real ({ω | Accepts Γ i b (j 0) ω} ∪
      {ω | Accepts Γ i b (j 1) ω}) ≤ 1 := measureReal_le_one
  change _ + _ = acceptProb Γ i b (j 0) + acceptProb Γ i b (j 1) at hh
  rw [ppi_acceptProb_eq_binomBelow Γ hA hatom i (j 0) (hj 0) b hb,
    ppi_acceptProb_eq_binomBelow Γ hA hatom i (j 1) (hj 1) b hb,
    alphaGt_eq Γ (j 1) (j 0) b] at hh
  have he : {ω | Accepts Γ i b (j 0) ω} ∩ {ω | Accepts Γ i b (j 1) ω} =
      {ω | Accepts Γ i b (j 0) ω ∧ Accepts Γ i b (j 1) ω} := rfl
  rw [he] at hh
  linarith

theorem eventually_nonrare_ppi_pair_pos
    (M C : ℕ → ℕ) (Γ : (r : ℕ) → FiniteGame (M r + 1) n (C r) Seed)
    (i : (r : ℕ) → Fin (M r + 1)) (j : Fin 2 → Fin n) (b : ℕ → ℝ)
    (hA : ∀ r, (Γ r).A = Schedule.ppi n)
    (hatom : ∀ r, PositiveVisibleAtomless (Γ r))
    (hj : ∀ r k, ProposerRationalAtFeasibleLists (Γ r) (j k))
    (hb : ∀ r, 0 < b r) (hM : Tendsto M atTop atTop) (hC : ∀ r, C r ≤ M r + 1)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hc : Tendsto (fun r => (C r : ℝ) / M r) atTop (𝓝 ρ))
    (ε : ℝ) (hε : 0 < ε)
    (hq : ∀ᶠ r in atTop, ε ≤ binomBelow (M r) (alphaGt (Γ r) (j 0) (b r)) (C r)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ r in atTop, d ≤ (backgroundLaw (Γ r)).real
      {ω | Accepts (Γ r) (i r) (b r) (j 0) ω ∧ Accepts (Γ r) (i r) (b r) (j 1) ω} := by
  let p : ℕ → ℝ := fun r => alphaGt (Γ r) (j 0) (b r)
  have hp0 : ∀ r, 0 ≤ p r := fun _ => measureReal_nonneg
  have hp1 : ∀ r, p r ≤ 1 := fun _ => measureReal_le_one
  apply BernoulliPairs.eventually_pos_of_compact_subsequences p _ 0 1
    (Filter.Eventually.of_forall fun r => ⟨hp0 r, hp1 r⟩) (fun _ => measureReal_nonneg)
  intro f hf p₀ hpf
  have hpρ := nonrare_rank_limit_le_capacity (M ∘ f) (C ∘ f) (p ∘ f) (hM.comp hf)
    (fun r => hC (f r)) (fun r => hp0 (f r)) (fun r => hp1 (f r)) hpf (hc.comp hf) ε hε (hf.eventually hq)
  by_cases hlt : p₀ < ρ
  · have hq1 := binomBelow_tendsto_one_of_subcritical (M ∘ f) (C ∘ f) (p ∘ f)
      (hM.comp hf) (fun r => hC (f r)) (fun r => hp0 (f r)) (fun r => hp1 (f r)) hpf (hc.comp hf) hlt
    refine ⟨1 / 2, by norm_num, ?_⟩
    filter_upwards [hq1.eventually (eventually_gt_nhds (by norm_num : (3 / 4 : ℝ) < 1))] with r hr
    have hh := ppi_pair_acceptance_ge_two_rank_sub_one (Γ (f r)) (hA (f r)) (hatom (f r))
      (i (f r)) j (hj (f r)) (b (f r)) (hb (f r))
    dsimp only [Function.comp_def, p] at hr
    linarith
  · have heq : p₀ = ρ := le_antisymm hpρ (le_of_not_gt hlt)
    subst p₀
    let σ : ℕ → ℝ := fun r => Real.sqrt ((M (f r) : ℝ) * p (f r) * (1 - p (f r)))
    have hv : ∀ r, (M (f r) : ℝ) * p (f r) * (1 - p (f r)) = σ r ^ 2 := by
      intro r
      exact (Real.sq_sqrt (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hp0 _))
        (sub_nonneg.mpr (hp1 _)))).symm
    have hs : Tendsto σ atTop atTop := by
      have hpv : Tendsto (fun r => p (f r) * (1 - p (f r))) atTop (𝓝 (ρ * (1 - ρ))) :=
        hpf.mul (tendsto_const_nhds.sub hpf)
      have hN : Tendsto (fun r => (M (f r) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (hM.comp hf)
      have hvarlim := hN.atTop_mul_pos (mul_pos hρ0 (by linarith : 0 < 1 - ρ)) hpv
      simpa only [σ, Function.comp_def, mul_assoc] using Real.tendsto_sqrt_atTop.comp hvarlim
    obtain ⟨L, hL⟩ := eventually_atTop.mp (hs.eventually_gt_atTop 0)
    let g : ℕ → ℕ := fun r => f (r + L)
    have hg : Tendsto g atTop atTop := hf.comp (tendsto_add_atTop_nat L)
    obtain ⟨d, hd, hde⟩ := eventually_nonrare_ppi_pair_acceptance_pos (M ∘ g) (C ∘ g)
      (fun r => Γ (g r)) (fun r => i (g r)) j (b ∘ g) (fun r => σ (r + L))
      (fun r => hA (g r)) (fun r => hatom (g r)) (fun r => hj (g r)) (fun r => hb (g r))
      (fun r => hL (r + L) (by omega)) (fun r => hv (r + L)) (hs.comp (tendsto_add_atTop_nat L))
      (hpf.comp (tendsto_add_atTop_nat L)) hρ0 hρ1 ε hε (hg.eventually hq)
    refine ⟨d, hd, ?_⟩
    let P : ℕ → ℝ := fun r => (backgroundLaw (Γ (f r))).real
      {ω | Accepts (Γ (f r)) (i (f r)) (b (f r)) (j 0) ω ∧
        Accepts (Γ (f r)) (i (f r)) (b (f r)) (j 1) ω}
    have hshift : ∀ᶠ r in Filter.map (fun r : ℕ => r + L) atTop, d ≤ P r := hde
    simpa only [map_add_atTop_eq_nat] using hshift

end FCAppendix.Bayes
