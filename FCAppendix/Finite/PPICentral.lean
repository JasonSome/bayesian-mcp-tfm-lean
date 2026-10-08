import FCAppendix.Finite.PPIWindowCalculus
import FCAppendix.Finite.PPIVisibleRanks

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem rank_zero_eventually_above_window
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b : ℕ → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hN : Tendsto N atTop atTop)
    (hcap : ∀ k, C k ≤ N k + 1)
    (hC : Tendsto (fun k => ((C k : ℝ) - N k * ρ) / Real.sqrt (N k)) atTop (𝓝 0))
    (hzero : Tendsto (fun k => binomBelow (N k) (alphaGt (Γ k) j (b k)) (C k))
      atTop (𝓝 0))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 ρ)) (s : ℝ)
    (hs : Tendsto (fun k => Real.sqrt (N k) * (r k - ρ)) atTop (𝓝 s)) :
    ∀ᶠ k in atTop, r k < alphaGt (Γ k) j (b k) := by
  classical
  by_contra hnot
  simp only [eventually_atTop, not_exists, not_forall, not_lt] at hnot
  choose t ht hle using hnot
  have htlim : Tendsto t atTop atTop := tendsto_atTop_mono ht tendsto_id
  have hmem : ∀ k, alphaGt (Γ (t k)) j (b (t k)) ∈ Icc (0 : ℝ) 1 :=
    fun _ => ⟨measureReal_nonneg, measureReal_le_one⟩
  obtain ⟨p₀, _, φ, hφ, hp⟩ := isCompact_Icc.tendsto_subseq hmem
  let u := t ∘ φ
  have hulim : Tendsto u atTop atTop := htlim.comp hφ.tendsto_atTop
  let p := fun k => alphaGt (Γ (u k)) j (b (u k))
  have hplim : Tendsto p atTop (𝓝 p₀) := hp
  have hNr := hN.comp hulim
  have hCr := hC.comp hulim
  have hrr := hr.comp hulim
  have hsr := hs.comp hulim
  have hzr := hzero.comp hulim
  have hpρ : p₀ ≤ ρ := le_of_tendsto_of_tendsto hplim hrr
    (Eventually.of_forall fun k => hle (φ k))
  have hratio : Tendsto (fun k => (C (u k) : ℝ) / N (u k)) atTop (𝓝 ρ) := by
    have hinv : Tendsto (fun k => 1 / Real.sqrt (N (u k))) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hNr))
    have hh := (hCr.mul hinv).add_const ρ
    simp only [zero_mul, zero_add] at hh
    apply hh.congr'
    filter_upwards [hNr.eventually_gt_atTop 0] with k hk
    have hspos : 0 < Real.sqrt (N (u k)) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N (u k) by positivity)
    dsimp only [Function.comp_apply]
    have hnne : (N (u k) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
    field_simp
    rw [hsq]
    ring
  have hpeq : p₀ = ρ := by
    by_contra hne
    have hgap : p₀ < ρ := lt_of_le_of_ne hpρ hne
    have hone := binomBelow_tendsto_one_of_subcritical (N ∘ u) (C ∘ u) p hNr
      (fun k => hcap (u k)) (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
      hplim hratio hgap
    have heq := tendsto_nhds_unique hzr hone
    norm_num at heq
  subst p₀
  let σ := fun k => Real.sqrt ((N (u k) : ℝ) * p k * (1 - p k))
  have hv (k : ℕ) : (N (u k) : ℝ) * p k * (1 - p k) = σ k ^ 2 := by
    symm
    apply Real.sq_sqrt
    have hp0 : 0 ≤ p k := measureReal_nonneg
    have hp1 : p k ≤ 1 := measureReal_le_one
    positivity
  have hσ := rankStdDev_tendsto_atTop (N ∘ u) p ρ hNr hρ hρ1 hplim
  have herr := rank_normal_error_tendsto_zero (N ∘ u) (C ∘ u) (fun k => Γ (u k))
    (fun k => i (u k)) j (b ∘ u) σ hv hσ
  have hden : Tendsto (fun k => Real.sqrt (p k * (1 - p k))) atTop
      (𝓝 (Real.sqrt (ρ * (1 - ρ)))) :=
    (hplim.mul (tendsto_const_nhds.sub hplim)).sqrt
  have hdpos : 0 < Real.sqrt (ρ * (1 - ρ)) := Real.sqrt_pos.mpr (by positivity)
  have hi : Tendsto (fun k => 1 / Real.sqrt (N (u k))) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hNr))
  have hlower := ((hCr.sub hi).sub hsr).div hden hdpos.ne'
  simp only [sub_zero, zero_sub] at hlower
  let L := -s / Real.sqrt (ρ * (1 - ρ)) - 1
  have hL : L < -s / Real.sqrt (ρ * (1 - ρ)) := by dsimp [L]; linarith
  have hΦ : 0 < cdf (gaussianReal 0 1) L := CorrelatedLoads.gaussian_cdf_pos L
  obtain ⟨k, hk⟩ := (Filter.Eventually.and
    (Filter.Eventually.and (hlower.eventually (eventually_gt_nhds hL))
      (hσ.eventually_gt_atTop 0))
    (Filter.Eventually.and (hzr.eventually (eventually_lt_nhds (half_pos hΦ)))
      (herr.eventually (eventually_lt_nhds (half_pos hΦ))))).exists
  have hthreshold : L ≤ pairRankThreshold (N (u k)) (C (u k)) (p k) (σ k) := by
    have hnpos : 0 < Real.sqrt (N (u k)) := by
      have : 0 < (N (u k) : ℝ) * p k * (1 - p k) := Real.sqrt_pos.mp hk.1.2
      apply Real.sqrt_pos.mpr
      by_contra hh
      have hz : (N (u k) : ℝ) = 0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _)
      rw [hz, zero_mul, zero_mul] at this
      exact (lt_irrefl _ this)
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ N (u k) by positivity)
    have heq : (((C (u k) : ℝ) - N (u k) * ρ) / Real.sqrt (N (u k)) -
        1 / Real.sqrt (N (u k)) - Real.sqrt (N (u k)) * (r (u k) - ρ)) /
        Real.sqrt (p k * (1 - p k)) =
        ((C (u k) : ℝ) - 1 - N (u k) * r (u k)) / σ k := by
      dsimp [σ]
      rw [mul_assoc, Real.sqrt_mul (Nat.cast_nonneg _), div_mul_eq_div_div]
      congr 1
      field_simp
      rw [hsq]
      ring
    apply hk.1.1.le.trans
    change _ ≤ ((C (u k) : ℝ) - 1 - N (u k) * p k) / σ k
    dsimp only [Function.comp_apply, Pi.div_apply]
    rw [heq]
    have hpr : p k ≤ r (u k) := hle (φ k)
    exact div_le_div_of_nonneg_right
      (by nlinarith [hpr, (Nat.cast_nonneg (N (u k)) : (0 : ℝ) ≤ N (u k))]) hk.1.2.le
  have hmono := monotone_cdf (gaussianReal 0 1) hthreshold
  have habs := (abs_lt.mp hk.2.2).1
  dsimp [p, u] at habs hmono hk
  linarith

namespace NearPPIAssumptions

theorem ppi_window_success_nonrare
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ ε > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse
        (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
          (f vstar * Real.sqrt (N k + 1 : ℕ))) * x) act →
      ε ≤ ((problem (Γ k) (i k)).outcome act).success := by
  classical
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  let σ := Real.sqrt (ρ * (1 - ρ))
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos h.ratio_pos (sub_pos.mpr h.ratio_lt_one))
  let r := fun k => ρ + σ * (R + 1) / Real.sqrt (N k + 1 : ℕ)
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [h.population_grows.eventually_ge_atTop (B + 1)] with k hk
    omega
  have hr : Tendsto r atTop (𝓝 ρ) := by
    have hh : Tendsto (fun k => σ * (R + 1) / Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
    simpa only [add_zero] using hh.const_add ρ
  have hs : Tendsto (fun k => Real.sqrt (N k) * (r k - ρ)) atTop (𝓝 (σ * (R + 1))) := by
    have hh := (sqrt_opponent_population_ratio N hN).mul_const (σ * (R + 1))
    simp only [one_mul] at hh
    apply hh.congr
    intro k
    dsimp [r]
    ring
  have hzero : Tendsto (fun k => binomBelow (N k) (alphaGt (Γ k) j 0) (C k))
      atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro z hz
      apply Eventually.of_forall
      intro k
      have hh := prob_rivals_lt (Γ k) (i k) (aboveAt j 0) (measurableSet_aboveAt j 0) (C k)
      simp only [Nat.add_sub_cancel] at hh
      rw [alphaGt, ← hh]
      exact hz.trans_le measureReal_nonneg
    · intro ε hε
      filter_upwards [h.ppi_rank_nonrare_bids_pos i hA ε hε] with k hk
      by_contra hh
      have hb := hk 0 (le_of_not_gt hh)
      linarith [h.price_pos]
  have hboundary := rank_zero_eventually_above_window N C Γ i j (fun _ => 0)
    ρ h.ratio_pos h.ratio_lt_one hN (fun k => (h.capacity_lt_population k).le)
    (opponent_capacity_centering N C ρ hN hC) hzero r hr (σ * (R + 1)) hs
  have hrex (k : ℕ) : ∃ b : ℝ,
      (0 < r k ∧ r k < alphaGt (Γ k) j 0) → 0 < b ∧ alphaGt (Γ k) j b = r k := by
    by_cases he : 0 < r k ∧ r k < alphaGt (Γ k) j 0
    · obtain ⟨b, hb⟩ := exists_positive_bid_at_rank (Γ k) (h.visible_atomless k) j (r k) he.1 he.2
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun hh => (he hh).elim⟩
  choose b hb using hrex
  have hbrank : ∀ᶠ k in atTop, 0 < b k ∧ alphaGt (Γ k) j (b k) = r k := by
    filter_upwards [hboundary, hr.eventually (eventually_gt_nhds h.ratio_pos)] with k hbd hp
    exact hb k ⟨hp, hbd⟩
  have hp : Tendsto (fun k => alphaGt (Γ k) j (b k)) atTop (𝓝 ρ) :=
    hr.congr' (hbrank.mono fun _ hk => hk.2.symm)
  have hscaled : Tendsto (fun k => Real.sqrt (N k) * (alphaGt (Γ k) j (b k) - ρ))
      atTop (𝓝 (-σ * (-(R + 1)))) := by
    have he : -σ * (-(R + 1)) = σ * (R + 1) := by ring
    rw [he]
    apply hs.congr'
    filter_upwards [hbrank] with k hk
    rw [hk.2]
  have hnormal := rank_cdf_tendsto_of_scaled_rank N C Γ i j b ρ (-(R + 1))
    h.ratio_pos h.ratio_lt_one hN hp (opponent_capacity_centering N C ρ hN hC) hscaled
  let ε := cdf (gaussianReal 0 1) (-(R + 1)) / 2
  have hε : 0 < ε := half_pos (CorrelatedLoads.gaussian_cdf_pos _)
  have hεlt : ε < cdf (gaussianReal 0 1) (-(R + 1)) :=
    half_lt_self (CorrelatedLoads.gaussian_cdf_pos _)
  have hexp := value_rank_window_expansion F f hf vstar U hUn hF hc hpos
    (fun k => N k + 1) h.population_grows n hn ρ σ hσ h.efficient_cutoff
    (Icc (-R) R) R hR (fun _ hx => abs_le.mpr hx)
  have hmass : ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R,
      F.real (Ioi (vstar + ((n : ℝ) * σ / (f vstar * Real.sqrt (N k + 1 : ℕ))) * x)) / n < r k := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hexp) (σ / 2) (half_pos hσ)] with k hk
    intro x hx
    have hh := hk x hx
    rw [Real.dist_eq] at hh
    have hupper := (abs_lt.mp hh).1
    have hspos : 0 < Real.sqrt (N k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    dsimp only [r]
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hspos]
    nlinarith [hx.1]
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hbrank, hnormal.eventually (eventually_gt_nhds hεlt), hmass,
    h.ppi_nonrare_one_route_uniform_on_compact i hA hV ε hε] with k hbq hq hm hone
  intro x hx act ha
  haveI : NullSingletonClass (Γ k).F := by rw [h.common_values k]; infer_instance
  apply ppi_success_ge_of_rank_mass (Γ k) (hA k) (h.visible_atomless k)
    (h.feasible_continuations k) (h.equilibria k).1 (i k) j V
    (by simpa only [h.common_values k] using hsupp) ε hone (b k) hbq.1 hq.le
    _ _ act ha
  rw [h.common_values k, hbq.2]
  exact hm x hx

theorem ppi_central_window
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {N C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed}
    {F : Measure ℝ} [IsProbabilityMeasure F] [NullSingletonClass F]
    {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions (fun k => N k + 1) C Γ F g a ρ vstar)
    (i : ∀ k, Fin (N k + 1)) (hA : ∀ k, (Γ k).A = Schedule.ppi n)
    {V : Set ℝ} (hV : IsCompact V) (hsupp : ∀ᵐ w ∂F, w ∈ V)
    (f : ℝ → ℝ) (hf : Measurable f) (U : Set ℝ) (hUn : U ∈ 𝓝 vstar)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f vstar) (hpos : 0 < f vstar)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0))
    (R : ℝ) (hR : 0 ≤ R) :
    ∀ δ > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, ∀ act : JointAction n,
      (problem (Γ k) (i k)).BestResponse
        (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
          (f vstar * Real.sqrt (N k + 1 : ℕ))) * x) act →
      act.routeCount = 1 ∧
        |((problem (Γ k) (i k)).outcome act).success - cdf (gaussianReal 0 1) x| < δ := by
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let K := V ∪ Icc (vstar - 1) (vstar + 1)
  have hK : IsCompact K := hV.union isCompact_Icc
  have hKsupp : ∀ᵐ w ∂F, w ∈ K := hsupp.mono fun _ hw => Or.inl hw
  let scale := fun k => (n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
    (f vstar * Real.sqrt (N k + 1 : ℕ))
  have hscale : Tendsto scale atTop (𝓝 0) := by
    have hh : Tendsto (fun k => ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) / f vstar) /
        Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
    simpa only [div_div, mul_comm (Real.sqrt _) (f vstar)] using hh
  have hvin : ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R, vstar + scale k * x ∈ K := by
    have htol : 0 < 1 / (R + 1) := by positivity
    have hsa : Tendsto (fun k => |scale k|) atTop (𝓝 0) := by
      simpa only [abs_zero] using hscale.abs
    filter_upwards [hsa.eventually (eventually_lt_nhds htol)] with k hk
    intro x hx
    apply Or.inr
    have hab : |x| ≤ R := abs_le.mpr hx
    have hb : |scale k * x| < 1 := by
      rw [abs_mul]
      have hh := mul_lt_mul_of_pos_right hk (by positivity : 0 < R + 1)
      rw [one_div_mul_cancel (by positivity : R + 1 ≠ 0)] at hh
      nlinarith [abs_nonneg (scale k)]
    exact ⟨by linarith [(abs_lt.mp hb).1], by linarith [(abs_lt.mp hb).2]⟩
  obtain ⟨ε, hε, hsuccess⟩ := h.ppi_window_success_nonrare i hA hV hsupp
    f hf U hUn hF hc hpos hC R hR
  have he : 0 < ε / n := div_pos hε hnR
  intro δ hδ
  filter_upwards [hsuccess, hvin,
    h.ppi_nonrare_one_route_uniform_on_compact i hA hK (ε / n) he,
    h.ppi_nonrare_window_uniform i hA hK hKsupp f hf U hUn hF hc hpos hC R hR
      (ε / n) he δ hδ] with k hsucc hval hone hgauss
  intro x hx act ha
  have hs := hsucc x hx act ha
  have hr : 1 ≤ act.routeCount := by
    by_contra hh
    have hz : act.routeCount = 0 := by omega
    have hl := load_le_routeCount_mul_success (Γ k) (i k) act
    rw [hz, Nat.cast_zero, zero_mul] at hl
    linarith [((problem (Γ k) (i k)).outcome act).success_le_load]
  have hq : ε / n ≤ binomBelow (N k) (alphaGt (Γ k) j act.bid) (C k) := by
    have hb := ppi_meanAcceptProb_le_rank (Γ k) (hA k) (h.feasible_continuations k)
      (i k) j act.bid act.bid_nonneg
    simp only [Nat.add_sub_cancel] at hb
    have hc := success_le_n_meanAcceptProb (Γ k) hn (i k) act
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  exact ⟨hone _ (hval x hx) act ha hr hq,
    hgauss x hx (hval x hx) act ha hr hq⟩

end NearPPIAssumptions
end FCAppendix.Bayes
