import FCAppendix.Finite.PPIRankTypes
import FCAppendix.Finite.RankNormal
import FCAppendix.Finite.RankWindow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Filter Set Topology

theorem interval_mass_eq_integral_of_local_density
    (F : Measure ℝ) [IsFiniteMeasure F] (f : ℝ → ℝ) (hf : Measurable f)
    (U : Set ℝ)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (a b : ℝ) (hsub : Ioc a b ⊆ U) (hpos : ∀ x ∈ Ioc a b, 0 ≤ f x) :
    F.real (Ioc a b) = ∫ x in Ioc a b, f x := by
  have hrestrict : F.restrict (Ioc a b) =
      (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict (Ioc a b) := by
    rw [← Measure.restrict_restrict_of_subset hsub, hF,
      Measure.restrict_restrict_of_subset hsub]
  calc
    F.real (Ioc a b) = ∫ _x in Ioc a b, (1 : ℝ) ∂F := by simp
    _ = ∫ _x in Ioc a b, (1 : ℝ) ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
      rw [hrestrict]
    _ = ∫ x in Ioc a b, (ENNReal.ofReal (f x)).toReal • (1 : ℝ) :=
      setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.ennreal_ofReal.aemeasurable
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Ioc
    _ = ∫ x in Ioc a b, f x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      simp only [ENNReal.toReal_ofReal (hpos x hx), smul_eq_mul, mul_one]

theorem value_tail_hasDerivAt_of_local_density
    (F : Measure ℝ) [IsFiniteMeasure F] (f : ℝ → ℝ) (hf : Measurable f)
    (v : ℝ) (U : Set ℝ) (hUn : U ∈ 𝓝 v)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f v) (hpos : 0 < f v) :
    HasDerivAt (fun x => F.real (Ioi x)) (-f v) v := by
  have he : ∀ᶠ x in 𝓝 v, x ∈ U ∧ 0 ≤ f x := by
    filter_upwards [hUn, hc (eventually_gt_nhds hpos)] with x hx hp
    exact ⟨hx, hp.le⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (IntervalIntegrable.refl (f := f) (a := v))
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hc).const_sub (F.real (Ioi v))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds v hr] with x hx
  have hbetween : ∀ z ∈ uIcc v x, z ∈ U ∧ 0 ≤ f z := by
    intro z hz
    apply hball
    have hzdist := Real.dist_le_of_mem_uIcc hz (left_mem_uIcc : v ∈ uIcc v x)
    rw [dist_comm v x] at hzdist
    exact hzdist.trans_lt hx
  have hmass (a b : ℝ) (hab : a ≤ b) (hsub : Ioc a b ⊆ uIcc v x) :
      F.real (Ioi a) - F.real (Ioi b) = ∫ z in a..b, f z := by
    rw [intervalIntegral.integral_of_le hab]
    have hi := interval_mass_eq_integral_of_local_density F f hf U hF a b
      (fun z hz => (hbetween z (hsub hz)).1) (fun z hz => (hbetween z (hsub hz)).2)
    have hm : F.real (Ioc a b) = F.real (Ioi a) - F.real (Ioi b) := by
      rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi hab) measurableSet_Ioi]
    exact hm.symm.trans hi
  rcases le_total v x with hvx | hxv
  · have hh := hmass v x hvx (by rw [uIcc_of_le hvx]; exact Ioc_subset_Icc_self)
    linarith
  · have hh := hmass x v hxv (by rw [uIcc_of_ge hxv]; exact Ioc_subset_Icc_self)
    rw [intervalIntegral.integral_symm x v]
    linarith

theorem hasDerivAt_small_scale_uniform {f : ℝ → ℝ} {v d : ℝ}
    (hf : HasDerivAt f d v) (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (hne : ∀ᶠ k in atTop, h k ≠ 0) (S : Set ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ x ∈ S, |x| ≤ R) :
    TendstoUniformlyOn (fun k x => (f (v + h k * x) - f v) / h k)
      (fun x => d * x) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hcoef : 0 < ε / (2 * (R + 1)) := by positivity
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff.mp (hf.isLittleO.bound hcoef)
  have htol : 0 < r / (R + 1) := by positivity
  have hhabs : Tendsto (fun k => |h k|) atTop (𝓝 0) := by simpa only [abs_zero] using hh.abs
  filter_upwards [hne, hhabs.eventually (eventually_lt_nhds htol)] with k hk hkr
  intro x hx
  have hy : dist (v + h k * x) v < r := by
    rw [Real.dist_eq, add_sub_cancel_left, abs_mul]
    have hxr := hbound x hx
    have hm := mul_lt_mul_of_pos_right hkr (by positivity : 0 < R + 1)
    rw [div_mul_cancel₀ r (by positivity : R + 1 ≠ 0)] at hm
    nlinarith [abs_nonneg (h k)]
  have he := hsmall hy
  simp only [Real.norm_eq_abs, add_sub_cancel_left, smul_eq_mul, abs_mul] at he
  have hid : (f (v + h k * x) - f v) / h k - d * x =
      (f (v + h k * x) - f v - h k * x * d) / h k := by
    field_simp
  rw [dist_comm, Real.dist_eq, hid, abs_div]
  have hkpos : 0 < |h k| := abs_pos.mpr hk
  apply (div_lt_iff₀ hkpos).mpr
  have hb := hbound x hx
  have hcoefR : ε / (2 * (R + 1)) * |x| < ε := by
    have hn : ε / (2 * (R + 1)) * (2 * (R + 1)) = ε :=
      div_mul_cancel₀ ε (by positivity)
    nlinarith
  have hm := mul_lt_mul_of_pos_right hcoefR hkpos
  nlinarith

theorem value_rank_window_expansion
    (F : Measure ℝ) [IsFiniteMeasure F] (f : ℝ → ℝ) (hf : Measurable f)
    (v : ℝ) (U : Set ℝ) (hUn : U ∈ 𝓝 v)
    (hF : F.restrict U = (volume.withDensity (fun x => ENNReal.ofReal (f x))).restrict U)
    (hc : ContinuousAt f v) (hpos : 0 < f v)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (n : ℕ) (hn : 0 < n)
    (ρ σ : ℝ) (hσ : 0 < σ) (hcut : F.real (Ioi v) = n * ρ)
    (S : Set ℝ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x ∈ S, |x| ≤ R) :
    TendstoUniformlyOn (fun k x => Real.sqrt (N k) *
      (F.real (Ioi (v + ((n : ℝ) * σ / (f v * Real.sqrt (N k))) * x)) / n - ρ))
      (fun x => -σ * x) atTop S := by
  let h : ℕ → ℝ := fun k => (n : ℝ) * σ / (f v * Real.sqrt (N k))
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have ht : Tendsto h atTop (𝓝 0) := by
    have he : h = fun k => ((n : ℝ) * σ / f v) / Real.sqrt (N k) := by
      funext k
      dsimp [h]
      ring
    rw [he]
    exact tendsto_const_nhds.div_atTop hsqrt
  have hhne : ∀ᶠ k in atTop, h k ≠ 0 := by
    filter_upwards [hN.eventually_gt_atTop 0] with k hk
    have hs : 0 < Real.sqrt (N k) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
    exact (div_pos (mul_pos hnR hσ) (mul_pos hpos hs)).ne'
  have hexp := hasDerivAt_small_scale_uniform
    (value_tail_hasDerivAt_of_local_density F f hf v U hUn hF hc hpos)
    h ht hhne S R hR hbound
  have hmul := (Real.uniformContinuous_const_mul (x := σ / f v)).comp_tendstoUniformlyOn hexp
  have hlim : (fun x => (σ / f v) * (-f v * x)) = (fun x => -σ * x) := by
    funext x
    field_simp
  simp only [Function.comp_def] at hmul
  rw [hlim] at hmul
  apply hmul.congr
  filter_upwards [hN.eventually_gt_atTop 0] with k hk
  intro x _
  have hs : 0 < Real.sqrt (N k) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  dsimp only [h]
  rw [hcut]
  field_simp

theorem rank_cdf_tendsto_of_scaled_rank
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b : ℕ → ℝ)
    (ρ x : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hN : Tendsto N atTop atTop)
    (hp : Tendsto (fun k => alphaGt (Γ k) j (b k)) atTop (𝓝 ρ))
    (hC : Tendsto (fun k => ((C k : ℝ) - N k * ρ) / Real.sqrt (N k)) atTop (𝓝 0))
    (hs : Tendsto (fun k => Real.sqrt (N k) * (alphaGt (Γ k) j (b k) - ρ)) atTop
      (𝓝 (-Real.sqrt (ρ * (1 - ρ)) * x))) :
    Tendsto (fun k => binomBelow (N k) (alphaGt (Γ k) j (b k)) (C k)) atTop
      (𝓝 (cdf (gaussianReal 0 1) x)) := by
  let p := fun k => alphaGt (Γ k) j (b k)
  let σ := fun k => Real.sqrt ((N k : ℝ) * p k * (1 - p k))
  have hv (k : ℕ) : (N k : ℝ) * p k * (1 - p k) = σ k ^ 2 := by
    symm
    apply Real.sq_sqrt
    have hp0 : 0 ≤ p k := measureReal_nonneg
    have hp1 : p k ≤ 1 := measureReal_le_one
    positivity
  have hσ := rankStdDev_tendsto_atTop N p ρ hN hρ hρ1 hp
  have hstd := rankThreshold_tendsto N C p ρ (-Real.sqrt (ρ * (1 - ρ)) * x)
    hN hρ hρ1 hp hC hs
  have hden : 0 < Real.sqrt (ρ * (1 - ρ)) := Real.sqrt_pos.mpr (by positivity)
  have heq : -(-Real.sqrt (ρ * (1 - ρ)) * x) / Real.sqrt (ρ * (1 - ρ)) = x := by
    field_simp
  rw [heq] at hstd
  exact rank_cdf_tendsto_normal N C Γ i j b σ hv hσ x hstd

theorem sqrt_opponent_population_ratio (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => Real.sqrt (N k) / Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 1) := by
  have hM : Tendsto (fun k => (N k + 1 : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_succ (N k)) hN
  have hinv : Tendsto (fun k => (1 : ℝ) / (N k + 1 : ℕ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hM)
  have hr : Tendsto (fun k => (N k : ℝ) / (N k + 1 : ℕ)) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    simp only [sub_zero] at hh
    apply hh.congr
    intro k
    push_cast
    field_simp
    ring
  have hh := hr.sqrt
  simpa only [Real.sqrt_one, Real.sqrt_div (Nat.cast_nonneg _)] using hh

theorem opponent_capacity_centering (N C : ℕ → ℕ) (ρ : ℝ)
    (hN : Tendsto N atTop atTop)
    (hC : Tendsto (fun k => ((C k : ℝ) - (N k + 1 : ℕ) * ρ) /
      Real.sqrt (N k + 1 : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun k => ((C k : ℝ) - N k * ρ) / Real.sqrt (N k)) atTop (𝓝 0) := by
  have hr := (sqrt_opponent_population_ratio N hN).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one, inv_div] at hr
  have hi : Tendsto (fun k => ρ / Real.sqrt (N k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN))
  have hh := (hC.mul hr).add hi
  simp only [zero_mul, zero_add] at hh
  apply hh.congr'
  filter_upwards [hN.eventually_gt_atTop 0] with k hk
  have hs : 0 < Real.sqrt (N k) := Real.sqrt_pos.mpr (by exact_mod_cast hk)
  have hs1 : 0 < Real.sqrt (N k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  push_cast
  field_simp
  ring

namespace NearPPIAssumptions

theorem comp_index
    {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {M C : ℕ → ℕ} {Γ : ∀ k, FiniteGame (M k) n (C k) Seed}
    {F : Measure ℝ} {g ρ vstar : ℝ} {a : ℕ → ℝ}
    (h : NearPPIAssumptions M C Γ F g a ρ vstar)
    (t : ℕ → ℕ) (ht : Tendsto t atTop atTop) :
    NearPPIAssumptions (M ∘ t) (C ∘ t) (fun k => Γ (t k)) F g (a ∘ t) ρ vstar where
  proposers_two := h.proposers_two
  capacity_lt_population k := h.capacity_lt_population (t k)
  common_values k := h.common_values (t k)
  common_fee k := h.common_fee (t k)
  ratio_pos := h.ratio_pos
  ratio_lt_one := h.ratio_lt_one
  population_grows := h.population_grows.comp ht
  capacity_ratio := h.capacity_ratio.comp ht
  equilibria k := h.equilibria (t k)
  feasible_continuations k := h.feasible_continuations (t k)
  visible_atomless k := h.visible_atomless (t k)
  policy_symmetry k := h.policy_symmetry (t k)
  scarcity := h.scarcity
  efficient_cutoff := h.efficient_cutoff
  local_density := h.local_density
  coefficient_limit := h.coefficient_limit.comp ht
  receipt_lower k := h.receipt_lower (t k)

theorem ppi_nonrare_window_success
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
    (xseq : ℕ → ℝ) (x : ℝ) (hx : Tendsto xseq atTop (𝓝 x))
    (R : ℝ) (hR : 0 ≤ R) (hxR : ∀ᶠ k in atTop, |xseq k| ≤ R)
    (act : ℕ → JointAction n)
    (ε : ℝ) (hε : 0 < ε)
    (hbr : ∀ᶠ k in atTop, (problem (Γ k) (i k)).BestResponse
      (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
        (f vstar * Real.sqrt (N k + 1 : ℕ))) * xseq k) (act k))
    (hvin : ∀ᶠ k in atTop, (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
        (f vstar * Real.sqrt (N k + 1 : ℕ))) * xseq k) ∈ V)
    (hrouted : ∀ᶠ k in atTop, 1 ≤ (act k).routeCount)
    (hq : ∀ᶠ k in atTop, ε ≤ binomBelow (N k) (alphaGt (Γ k)
      (⟨0, by have hh := h.proposers_two; omega⟩ : Fin n) (act k).bid) (C k)) :
    Tendsto (fun k => ((problem (Γ k) (i k)).outcome (act k)).success) atTop
      (𝓝 (cdf (gaussianReal 0 1) x)) := by
  let j : Fin n := ⟨0, by have hh := h.proposers_two; omega⟩
  let σ := Real.sqrt (ρ * (1 - ρ))
  let scale := fun k => (n : ℝ) * σ / (f vstar * Real.sqrt (N k + 1 : ℕ))
  let v := fun k => vstar + scale k * xseq k
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos h.ratio_pos (sub_pos.mpr h.ratio_lt_one))
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [h.population_grows.eventually_ge_atTop (b + 1)] with k hk
    omega
  have hscale : Tendsto scale atTop (𝓝 0) := by
    have hh : Tendsto (fun k => ((n : ℝ) * σ / f vstar) / Real.sqrt (N k + 1 : ℕ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp h.population_grows))
    simpa only [div_div, mul_comm (Real.sqrt _) (f vstar)] using hh
  have hv : Tendsto v atTop (𝓝 vstar) := by
    simpa only [zero_mul, add_zero] using (hscale.mul hx).const_add vstar
  have hranks := h.ppi_nonrare_rank_value_uniform_on_compact i hA hV hsupp ε hε
  have heq : ∀ᶠ k in atTop, alphaGt (Γ k) j (act k).bid = F.real (Ioi (v k)) / n := by
    filter_upwards [hranks, hbr, hvin, hrouted, hq] with k hk hb hv hr hqk
    exact hk (v k) hv (act k) hb hr hqk j
  have hd := value_tail_hasDerivAt_of_local_density F f hf vstar U hUn hF hc hpos
  have hp : Tendsto (fun k => alphaGt (Γ k) j (act k).bid) atTop (𝓝 ρ) := by
    have hh := (hd.continuousAt.tendsto.comp hv).div_const (n : ℝ)
    have he : F.real (Ioi vstar) / n = ρ := by
      rw [h.efficient_cutoff]
      field_simp
    rw [he] at hh
    exact hh.congr' (heq.mono fun _ hk => hk.symm)
  have hwithin : Tendsto xseq atTop (𝓝[Icc (-R) R] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, hxR.mono (fun _ hk => abs_le.mp hk)⟩
  have hscaled := (value_rank_window_expansion F f hf vstar U hUn hF hc hpos
    (fun k => N k + 1) h.population_grows n hn ρ σ hσ h.efficient_cutoff
    (Icc (-R) R) R hR (fun _ hx => abs_le.mpr hx)).tendsto_comp
      (by fun_prop) hwithin
  have hscaled' := (sqrt_opponent_population_ratio N hN).mul hscaled
  simp only [one_mul] at hscaled'
  have hsq : Tendsto (fun k => Real.sqrt (N k) * (alphaGt (Γ k) j (act k).bid - ρ))
      atTop (𝓝 (-σ * x)) := by
    apply hscaled'.congr'
    filter_upwards [heq] with k hk
    have hroot : 0 < Real.sqrt (N k + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    rw [hk]
    dsimp only [v, scale]
    field_simp
  have hnormal := rank_cdf_tendsto_of_scaled_rank N C Γ i j (fun k => (act k).bid)
    ρ x h.ratio_pos h.ratio_lt_one hN hp (opponent_capacity_centering N C ρ hN hC) hsq
  apply hnormal.congr'
  filter_upwards [h.ppi_nonrare_one_route_uniform_on_compact i hA hV ε hε,
    h.ppi_rank_nonrare_bids_pos i hA ε hε, hbr, hvin, hrouted, hq] with k hk hp hb hv hr hqk
  have hone := hk (v k) hv (act k) hb hr hqk
  have hbid := (half_pos h.price_pos).trans (hp (act k).bid hqk)
  rw [singleton_success (Γ k) hn (i k) (act k) hone,
    ppi_meanAcceptProb_eq_rank (Γ k) (hA k) (h.visible_atomless k)
      (h.feasible_continuations k) (i k) j (act k).bid hbid]

theorem ppi_nonrare_window_uniform
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
    (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
    ∀ δ > 0, ∀ᶠ k in atTop, ∀ x ∈ Icc (-R) R,
      (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
        (f vstar * Real.sqrt (N k + 1 : ℕ))) * x) ∈ V →
      ∀ act : JointAction n, (problem (Γ k) (i k)).BestResponse
        (vstar + ((n : ℝ) * Real.sqrt (ρ * (1 - ρ)) /
          (f vstar * Real.sqrt (N k + 1 : ℕ))) * x) act →
      1 ≤ act.routeCount →
      ε ≤ binomBelow (N k) (alphaGt (Γ k)
        (⟨0, by have hh := h.proposers_two; omega⟩ : Fin n) act.bid) (C k) →
      |((problem (Γ k) (i k)).outcome act).success - cdf (gaussianReal 0 1) x| < δ := by
  classical
  intro δ hδ
  by_contra hnot
  simp only [eventually_atTop, not_exists, not_forall] at hnot
  choose t ht x hx hv act hbr hr hq hbad using hnot
  have htlim : Tendsto t atTop atTop := tendsto_atTop_mono ht tendsto_id
  obtain ⟨x₀, _, φ, hφ, hxlim⟩ := isCompact_Icc.tendsto_subseq hx
  let s := t ∘ φ
  have hslim : Tendsto s atTop atTop := htlim.comp hφ.tendsto_atTop
  have hs := h.comp_index s hslim
  have hlim := hs.ppi_nonrare_window_success (fun k => i (s k)) (fun k => hA (s k))
    hV hsupp f hf U hUn hF hc hpos (hC.comp hslim) (x ∘ φ) x₀ hxlim R hR
    (Eventually.of_forall fun k => abs_le.mpr (hx (φ k))) (act ∘ φ) ε hε
    (Eventually.of_forall fun k => hbr (φ k))
    (Eventually.of_forall fun k => hv (φ k))
    (Eventually.of_forall fun k => hr (φ k))
    (Eventually.of_forall fun k => hq (φ k))
  have hnormal := (show Continuous (fun x => cdf (gaussianReal 0 1) x) from continuous_Φ).tendsto x₀
  have he : Tendsto (fun k => |((problem (Γ (s k)) (i (s k))).outcome (act (φ k))).success -
      cdf (gaussianReal 0 1) (x (φ k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hlim.sub (hnormal.comp hxlim)).abs
  obtain ⟨k, hk⟩ := (he.eventually (eventually_lt_nhds hδ)).exists
  exact hbad (φ k) hk

end NearPPIAssumptions
end FCAppendix.Bayes
