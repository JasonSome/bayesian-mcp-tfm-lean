import FCAppendix.Finite.EnvelopeLimits
import FCAppendix.Probability.CountLimits

namespace FCAppendix
namespace NearPPI

open Filter MeasureTheory Topology

noncomputable def cutoffSuccess (x : ℝ) : ℝ := if 0 < x then 1 else 0

theorem price_bounds {x p U S D e δ : ℝ}
    (hp : 0 ≤ p) (hU : 0 ≤ U) (hS0 : 0 ≤ S) (hS1 : S ≤ 1)
    (hD : 0 ≤ D) (he : 0 ≤ e) (hδ : 0 ≤ δ)
    (hupper : U ≤ x * S - p * D + e)
    (hlower : max x 0 - δ ≤ U) :
    p * D ≤ e + δ ∧ |U - max x 0| ≤ e + δ ∧
      |x| * |S - cutoffSuccess x| ≤ e + δ := by
  have hPD : 0 ≤ p * D := mul_nonneg hp hD
  have hxS : x * S ≤ max x 0 := by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx]
      nlinarith
    · rw [max_eq_right hx]
      exact mul_nonpos_of_nonpos_of_nonneg hx hS0
  refine ⟨by linarith, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith
  · by_cases hx : 0 < x
    · simp only [cutoffSuccess, if_pos hx, abs_of_pos hx,
        abs_of_nonpos (sub_nonpos.mpr hS1)]
      rw [max_eq_left hx.le] at hlower
      nlinarith
    · have hx0 : x ≤ 0 := le_of_not_gt hx
      simp only [cutoffSuccess, if_neg hx, sub_zero, abs_of_nonpos hx0,
        abs_of_nonneg hS0]
      nlinarith

theorem change_price {n : ℕ} (μ : CountLaw n) {U w p t e : ℝ}
    (hupper : U ≤ (w - t) * μ.success - t * μ.duplicates + e) :
    U ≤ (w - p) * μ.success - p * μ.duplicates +
      (e + (n : ℝ) * |t - p|) := by
  have hL := μ.load_le_n
  have hL0 := μ.load_nonneg
  have hp : p - t ≤ |t - p| := by
    have h := neg_le_abs (t - p)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hp hL0
  have hn := mul_le_mul_of_nonneg_left hL (abs_nonneg (t - p))
  unfold CountLaw.duplicates at hupper ⊢
  nlinarith

theorem tendsto_utility {x p : ℝ} {U S D e δ : ℕ → ℝ}
    (hp : 0 ≤ p) (hU : ∀ m, 0 ≤ U m) (hS0 : ∀ m, 0 ≤ S m)
    (hS1 : ∀ m, S m ≤ 1) (hD : ∀ m, 0 ≤ D m)
    (he : ∀ m, 0 ≤ e m) (hδ : ∀ m, 0 ≤ δ m)
    (hupper : ∀ m, U m ≤ x * S m - p * D m + e m)
    (hlower : ∀ m, max x 0 - δ m ≤ U m)
    (he0 : Tendsto e atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto U atTop (𝓝 (max x 0)) := by
  have h : Tendsto (fun m => |U m - max x 0|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _)
      (fun m => (price_bounds hp (hU m) (hS0 m) (hS1 m) (hD m)
        (he m) (hδ m) (hupper m) (hlower m)).2.1)
    simpa using he0.add hδ0
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [Real.dist_eq] using h)

theorem tendsto_success {x p : ℝ} {U S D e δ : ℕ → ℝ}
    (hx : x ≠ 0) (hp : 0 ≤ p) (hU : ∀ m, 0 ≤ U m) (hS0 : ∀ m, 0 ≤ S m)
    (hS1 : ∀ m, S m ≤ 1) (hD : ∀ m, 0 ≤ D m)
    (he : ∀ m, 0 ≤ e m) (hδ : ∀ m, 0 ≤ δ m)
    (hupper : ∀ m, U m ≤ x * S m - p * D m + e m)
    (hlower : ∀ m, max x 0 - δ m ≤ U m)
    (he0 : Tendsto e atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto S atTop (𝓝 (cutoffSuccess x)) := by
  have hx0 := abs_pos.mpr hx
  have h : Tendsto (fun m => |S m - cutoffSuccess x|) atTop (𝓝 0) := by
    apply squeeze_zero (g := fun m => (e m + δ m) / |x|) (fun _ => abs_nonneg _)
    · intro m
      apply (le_div_iff₀ hx0).mpr
      simpa only [mul_comm] using
        (price_bounds hp (hU m) (hS0 m) (hS1 m) (hD m)
          (he m) (hδ m) (hupper m) (hlower m)).2.2
    · simpa using (he0.add hδ0).div_const |x|
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa only [Real.dist_eq] using h)

theorem tendsto_duplicates {x p : ℝ} {U S D e δ : ℕ → ℝ}
    (hp : 0 < p) (hU : ∀ m, 0 ≤ U m) (hS0 : ∀ m, 0 ≤ S m)
    (hS1 : ∀ m, S m ≤ 1) (hD : ∀ m, 0 ≤ D m)
    (he : ∀ m, 0 ≤ e m) (hδ : ∀ m, 0 ≤ δ m)
    (hupper : ∀ m, U m ≤ x * S m - p * D m + e m)
    (hlower : ∀ m, max x 0 - δ m ≤ U m)
    (he0 : Tendsto e atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto D atTop (𝓝 0) := by
  apply squeeze_zero (g := fun m => (e m + δ m) / p) hD
  · intro m
    apply (le_div_iff₀ hp).mpr
    simpa only [mul_comm] using
      (price_bounds hp.le (hU m) (hS0 m) (hS1 m) (hD m)
        (he m) (hδ m) (hupper m) (hlower m)).1
  · simpa using (he0.add hδ0).div_const p

theorem count_limits {n : ℕ} (μ : ℕ → CountLaw n) {x p : ℝ} {U e δ : ℕ → ℝ}
    (hx : x ≠ 0) (hp : 0 < p) (hU : ∀ m, 0 ≤ U m)
    (he : ∀ m, 0 ≤ e m) (hδ : ∀ m, 0 ≤ δ m)
    (hupper : ∀ m, U m ≤ x * (μ m).success - p * (μ m).duplicates + e m)
    (hlower : ∀ m, max x 0 - δ m ≤ U m)
    (he0 : Tendsto e atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto U atTop (𝓝 (max x 0)) ∧
    Tendsto (fun m => (μ m).success) atTop (𝓝 (cutoffSuccess x)) ∧
    Tendsto (fun m => (μ m).duplicates) atTop (𝓝 0) ∧
    Tendsto (fun m => (μ m).load) atTop (𝓝 (cutoffSuccess x)) ∧
    Tendsto (fun m => (μ m).prob (fun r => r.val ≠ if 0 < x then 1 else 0))
      atTop (𝓝 0) := by
  have hS := tendsto_success hx hp.le hU (fun m => (μ m).success_nonneg)
    (fun m => (μ m).success_le_one) (fun m => (μ m).duplicates_nonneg)
    he hδ hupper hlower he0 hδ0
  have hD := tendsto_duplicates hp hU (fun m => (μ m).success_nonneg)
    (fun m => (μ m).success_le_one) (fun m => (μ m).duplicates_nonneg)
    he hδ hupper hlower he0 hδ0
  refine ⟨tendsto_utility hp.le hU (fun m => (μ m).success_nonneg)
    (fun m => (μ m).success_le_one) (fun m => (μ m).duplicates_nonneg)
    he hδ hupper hlower he0 hδ0, hS, hD, ?_, ?_⟩
  · convert hD.add hS using 1 <;> simp [CountLaw.duplicates]
  · by_cases hpos : 0 < x
    · simpa only [if_pos hpos] using CountLaw.tendsto_unit_count μ
        (by simpa only [cutoffSuccess, if_pos hpos] using hS) hD
    · simpa only [if_neg hpos, CountLaw.success, FiniteLaw.prob,
        successIndicator, cutoffSuccess, ne_eq, ite_not] using hS

theorem mean_error_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (e : ℕ → Ω → ℝ)
    (he : ∀ m, 0 ≤ᵐ[ν] e m) (hIe : ∀ m, Integrable (e m) ν)
    (hmean : Tendsto (fun m => ∫ v, e m v ∂ν) atTop (𝓝 0)) :
    TendstoInMeasure ν e atTop (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (by norm_num)
    (fun m => (hIe m).aestronglyMeasurable) aestronglyMeasurable_const
  have heq : ∀ m, eLpNorm (e m - fun _ => 0) 1 ν = ENNReal.ofReal (∫ v, e m v ∂ν) := by
    intro m
    rw [eLpNorm_one_eq_lintegral_enorm,
      ofReal_integral_eq_lintegral_ofReal (hIe m) (he m)]
    apply lintegral_congr_ae
    filter_upwards [he m] with v hv
    simp only [Pi.sub_apply, sub_zero, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hv]
  simp_rw [heq]
  simpa [Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp hmean

theorem aggregate_limits {n : ℕ} (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (μ : ℕ → ℝ → CountLaw n) (U e δ : ℕ → ℝ → ℝ) (c p : ℝ)
    (hp : 0 < p) (hc : ν {c} = 0)
    (hSmeas : ∀ m, AEStronglyMeasurable (fun v => (μ m v).success) ν)
    (hDmeas : ∀ m, AEStronglyMeasurable (fun v => (μ m v).duplicates) ν)
    (hU : ∀ m, ∀ᵐ v ∂ν, 0 ≤ U m v)
    (he : ∀ m, 0 ≤ᵐ[ν] e m) (hδ : ∀ m, 0 ≤ᵐ[ν] δ m)
    (hupper : ∀ m, ∀ᵐ v ∂ν,
      U m v ≤ (v - c) * (μ m v).success - p * (μ m v).duplicates + e m v)
    (hlower : ∀ m, ∀ᵐ v ∂ν, max (v - c) 0 - δ m v ≤ U m v)
    (hIe : ∀ m, Integrable (e m) ν)
    (he0 : Tendsto (fun m => ∫ v, e m v ∂ν) atTop (𝓝 0))
    (hδ0 : ∀ᵐ v ∂ν, Tendsto (fun m => δ m v) atTop (𝓝 0)) :
    Tendsto (fun m =>
      (∫ v, (μ m v).success ∂ν,
        (∫ v, (μ m v).duplicates ∂ν, ∫ v, (μ m v).load ∂ν))) atTop
      (𝓝 (∫ v, cutoffSuccess (v - c) ∂ν, (0, ∫ v, cutoffSuccess (v - c) ∂ν))) := by
  have heM := mean_error_tendstoInMeasure ν e he hIe he0
  have hcAE : ∀ᵐ v ∂ν, v - c ≠ 0 := by
    have h : ∀ᵐ v ∂ν, v ∉ ({c} : Set ℝ) := by
      rw [ae_iff]
      simpa using hc
    filter_upwards [h] with v hv
    simpa only [Set.mem_singleton_iff, sub_ne_zero] using hv
  have hbounds : ∀ᵐ v ∂ν, ∀ m,
      0 ≤ U m v ∧ 0 ≤ e m v ∧ 0 ≤ δ m v ∧
      U m v ≤ (v - c) * (μ m v).success - p * (μ m v).duplicates + e m v ∧
      max (v - c) 0 - δ m v ≤ U m v := by
    apply ae_all_iff.mpr
    intro m
    filter_upwards [hU m, he m, hδ m, hupper m, hlower m] with v h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, heAE⟩ := (heM.comp hns).exists_seq_tendsto_ae
  have hlim : ∀ᵐ v ∂ν,
      Tendsto (fun k => (μ (ns (ms k)) v).success) atTop (𝓝 (cutoffSuccess (v - c))) ∧
      Tendsto (fun k => (μ (ns (ms k)) v).duplicates) atTop (𝓝 0) ∧
      Tendsto (fun k => (μ (ns (ms k)) v).load) atTop (𝓝 (cutoffSuccess (v - c))) := by
    filter_upwards [hcAE, hbounds, hδ0, heAE] with v hv hb hd he'
    have h := count_limits (fun k => μ (ns (ms k)) v) hv hp
      (fun k => (hb (ns (ms k))).1)
      (fun k => (hb (ns (ms k))).2.1)
      (fun k => (hb (ns (ms k))).2.2.1)
      (fun k => (hb (ns (ms k))).2.2.2.1)
      (fun k => (hb (ns (ms k))).2.2.2.2)
      he' (hd.comp (hns.comp hms.tendsto_atTop))
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
  have hQ := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (1 : ℝ))
    (fun k => hSmeas (ns (ms k))) (integrable_const (1 : ℝ))
    (fun k => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (μ (ns (ms k)) v).success_nonneg]
      exact (μ (ns (ms k)) v).success_le_one)
    (hlim.mono fun _ hv => hv.1)
  have hD := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (n : ℝ))
    (fun k => hDmeas (ns (ms k))) (integrable_const (n : ℝ))
    (fun k => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (μ (ns (ms k)) v).duplicates_nonneg]
      have h := (μ (ns (ms k)) v).load_le_n
      have h0 := (μ (ns (ms k)) v).success_nonneg
      unfold CountLaw.duplicates
      linarith)
    (hlim.mono fun _ hv => hv.2.1)
  have hLmeas : ∀ k, AEStronglyMeasurable (fun v => (μ (ns (ms k)) v).load) ν := by
    intro k
    convert (hDmeas (ns (ms k))).add (hSmeas (ns (ms k))) using 1
    ext v
    simp [CountLaw.duplicates]
  have hL := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ => (n : ℝ))
    hLmeas (integrable_const (n : ℝ))
    (fun k => ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (μ (ns (ms k)) v).load_nonneg]
      exact (μ (ns (ms k)) v).load_le_n)
    (hlim.mono fun _ hv => hv.2.2)
  exact ⟨ms, by simpa using hQ.prodMk_nhds (hD.prodMk_nhds hL)⟩

theorem integral_cutoffSuccess (ν : Measure ℝ) [IsProbabilityMeasure ν] (c : ℝ) :
    (∫ v, cutoffSuccess (v - c) ∂ν) = (ν (Set.Ioi c)).toReal := by
  have heq : (fun v => cutoffSuccess (v - c)) = (Set.Ioi c).indicator (fun _ => (1 : ℝ)) := by
    funext v
    simp [cutoffSuccess, Set.indicator, sub_pos]
  rw [heq, integral_indicator measurableSet_Ioi]
  simp [Measure.real]

theorem multiplicity_limit {Q L : ℕ → ℝ} {q : ℝ}
    (hq : q ≠ 0) (hQ : Tendsto Q atTop (𝓝 q)) (hL : Tendsto L atTop (𝓝 q)) :
    Tendsto (fun m => L m / Q m) atTop (𝓝 1) := by
  convert hL.div hQ hq using 1
  · rfl
  · simp [div_self hq]

theorem utility_limit_across_support_gaps {U δ : ℕ → ℝ → ℝ} {c : ℝ}
    (hmono : ∀ m, Monotone (U m))
    (hLip : ∀ m v w, |U m v - U m w| ≤ |v - w|)
    (hlower : ∀ m v, max (v - c) 0 - δ m v ≤ U m v)
    (hδ : ∀ v, Tendsto (fun m => δ m v) atTop (𝓝 0))
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ w : ℝ, c - ε < w ∧ w < c ∧
      Tendsto (fun m => U m w) atTop (𝓝 0)) :
    ∀ v, Tendsto (fun m => U m v) atTop (𝓝 (max (v - c) 0)) := by
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w, hclose, hwc, hwlim⟩ := hnear (ε / 2) (half_pos hε)
  have hW : ∀ᶠ m in atTop, U m w < ε / 2 := hwlim.eventually (gt_mem_nhds (half_pos hε))
  have hδ' : ∀ᶠ m in atTop, δ m v < ε := (hδ v).eventually (gt_mem_nhds hε)
  filter_upwards [hW, hδ'] with m hm hd
  have hup : U m v ≤ U m w + max (v - w) 0 := by
    by_cases hvw : v ≤ w
    · rw [max_eq_right (sub_nonpos.mpr hvw), add_zero]
      exact hmono m hvw
    · have h := (le_abs_self (U m v - U m w)).trans (hLip m v w)
      have hwv := le_of_not_ge hvw
      rw [abs_of_nonneg (sub_nonneg.mpr hwv), max_eq_left (sub_nonneg.mpr hwv)] at *
      linarith
  have hmax : max (v - w) 0 ≤ max (v - c) 0 + (c - w) := by
    apply max_le
    · linarith [le_max_left (v - c) 0]
    · linarith [le_max_right (v - c) 0]
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hlower m v]
  · linarith

theorem uniformOn_compact_of_lipschitz {U : ℕ → ℝ → ℝ} {u : ℝ → ℝ} (C : NNReal)
    (hLip : ∀ m, LipschitzWith C (U m))
    (hlim : ∀ v, Tendsto (fun m => U m v) atTop (𝓝 (u v)))
    {K : Set ℝ} (hK : IsCompact K) : TendstoUniformlyOn U u atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLipK : ∀ m, LipschitzWith C (fun v : K => U m v) := by
    intro m
    exact LipschitzWith.of_dist_le_mul fun v w => (hLip m).dist_le_mul v w
  have hEqui := (LipschitzWith.uniformEquicontinuous _ C hLipK).equicontinuous
  have h := (hEqui.tendsto_uniformFun_iff_pi atTop (fun v : K => u v)).mpr
    (tendsto_pi_nhds.mpr (fun v => hlim v))
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp h)

end NearPPI

namespace Interim.Problem

open Filter Topology

theorem bestResponse_success_tendsto {n : ℕ} (P : ℕ → Problem n)
    (c v : ℝ) (hv : v ≠ c) (a : ℕ → Game.JointAction n)
    (ha : ∀ m, (P m).BestResponse v (a m))
    (hU : ∀ w, Tendsto (fun m => (P m).envelope w) atTop (𝓝 (max (w - c) 0))) :
    Tendsto (fun m => ((P m).outcome (a m)).success) atTop
      (𝓝 (NearPPI.cutoffSuccess (v - c))) := by
  let w := (v + c) / 2
  rcases lt_or_gt_of_ne hv with hvc | hcv
  · have hwc : w < c := by dsimp [w]; linarith
    have hvw : 0 < w - v := by dsimp [w]; linarith
    have hzero : Tendsto (fun m => ((P m).envelope w - (P m).envelope v) / (w - v))
        atTop (𝓝 0) := by
      have h := (hU w |>.sub (hU v)).div_const (w - v)
      simpa [max_eq_right (sub_nonpos.mpr hwc.le),
        max_eq_right (sub_nonpos.mpr hvc.le)] using h
    have hS : Tendsto (fun m => ((P m).outcome (a m)).success) atTop (𝓝 0) := by
      apply squeeze_zero (fun m => ((P m).outcome (a m)).success_nonneg) _ hzero
      intro m
      apply (le_div_iff₀ hvw).mpr
      have h := (P m).supporting_line v (a m) (ha m) w
      nlinarith
    simpa [NearPPI.cutoffSuccess, not_lt.mpr (sub_nonpos.mpr hvc.le)] using hS
  · have hcw : c < w := by dsimp [w]; linarith
    have hwv : 0 < v - w := by dsimp [w]; linarith
    have hone : Tendsto (fun m => ((P m).envelope v - (P m).envelope w) / (v - w))
        atTop (𝓝 1) := by
      have h := (hU v |>.sub (hU w)).div_const (v - w)
      simpa [max_eq_left (sub_nonneg.mpr hcw.le),
        max_eq_left (sub_nonneg.mpr hcv.le), div_self hwv.ne'] using h
    have herr : Tendsto (fun m => 1 - ((P m).outcome (a m)).success) atTop (𝓝 0) := by
      apply squeeze_zero
        (fun m => sub_nonneg.mpr ((P m).outcome (a m)).success_le_one)
        (g := fun m => 1 - ((P m).envelope v - (P m).envelope w) / (v - w))
      · intro m
        have h := (P m).supporting_line v (a m) (ha m) w
        have hs : ((P m).envelope v - (P m).envelope w) / (v - w) ≤
            ((P m).outcome (a m)).success := by
          apply (div_le_iff₀ hwv).mpr
          nlinarith
        linarith
      · simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hone
    have hS := (tendsto_const_nhds (x := (1 : ℝ))).sub herr
    simpa [NearPPI.cutoffSuccess, sub_pos.mpr hcv] using hS

theorem envelope_uniformOn_compact {n : ℕ} (P : ℕ → Problem n) (u : ℝ → ℝ)
    (hU : ∀ v, Tendsto (fun m => (P m).envelope v) atTop (𝓝 (u v)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun m => (P m).envelope) u atTop K := by
  apply NearPPI.uniformOn_compact_of_lipschitz 1 _ hU hK
  intro m
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    (P m).envelope_lipschitz_inequality v w

end Interim.Problem
end FCAppendix
