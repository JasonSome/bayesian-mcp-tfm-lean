import FCAppendix.Finite.PairRanks
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology Set
open scoped BigOperators

universe u

theorem exists_rank_nonuniform_normal_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ {N n c : ℕ} {Seed : Type u} [MeasurableSpace Seed]
        (Γ : FiniteGame (N + 1) n c Seed) (_i : Fin (N + 1)) (j : Fin n)
        (b σ : ℝ), 0 < σ →
        (N : ℝ) * alphaGt Γ j b * (1 - alphaGt Γ j b) = σ ^ 2 →
        |binomBelow N (alphaGt Γ j b) c -
          cdf (gaussianReal 0 1) (pairRankThreshold N c (alphaGt Γ j b) σ)| ≤
          K / σ / (1 + |pairRankThreshold N c (alphaGt Γ j b) σ| ^ 3) := by
  obtain ⟨K, hK, hBE⟩ := BernoulliApproximation.exists_bernoulli_nonuniform_bound.{0, 0}
  refine ⟨K, hK, ?_⟩
  intro N n c Seed _ Γ i j b σ hσ hvar
  let μ := Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)
  let X := pairRankIndicators i (fun _ : Fin 2 => j) b
  have hXm : ∀ l k, Measurable (X l k) := pairRankIndicators_measurable i _ b
  have hX : ∀ l k, ∀ᵐ d ∂μ, X l k d = 0 ∨ X l k d = 1 :=
    fun l k => Eventually.of_forall (pairRankIndicators_bernoulli i _ b l k)
  have hm : ∀ l k, ∫ d, X l k d ∂μ = alphaGt Γ j b := pairRankIndicators_integral Γ i _ b
  have hXi := BernoulliPairs.indep_coordinate X (pairRankIndicators_indep Γ i _ b) 0
  have hv : (∑ l, (∫ d, X l 0 d ∂μ) * (1 - ∫ d, X l 0 d ∂μ)) = σ ^ 2 := by
    simpa only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc] using hvar
  have hb := hBE μ (fun l => X l 0) σ (fun l => hXm l 0) hXi (fun l => hX l 0)
    hσ hv (pairRankThreshold N c (alphaGt Γ j b) σ)
  have he : (fun d => (∑ l, (X l 0 d - ∫ d', X l 0 d' ∂μ)) / σ) =
      BernoulliPairs.load X (alphaGt Γ j b) σ 0 := by
    funext d
    simp only [hm, BernoulliPairs.load_eq]
  rw [he] at hb
  have hload := (BernoulliPairs.memLp_load X (alphaGt Γ j b) σ hXm hX 2 0).aemeasurable
  haveI := Measure.isProbabilityMeasure_map hload
  have hprob : cdf (μ.map (BernoulliPairs.load X (alphaGt Γ j b) σ 0))
      (pairRankThreshold N c (alphaGt Γ j b) σ) = binomBelow N (alphaGt Γ j b) c := by
    rw [cdf_eq_real, Measure.real, Measure.map_apply_of_aemeasurable hload measurableSet_Iic]
    exact pairRank_cdf_eq_binomBelow Γ i (fun _ : Fin 2 => j) b (alphaGt Γ j b) σ hσ 0
  rwa [hprob] at hb

variable {n : ℕ} {Seed : Type u} [MeasurableSpace Seed]

theorem rank_normal_error_tendsto_zero
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b σ : ℕ → ℝ)
    (hv : ∀ k, (N k : ℝ) * alphaGt (Γ k) j (b k) * (1 - alphaGt (Γ k) j (b k)) = σ k ^ 2)
    (hσ : Tendsto σ atTop atTop) :
    Tendsto (fun k => |binomBelow (N k) (alphaGt (Γ k) j (b k)) (C k) -
      cdf (gaussianReal 0 1) (pairRankThreshold (N k) (C k) (alphaGt (Γ k) j (b k)) (σ k))|)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_rank_nonuniform_normal_bound.{u}
  have ht : Tendsto (fun k => K / σ k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hσ
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ ht
  filter_upwards [hσ.eventually_gt_atTop 0] with k hk
  have hh := hbound (Γ k) (i k) j (b k) (σ k) hk (hv k)
  exact hh.trans (div_le_self (div_nonneg hK.le hk.le) (le_add_of_nonneg_right (by positivity)))

theorem rank_cdf_tendsto_normal
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b σ : ℕ → ℝ)
    (hv : ∀ k, (N k : ℝ) * alphaGt (Γ k) j (b k) * (1 - alphaGt (Γ k) j (b k)) = σ k ^ 2)
    (hσ : Tendsto σ atTop atTop) (x : ℝ)
    (hx : Tendsto (fun k => pairRankThreshold (N k) (C k) (alphaGt (Γ k) j (b k)) (σ k))
      atTop (𝓝 x)) :
    Tendsto (fun k => binomBelow (N k) (alphaGt (Γ k) j (b k)) (C k))
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have herr := rank_normal_error_tendsto_zero N C Γ i j b σ hv hσ
  have hd : Tendsto (fun k => binomBelow (N k) (alphaGt (Γ k) j (b k)) (C k) -
      cdf (gaussianReal 0 1) (pairRankThreshold (N k) (C k) (alphaGt (Γ k) j (b k)) (σ k)))
      atTop (𝓝 0) := by
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using herr)
  have hnormal := (show Continuous (fun x => cdf (gaussianReal 0 1) x) from continuous_Φ).tendsto x
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hd.add (hnormal.comp hx)

theorem rank_normal_error_uniformOn {Z : Type*}
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b σ : ℕ → Z → ℝ)
    (S : Set Z) (σmin : ℕ → ℝ)
    (hv : ∀ k, ∀ z ∈ S, (N k : ℝ) * alphaGt (Γ k) j (b k z) *
      (1 - alphaGt (Γ k) j (b k z)) = σ k z ^ 2)
    (hmin : ∀ᶠ k in atTop, ∀ z ∈ S, σmin k ≤ σ k z)
    (hσ : Tendsto σmin atTop atTop) :
    TendstoUniformlyOn (fun k z => binomBelow (N k) (alphaGt (Γ k) j (b k z)) (C k) -
      cdf (gaussianReal 0 1) (pairRankThreshold (N k) (C k)
        (alphaGt (Γ k) j (b k z)) (σ k z))) (fun _ => 0) atTop S := by
  obtain ⟨K, hK, hbound⟩ := exists_rank_nonuniform_normal_bound.{u}
  have ht : Tendsto (fun k => K / σmin k) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hσ
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hmin, hσ.eventually_gt_atTop 0,
    ht.eventually (eventually_lt_nhds hε)] with k hk hpos hsmall
  intro z hz
  rw [Real.dist_eq, zero_sub, abs_neg]
  have hzpos : 0 < σ k z := hpos.trans_le (hk z hz)
  have hh := hbound (Γ k) (i k) j (b k z) (σ k z) hzpos (hv k z hz)
  have he := hh.trans (div_le_self (div_nonneg hK.le hzpos.le)
    (le_add_of_nonneg_right (by positivity)))
  exact (he.trans (div_le_div_of_nonneg_left hK.le hpos (hk z hz))).trans_lt hsmall

theorem rank_cdf_uniformOn_normal {Z : Type*}
    (N C : ℕ → ℕ) (Γ : ∀ k, FiniteGame (N k + 1) n (C k) Seed)
    (i : ∀ k, Fin (N k + 1)) (j : Fin n) (b σ : ℕ → Z → ℝ)
    (S : Set Z) (σmin : ℕ → ℝ)
    (hv : ∀ k, ∀ z ∈ S, (N k : ℝ) * alphaGt (Γ k) j (b k z) *
      (1 - alphaGt (Γ k) j (b k z)) = σ k z ^ 2)
    (hmin : ∀ᶠ k in atTop, ∀ z ∈ S, σmin k ≤ σ k z)
    (hσ : Tendsto σmin atTop atTop) (x : Z → ℝ) (R : ℝ)
    (hxR : ∀ z ∈ S, |x z| ≤ R)
    (hx : TendstoUniformlyOn (fun k z => pairRankThreshold (N k) (C k)
      (alphaGt (Γ k) j (b k z)) (σ k z)) x atTop S) :
    TendstoUniformlyOn (fun k z => binomBelow (N k) (alphaGt (Γ k) j (b k z)) (C k))
      (fun z => cdf (gaussianReal 0 1) (x z)) atTop S := by
  have herr := rank_normal_error_uniformOn N C Γ i j b σ S σmin hv hmin hσ
  have hc : UniformContinuousOn (fun t : ℝ => cdf (gaussianReal 0 1) t)
      (Icc (-R - 1) (R + 1)) := isCompact_Icc.uniformContinuousOn_of_continuous continuous_Φ.continuousOn
  have hnear := Metric.tendstoUniformlyOn_iff.mp hx 1 (by norm_num)
  have hrange : ∀ᶠ k in atTop, ∀ z ∈ S, pairRankThreshold (N k) (C k)
      (alphaGt (Γ k) j (b k z)) (σ k z) ∈ Icc (-R - 1) (R + 1) := by
    filter_upwards [hnear] with k hk
    intro z hz
    have h1 := abs_le.mp (hxR z hz)
    have h2 := hk z hz
    rw [Real.dist_eq] at h2
    have h3 := abs_lt.mp h2
    constructor <;> linarith
  have hxr : ∀ z ∈ S, x z ∈ Icc (-R - 1) (R + 1) := by
    intro z hz
    have hh := abs_le.mp (hxR z hz)
    constructor <;> linarith
  have hnorm := UniformContinuousOn.comp_tendstoUniformlyOn_eventually hrange hxr hc hx
  simpa only [Pi.add_def, sub_add_cancel, zero_add] using herr.add hnorm

end FCAppendix.Bayes
