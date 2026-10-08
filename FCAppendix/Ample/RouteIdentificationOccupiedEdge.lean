import FCAppendix.Ample.RouteIdentificationRankLocalization

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped ENNReal BigOperators
open Ample Ample.DownstreamNormalizationCore

namespace RouteIdentificationDetails
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  {M C : ℕ → ℕ} {Γ : ∀ t, FiniteGame (M t) n (C t) Seed}

lemma localized_tail_at_edge {pi : ℕ → ℝ} {h : ℝ} {nu : ℕ → Measure ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j)
    (hmass : (∑ j ∈ Finset.Icc 1 n, pi j) = h)
    (hloc : ∀ j ∈ Finset.Icc 1 n,
      nu j = volume.restrict (Ioc (rankLowerEdge n j pi) (rankLowerEdge n j pi+pi j)))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) :
    ∀ j ∈ Finset.Icc 1 n,
      rankTail nu h (rankLowerEdge n k pi) j = prefixLaw pi k j := by
  intro j hj
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjn := (Finset.mem_Icc.mp hj).2
  have hk1 := (Finset.mem_Icc.mp hk).1
  obtain ⟨hLj, hLjj, hUj⟩ := edge_bounds hj hp hmass
  rw [rankTail, hloc j hj, measureReal_restrict_apply measurableSet_Ioc]
  by_cases hjk : j ≤ k
  · have horder : rankLowerEdge n k pi ≤ rankLowerEdge n j pi :=
      suffix_mono hp (by omega) (by omega)
    have hsub : Ioc (rankLowerEdge n j pi) (rankLowerEdge n j pi+pi j) ⊆
        Ioc (rankLowerEdge n k pi) h :=
      fun _ hx => ⟨horder.trans_lt hx.1, hx.2.trans hUj⟩
    rw [inter_eq_right.mpr hsub, interval_volume_real hLjj]
    simp only [prefixLaw, hjk, if_true]
    ring
  · have hkj : k+1 ≤ j := by omega
    have horder : rankLowerEdge n j pi+pi j ≤ rankLowerEdge n k pi := by
      rw [add_comm, rankLowerEdge, ← sum_Icc_head hjn]
      exact suffix_mono hp (by omega) hkj
    have hempty : Ioc (rankLowerEdge n k pi) h ∩
        Ioc (rankLowerEdge n j pi) (rankLowerEdge n j pi+pi j) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact (not_lt_of_ge (hu.2.2.trans horder)) hu.1.1
    rw [hempty, measureReal_empty]
    simp only [prefixLaw, hjk, if_false]

lemma rankTail_valid {pi : ℕ → ℝ} {h : ℝ} {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi h nu) (hmass : (∑ j ∈ Finset.Icc 1 n, pi j) = h)
    (hh : h ≤ 1) (u : ℝ) : ValidLaw n (rankTail nu h u) := by
  refine ⟨fun _ _ => measureReal_nonneg, ?_⟩
  calc
    (∑ j ∈ Finset.Icc 1 n, rankTail nu h u j) ≤ ∑ j ∈ Finset.Icc 1 n, pi j := by
      apply Finset.sum_le_sum
      intro j hj
      letI : IsFiniteMeasure (nu j) := interval_dom_finite (hr.dominated j hj)
      rw [← hr.mass j hj]
      exact measureReal_mono (subset_univ _)
    _ = h := hmass
    _ ≤ 1 := hh

lemma dominated_atom_zero {μ : Measure ℝ} {h : ℝ}
    (hd : μ ≤ volume.restrict (Ioc 0 h)) (u : ℝ) : μ {u} = 0 := by
  have hle : μ {u} ≤ (volume : Measure ℝ) {u} :=
    (Measure.le_iff'.mp hd {u}).trans (Measure.le_iff'.mp Measure.restrict_le_self {u})
  exact le_antisymm (by simpa only [measure_singleton] using hle) bot_le

lemma rankTail_continuous {pi : ℕ → ℝ} {h : ℝ} {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi h nu) {j : ℕ} (hj : j ∈ Finset.Icc 1 n) :
    Continuous (fun u => rankTail nu h u j) := by
  letI : IsFiniteMeasure (nu j) := interval_dom_finite (hr.dominated j hj)
  have he (u : ℝ) : rankTail nu h u j = (nu j).real (Ioi u) := by
    apply measureReal_congr
    filter_upwards [interval_dom_support (hr.dominated j hj)] with x hx
    apply propext
    exact ⟨fun hxu => hxu.1, fun hxu => ⟨hxu, hx.2⟩⟩
  rw [show (fun u => rankTail nu h u j) = (fun u => (nu j).real (Ioi u)) from funext he]
  exact continuous_iff_continuousAt.mpr fun u =>
    continuousAt_real_tail_of_no_atom (nu j) u (dominated_atom_zero (hr.dominated j hj) u)

theorem occupied_edge_rate_ge {pi : ℕ → ℝ} {h rho J : ℝ} {nu : ℕ → Measure ℝ}
    (hr : RankLimit Γ pi h nu)
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ pi j)
    (hmass : (∑ j ∈ Finset.Icc 1 n, pi j) = h) (hh : h ≤ 1)
    (hmean : contactMarginal n pi < rho) (hrho : rho < 1)
    (hloc : ∀ j ∈ Finset.Icc 1 n,
      nu j = volume.restrict (Ioc (rankLowerEdge n j pi) (rankLowerEdge n j pi+pi j)))
    {k : ℕ} (hk : k ∈ Finset.Icc 1 n) (hpk : 0 < pi k)
    (hused : ∀ᵐ u ∂nu k, J ≤ rivalRate n rho k (rankTail nu h u)) :
    J ≤ prefixRate n rho k pi := by
  have hk1 := (Finset.mem_Icc.mp hk).1
  have hkn := (Finset.mem_Icc.mp hk).2
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpvalid : ValidLaw n pi := ⟨hp, hmass.le.trans hh⟩
  have hpref := prefixLaw_valid hpvalid k
  have hslack : contactMarginal n (prefixLaw pi k) < rho :=
    (prefixLaw_marginal_le hp k).trans_lt hmean
  have htop : ∃ j ∈ Finset.Icc 1 n, 0 < prefixLaw pi k j ∧
      (k : ℝ)*rho < (min k j : ℕ) := by
    refine ⟨k, hk, by simpa [prefixLaw] using hpk, ?_⟩
    simpa only [min_self, mul_one] using mul_lt_mul_of_pos_left hrho hkR
  let L := rankLowerEdge n k pi
  have hedge := localized_tail_at_edge hp hmass hloc hk
  have hconv : ∀ j ∈ Finset.Icc 1 n,
      Tendsto (fun u => rankTail nu h u j) (𝓝 L) (𝓝 (prefixLaw pi k j)) := by
    intro j hj
    have hc : Tendsto (fun u => rankTail nu h u j) (𝓝 L)
        (𝓝 (rankTail nu h L j)) :=
      (rankTail_continuous hr hj).continuousAt.tendsto
    rwa [hedge j hj] at hc
  have hrate : Tendsto (fun u => rivalRate n rho k (rankTail nu h u))
      (𝓝 L) (𝓝 (prefixRate n rho k pi)) := by
    have hh' := rivalRate_tendsto hk1 hkn (rankTail_valid hr hmass hh) hpref hconv
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => rho) (𝓝 L) (𝓝 rho)) hslack htop
    rw [prefixRate_eq_rivalRate hkn]
    exact hh'
  by_contra hnot
  have hlt : prefixRate n rho k pi < J := lt_of_not_ge hnot
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hrate.eventually_lt_const hlt)
  let d : ℝ := min (ε/2) (pi k/2)
  have hd : 0 < d := lt_min (half_pos hε) (half_pos hpk)
  have hdε : d < ε := (min_le_left _ _).trans_lt (by linarith)
  have hdp : d ≤ pi k := (min_le_right _ _).trans (by linarith)
  let I : Set ℝ := Ioc L (L+d)
  have hsub : I ⊆ {u | ¬ J ≤ rivalRate n rho k (rankTail nu h u)} := by
    intro u hu hge
    have hdist : dist u L < ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu.1.le)]
      linarith [hu.2]
    exact (not_le_of_gt (hb (Metric.mem_ball.mpr hdist))) hge
  have hnull : (nu k) I = 0 := measure_mono_null hsub (ae_iff.mp hused)
  have hIL : I ⊆ Ioc (rankLowerEdge n k pi) (rankLowerEdge n k pi+pi k) := by
    intro u hu
    exact ⟨hu.1, hu.2.trans (add_le_add (le_refl L) hdp)⟩
  have hmassI : (nu k).real I = d := by
    rw [hloc k hk, measureReal_restrict_apply (show MeasurableSet I from measurableSet_Ioc),
      inter_eq_left.mpr hIL, interval_volume_real (show L ≤ L+d from le_add_of_nonneg_right hd.le)]
    ring
  have : (nu k).real I = 0 := by simp only [Measure.real, hnull, ENNReal.toReal_zero]
  linarith

end RouteIdentificationDetails
end FCAppendix.Bayes
