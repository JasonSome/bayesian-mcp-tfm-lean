import FCAppendix.Finite.PPIVisibleRanks

namespace FCAppendix.PayOnce.GoodQuantileSelection
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem exists_at_tail (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    {g q : ℝ} (hactive : ∀ᵐ v ∂F, g < v) (hq : q ∈ Ioo (0:ℝ) 1) :
    ∃ v : ℝ, F.real (Ioi v) = q := by
  have hg : F (Ioi g) = 1 := by
    rw [← measure_univ (μ := F)]
    apply measure_congr
    filter_upwards [hactive] with v hv
    exact propext ⟨fun _ => trivial, fun _ => hv⟩
  have hgR : F.real (Ioi g) = 1 := by simp only [measureReal_def, hg, ENNReal.toReal_one]
  obtain ⟨R, hgR', hR⟩ := ((eventually_ge_atTop g).and
    ((TailQuantile.tail_tendsto_zero F).eventually_lt_const hq.1)).exists
  have hcont : Continuous (fun v => F.real (Ioi v)) := continuous_iff_continuousAt.mpr fun v =>
    Bayes.continuousAt_real_tail_of_no_atom F v (measure_singleton v)
  obtain ⟨v, _, hv⟩ := intermediate_value_Icc' hgR' hcont.continuousOn
    (show q ∈ Icc (F.real (Ioi R)) (F.real (Ioi g)) from ⟨hR.le, by rw [hgR]; exact hq.2.le⟩)
  exact ⟨v, hv⟩

theorem exists_good_tail_between (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    {g : ℝ} (hactive : ∀ᵐ v ∂F, g < v) (Good : ℝ → Prop) (hgood : ∀ᵐ v ∂F, Good v)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l < u) (hu : u ≤ 1) :
    ∃ v : ℝ, Good v ∧ g < v ∧ l < F.real (Ioi v) ∧ F.real (Ioi v) < u := by
  let p := (2*l+u)/3
  let r := (l+2*u)/3
  have hp : 0 < p ∧ l < p ∧ p < r ∧ r < u ∧ r < 1 := by dsimp [p, r]; and_intros <;> linarith
  obtain ⟨L, hL⟩ := exists_at_tail F hactive (show r ∈ Ioo (0:ℝ) 1 from ⟨hp.1.trans hp.2.2.1, hp.2.2.2.2⟩)
  obtain ⟨R, hR⟩ := exists_at_tail F hactive (show p ∈ Ioo (0:ℝ) 1 from ⟨hp.1, hp.2.2.1.trans hp.2.2.2.2⟩)
  have hLR : L < R := by
    by_contra hn
    have hh := measureReal_mono (μ := F) (Ioi_subset_Ioi (le_of_not_gt hn))
    rw [hL, hR] at hh
    exact hp.2.2.1.not_ge hh
  have hmassR : 0 < F.real (Ioc L R) := by
    rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi hLR.le) measurableSet_Ioi, hL, hR]
    exact sub_pos.mpr hp.2.2.1
  have hmass : F (Ioc L R) ≠ 0 := by
    intro hz
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hmassR
  have hfreq : ∃ᵐ v ∂F, v ∈ Ioc L R := frequently_ae_iff.mpr hmass
  obtain ⟨v, hv, hG, hg⟩ := (hfreq.and_eventually (hgood.and hactive)).exists
  refine ⟨v, hG, hg, ?_, ?_⟩
  · exact hp.2.1.trans_le (hR ▸ measureReal_mono (μ := F) (Ioi_subset_Ioi hv.2))
  · exact (measureReal_mono (μ := F) (Ioi_subset_Ioi hv.1.le)).trans_lt (hL ▸ hp.2.2.2.1)

theorem exists_four_good_quantiles (F : Measure ℝ) [IsProbabilityMeasure F] [NullSingletonClass F]
    {g q : ℝ} (hactive : ∀ᵐ v ∂F, g < v) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (Good : ℝ → Prop) (hgood : ∀ᵐ v ∂F, Good v) :
    ∃ a x y b : ℝ, Good a ∧ Good x ∧ Good y ∧ Good b ∧
      g < a ∧ a < x ∧ x < y ∧ y < b ∧
      0 < F (Icc a x) ∧ 0 < F (Ioc x y) ∧ 0 < F (Icc y b) ∧
      0 < F (Iic y) ∧ q < F.real (Ioi b) := by
  obtain ⟨b, hbG, hgb, hqb, hb1⟩ := exists_good_tail_between F hactive Good hgood hq0 hq1 le_rfl
  obtain ⟨y, hyG, hgy, hby, hy1⟩ := exists_good_tail_between F hactive Good hgood
    (hq0.trans hqb.le) hb1 le_rfl
  obtain ⟨x, hxG, hgx, hyx, hx1⟩ := exists_good_tail_between F hactive Good hgood
    ((hq0.trans hqb.le).trans hby.le) hy1 le_rfl
  obtain ⟨a, haG, hga, hxa, _⟩ := exists_good_tail_between F hactive Good hgood
    (((hq0.trans hqb.le).trans hby.le).trans hyx.le) hx1 le_rfl
  have horder {v w : ℝ} (h : F.real (Ioi w) < F.real (Ioi v)) : v < w := by
    by_contra hn
    exact h.not_ge (measureReal_mono (Ioi_subset_Ioi (le_of_not_gt hn)))
  have hgap {v w : ℝ} (h : F.real (Ioi w) < F.real (Ioi v)) : 0 < F (Ioc v w) := by
    have hr : 0 < F.real (Ioc v w) := by
      rw [← Ioi_sdiff_Ioi, measureReal_sdiff (Ioi_subset_Ioi (horder h).le) measurableSet_Ioi]
      exact sub_pos.mpr h
    exact pos_iff_ne_zero.mpr fun hz => by simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hr
  refine ⟨a, x, y, b, haG, hxG, hyG, hbG, hga, horder hxa, horder hyx, horder hby,
    (hgap hxa).trans_le (measure_mono Ioc_subset_Icc_self), hgap hyx,
    (hgap hby).trans_le (measure_mono Ioc_subset_Icc_self), ?_, hqb⟩
  have hr : 0 < F.real (Iic y) := by
    rw [← compl_Ioi, probReal_compl_eq_one_sub measurableSet_Ioi]
    exact sub_pos.mpr hy1
  exact pos_iff_ne_zero.mpr fun hz => by simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hr

end FCAppendix.PayOnce.GoodQuantileSelection
