import FCAppendix.PayOnce.BidFormula

namespace FCAppendix.PayOnce.Limit
open MeasureTheory Set Filter Topology

theorem pStar_max_zero (n : ℕ) (L w : ℝ) :
    pStar n L (max w 0) = pStar n L w := by
  by_cases hw : 0 ≤ w
  · rw [max_eq_left hw]
  · rw [max_eq_right (le_of_not_ge hw),pStar_of_nonpos le_rfl,
      pStar_of_nonpos (le_of_not_ge hw)]

theorem bidStar_max_zero (n : ℕ) {L : ℝ} (hL : 0 ≤ L) (w : ℝ) :
    bidStar n L (max w 0) = bidStar n L w := by
  by_cases hw : 0 ≤ w
  · rw [max_eq_left hw]
  · have hw0 : w ≤ 0 := le_of_not_ge hw
    rw [max_eq_right hw0,bidStar_of_le hL,bidStar_of_le (hw0.trans hL),
      max_eq_right hw0,max_self]

theorem demand_map_max_sub_eq (F : Measure ℝ) (g : ℝ) (n : ℕ) (L : ℝ) :
    demand (F.map (fun v => max (v-g) 0)) n L =
      demand (F.map (fun v => v-g)) n L := by
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  have hraw : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  unfold demand
  rw [integral_map hnet.aemeasurable
      (measurable_pStar n L).aestronglyMeasurable,
    integral_map hraw.aemeasurable
      (measurable_pStar n L).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => pStar_max_zero n L (v-g))

theorem coverage_map_max_sub_eq (F : Measure ℝ) (g : ℝ) (n : ℕ) (L : ℝ) :
    coverage (F.map (fun v => max (v-g) 0)) n L =
      coverage (F.map (fun v => v-g)) n L := by
  have hm := (continuous_success n).measurable.comp (measurable_pStar n L)
  change Measurable (fun w : ℝ => success n (pStar n L w)) at hm
  have hnet : Measurable (fun v : ℝ => max (v-g) 0) :=
    (measurable_id.sub_const g).max measurable_const
  have hraw : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  unfold coverage
  rw [integral_map hnet.aemeasurable
      hm.aestronglyMeasurable,
    integral_map hraw.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => congrArg (success n) (pStar_max_zero n L (v-g))

theorem capRoot_map_max_sub_eq (F : Measure ℝ) (g : ℝ) (n : ℕ) (ρ : ℝ) :
    capRoot (F.map (fun v => max (v-g) 0)) n ρ =
      capRoot (F.map (fun v => v-g)) n ρ := by
  have hd : demand (F.map (fun v => max (v-g) 0)) n = demand (F.map (fun v => v-g)) n :=
    funext fun L => demand_map_max_sub_eq F g n L
  unfold capRoot
  rw [hd]

theorem pStar_sub_eq_source (n : ℕ) (L g v : ℝ) :
    pStar n L (v-g) =
      max 0 (1-(L/(v-g))^(1/((n:ℝ)-1)))*(Ioi g).indicator (fun _ => (1:ℝ)) v := by
  by_cases hv : g < v
  · rw [pStar_of_pos (sub_pos.mpr hv),indicator_of_mem (show v ∈ Ioi g from hv),mul_one]
  · rw [pStar_of_nonpos (sub_nonpos.mpr (le_of_not_gt hv)),
      indicator_of_notMem (show v ∉ Ioi g from hv),mul_zero]

theorem demand_map_max_sub_eq_source (F : Measure ℝ) (g : ℝ) (n : ℕ) (L : ℝ) :
    demand (F.map (fun v => max (v-g) 0)) n L =
      ∫ v, max 0 (1-(L/(v-g))^(1/((n:ℝ)-1)))*(Ioi g).indicator (fun _ => (1:ℝ)) v ∂F := by
  have hraw : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  rw [demand_map_max_sub_eq]
  unfold demand
  rw [integral_map hraw.aemeasurable
    (measurable_pStar n L).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => pStar_sub_eq_source n L g v)

theorem bidStar_eq_self_of_nonneg_le {n : ℕ} {L w : ℝ} (hw : 0 ≤ w) (hwt : w ≤ L) :
    bidStar n L w = w := by
  rw [bidStar_of_le hwt,max_eq_left hw]

theorem bidStar_eq_zero_of_nonpos {n : ℕ} {L w : ℝ} (hL : 0 ≤ L) (hw : w ≤ 0) :
    bidStar n L w = 0 := by
  rw [bidStar_of_le (hw.trans hL),max_eq_right hw]

theorem bidStar_eq_source_of_lt {n : ℕ} (hn : 2 ≤ n) {L w : ℝ}
    (hL : 0 ≤ L) (hw : L < w) :
    bidStar n L w = L*(n:ℝ)*pStar n L w/(1-(1-pStar n L w)^n) := by
  have hp : 0 < pStar n L w := (pStar_pos_iff hn hL).mpr hw
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hH : H n (pStar n L w) ≠ 0 :=
    (H_pos n (by omega) _ hp.le (pStar_le_one hL)).ne'
  change bidStar n L w = L*(n:ℝ)*pStar n L w/success n (pStar n L w)
  rw [bidStar_of_lt hw,← H_mul n (by omega)]
  field_simp [hp.ne',hn0,hH]

theorem nonnegative_bids_not_tendsto_negative (b : ℕ → ℝ) (hb : ∀ t, 0 ≤ b t)
    {w : ℝ} (hw : w < 0) : ¬ Tendsto b atTop (𝓝 w) := by
  intro h
  exact hw.not_ge (ge_of_tendsto h (Eventually.of_forall hb))

end FCAppendix.PayOnce.Limit
