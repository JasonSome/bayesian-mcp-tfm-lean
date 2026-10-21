import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Menu
import FCAppendix.Affine.Uniform06.SourceRankOutput
import FCAppendix.Affine.Uniform06.EarlyRankCeiling

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open FCAppendix.Affine Uniform07
open Uniform06 Uniform06.PureRankCounts Uniform06.SourcePrefixConstructor

theorem eventually_received_sort_active (row : Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀ᵐp∂(Received05.G row m E:Measure (ℝ×ℝ)),
        p.1∈Icc (SourcePrefixConstructor.sortEnd row) (cutoff row)→
          |p.2-ActiveGraphComponent.activeBid row p.1|≤ SourcePrefixConstructor.activeError row := by
  have ht:=cutoff_pos row
  have hactive:=SourceEarlyFamily.source_early_active_closed
    (Received05.G row) (Received05.g row) (Received05.cm row) row (Received05.earlyMenu row)
    (cutoff row/20000) (by positivity)
    (SourcePrefixConstructor.activeError row) (by unfold SourcePrefixConstructor.activeError; positivity)
  filter_upwards [hactive] with m hm E
  filter_upwards [hm E] with p hp hv
  exact (hp (by simpa only [SourcePrefixConstructor.sortEnd] using hv)).le

theorem eventually_received_local_used_rank (row : Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀ᵐp∂(Received05.G row m E:Measure (ℝ×ℝ)),
        p.2≤ SourcePrefixConstructor.extensionEnd row→
          sourceRank (cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) p.2=p.1 := by
  let O:=SourceRankOutput.from_early_source
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.atoms row)
    (Received05.roots row).literal (Received05.roots row).rejection
  obtain ⟨hH,_,hHZ,hZK,_,_,_,hgap,_,_⟩:=SourcePrefixConstructor.band_geometry row
  have hK : 0< SourcePrefixConstructor.sortEnd row:=(hH.trans hHZ).trans_le hZK
  filter_upwards [O.used_rank,eventually_received_sort_active row] with m hrank hactive E
  have hexclude:=CrossoverRankPreparation.active_exclusion row
    (Received05.G row m E:Measure (ℝ×ℝ)) (Received05.value row m E) hK hgap (hactive E)
  filter_upwards [hrank E,hexclude] with p hp hx hb
  exact hp (hx hb)

theorem eventually_received_prefix_rank_ceiling (row : Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀b : ℝ,b≤ EarlyRankCeiling.prefixEnd row→
        sourceRank (cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) b<
          RankCutoff.Mstar row := by
  have ht:=cutoff_pos row
  have ha : 0< EarlyRankCeiling.ceilingValue row-entry row :=
    sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds row).1.1
  have hactive:=SourceEarlyFamily.source_early_active
    (Received05.G row) (Received05.g row) (Received05.cm row) row (Received05.earlyMenu row)
    (EarlyRankCeiling.ceilingValue row-entry row) ha (cutoff row/10000) (by positivity)
  filter_upwards [hactive] with m hm E
  have hA : ∀ᵐp∂(Received05.G row m E:Measure (ℝ×ℝ)),
      p.1∈Ioc (EarlyRankCeiling.ceilingValue row) (cutoff row)→
        |p.2-ActiveGraphComponent.activeBid row p.1|≤ cutoff row/10000 := by
    filter_upwards [hm E] with p hp hv
    exact hp ⟨by linarith [hv.1],hv.2⟩
  exact EarlyRankCeiling.source_early_rank_ceiling row
    (Received05.G row m E:Measure (ℝ×ℝ)) (Received05.value row m E) hA

theorem eventually_received_crossover_rank_ceiling (row : Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀b : ℝ,b≤ SourcePrefixConstructor.crossoverEnd row→
        sourceRank (cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) b≤
          RankCutoff.Mstar row := by
  have hH : SourcePrefixConstructor.crossoverEnd row≤ EarlyRankCeiling.prefixEnd row := by
    have ht:=cutoff_pos row
    unfold SourcePrefixConstructor.crossoverEnd EarlyRankCeiling.prefixEnd
    linarith
  filter_upwards [eventually_received_prefix_rank_ceiling row] with m hm E b hb
  exact (hm E b (hb.trans hH)).le

theorem rank_bounds_of_uniform_value_no_overbid (row : Row)
    (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw row)
    (hno : ∀ᵐp∂G,p.2≤ p.1) {b : ℝ} (hb : b∈Icc (0:ℝ) (cutoff row)) :
    b≤ sourceRank (cutoff row) (G.map Prod.snd) b ∧
      sourceRank (cutoff row) (G.map Prod.snd) b≤ cutoff row := by
  letI : IsProbabilityMeasure (G.map Prod.snd):=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hsub : {p : ℝ×ℝ | p.1≤ b}≤ᵐ[G]{p | p.2≤ b} := by
    filter_upwards [hno] with p hp hv
    exact hp.trans hv
  have hmass : (G.map Prod.fst).real (Iic b)≤(G.map Prod.snd).real (Iic b) := by
    rw [measureReal_def,Measure.map_apply measurable_fst measurableSet_Iic,
      measureReal_def,Measure.map_apply measurable_snd measurableSet_Iic]
    exact ENNReal.toReal_mono (measure_ne_top G _) (measure_mono_ae hsub)
  have hscaled:=mul_le_mul_of_nonneg_left hmass (cutoff_pos row).le
  rw [hvalue,EarlyRankCeiling.conditional_value_scaled_cdf row hb] at hscaled
  refine ⟨hscaled,?_⟩
  change cutoff row*(G.map Prod.snd).real (Iic b)≤ cutoff row
  exact mul_le_of_le_one_right (cutoff_pos row).le measureReal_le_one

theorem received_rank_bounds (row : Row) (m : ℕ) (E : Received05.ReadyLaw row m)
    {b : ℝ} (hb : b∈Icc (0:ℝ) (cutoff row)) :
    b≤ sourceRank (cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) b ∧
      sourceRank (cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) b≤ cutoff row :=
  rank_bounds_of_uniform_value_no_overbid row (Received05.G row m E:Measure (ℝ×ℝ))
    (Received05.value row m E)
    ((Received05.permitted row m E).mono (fun _ hp=>hp.2.trans (min_le_left _ _))) hb

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
