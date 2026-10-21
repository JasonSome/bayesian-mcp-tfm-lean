import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Regularity
import FCAppendix.Affine.Uniform06.LiteralStieltjesIC

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment
open Uniform06.LowRankMeasures Uniform06.SourceSharpDensityConstants
open Uniform06.PrimitiveStieltjesMeasures Uniform06.LiteralPureComponents
open Uniform06.LiteralPrefixStieltjes Uniform06.PureRankCounts
open Uniform06.WeightedBorelContraction Uniform06.ICAbsorption Uniform06.RankDensityRepresentative

def lowRankConstant (row : Uniform07.Row) : ℝ :=
  2*densityConstant row*(1+1/(Uniform07.kappa row*Physical.sourceCrossoverStart row))

theorem lowRankConstant_nonnegative (row : Uniform07.Row) : 0≤ lowRankConstant row := by
  have hC:=densityConstant_pos row
  have hL:=(source_crossover_geometry row).1
  have hκ : 0< Uniform07.kappa row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  unfold lowRankConstant
  positivity

theorem contracted_crossover_geometry (row : Uniform07.Row) :
    0< Uniform07.kappa row ∧ Uniform07.kappa row≤ 1 ∧
    Uniform07.kappa row*SourcePrefixConstructor.crossoverEnd row< lowEnd row := by
  have ht:=Uniform07.cutoff_pos row
  have hκ : 0< Uniform07.kappa row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  have hκ1 : Uniform07.kappa row≤ 1 := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  have hq : Uniform07.kappa row*(Uniform07.x row+1/160000)<(1/2:ℝ) := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,
      Uniform07.etaQ,Uniform07.x,Uniform07.xQ]
  have hh:=mul_lt_mul_of_pos_right hq ht
  refine ⟨hκ,hκ1,?_⟩
  unfold SourcePrefixConstructor.crossoverEnd Uniform07.entry lowEnd
  nlinarith

theorem eventually_received_low_density (row : Uniform07.Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀lo : ℝ,0< lo→∀A : Set ℝ,MeasurableSet A→ A⊆Icc lo (lowEnd row)→
      (lowBidMeasure row (Received05.G row m E) (lowEnd row)).real A≤
        densityConstant row*(volume.real A/(1-scaledCoefficient row m*Uniform07.kappa row)+
          (∫ b in A,1/((m:ℝ)*b))/(1-scaledCoefficient row m)) := by
  have ht:=Uniform07.cutoff_pos row
  have hp:=SourceEarlyFamily.eventually_source_prefix
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.roots row).literal (Received05.roots row).rejection
  have ha:=SourceEarlyFamily.source_early_active_closed
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Uniform07.cutoff row/20000) (by positivity)
    (Uniform07.cutoff row/10000) (by positivity)
  have hK : Uniform07.entry row< SourcePrefixConstructor.sortEnd row := by
    unfold SourcePrefixConstructor.sortEnd
    linarith
  have hKM : SourcePrefixConstructor.sortEnd row< RankCutoff.Mstar row := by
    unfold SourcePrefixConstructor.sortEnd RankCutoff.Mstar Uniform07.entry
    nlinarith
  have hKfloor : SourcePrefixConstructor.sortEnd row≤ Uniform07.entry row+Uniform07.cutoff row/400 := by
    unfold SourcePrefixConstructor.sortEnd
    linarith
  filter_upwards [LiteralRankDensity.eventually_source_low_rank_density row,hp,ha]
    with m hm hp ha E
  have hactive : ∀ᵐp∂(Received05.G row m E : Measure (ℝ×ℝ)),
      p.1∈Icc (SourcePrefixConstructor.sortEnd row) (Uniform07.cutoff row)→
      |p.2-ActiveGraphComponent.activeBid row p.1|≤ Uniform07.cutoff row/10000 := by
    filter_upwards [ha E] with p hp hv
    exact (hp hv).le
  exact (hm (Received05.G row m E) inferInstance (Received05.value row m E)
    (Received05.permitted row m E) (Received05.atoms row m E) (Received05.g row m E)
    (SourcePrefixConstructor.sortEnd row) (Received05.cm row m E) (hp E).2.1
    hK hKM hKfloor (hp E).2.2 hactive (Received05.all_action_IC row m E)).2

theorem geometricBound_uniform {κ ε C m lo : ℝ}
    (_hκ0 : 0≤κ) (hκ1 : κ≤ 1) (hε0 : 0≤ε) (hε : ε≤ 1/2)
    (hC : 0≤ C) (hm : 1≤ m) (hlo : 0< lo) :
    geometricBound κ ε C m lo≤ 2*C*(1+1/lo) := by
  have hεκ : ε*κ≤ 1/2 := (mul_le_mul_of_nonneg_left hκ1 hε0).trans (by simpa using hε)
  have hden1 : 0<1-ε*κ := by linarith
  have hden2 : 0<1-ε := by linarith
  have hfirst : 1/(1-ε*κ)≤ 2 := (div_le_iff₀ hden1).mpr (by linarith)
  have hprod : lo/2≤(1-ε)*m*lo := by
    have hbase : (1/2:ℝ)≤(1-ε)*m := by
      have hmul:=mul_le_mul_of_nonneg_left hm hden2.le
      linarith
    have hh:=mul_le_mul_of_nonneg_right hbase hlo.le
    nlinarith
  have hsecond : 1/((1-ε)*m*lo)≤ 2/lo := by
    have hh:=div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤ 1) (half_pos hlo) hprod
    calc
      _ ≤ 1/(lo/2) := hh
      _ = _ := by field_simp
  rw [RankDensityRepresentative.geometricBound_eq]
  have hbound:=mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hC
  calc
    _ ≤ C*(2+2/lo) := hbound
    _ = _ := by ring

theorem eventually_received_contracted_rank (row : Uniform07.Row) :
    ∀ᶠ m in atTop,∀E : Received05.ReadyLaw row m,
      ∀x∈Icc (Physical.sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row),
      ∀y∈Icc (Physical.sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row),
      x≤ y→
      sourceRank (Uniform07.cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd)
          (Uniform07.kappa row*y)-
        sourceRank (Uniform07.cutoff row) ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd)
          (Uniform07.kappa row*x)≤ lowRankConstant row*(y-x) := by
  have hsmall : ∀ᶠm in atTop,scaledCoefficient row m≤ 1/2 :=
    (scaledCoefficient_tendsto_zero row).eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [eventually_received_low_density row,eventually_sharp_absorption_small row,
    hsmall,eventually_ge_atTop (1:ℕ)] with m hden hsmall hhalf hm E x hx y hy hxy
  let μ:=lowBidMeasure row (Received05.G row m E) (lowEnd row)
  let κ:=Uniform07.kappa row
  let L:=Physical.sourceCrossoverStart row
  let C:=densityConstant row
  have hgeo:=contracted_crossover_geometry row
  have hκ : 0<κ:=hgeo.1
  have hκ1 : κ≤ 1:=hgeo.2.1
  have hL : 0< L:=(source_crossover_geometry row).1
  have hMr : (1:ℝ)≤ m := by exact_mod_cast hm
  have hM0 : (0:ℝ)< m := lt_of_lt_of_le zero_lt_one hMr
  have hεκ : scaledCoefficient row m*κ<1 := by
    have hh:=mul_le_mul_of_nonneg_left hκ1 hsmall.1
    linarith [hsmall.2.1]
  have hκxy : κ*x≤κ*y := mul_le_mul_of_nonneg_left hxy hκ.le
  have hbound:=LiteralStieltjesIC.compact_rank_interval_bound μ hM0 (mul_pos hκ hL)
    (densityConstant_pos row).le hsmall.2.1 hεκ (hden E)
    (mul_le_mul_of_nonneg_left hx.1 hκ.le) hκxy
    ((mul_le_mul_of_nonneg_left hy.2 hκ.le).trans hgeo.2.2.le)
  have hK:=geometricBound_uniform hκ.le hκ1 hsmall.1 hhalf
    (densityConstant_pos row).le hMr (mul_pos hκ hL)
  have h0 : 0≤ 2*C*(1+1/(κ*L)) := by
    have hc:=densityConstant_pos row
    dsimp [C]
    positivity
  have hinc : sourceRank (Uniform07.cutoff row)
        ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) (κ*y)-
      sourceRank (Uniform07.cutoff row)
        ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd) (κ*x)=μ.real (Ioc (κ*x) (κ*y)) := by
    rw [SharpPureDerivative.rank_increment _ hκxy]
    have hsub : Ioc (κ*x) (κ*y)⊆Ioc (0:ℝ) (lowEnd row) := fun b hb=>
      ⟨(mul_pos hκ (hL.trans_le hx.1)).trans hb.1,
        hb.2.trans ((mul_le_mul_of_nonneg_left hy.2 hκ.le).trans hgeo.2.2.le)⟩
    rw [show μ.real (Ioc (κ*x) (κ*y))=(bidMeasure row (Received05.G row m E)).real
      (Ioc (κ*x) (κ*y)) by
        simp only [μ,lowBidMeasure,Measure.real,Measure.restrict_apply measurableSet_Ioc,
          inter_eq_left.mpr hsub],bidMeasure_real]
  rw [hinc]
  calc
    μ.real (Ioc (κ*x) (κ*y))≤ _:=hbound
    _≤(2*C*(1+1/(κ*L)))*(κ*y-κ*x):=
      mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hκxy)
    _≤ lowRankConstant row*(y-x) := by
      have hh:=mul_le_mul_of_nonneg_left hκ1 (sub_nonneg.mpr hxy)
      have hh':κ*y-κ*x≤ y-x := by nlinarith
      exact mul_le_mul_of_nonneg_left hh' h0

theorem pure_duplicate_increment_of_contracted_rank
    (row : Uniform07.Row) (m : ℕ) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (cm : (Fin (m-1)→ Fin 4)→ℝ) {L H K : ℝ}
    (P : PrimitiveStieltjesBounds row m G g cm L H) (hK : 0≤ K)
    (hscaled : ∀x∈Icc L H,∀y∈Icc L H,x≤ y→
      sourceRank (Uniform07.cutoff row) (G.map Prod.snd) (Uniform07.kappa row*y)-
      sourceRank (Uniform07.cutoff row) (G.map Prod.snd) (Uniform07.kappa row*x)≤ K*(y-x)) :
    ∀x∈Icc L H,∀y∈Icc L H,x≤ y→
      0≤ sourcePureDuplicate row m G y-sourcePureDuplicate row m G x ∧
      sourcePureDuplicate row m G y-sourcePureDuplicate row m G x≤
        (m:ℝ)*LiteralLowDuplicate.pureRare m*
          (sourceRank (Uniform07.cutoff row) (G.map Prod.snd) y-
            sourceRank (Uniform07.cutoff row) (G.map Prod.snd) x+K*(y-x)) := by
  letI : IsFiniteMeasure P.pureDuplicate.measure:=CompactStieltjes.finite_of_bounds
    P.pureDuplicate P.duplicate_bounds
  intro x hx y hy hxy
  have hsub : Ioc x y⊆Ioc L H:=fun z hz=>⟨hx.1.trans_lt hz.1,hz.2.trans hy.2⟩
  have hmeasure:=ENNReal.toReal_mono (measure_ne_top _ _)
    (P.pure_upper (Ioc x y))
  simp only [Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub] at hmeasure
  change P.pureDuplicate.measure.real (Ioc x y)≤(pureComparison row m G).real (Ioc x y) at hmeasure
  rw [CompactStieltjes.measure_real_Ioc P.pureDuplicate hxy,
    P.duplicate_agrees y hy,P.duplicate_agrees x hx,pureComparison_interval] at hmeasure
  have hκ : 0< Uniform07.kappa row:=(contracted_crossover_geometry row).1
  rw [←SharpPureDerivative.rank_increment (G.map Prod.snd) hxy,
    ←SharpPureDerivative.rank_increment (G.map Prod.snd)
      (mul_le_mul_of_nonneg_left hxy hκ.le)] at hmeasure
  have hmono:=SharpPureDerivative.monotone_rank (Uniform07.cutoff_pos row).le (G.map Prod.snd)
  have hd : 0≤ sourcePureDuplicate row m G y-sourcePureDuplicate row m G x := by
    rw [←P.duplicate_agrees y hy,←P.duplicate_agrees x hx]
    exact sub_nonneg.mpr (P.pureDuplicate.mono hxy)
  have hS:=hscaled x hx y hy hxy
  have hr : 0≤ LiteralLowDuplicate.pureRare m := by unfold LiteralLowDuplicate.pureRare; positivity
  have hM : 0≤ sourceRank (Uniform07.cutoff row) (G.map Prod.snd) y-
      sourceRank (Uniform07.cutoff row) (G.map Prod.snd) x:=sub_nonneg.mpr (hmono hxy)
  have hB : 0≤ sourceRank (Uniform07.cutoff row) (G.map Prod.snd) y-
      sourceRank (Uniform07.cutoff row) (G.map Prod.snd) x+K*(y-x):=
    add_nonneg hM (mul_nonneg hK (sub_nonneg.mpr hxy))
  have hN : ((m-1:ℕ):ℝ)≤ m := by exact_mod_cast Nat.sub_le m 1
  refine ⟨hd,hmeasure.trans ?_⟩
  change ((m-1:ℕ):ℝ)*LiteralLowDuplicate.pureRare m*(_+_)≤ _
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hS)
    (mul_nonneg (Nat.cast_nonneg _) hr)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hN hr) hB)

theorem derivative_bound_of_increment {M D : ℝ→ℝ} {L H K C b M' D' : ℝ}
    (hb : b∈Ioo L H) (hM : HasDerivAt M M' b) (hD : HasDerivAt D D' b)
    (hinc : ∀x∈Icc L H,∀y∈Icc L H,x≤ y→
      0≤ D y-D x ∧ D y-D x≤ C*(M y-M x+K*(y-x))) :
    0≤ D' ∧ D'≤ C*(M'+K) := by
  let F:=𝓝[>] b
  have hfilter : F≤𝓝[≠] b:=nhdsWithin_mono b
    (show Ioi b⊆{b}ᶜ from fun y hy=>ne_of_gt hy)
  have htM : Tendsto (fun y=>(M y-M b)/(y-b)) F (𝓝 M'):=by
    simpa only [show slope M b=(fun y => (M y-M b)/(y-b)) from
      funext (slope_def_field M b)] using hM.tendsto_slope.mono_left hfilter
  have htD : Tendsto (fun y=>(D y-D b)/(y-b)) F (𝓝 D'):=by
    simpa only [show slope D b=(fun y => (D y-D b)/(y-b)) from
      funext (slope_def_field D b)] using hD.tendsto_slope.mono_left hfilter
  have hupper : ∀ᶠy in F,y< H:=mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb.2)
  constructor
  · apply ge_of_tendsto htD
    filter_upwards [self_mem_nhdsWithin,hupper] with y hy hyH
    change b<y at hy
    exact div_nonneg (hinc b ⟨hb.1.le,hb.2.le⟩ y ⟨hb.1.le.trans hy.le,hyH.le⟩ hy.le).1
      (sub_nonneg.mpr hy.le)
  · apply le_of_tendsto_of_tendsto htD ((htM.add_const K).const_mul C)
    filter_upwards [self_mem_nhdsWithin,hupper] with y hy hyH
    change b<y at hy
    have hh:=div_le_div_of_nonneg_right
      (hinc b ⟨hb.1.le,hb.2.le⟩ y ⟨hb.1.le.trans hy.le,hyH.le⟩ hy.le).2
      (sub_nonneg.mpr hy.le)
    have he : C*(M y-M b+K*(y-b))/(y-b)=C*((M y-M b)/(y-b)+K) := by
      field_simp [(sub_pos.mpr hy).ne']
    exact hh.trans_eq he

theorem eventually_received_pure_duplicate_derivative (row : Uniform07.Row) :
    ∀ᶠm in atTop,∀E : Received05.ReadyLaw row m,
      ∀b M' D' : ℝ,
      b∈Ioo (Physical.sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row)→
      HasDerivAt (sourceRank (Uniform07.cutoff row)
        ((Received05.G row m E:Measure (ℝ×ℝ)).map Prod.snd)) M' b→
      HasDerivAt (sourcePureDuplicate row m (Received05.G row m E)) D' b→
      0≤ D' ∧ D'≤(m:ℝ)*LiteralLowDuplicate.pureRare m*(M'+lowRankConstant row) := by
  let O:=SourceRankOutput.from_early_source
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.atoms row)
    (Received05.roots row).literal (Received05.roots row).rejection
  filter_upwards [eventually_received_contracted_rank row,O.primitive_measures] with m hscaled hP E
  let P:=Classical.choice (hP E _ (source_crossover_geometry row).1
    (source_crossover_geometry row).2.2.1.le)
  have hinc:=pure_duplicate_increment_of_contracted_rank row m (Received05.G row m E)
    (Received05.g row m E) (Received05.cm row m E) P
    (lowRankConstant_nonnegative row) (hscaled E)
  intro b M' D' hb hM hD
  exact derivative_bound_of_increment hb hM hD hinc

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
