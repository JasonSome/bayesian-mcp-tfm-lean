import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Menu
import FCAppendix.Affine.Uniform07Finishing.Crossover.StieltjesAnalytic
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalFamilies
import FCAppendix.Affine.Uniform06.SourceRankOutput
import FCAppendix.Affine.Uniform06.SourceCanonicalRegularity
import FCAppendix.Affine.Uniform06.RankDensityRepresentative

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Uniform06.LiteralPureComponents
open Uniform06.LowRankMeasures Uniform06.ScaledMeasure
open Uniform06.PrimitiveStieltjesMeasures Uniform06.SourceCanonicalRegularity
open Uniform06.CanonicalPrefixLipschitz Uniform06.LiteralPrefixStieltjes

theorem ac_measure_of_le {μ ν : Measure ℝ} (h : μ≤ν) (hν : ν≪volume) : μ≪volume := by
  intro A hA
  exact le_antisymm ((h A).trans_eq (hν hA)) bot_le

theorem ac_restrict_subset {μ : Measure ℝ} {A B : Set ℝ}
    (hAB : A⊆B) (hAC : μ.restrict B≪volume) : μ.restrict A≪volume :=
  ac_measure_of_le (Measure.restrict_mono_set μ hAB) hAC

theorem scaled_restrict_ac {μ : Measure ℝ} {κ L H : ℝ}
    (hκ : 0<κ) (hκ1 : κ≤ 1) (hL : 0≤ L)
    (hAC : μ.restrict (Ioc (0:ℝ) H)≪volume) :
    (scaledRankMeasure κ μ).restrict (Ioc L H)≪volume := by
  intro A hA
  obtain ⟨C,hACset,hCm,hCv⟩:=exists_measurable_superset_of_null hA
  let B:=C∩Ioc L H
  have hBm : MeasurableSet B:=hCm.inter measurableSet_Ioc
  have hBv : volume B=0:=measure_mono_null inter_subset_left hCv
  have hBs : B⊆Ioc (0:ℝ) H:=fun x hx=>⟨hL.trans_lt hx.2.1,hx.2.2⟩
  have hscaled:=scaled_positive_interval hκ hκ1 hBs
  have hscaledNull : volume (scaledSet κ B)=0 := by
    rw [volume_scaled hκ hBm,hBv,mul_zero]
  have hμ : μ (scaledSet κ B)=0 := by
    have hz:=hAC hscaledNull
    rwa [Measure.restrict_apply (measurableSet_scaled hκ.ne' hBm),
      inter_eq_left.mpr hscaled] at hz
  apply le_antisymm _ bot_le
  calc
    ((scaledRankMeasure κ μ).restrict (Ioc L H)) A≤
        ((scaledRankMeasure κ μ).restrict (Ioc L H)) C:=measure_mono hACset
    _=(scaledRankMeasure κ μ) B:=Measure.restrict_apply hCm
    _=μ (scaledSet κ B):=scaledRankMeasure_apply hκ.ne' μ hBm
    _=0:=hμ

theorem pureComparison_restrict_ac (row : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ×ℝ)) {L H : ℝ} (hL : 0≤ L)
    (hAC : lowBidMeasure row G H≪volume) :
    (pureComparison row m G).restrict (Ioc L H)≪volume := by
  have hκ : 0< Uniform07.kappa row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  have hκ1 : Uniform07.kappa row≤ 1 := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  have hsub : Ioc L H⊆Ioc (0:ℝ) H:=fun _ hx=>⟨hL.trans_lt hx.1,hx.2⟩
  have hfirst:=ac_restrict_subset hsub hAC
  have hsecond:=scaled_restrict_ac hκ hκ1 hL hAC
  intro A hA
  rw [pureComparison,Measure.restrict_smul,Measure.restrict_add,
    Measure.smul_apply,Measure.add_apply,hfirst hA,hsecond hA]
  simp

theorem source_rank_ac (row : Uniform07.Row) (G : Measure (ℝ×ℝ))
    [IsProbabilityMeasure G] {L H : ℝ} (hL : 0≤ L) (hLH : L≤ H)
    (hAC : lowBidMeasure row G H≪volume) :
    AbsolutelyContinuousOnInterval
      (Uniform06.PureRankCounts.sourceRank (Uniform07.cutoff row) (G.map Prod.snd)) L H := by
  letI : IsProbabilityMeasure (G.map Prod.snd):=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply StieltjesAnalytic.absolutelyContinuous_of_measure_increments
    (bidMeasure row G) _ hLH
    (ac_restrict_subset (μ := bidMeasure row G) (A := Ioc L H) (B := Ioc (0:ℝ) H)
      (fun _ hx=>⟨hL.trans_lt hx.1,hx.2⟩) hAC)
  intro x hx
  rw [Uniform06.SharpPureDerivative.rank_increment _ hx.1,bidMeasure_real]

theorem source_canonical_duplicate_lipschitz (row : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐp∂G,LowChernoff.physicalFloor row p.1≤ p.2)
    (g : GuardData) {L H : ℝ} (hg : PrefixConditions (Uniform07.xi row) g H)
    (hH : 0≤ H) (hL : 0< L) (cm : (Fin (m-1)→ Fin 4)→ℝ) :
    LipschitzOnWith (Real.nnabs (canonicalConstant (Uniform07.xi row) g H/L))
      (sourceCanonicalDuplicate row m G g cm) (Icc L H) := by
  have hK:=(canonicalConstant_pos (Uniform07.xi_pos row) hH hg).le
  have hmono:=(source_canonical_monotone row m G hfloor g hg cm).2
  apply FixedPriceCanonicalIntegral.lipschitz_of_ordered_increments _ _ (div_nonneg hK hL.le)
  intro x hx y hy hxy
  have hx0:=hL.trans_le hx.1
  have hi:=(source_canonical_increments row m G hfloor g hg cm hx0 hxy hy.2).2
  have he:=div_le_div_of_nonneg_left (mul_nonneg hK (sub_nonneg.mpr hxy)) hL hx.1
  have he' : canonicalConstant (Uniform07.xi row) g H*(y-x)/x≤
      canonicalConstant (Uniform07.xi row) g H/L*(y-x) := by
    calc
      _ ≤ (canonicalConstant (Uniform07.xi row) g H*(y-x))/L := he
      _ = _ := by ring
  exact ⟨sub_nonneg.mpr (hmono ⟨hx0.le,hx.2⟩
    ⟨(hL.trans_le hy.1).le,hy.2⟩ hxy),hi.trans he'⟩

structure SourceBandAC (row : Uniform07.Row) (m : ℕ) (G : Measure (ℝ×ℝ))
    (g : GuardData) (cm : (Fin (m-1)→ Fin 4)→ℝ) (L H : ℝ) : Prop where
  rank : AbsolutelyContinuousOnInterval
    (Uniform06.PureRankCounts.sourceRank (Uniform07.cutoff row) (G.map Prod.snd)) L H
  pureSuccess : AbsolutelyContinuousOnInterval (sourcePureSuccess row m G) L H
  pureDuplicate : AbsolutelyContinuousOnInterval (sourcePureDuplicate row m G) L H
  success : AbsolutelyContinuousOnInterval (sourceSuccess row m G g cm) L H
  duplicate : AbsolutelyContinuousOnInterval (sourceDuplicate row m G g cm) L H
  canonical : AbsolutelyContinuousOnInterval (sourceCanonicalMarginal row m G g cm) L H
  canonicalDuplicate : AbsolutelyContinuousOnInterval (sourceCanonicalDuplicate row m G g cm) L H

private theorem ac_congr_on {f g : ℝ → ℝ} {L H : ℝ}
    (hf : AbsolutelyContinuousOnInterval f L H) (h : EqOn f g (uIcc L H)) :
    AbsolutelyContinuousOnInterval g L H := by
  apply hf.congr'
  apply Filter.Eventually.filter_mono inf_le_right
  rw [Filter.eventually_principal]
  intro E hE
  apply Finset.sum_congr rfl
  intro j hj
  rw [h (hE.1 j hj).1,h (hE.1 j hj).2]

theorem source_band_ac (row : Uniform07.Row) (m : ℕ)
    (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (hfloor : ∀ᵐp∂G,LowChernoff.physicalFloor row p.1≤ p.2)
    (hcap : ∀ᵐp∂G,p.2≤ ReceiptGap.cap row)
    (hatom : ∀b,(G.map Prod.snd) {b}=0)
    (g : GuardData) (cm : (Fin (m-1)→ Fin 4)→ℝ) {L H : ℝ}
    (hL : 0< L) (hLH : L≤ H) (hκU : Uniform07.kappa row*ReceiptGap.cap row< L)
    (hg : PrefixConditions (Uniform07.xi row) g H)
    (hAC : lowBidMeasure row G H≪volume)
    (P : PrimitiveStieltjesBounds row m G g cm L H) :
    SourceBandAC row m G g cm L H := by
  letI : IsProbabilityMeasure (G.map Prod.snd):=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hcap' : ∀ᵐb∂G.map Prod.snd,b≤ ReceiptGap.cap row := by
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Iic).mpr hcap
  have hrestrict:=ac_restrict_subset (μ := bidMeasure row G) (A := Ioc L H) (B := Ioc (0:ℝ) H)
    (fun _ hx=>⟨hL.trans hx.1,hx.2⟩) hAC
  obtain ⟨F,hFc,hFb,hFe,hFAC⟩:=Uniform06.SharpPureMeasure.source_pure_measure_AC
    row (G.map Prod.snd) hcap' hatom (m-1) (Uniform07.capacity m) hL hκU hLH hrestrict
  letI : IsFiniteMeasure F.measure:=Uniform06.CompactStieltjes.finite_of_bounds F hFb
  letI : IsFiniteMeasure P.pureDuplicate.measure:=
    Uniform06.CompactStieltjes.finite_of_bounds P.pureDuplicate P.duplicate_bounds
  have hPS : AbsolutelyContinuousOnInterval (sourcePureSuccess row m G) L H :=
    StieltjesAnalytic.absolutelyContinuous_literal_kernel F _ hLH hFAC hFe
  have hPD : AbsolutelyContinuousOnInterval (sourcePureDuplicate row m G) L H :=
    StieltjesAnalytic.absolutelyContinuous_literal_kernel P.pureDuplicate _ hLH
      (ac_measure_of_le P.pure_upper (pureComparison_restrict_ac row m G hL.le hAC)) P.duplicate_agrees
  have hC := source_canonical_lipschitz row m G hfloor g hg (hL.le.trans hLH) hL cm
  have hR := source_canonical_duplicate_lipschitz row m G hfloor g hg (hL.le.trans hLH) hL cm
  have hCa : AbsolutelyContinuousOnInterval (sourceCanonicalMarginal row m G g cm) L H := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hLH] using hC
  have hRa : AbsolutelyContinuousOnInterval (sourceCanonicalDuplicate row m G g cm) L H := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hLH] using hR
  refine ⟨source_rank_ac row G hL.le hLH hAC,hPS,hPD,?_,?_,hCa,hRa⟩
  · apply ac_congr_on ((hPS.fun_add (hCa.const_mul 2)).fun_sub hRa)
    intro b hb
    have hb' : b∈Icc L H:=by simpa only [uIcc_of_le hLH] using hb
    exact (source_both_decompositions row m G g hg cm
      ⟨hL.le.trans hb'.1,hb'.2⟩).1.symm
  · apply ac_congr_on (hPD.fun_add hRa)
    intro b hb
    have hb' : b∈Icc L H:=by simpa only [uIcc_of_le hLH] using hb
    exact (source_both_decompositions row m G g hg cm
      ⟨hL.le.trans hb'.1,hb'.2⟩).2.symm

theorem source_crossover_geometry (row : Uniform07.Row) :
    0< Physical.sourceCrossoverStart row ∧
    Uniform07.kappa row*ReceiptGap.cap row< Physical.sourceCrossoverStart row ∧
    Physical.sourceCrossoverStart row< Uniform06.SourcePrefixConstructor.crossoverEnd row ∧
    Physical.sourceCrossoverEnd row< Uniform06.SourcePrefixConstructor.crossoverEnd row ∧
    Uniform06.SourcePrefixConstructor.crossoverEnd row≤ Uniform06.SourcePrefixConstructor.sortEnd row := by
  have ht:=Uniform07.cutoff_pos row
  have hκ : Uniform07.kappa row*ReceiptGap.capFactor row<(1/2:ℝ) := by
    cases row <;> norm_num [ReceiptGap.capFactor,Uniform07.kappa,Uniform07.kappaQ,
      Uniform07.xi,Uniform07.xiQ,Uniform07.etaQ,Uniform07.x,Uniform07.xQ]
  have hx : (1/2:ℝ)< Uniform07.x row := by cases row <;> norm_num [Uniform07.x,Uniform07.xQ]
  have hz : Uniform07.sourceZhi row< Uniform07.x row := by
    cases row <;> norm_num [Uniform07.sourceZhi,Uniform07.x,Uniform07.xQ]
  rw [ReceiptGap.cap_scaled]
  unfold Physical.sourceCrossoverStart Physical.sourceCrossoverEnd
    Uniform06.SourcePrefixConstructor.crossoverEnd Uniform06.SourcePrefixConstructor.sortEnd Uniform07.entry
  have hk:=mul_lt_mul_of_pos_right hκ ht
  have hxx:=mul_lt_mul_of_pos_right hx ht
  have hzz:=mul_lt_mul_of_pos_right hz ht
  exact ⟨by positivity,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem eventually_received_band_ac (row : Uniform07.Row) :
    ∀ᶠm in atTop,∀E : Received05.ReadyLaw row m,
      SourceBandAC row m (Received05.G row m E) (Received05.g row m E)
        (Received05.cm row m E) (Physical.sourceCrossoverStart row)
        (Uniform06.SourcePrefixConstructor.crossoverEnd row) := by
  let O:=Uniform06.SourceRankOutput.from_early_source
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.atoms row)
    (Received05.roots row).literal (Received05.roots row).rejection
  obtain ⟨γ,hγ,hreg⟩:=O.regularity
  have hp:=Uniform06.SourceEarlyFamily.eventually_source_prefix
    (Received05.G row) (Received05.g row) (Received05.cm row) row
    (Received05.earlyMenu row) (Received05.roots row).literal (Received05.roots row).rejection
  filter_upwards [hreg,O.primitive_measures,hp] with m hreg hprim hp E
  have hgeo:=source_crossover_geometry row
  exact source_band_ac row m (Received05.G row m E)
    ((Received05.permitted row m E).mono fun _ h=>h.1)
    ((Received05.permitted row m E).mono fun _ h=>h.2.trans (min_le_right _ _))
    (Received05.atoms row m E) (Received05.g row m E) (Received05.cm row m E)
    hgeo.1 hgeo.2.2.1.le hgeo.2.1
    (LowRankMeasures.PrefixConditions.mono (hp E).2.1 hgeo.2.2.2.2)
    (hreg E).1 (Classical.choice (hprim E _ hgeo.1 hgeo.2.2.1.le))

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
