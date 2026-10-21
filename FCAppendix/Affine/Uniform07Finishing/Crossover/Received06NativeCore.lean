import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06NativeKernels
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06RankGeometry
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06PureHazard
import FCAppendix.Affine.Uniform07Finishing.Crossover.NativeFiniteFOC

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Physical Received05

def receivedRmax (row : Uniform07.Row) : ℝ:=
  4/(Uniform07.xi row*sourceCrossoverStart row*(sourceRateConstants row).Amin)

def receivedDmax (row : Uniform07.Row) : ℝ:=4/(Uniform07.xi row*sourceCrossoverStart row)

def nativeRemote (row : Uniform07.Row) : Set (Icc (0:ℝ) (Early.bidCap row)):=
  {b | (b:ℝ)< SourcePrefixConstructor.extensionEnd row}

theorem nativeRemote_open (row : Uniform07.Row) : IsOpen (nativeRemote row) :=
  isOpen_lt continuous_subtype_val continuous_const

theorem nativeRemote_contains (row : Uniform07.Row) {b : ℝ}
    (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row))
    (hcap : b∈Icc (0:ℝ) (Early.bidCap row)) : (⟨b,hcap⟩:Icc (0:ℝ) (Early.bidCap row))∈nativeRemote row := by
  have hgeo:=SourcePrefixConstructor.band_geometry row
  exact hb.2.trans_lt ((source_crossover_geometry row).2.2.2.1.trans hgeo.2.2.1)

theorem native_local_sorted (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ)
    (hs : ∀ᵐp∂(G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)),
      p.2≤ SourcePrefixConstructor.extensionEnd row→
        PureRankCounts.sourceRank (Uniform07.cutoff row)
          ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) p.2=p.1) :
    ∀ᵐz∂((F.toAuxiliaryData.crossoverBroadcastLaw row k).lower :
        Measure (ℝ×Icc (0:ℝ) (Early.bidCap row))),
      z.2∈nativeRemote row→ z.1=rank (F.toReadyLowerFamily.market row k).native
        (Uniform07.cutoff row) z.2.1 := by
  let P:=F.toAuxiliaryData.crossoverBroadcastLaw row k
  have hmap : (P.lower : Measure (ℝ×Icc (0:ℝ) (Early.bidCap row))).map
      (fun z=>(z.1,(z.2:ℝ)))=(G row (F.start+k) (F.law row k):Measure (ℝ×ℝ)) :=
    crossoverBroadcastLaw_real F.toAuxiliaryData row k (F.law row k).1 rfl
  have hm : Measurable (fun z : ℝ×Icc (0:ℝ) (Early.bidCap row)=>(z.1,(z.2:ℝ))):=
    measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  have hM : Measurable (PureRankCounts.sourceRank (Uniform07.cutoff row)
      ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd)) :=
    (SharpPureDerivative.monotone_rank (Uniform07.cutoff_pos row).le _).measurable
  have hp : ∀ᵐz∂(P.lower : Measure (ℝ×Icc (0:ℝ) (Early.bidCap row))),
      (z.2:ℝ)≤ SourcePrefixConstructor.extensionEnd row→
        PureRankCounts.sourceRank (Uniform07.cutoff row)
          ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) z.2.1=z.1 := by
    have hpred : MeasurableSet {p : ℝ×ℝ |
        p.2≤SourcePrefixConstructor.extensionEnd row→
          PureRankCounts.sourceRank (Uniform07.cutoff row)
            ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) p.2=p.1} :=
      (measurableSet_le measurable_snd measurable_const).imp
        (measurableSet_eq_fun (hM.comp measurable_snd) measurable_fst)
    apply (ae_map_iff hm.aemeasurable hpred).mp
    rwa [hmap]
  filter_upwards [hp] with z hz hremote
  rw [native_rank_eq]
  exact (hz hremote.le).symm

theorem eventually_native_remote_core (F : BroadcastLowerFamily) (row : Uniform07.Row) :
    ∀ᶠk in atTop,∀i : Fin (F.start+k),Nonempty
      (RemoteCore06 row (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i)
        (sourceCrossoverStart row) (sourceCrossoverEnd row) (Early.bidCap row)
        (F.toAuxiliaryData.crossoverBroadcastLaw row k) (OptimizedPhysicalRate.A row)
        (sourceRateConstants row).Amin (sourceRateConstants row).Amax
        (receivedRmax row) (receivedDmax row) (receivedU19Error row (F.start+k))
        (lowBenchmark (F.start+k))) := by
  have ht:=tail_population_tendsto F.start
  have hAC:=ht.eventually (eventually_received_band_ac row)
  have hU19:=ht.eventually (eventually_u19Tolerance row)
  have hsort:=ht.eventually (eventually_received_local_used_rank row)
  have hsize:=ht.eventually (eventually_ge_atTop (10000000000:ℕ))
  have hsmall : ∀ᶠk in atTop,lowDuplicateEnvelope row (F.start+k)≤ lowBenchmark (F.start+k)/2 := by
    have hh:=((low_relative_tendsto row).comp ht).eventually (Iic_mem_nhds (by norm_num : (0:ℝ)<1/2))
    filter_upwards [hh] with k hk
    have hd:=(div_le_iff₀ (lowBenchmark_pos (F.start+k))).mp hk
    linarith
  have hhalf:=(F.toReadyLowerFamily.low row).halfValue
  have hdup:=(F.toReadyLowerFamily.low row).duplicate
  filter_upwards [hAC,hU19,hsort,hsize,hsmall,hhalf,hdup] with k hAC hU19 hsort hsize hsmall hhalf hdup
  intro i
  let M:=F.toReadyLowerFamily.market row k
  let P:=F.toAuxiliaryData.crossoverBroadcastLaw row k
  let B:=crossoverEvent F row k i
  have hgeo:=source_crossover_geometry row
  have hLR:=(source_crossover_end_gt_start row).le
  have hRU : sourceCrossoverEnd row≤ Early.bidCap row:=
    (hgeo.2.2.2.1.trans (source_large_band_below_cap row)).le
  have hRt : sourceCrossoverEnd row< Uniform07.cutoff row := by
    have hs : Uniform07.sourceZhi row<1:=by cases row <;> norm_num [Uniform07.sourceZhi]
    exact (mul_lt_mul_of_pos_right hs (Uniform07.cutoff_pos row)).trans_eq (one_mul _)
  have hbt {b : ℝ} (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      b∈Icc (0:ℝ) (Uniform07.cutoff row):=⟨hgeo.1.le.trans hb.1,hb.2.trans hRt.le⟩
  have hRbounds {b : ℝ} (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      rank M.native (Uniform07.cutoff row) b∈Icc (Uniform07.cutoff row/2) (Uniform07.cutoff row) := by
    rw [native_rank_eq]
    have hh:=received_rank_bounds row (F.start+k) (F.law row k) (hbt hb)
    exact ⟨hb.1.trans hh.1,hh.2⟩
  have hnear {b : ℝ} (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :=
    native_canonical_near F row k i (show b∈Ioo (0:ℝ) (ReceiptGap.cap row) from
      ⟨hgeo.1.trans_le hb.1,(hb.2.trans_lt (hgeo.2.2.2.1.trans
        (source_large_band_below_cap row))).trans_eq (receiptCap_eq row).symm⟩)
  have hcanon (b : ℝ) (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :=
    native_canonical_at row M.native i B (G row (F.start+k) (F.law row k))
      (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k))
      (show 0< F.start+k by omega) hgeo.1 hb.1 (sourceRateConstants row).Amin_pos
      ((sourceRateConstants row).bounds b hb) (u19Tolerance_mem row (F.start+k))
      (hnear hb).1 (hnear hb).2 (hU19 (F.law row k) b hb)
  have hac:=native_band_AC F row k i (hAC (F.law row k))
  have hs:=native_local_sorted F row k (hsort (F.law row k))
  refine ⟨{
    interval:=hLR
    bid0:=hgeo.1
    bid1:=hRt.le.trans (Uniform07.cutoff_lt_one row).le
    feasible:=hRU
    halfFeasible:=(source_half_value_cap row le_rfl).1
    sourceInterval:=fun _ h=>h
    remote:=nativeRemote row
    remoteOpen:=nativeRemote_open row
    remoteContains:=fun b hb=>nativeRemote_contains row hb _
    sorted:=hs
    rankRange:=fun b hb=>⟨(half_pos (Uniform07.cutoff_pos row)).le.trans (hRbounds hb).1,(hRbounds hb).2⟩
    rankAC:=hac.1
    successAC:=hac.2.1
    duplicateAC:=hac.2.2.1
    canonicalAC:=hac.2.2.2.1
    canonicalDuplicateAC:=hac.2.2.2.2
    canonicalAE:=ae_of_all _ (fun b hb=>(hcanon b hb).1)
    canonicalPositive:=?_
    purePositive:=?_
    canonicalDuplicateProbability:=fun b _=>actual_canonical_probability_bounds M.native i B b
    pureDerivative:=?_
    pureDerivativePositive:=fun b hb=>(source_rank_polynomial_upper row hsize (hRbounds hb)).1
    pureDerivativeUpper:=fun b hb=>(source_rank_polynomial_upper row hsize (hRbounds hb)).2
    sourceDerivative:=fun b hb=>actual_source_rate_derivative row hb
    rateContinuous:=(OptimizedPhysicalRate.continuousOn_A row).mono (source_band_subset_rate row)
    rateBounds:=(sourceRateConstants row).bounds
    canonicalRatio:=fun b hb=>(hcanon b hb).2
    halfValueAcceptance:=fun w hw=>hhalf i w hw
    halfValueDuplicate:=?_
    commonDensity:=common_density_from_native_finite_IC P (source_eta_mem row).1
      (source_eta_mem row).2 rfl rfl hLR hgeo.1 hRU (nativeRemote row) (nativeRemote_open row)
      (fun b hb=>nativeRemote_contains row hb _) hs i hac.1 hac.2.1 hac.2.2.1 }⟩
  · intro b hb
    rw [(hnear hb).1.self_of_nhds]
    exact (hU19 (F.law row k) b hb).canonical_pos
  · intro b hb
    have hw:=hRbounds hb
    have hp : (1+Uniform07.cutoff row)/2-rank M.native (Uniform07.cutoff row) b∈Ioo (0:ℝ) 1 := by
      constructor <;> linarith [hw.1,hw.2,Uniform07.cutoff_lt_one row]
    exact Bayes.binomBelow_pos (F.start+k-1) (Uniform07.capacity (F.start+k))
      (Uniform06.PhysicalRates.capacity_positive (by omega)) _ hp
  · intro b hb
    have hh:=source_rank_polynomial_derivative row (by omega : 4≤ F.start+k)
      (rank M.native (Uniform07.cutoff row) b)
    convert hh using 1
    exact hh.deriv
  · intro w hw
    exact (hdup i (w/2) ⟨(half_pos hw.1).le,(source_half_value_cap row hw.2).2⟩).trans hsmall

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
