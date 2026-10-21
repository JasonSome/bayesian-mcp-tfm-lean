import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Auxiliary
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05LowEntry
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Rate
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05CanonicalKernels
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Rank

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Uniform06.LiteralKernelDecomposition
open Uniform06.LiteralPureComponents
open Physical Received05

theorem receiptCap_eq (row : Uniform07.Row) : ReceiptGap.cap row=Early.bidCap row :=
  (Received05.cap_eq row).symm.trans (Concrete05.cap_eq row)

theorem source_large_band_below_cap (row : Uniform07.Row) :
    SourcePrefixConstructor.crossoverEnd row< Early.bidCap row := by
  have h:=SourcePrefixConstructor.band_geometry row
  exact h.2.2.1.trans (h.2.2.2.2.1.trans_eq (receiptCap_eq row))

theorem source_band_mem_cap (row : Uniform07.Row) {b : ℝ}
    (hb : b∈Icc (sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row)) :
    b∈Ioc (0:ℝ) (ReceiptGap.cap row) :=
  ⟨(source_crossover_geometry row).1.trans_le hb.1,
    hb.2.trans ((source_large_band_below_cap row).le.trans_eq (receiptCap_eq row).symm)⟩

def crossoverEvent (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ) (i : Fin (F.start+k)) :
    CanonicalEvent (F.toReadyLowerFamily.market row k).native := by
  letI : Nonempty (Fin (F.start+k)):=(F.toReadyLowerFamily.market row k).fin_nonempty
  exact Concrete05.nativeCanonicalEvent (F.law row k).1
    (F.toReadyLowerFamily.market row k).capacity_positive (sourceLowerPriceCeiling row) i

theorem native_rank_eq (F : BroadcastLowerFamily) (row : Uniform07.Row) (k : ℕ) :
    rank (F.toReadyLowerFamily.market row k).native (Uniform07.cutoff row)=
      PureRankCounts.sourceRank (Uniform07.cutoff row)
        ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) := by
  funext b
  exact Concrete05.received_native_rank_eq F.toReadyLowerFamily row k b

theorem native_positive_canonical (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ) (i : Fin (F.start+k)) {b : ℝ}
    (hb : b∈Ioc (0:ℝ) (ReceiptGap.cap row)) :
    canonicalMarginal (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i) b=
      sourceCanonicalMarginal row (F.start+k) (G row (F.start+k) (F.law row k))
        (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k)) b ∧
    canonicalDuplicate (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i) b=
      sourceCanonicalDuplicate row (F.start+k) (G row (F.start+k) (F.law row k))
        (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k)) b := by
  let M:=F.toReadyLowerFamily.market row k
  letI : Nonempty (Fin (F.start+k)):=M.fin_nonempty
  let own : Uniform05.Bid row:=⟨b,by
    change b∈Icc (0:ℝ) (Uniform05.cap row)
    rw [Received05.cap_eq]
    exact ⟨hb.1.le,hb.2⟩⟩
  exact Concrete05.native_canonical_kernels_eq_source06 (F.law row k).1 M.capacity_positive
    (source_auxiliary_floor_guards row).1 (source_auxiliary_floor_guards row).2.1
    (source_auxiliary_floor_guards row).2.2.1
    (Concrete05.auxiliary_receipt_gap (F.law row k).1) i own hb.1

theorem actual_canonical_probability_bounds {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (B : CanonicalEvent Γ) (b : ℝ) :
    canonicalDuplicate Γ i B b∈Icc (0:ℝ) (canonicalMarginal Γ i B b) := by
  let μ:=(sampleLaw Γ).restrict (B.event b)
  let K:=focalCount Γ i (two b)
  have hK : Measurable K:=measurable_focalCount Γ i (two b)
  have hs : Integrable (fun ω=>successIndicator (K ω).val) μ:=
    CountLaw.integrable_comp μ K hK (fun k=>successIndicator k.val)
  have hd : Integrable (fun ω=>(K ω:ℝ)-successIndicator (K ω).val) μ:=
    CountLaw.integrable_comp μ K hK (fun k=>(k:ℝ)-successIndicator k.val)
  have hpoint (ω) : 0≤(K ω:ℝ)-successIndicator (K ω).val ∧
      (K ω:ℝ)-successIndicator (K ω).val≤ successIndicator (K ω).val := by
    generalize K ω=z
    fin_cases z <;> norm_num [successIndicator]
  have hn : 0≤ canonicalDuplicate Γ i B b:=integral_nonneg (fun ω=>(hpoint ω).1)
  have hle : canonicalDuplicate Γ i B b≤ canonicalSuccess Γ i B b:=
    integral_mono hd hs (fun ω=>(hpoint ω).2)
  refine ⟨hn,?_⟩
  unfold canonicalMarginal
  linarith

theorem native_canonical_near (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ) (i : Fin (F.start+k)) {b : ℝ}
    (hb : b∈Ioo (0:ℝ) (ReceiptGap.cap row)) :
    canonicalMarginal (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i)
        =ᶠ[𝓝 b] sourceCanonicalMarginal row (F.start+k) (G row (F.start+k) (F.law row k))
          (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k)) ∧
    canonicalDuplicate (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i)
        =ᶠ[𝓝 b] sourceCanonicalDuplicate row (F.start+k) (G row (F.start+k) (F.law row k))
          (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k)) := by
  constructor <;> filter_upwards [Ioo_mem_nhds hb.1 hb.2] with x hx
  · exact (native_positive_canonical F row k i ⟨hx.1,hx.2.le⟩).1
  · exact (native_positive_canonical F row k i ⟨hx.1,hx.2.le⟩).2

private theorem native_ac_congr_on {f g : ℝ→ℝ} {L H : ℝ}
    (hf : AbsolutelyContinuousOnInterval f L H) (h : EqOn f g (uIcc L H)) :
    AbsolutelyContinuousOnInterval g L H := by
  apply hf.congr'
  apply Filter.Eventually.filter_mono inf_le_right
  rw [Filter.eventually_principal]
  intro E hE
  apply Finset.sum_congr rfl
  intro j hj
  rw [h (hE.1 j hj).1,h (hE.1 j hj).2]

theorem native_band_AC (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ) (i : Fin (F.start+k))
    (H : SourceBandAC row (F.start+k) (G row (F.start+k) (F.law row k))
      (g row (F.start+k) (F.law row k)) (cm row (F.start+k) (F.law row k))
      (sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row)) :
    AbsolutelyContinuousOnInterval
      (rank (F.toReadyLowerFamily.market row k).native (Uniform07.cutoff row))
        (sourceCrossoverStart row) (sourceCrossoverEnd row) ∧
    AbsolutelyContinuousOnInterval (success (F.toReadyLowerFamily.market row k).native i)
        (sourceCrossoverStart row) (sourceCrossoverEnd row) ∧
    AbsolutelyContinuousOnInterval (duplicate (F.toReadyLowerFamily.market row k).native i)
        (sourceCrossoverStart row) (sourceCrossoverEnd row) ∧
    AbsolutelyContinuousOnInterval
      (canonicalMarginal (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i))
        (sourceCrossoverStart row) (sourceCrossoverEnd row) ∧
    AbsolutelyContinuousOnInterval
      (canonicalDuplicate (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i))
        (sourceCrossoverStart row) (sourceCrossoverEnd row) := by
  have hgeo:=source_crossover_geometry row
  have hLR:=(source_crossover_end_gt_start row).le
  have hsub : uIcc (sourceCrossoverStart row) (sourceCrossoverEnd row)⊆
      uIcc (sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row) := by
    rw [uIcc_of_le hLR,uIcc_of_le hgeo.2.2.1.le]
    exact Icc_subset_Icc le_rfl hgeo.2.2.2.1.le
  have hmem {b : ℝ} (hb : b∈uIcc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      b∈Ioc (0:ℝ) (ReceiptGap.cap row) :=
    source_band_mem_cap row (by simpa only [uIcc_of_le hgeo.2.2.1.le] using hsub hb)
  have T:=F.toReadyLowerFamily.positive_counts row k i
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [native_rank_eq]
    exact H.rank.mono hsub
  · exact native_ac_congr_on (H.success.mono hsub) (fun b hb=>(T.success b (hmem hb)).symm)
  · exact native_ac_congr_on (H.duplicate.mono hsub) (fun b hb=>(T.duplicate b (hmem hb)).symm)
  · exact native_ac_congr_on (H.canonical.mono hsub)
      (fun b hb=>(native_positive_canonical F row k i (hmem hb)).1.symm)
  · exact native_ac_congr_on (H.canonicalDuplicate.mono hsub)
      (fun b hb=>(native_positive_canonical F row k i (hmem hb)).2.symm)

theorem native_errors_eq (F : BroadcastLowerFamily) (row : Uniform07.Row)
    (k : ℕ) (i : Fin (F.start+k))
    (hp : LiteralPrefixStieltjes.PrefixConditions (Uniform07.xi row)
      (g row (F.start+k) (F.law row k)) (SourcePrefixConstructor.crossoverEnd row))
    {b : ℝ} (hb : b∈Ioc (0:ℝ) (SourcePrefixConstructor.crossoverEnd row)) :
    successError (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i)
        (Uniform07.cutoff row) b=
      LiteralPureComponents.sourcePureSuccess row (F.start+k) (G row (F.start+k) (F.law row k)) b-
        2*pureRank (F.start+k) (Uniform07.capacity (F.start+k)) (Uniform07.cutoff row)
          (PureRankCounts.sourceRank (Uniform07.cutoff row)
            ((G row (F.start+k) (F.law row k) : Measure (ℝ×ℝ)).map Prod.snd) b) ∧
    duplicateError (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i) b=
      LiteralPureComponents.sourcePureDuplicate row (F.start+k) (G row (F.start+k) (F.law row k)) b := by
  have hcap : b∈Ioc (0:ℝ) (ReceiptGap.cap row):=
    ⟨hb.1,hb.2.trans ((source_large_band_below_cap row).le.trans_eq (receiptCap_eq row).symm)⟩
  have T:=F.toReadyLowerFamily.positive_counts row k i
  have hc:=native_positive_canonical F row k i hcap
  have hdec:=source_both_decompositions row (F.start+k) (G row (F.start+k) (F.law row k))
    (g row (F.start+k) (F.law row k)) hp (cm row (F.start+k) (F.law row k)) ⟨hb.1.le,hb.2⟩
  unfold successError duplicateError comparisonMarginal
  rw [T.success b hcap,T.duplicate b hcap,hc.1,hc.2,native_rank_eq,hdec.1,hdec.2]
  constructor <;> ring

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
