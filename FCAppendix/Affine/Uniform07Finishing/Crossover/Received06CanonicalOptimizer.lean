import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06CanonicalLower
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Rate
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalOptimizerCover
import FCAppendix.Affine.Uniform06.SourceOptimizerGap

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform07 LiteralExperiment LiteralPureComponents
open Physical

namespace Received06

theorem two_point_full_gap (row : Row) (m : ℕ)
    (μ : Measure (ℝ×ℝ)) [IsProbabilityMeasure μ]
    (g : GuardData) {H : ℝ}
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi row) g H)
    (cm : (Fin (m-1)→ Fin 4)→ℝ) {v a c e : ℝ}
    (hv : v≤ cutoff row) (hvH : v≤ H)
    (ha : a∈Icc (0:ℝ) v) (hc : c∈Icc (0:ℝ) v)
    (hopt : CanonicalOptimizer.one (sourceCanonicalMarginal row m μ g cm) v a≤
      CanonicalOptimizer.one (sourceCanonicalMarginal row m μ g cm) v c)
    (_he : 0≤ e)
    (hSa : sourcePureSuccess row m μ a≤ e)
    (hDa : sourcePureDuplicate row m μ a≤ e)
    (hDc : sourcePureDuplicate row m μ c≤ e)
    (hgain : (1+eta row)*cutoff row*e<
      CanonicalOptimizer.two (eta row) (sourceCanonicalMarginal row m μ g cm)
        (sourceCanonicalDuplicate row m μ g cm) v c-
      CanonicalOptimizer.one (sourceCanonicalMarginal row m μ g cm) v c) :
    CanonicalPureTransfer.single row m μ g cm v a<
      CanonicalPureTransfer.broadcast row m μ g cm v c := by
  have hpa:=CanonicalPureTransfer.pure_bounds row m μ a
  have hpc:=CanonicalPureTransfer.pure_bounds row m μ c
  have hda:=CanonicalPureTransfer.exact_payoff_decomposition row m μ g hg cm v
    ⟨ha.1,ha.2.trans hvH⟩
  have hdc:=CanonicalPureTransfer.exact_payoff_decomposition row m μ g hg cm v
    ⟨hc.1,hc.2.trans hvH⟩
  have hvat : v-a≤ cutoff row := by linarith [ha.1]
  have hplus : sourcePureSuccess row m μ a+sourcePureDuplicate row m μ a≤ 2*e := by
    linarith
  have hex : CanonicalPureTransfer.excess row m μ v a≤ cutoff row*e := by
    unfold CanonicalPureTransfer.excess
    have hh:=mul_le_mul hvat hplus (add_nonneg hpa.1.1 hpa.2.1) (cutoff_pos row).le
    nlinarith
  have hcharge : eta row*c*sourcePureDuplicate row m μ c≤ eta row*cutoff row*e := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hc.2.trans hv) (eta_pos row).le)
      hDc hpc.2.1 (mul_nonneg (eta_pos row).le (cutoff_pos row).le)
  have hpurec : 0≤(v-c)*sourcePureSuccess row m μ c :=
    mul_nonneg (sub_nonneg.mpr hc.2) hpc.1.1
  rw [hda.1,hdc.2]
  nlinarith

end Received06

namespace Received05

theorem ReadyLowerFamily.canonical (F : ReadyLowerFamily) (row : Row) :
    CanonicalOptimizer06 (fun k=>(F.market row k).native) row where
  compare := by
    intro w v₀ b₀ hvlim hblim hvEntry hb₀ hrate
    have ht:=cutoff_pos row
    have hb₀' : b₀∈Ioo (cutoff row/2) (entry row):=hb₀
    have hb₀v : b₀≤ v₀ := le_of_tendsto_of_tendsto hblim hvlim
      (Eventually.of_forall fun k=>(w.bidMem k).2.trans (min_le_left _ _))
    obtain ⟨bstar,hbstar,hrstar⟩:=Received06.exists_lower_bid_with_rate_gap row hb₀' hrate
    have hbstarEntry : bstar∈Ioo (cutoff row/2) (entry row):=
      ⟨hbstar.1,hbstar.2.trans hb₀'.2⟩
    have hbstar0 : 0< bstar:=(half_pos ht).trans hbstar.1
    have hbstarv : bstar< v₀:=hbstar.2.trans_le hb₀v
    let vmin:ℝ:=(bstar+v₀)/2
    let vmax:ℝ:=(v₀+entry row)/2
    have hvmin : cutoff row/2< vmin := by dsimp [vmin]; linarith [hbstar.1]
    have hvminv : vmin< v₀ := by dsimp [vmin]; linarith
    have hvvmax : v₀< vmax := by dsimp [vmax]; linarith
    have hvmax : vmax< entry row := by dsimp [vmax]; linarith
    have hminmax : vmin≤ vmax:=hvminv.le.trans hvvmax.le
    have hd : 0< vmin-bstar := by dsimp [vmin]; linarith
    have hvmax0 : 0≤ vmax := ((half_pos ht).trans hvmin).le.trans hminmax
    let m:ℕ→ℕ:=fun k=>F.start+w.market k
    let E:=fun k=>F.law row (w.market k)
    let μ:=fun k=>G row (m k) (E k)
    let C:=fun k=>sourceCanonicalMarginal row (m k) (μ k)
      (g row (m k) (E k)) (cm row (m k) (E k))
    let R:=fun k=>sourceCanonicalDuplicate row (m k) (μ k)
      (g row (m k) (E k)) (cm row (m k) (E k))
    let c:=fun k=>SourceCanonicalOptimizer.chosen (G row) (g row) (cm row) row
      vmin (m k) (E k) (w.value k)
    have hm : Tendsto m atTop atTop := (Physical.tail_population_tendsto F.start).comp w.marketTendsto
    have hμ : Tendsto μ atTop (𝓝 (FullJointLaw.law row)):=
      F.full_joint_tendsto row w.market w.marketTendsto
    have hrank:=Received06.eventually_subentry_rank_le_entry row μ hμ hvmax0 hvmax
    have hcanon:=SourceCanonicalOptimizer.original_optimizer (G row) (g row) (cm row) row
      (earlyMenu row) (roots row).literal (roots row).rejection hvmin hminmax hvmax
    have hcanongap:=SourceOptimizerGap.eventual_positive_canonical_gap
      (G row) (g row) (cm row) row (earlyMenu row) (atoms row)
      (roots row).literal (roots row).rejection (Received06.readyKernelFields row)
      hvmin hminmax hvmax
    have hprefix:=SourceEarlyFamily.eventually_source_prefix (G row) (g row) (cm row) row
      (earlyMenu row) (roots row).literal (roots row).rejection
    have hK : 0<(1+eta row)*cutoff row*(2*Received06.entryPureCoefficient row+1) := by
      have := eta_pos row
      have := Received06.entryPureCoefficient_positive row
      positivity
    have hL : 0< SourceOptimizerGap.gapFactor row*(vmin-bstar) :=
      mul_pos (SourceOptimizerGap.gapFactor_pos row) hd
    have hpay:=F.canonical_beats_exponential row w.market w.marketTendsto hbstarEntry
      (Received06.entry_pure_rate_mem row).1 hrstar hK hL
    have hvalues:=hvlim.eventually (Ioo_mem_nhds hvminv hvvmax)
    have hpositive:=hblim.eventually (Ioi_mem_nhds ((half_pos ht).trans hb₀'.1))
    have hcap : ReceiptGap.cap row=Early.bidCap row :=
      (cap_eq row).symm.trans (Concrete05.cap_eq row)
    filter_upwards [hm.eventually (eventually_ge_atTop 4),hrank,
      hm.eventually hcanon,hm.eventually hcanongap,hm.eventually hprefix,
      hpay,hvalues,hpositive] with k hmk hrankk hoptk hgapk hprefixk hpayk hvk hbpos
    have hvk' : w.value k∈Icc vmin vmax:=⟨hvk.1.le,hvk.2.le⟩
    have hopt:=hoptk (E k) (w.value k) hvk'
    have hgap:=hgapk (E k) (w.value k) hvk'
    change CanonicalOptimizer.Optimal (C k) (w.value k) (c k) ∧
      SourceCanonicalOptimizer.leftBid row vmin< c k ∧ c k< w.value k ∧
      0< CanonicalOptimizer.one (C k) (w.value k) (c k) ∧
      c k∈Icc (LowChernoff.physicalFloor row (w.value k))
        (min (w.value k) (ReceiptGap.cap row)) ∧
      ∀a : ℝ,0≤ a→ CanonicalOptimizer.one (C k) (w.value k) a≤
        CanonicalOptimizer.one (C k) (w.value k) (c k) at hopt
    change CanonicalOptimizer.Optimal (C k) (w.value k) (c k) ∧
      0< CanonicalOptimizer.one (C k) (w.value k) (c k) ∧
      c k∈Icc (LowChernoff.physicalFloor row (w.value k))
        (min (w.value k) (ReceiptGap.cap row)) ∧
      SourceOptimizerGap.gapFactor row*CanonicalOptimizer.one (C k) (w.value k) (c k)<
        CanonicalOptimizer.two (eta row) (C k) (R k) (w.value k) (c k)-
          CanonicalOptimizer.one (C k) (w.value k) (c k) at hgap
    have hc0 : 0< c k := by
      have hleft : 0< SourceCanonicalOptimizer.leftBid row vmin := by
        unfold SourceCanonicalOptimizer.leftBid
        linarith
      exact hleft.trans hopt.2.1
    have hcU : c k≤ ReceiptGap.cap row:=hopt.2.2.2.2.1.2.trans (min_le_right _ _)
    have has : (w.action k).bid∈Icc (0:ℝ) (w.value k):=
      ⟨(w.bidMem k).1,(w.bidMem k).2.trans (min_le_left _ _)⟩
    have haU : (w.action k).bid≤ ReceiptGap.cap row := by
      rw [hcap]
      exact (w.bidMem k).2.trans (min_le_right _ _)
    have hps:=Received06.source_pure_subentry_bound row hmk (μ k:Measure (ℝ×ℝ))
      (atoms row (m k) (E k)) hbpos
      (hrankk (w.action k).bid (has.2.trans hvk'.2))
    have hpc:=Received06.source_pure_subentry_bound row hmk (μ k:Measure (ℝ×ℝ))
      (atoms row (m k) (E k)) hc0 (hrankk (c k) (hopt.1.1.2.trans hvk'.2))
    have hCstar : 0≤ C k bstar :=
      (SourceCanonicalRegularity.source_canonical_nonnegative row (m k) (μ k)
        (g row (m k) (E k)) (cm row (m k) (E k)) bstar).1
    have hstar : (vmin-bstar)*C k bstar≤ CanonicalOptimizer.one (C k) (w.value k) (c k) := by
      calc
        (vmin-bstar)*C k bstar≤(w.value k-bstar)*C k bstar :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right hvk'.1 _) hCstar
        _ ≤ CanonicalOptimizer.one (C k) (w.value k) (c k) :=
          hopt.2.2.2.2.2 bstar hbstar0.le
    have hbudget : (1+eta row)*cutoff row*Received06.pureRemainderBound row (m k)<
        SourceOptimizerGap.gapFactor row*CanonicalOptimizer.one (C k) (w.value k) (c k) := by
      have hl:=mul_le_mul_of_nonneg_left hstar (SourceOptimizerGap.gapFactor_pos row).le
      have hpay' : (1+eta row)*cutoff row*Received06.pureRemainderBound row (m k)<
          SourceOptimizerGap.gapFactor row*((vmin-bstar)*C k bstar) := by
        simpa only [Received06.pureRemainderBound,C,μ,m,E,mul_assoc] using hpayk
      exact hpay'.trans_le hl
    have hvsort : w.value k≤ SourcePrefixConstructor.sortEnd row := by
      unfold SourcePrefixConstructor.sortEnd
      linarith [hvk'.2]
    have hfull:=Received06.two_point_full_gap row (m k) (μ k:Measure (ℝ×ℝ))
      (g row (m k) (E k)) (hprefixk (E k)).2.1 (cm row (m k) (E k))
      (w.valueMem k).2 hvsort has hopt.1.1 (hopt.1.2 (w.action k).bid has)
      (Received06.pureRemainderBound_pos row (m k)).le hps.1 hps.2 hpc.2
      (hbudget.trans hgap.2.2.2)
    refine ⟨c k,⟨hc0.le,by simpa only [hcap] using hcU⟩,?_⟩
    have T:=F.positive_counts row (w.market k) (w.identity k)
    rw [T.one_payoff rfl (w.value k) (w.action k) (w.route k) ⟨hbpos,haU⟩,
      T.two_payoff rfl rfl (w.value k) ⟨hc0,hcU⟩]
    exact hfull

end Received05
end FCAppendix.Affine.Uniform07Finishing.Crossover
