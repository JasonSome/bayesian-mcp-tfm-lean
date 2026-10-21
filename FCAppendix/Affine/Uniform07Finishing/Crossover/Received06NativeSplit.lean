import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06NativeCore
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06Errors

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Uniform06.LiteralPureComponents
open Uniform06.PureRankCounts Uniform06.SharpPureDerivative Physical Received05

theorem source_rare_factor (m : ℕ) : LiteralLowDuplicate.pureRare m=
    Real.exp (-(6/1000000:ℝ)*(m:ℝ))*Real.exp (-(3/1000000:ℝ)*(m:ℝ)) := by
  rw [←Real.exp_add]
  unfold LiteralLowDuplicate.pureRare
  congr 1
  ring

theorem source_large_band_below_Mstar (row : Uniform07.Row) :
    SourcePrefixConstructor.crossoverEnd row≤ RankCutoff.Mstar row := by
  have ht:=Uniform07.cutoff_pos row
  unfold SourcePrefixConstructor.crossoverEnd RankCutoff.Mstar Uniform07.entry
  linarith

theorem source_pivotal_lower_of_boundary {row : Uniform07.Row} {m : ℕ}
    (hm : 2≤ m) (w : ℝ)
    (h : (1/20000:ℝ)*Real.exp (-(3/1000000:ℝ)*(m:ℝ))≤
      PiBinomial.pmf (m-2) ((1+Uniform07.cutoff row)/2-w) (Uniform07.capacity m-1)) :
    (m:ℝ)/40000*Real.exp (-(3/1000000:ℝ)*(m:ℝ))≤ rankSlope row m w := by
  have hN : (m:ℝ)/2≤(m-1:ℕ) := by
    rw [Nat.cast_sub (by omega : 1≤ m),Nat.cast_one]
    have hmR : (2:ℝ)≤ m:=by exact_mod_cast hm
    linarith
  have hfirst:=mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (m-1))
  have hsecond:=mul_le_mul_of_nonneg_right hN
    (show 0≤(1/20000:ℝ)*Real.exp (-(3/1000000:ℝ)*(m:ℝ)) by positivity)
  unfold rankSlope
  nlinarith only [hfirst,hsecond]

theorem eventually_native_split (F : BroadcastLowerFamily) (row : Uniform07.Row) :
    ∀ᶠk in atTop,∀i : Fin (F.start+k),Nonempty
      (PureDerivativeBounds06 (F.toReadyLowerFamily.market row k).native i (crossoverEvent F row k i)
        (Uniform07.cutoff row) (sourceCrossoverStart row) (sourceCrossoverEnd row)
        (receivedSuccessError row (F.start+k)) (receivedDuplicateError row (F.start+k))) := by
  have ht:=tail_population_tendsto F.start
  have hprefix:=SourceEarlyFamily.eventually_source_prefix (G row) (g row) (cm row) row
    (earlyMenu row) (roots row).literal (roots row).rejection
  have hvalue:=(Classical.choose_spec (eventually_source_pure_union_relative row)).2
  have hder:=(Classical.choose_spec (eventually_source_derivative_bounds row)).2
  have hsource:=(eventually_received_band_ac row).and
    ((eventually_received_crossover_rank_ceiling row).and
      (hprefix.and (hvalue.and (hder.and
        ((eventually_received_pure_duplicate_derivative row).and
          ((source_boundary_mass_lower row).and
            ((SourceRankRates.eventually_Lm_lower row).and (eventually_ge_atTop (4:ℕ)))))))))
  filter_upwards [ht.eventually hsource] with k hk
  rcases hk with ⟨hac,hceil,hprefix,hvalue,hder,hDD,hmass,hLm,hm⟩
  intro i
  let M:=F.toReadyLowerFamily.market row k
  let μ:=G row (F.start+k) (F.law row k)
  let μb:=(μ : Measure (ℝ×ℝ)).map Prod.snd
  let g₀:=g row (F.start+k) (F.law row k)
  let cm₀:=cm row (F.start+k) (F.law row k)
  let B:=crossoverEvent F row k i
  let q₀:=fun b=>comparisonMarginal M.native i B (Uniform07.cutoff row) b
  let M₀:=PureRankCounts.sourceRank (Uniform07.cutoff row) μb
  let Q:=fun b=>pureRank (F.start+k) (Uniform07.capacity (F.start+k)) (Uniform07.cutoff row) (M₀ b)
  let SP:=sourcePureSuccess row (F.start+k) μ
  let DP:=sourcePureDuplicate row (F.start+k) μ
  let E₀:=Real.exp (-(3/1000000:ℝ)*((F.start+k:ℕ):ℝ))
  let r₀:=Real.exp (-(6/1000000:ℝ)*((F.start+k:ℕ):ℝ))
  letI : IsProbabilityMeasure μb:=Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hgeo:=source_crossover_geometry row
  have hH:=hgeo.2.2.1.le
  have hLR:=(source_crossover_end_gt_start row).le
  have hp : LiteralPrefixStieltjes.PrefixConditions (Uniform07.xi row) g₀
      (SourcePrefixConstructor.crossoverEnd row) :=
    LowRankMeasures.PrefixConditions.mono (hprefix (F.law row k)).2.1 hgeo.2.2.2.2
  have hmR : (0:ℝ)< ((F.start+k:ℕ):ℝ):=Nat.cast_pos.mpr (by omega)
  have hE : 0< E₀:=Real.exp_pos _
  have hr : 0≤ r₀:=(Real.exp_pos _).le
  have hK:=lowRankConstant_nonnegative row
  have hlarge {b : ℝ} (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      b∈Icc (sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row):=
    ⟨hb.1,hb.2.trans hgeo.2.2.2.1.le⟩
  have hpositive {b : ℝ} (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      b∈Ioc (0:ℝ) (SourcePrefixConstructor.crossoverEnd row):=
    ⟨hgeo.1.trans_le hb.1,(hlarge hb).2⟩
  have hEQ (b : ℝ) : E₀≤ Q b := by
    have hq:=PureRankProbability.unilateral_le_pureRank (Uniform07.cutoff_pos row).le
      (Uniform07.cutoff_lt_one row) μb b (F.start+k-1) (Uniform07.capacity (F.start+k))
    exact (show E₀≤ SourceRankRates.Lm row (F.start+k) by
      simpa only [E₀,neg_mul,mul_neg,mul_comm] using! hLm).trans hq
  have hQq (b : ℝ) : Q b≤ q₀ b := by
    have hc:=actual_canonical_probability_bounds M.native i B b
    have hn : 0≤ canonicalMarginal M.native i B b:=hc.1.trans hc.2
    dsimp only [q₀,comparisonMarginal,Q]
    rw [native_rank_eq]
    exact le_add_of_nonneg_right hn
  have hq (b : ℝ) : 0≤ q₀ b:=hE.le.trans ((hEQ b).trans (hQq b))
  have hP (b : ℝ) (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      ((F.start+k:ℕ):ℝ)/40000*E₀≤ rankSlope row (F.start+k) (M₀ b) :=
    source_pivotal_lower_of_boundary (by omega) (M₀ b)
      (hmass μb inferInstance b (hceil (F.law row k) b (hlarge hb).2))
  have hD (b : ℝ) (hb : b∈Icc (sourceCrossoverStart row) (sourceCrossoverEnd row)) :
      DP b∈Icc (0:ℝ) (r₀*E₀) := by
    have hh:=source_pure_duplicate_nonnegative_le_rare row hm μ
      (value row (F.start+k) (F.law row k))
      ((permitted row (F.start+k) (F.law row k)).mono (fun _ h=>h.1))
      (hpositive hb).1 ((hlarge hb).2.trans (source_large_band_below_Mstar row))
    simpa only [source_rare_factor,E₀,r₀,Set.mem_Icc,DP] using! hh
  have hzeroD (b : ℝ) : (0:ℝ)∈Icc (0:ℝ) (((F.start+k:ℕ):ℝ)*(r₀*E₀)*(0+lowRankConstant row)) :=
    ⟨le_rfl,by positivity⟩
  refine ⟨{successValue:=?_,duplicateValue:=?_,derivatives:=?_}⟩
  · intro b hb
    rw [(native_errors_eq F row k i hp (hpositive hb)).1]
    have hh:=hvalue μb inferInstance b (hpositive hb).1 (atoms row _ (F.law row k) b)
      (hceil (F.law row k) b (hlarge hb).2)
    have hh' : |SP b-2*Q b|≤ pureValueError row (F.start+k)*Q b:=hh
    exact hh'.trans ((mul_le_mul_of_nonneg_left (hQq b)
      (by unfold pureValueError; positivity)).trans
        (mul_le_mul_of_nonneg_right (pureValueError_le_received row _) (hq b)))
  · intro b hb
    rw [(native_errors_eq F row k i hp (hpositive hb)).2]
    exact (normalize_pure_duplicate hmR hK hE hr (hEQ b) (hQq b) (hP b hb)
      (by norm_num : (0:ℝ)≤ 0) (hD b hb) (hzeroD b)).1
  · have hhac:=hac (F.law row k)
    have hcommon:=StieltjesAnalytic.common_derivatives_of_three_AC
      hhac.rank hhac.pureSuccess hhac.pureDuplicate
    have hne : ∀ᵐb∂(volume : Measure ℝ),b≠sourceCrossoverStart row:=by rw [ae_iff]; simp
    filter_upwards [hcommon,hne] with b hb hne hbI
    have hb' : b∈Ioo (sourceCrossoverStart row) (SourcePrefixConstructor.crossoverEnd row):=
      ⟨lt_of_le_of_ne hbI.1 (Ne.symm hne),hbI.2.trans_lt hgeo.2.2.2.1⟩
    have hd:=hb (by simpa only [uIcc_of_le hH] using hlarge hbI)
    have hM : HasDerivAt M₀ (deriv M₀ b) b:=hd.1
    have hSP : HasDerivAt SP (deriv SP b) b:=hd.2.1
    have hDP : HasDerivAt DP (deriv DP b) b:=hd.2.2
    have hcap : ∀ᵐz∂μb,z≤ ReceiptGap.cap row:=by
      apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Iic).mpr
      exact (permitted row _ (F.law row k)).mono (fun _ h=>h.2.trans (min_le_right _ _))
    have hs:=hder μb inferInstance hcap (atoms row _ (F.law row k))
      (SourcePrefixConstructor.crossoverEnd row) (hceil (F.law row k))
      b (deriv M₀ b) (deriv SP b) (hpositive hbI).1
      (hgeo.2.1.trans_le hbI.1) hb'.2 hM hSP
    have hdd:=hDD (F.law row k) b (deriv M₀ b) (deriv DP b) hb' hM hDP
    have hdd' : deriv DP b∈Icc (0:ℝ)
        (((F.start+k:ℕ):ℝ)*(r₀*E₀)*(deriv M₀ b+lowRankConstant row)) := by
      simpa only [source_rare_factor,E₀,r₀,Set.mem_Icc] using! hdd
    have hn:=normalize_pure_duplicate hmR hK hE hr (hEQ b) (hQq b) (hP b hbI) hs.1 (hD b hbI) hdd'
    have hQ : HasDerivAt Q (rankSlope row (F.start+k) (M₀ b)*deriv M₀ b) b:=
      (source_rank_polynomial_derivative row hm (M₀ b)).comp b hM
    have hidS : successError M.native i B (Uniform07.cutoff row)=ᶠ[𝓝 b]
        (fun x=>SP x-2*Q x) := by
      filter_upwards [Ioo_mem_nhds (hpositive hbI).1 hb'.2] with x hx
      exact (native_errors_eq F row k i hp ⟨hx.1,hx.2.le⟩).1
    have hidD : duplicateError M.native i B=ᶠ[𝓝 b] DP := by
      filter_upwards [Ioo_mem_nhds (hpositive hbI).1 hb'.2] with x hx
      exact (native_errors_eq F row k i hp ⟨hx.1,hx.2.le⟩).2
    have hSerr:=(hSP.sub (hQ.const_mul 2)).congr_of_eventuallyEq hidS
    have hDerr:=hDP.congr_of_eventuallyEq hidD
    have hflow : physicalFlow M.native (Uniform07.cutoff row) b=
        rankSlope row (F.start+k) (M₀ b)*deriv M₀ b := by
      unfold physicalFlow
      rw [native_rank_eq,(source_rank_polynomial_derivative row hm (M₀ b)).deriv]
    have hflow0 : 0≤ rankSlope row (F.start+k) (M₀ b)*deriv M₀ b:=mul_nonneg hs.2.1.le hs.1
    constructor
    · rw [hSerr.deriv,hflow]
      have he:=mul_le_mul_of_nonneg_right (pureDerivativeError_le_received row (F.start+k)) hflow0
      have hextra : 0≤ receivedDuplicateError row (F.start+k)*
          ((rankSlope row (F.start+k) (M₀ b)*deriv M₀ b)/((F.start+k:ℕ):ℝ)+q₀ b):=
        mul_nonneg (receivedDuplicateError_nonnegative row _) (add_nonneg (div_nonneg hflow0 hmR.le) (hq b))
      have hs' : |deriv SP b-2*(rankSlope row (F.start+k) (M₀ b)*deriv M₀ b)|≤
          (2*SharpPureDerivative.relativeError (pureDerivativeRate row) (F.start+k))*
            (rankSlope row (F.start+k) (M₀ b)*deriv M₀ b) := by
        have hs0 : |deriv SP b-2*rankSlope row (F.start+k) (M₀ b)*deriv M₀ b|≤
            2*rankSlope row (F.start+k) (M₀ b)*deriv M₀ b*
              SharpPureDerivative.relativeError (pureDerivativeRate row) (F.start+k) := hs.2.2
        calc
          |deriv SP b-2*(rankSlope row (F.start+k) (M₀ b)*deriv M₀ b)|=
              |deriv SP b-2*rankSlope row (F.start+k) (M₀ b)*deriv M₀ b| := by
            rw [mul_assoc]
          _≤_:=hs0
          _=_:=by ring
      exact (hs'.trans he).trans (le_add_of_nonneg_right hextra)
    · rw [hDerr.deriv,hflow]
      exact hn.2

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
