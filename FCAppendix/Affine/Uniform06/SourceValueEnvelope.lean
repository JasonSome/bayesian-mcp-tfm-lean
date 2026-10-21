import FCAppendix.Affine.Uniform06.PureEnvelope
import FCAppendix.Affine.Uniform06.LiteralRankIC

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceValueEnvelope

open MeasureTheory Set Filter Topology
open FCAppendix.Affine.Uniform07
open LiteralExperiment LiteralKernelDecomposition LiteralRankIC
open ValueEnvelope

def rightSlope (η U : ℝ) (S D : ℝ → ℝ) (v : ℝ) : ℝ :=
  derivWithin (optimized η U S D) (Ioi v) v

section Scalar
variable {η U : ℝ} {S D : ℝ → ℝ}
variable (hU : 0 ≤ U) (hη : 0 ≤ η)
variable (hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1)
variable (hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b)
include hU hη hS hD

theorem slope_subgradient (v w : ℝ) :
    optimized η U S D v+(w-v)*rightSlope η U S D v ≤ optimized η U S D w :=
  FCAppendix.Subgradient.rightDeriv_subgradient (optimized_convex hU hη hS hD)
    (by simp) (by simp)

theorem slope_monotone : Monotone (rightSlope η U S D) := by
  intro v w hvw
  rcases hvw.eq_or_lt with h | h
  · rw [h]
  · exact FCAppendix.Subgradient.ordered h
      (slope_subgradient hU hη hS hD v w) (slope_subgradient hU hη hS hD w v)

theorem slope_measurable : Measurable (rightSlope η U S D) :=
  (slope_monotone hU hη hS hD).measurable

theorem slope_countable_exceptions : {v | ¬ ContinuousAt (rightSlope η U S D) v}.Countable :=
  (slope_monotone hU hη hS hD).countable_not_continuousAt

theorem all_used_success_eq_slope {v b : ℝ}
    (hcont : ContinuousAt (rightSlope η U S D) v)
    (hb : b ∈ Icc (0:ℝ) U)
    (he : optimized η U S D v=utility η S D v b) :
    S b=rightSlope η U S D v := by
  exact FCAppendix.Subgradient.eq_of_continuousAt (x := v-1) (y := v+1)
    (fun u _ w _ => slope_subgradient hU hη hS hD u w)
    (by constructor <;> linarith)
    (fun w _ => optimized_supporting_line hη hS hD hb he w) hcont

theorem optimized_zero : optimized η U S D 0=0 := by
  apply le_antisymm
  · apply optimized_le hU
    intro b hb
    simpa using utility_upper hη hS hD 0 hb
  · have hz := action_le_optimized hη hS hD 0 (b := 0) ⟨le_rfl,hU⟩
    simpa [utility,Rank.payoff] using hz

theorem optimized_integral {v : ℝ} (hv : 0 ≤ v) :
    optimized η U S D v=∫ w in (0:ℝ)..v, rightSlope η U S D w := by
  have hh := FCAppendix.Subgradient.sub_eq_integral hv
    (fun u (_ : u ∈ Icc (0:ℝ) v) w (_ : w ∈ Icc (0:ℝ) v) =>
      slope_subgradient hU hη hS hD u w)
  simpa only [optimized_zero hU hη hS hD,sub_zero] using hh

end Scalar

theorem original_type_predicate (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {A : Set ℝ} (hA : MeasurableSet A) (hG : ∀ᵐ p ∂G, p.1 ∈ A) :
    ∀ᵐ v ∂volume, v ∈ Icc (0:ℝ) (cutoff i) → v ∈ A := by
  have hh : ∀ᵐ v ∂G.map Prod.fst, v ∈ A :=
    (ae_map_iff measurable_fst.aemeasurable hA).mpr hG
  rw [hvalue,LowChernoff.conditionalValueLaw,ae_iff] at hh
  have hc : ENNReal.ofReal (1/cutoff i) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (one_div_pos.mpr (cutoff_pos i)))
  have hz : (volume.restrict (Icc (0:ℝ) (cutoff i))) {v | v ∉ A}=0 := by
    change ENNReal.ofReal (1/cutoff i)*
      (volume.restrict (Icc (0:ℝ) (cutoff i))) {v | v ∉ A}=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left hc
  exact (ae_restrict_iff' measurableSet_Icc).mp (ae_iff.mpr hz)

theorem original_ae_continuity (i : Row) (G : Measure (ℝ × ℝ))
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    {f : ℝ → ℝ} (hc : {v | ¬ ContinuousAt f v}.Countable) :
    ∀ᵐ p ∂G, ContinuousAt f p.1 := by
  have hm : MeasurableSet {v | ContinuousAt f v} := by
    simpa only [compl_setOf,not_not] using hc.measurableSet.compl
  apply (ae_map_iff measurable_fst.aemeasurable hm).mp
  rw [hvalue,LowChernoff.conditionalValueLaw]
  apply Measure.ae_smul_measure
  have hh : ∀ᵐ v ∂volume, ContinuousAt f v := by
    simpa only [mem_setOf_eq,not_not] using hc.ae_notMem volume
  exact hh.filter_mono (ae_mono Measure.restrict_le_self)

def canonicalFirst (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ))
    (g : GuardData) (margin : (Fin (m-1) → Fin 4) → ℝ) (b : ℝ) : ℝ :=
  2*sourceCanonicalMarginal i m G g margin b-sourceCanonicalDuplicate i m G g margin b

theorem actual_envelope_on_usedSet (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K U : ℝ} (hU : 0 ≤ U)
    (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g K)
    (margin : (Fin (m-1) → Fin 4) → ℝ)
    (hcommon : ∀ᵐ p ∂G, p ∈ usedSet i m G g margin U) :
    ∀ p ∈ usedSet i m G g margin U,
      p.1 < K → p.1 ≤ entry i → p.1 ≤ RankCutoff.Mstar i →
      Rank.payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2)
        (sourceDuplicate i m G g margin p.2) ≤
      (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) p.1+
        p.1*Real.exp (-(9/1000000:ℝ)*m)+p.1*canonicalFirst i m G g margin p.2 := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let S := sourceSuccess i m G g margin
  let D := sourceDuplicate i m G g margin
  let F := optimized (eta i) U S D
  let s := rightSlope (eta i) U S D
  let Q := Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2)
  have hη : 0 ≤ eta i := (eta_pos i).le
  have hS : ∀ b ∈ Icc (0:ℝ) U, S b ∈ Icc (0:ℝ) 1 :=
    fun b _ => (source_first_duplicate_bounds i m G g margin b).1
  have hD : ∀ b ∈ Icc (0:ℝ) U, 0 ≤ D b :=
    fun b _ => (source_first_duplicate_bounds i m G g margin b).2.1
  have hfloor := hcommon.mono fun _ hp => hp.2.2.1.1
  have hsort := usedSet_sorted i hm G hfloor hatom g hg margin U
  have hrank := source_rank_identity_on_usedSet i hm G hvalue hatom g hg margin U hcommon
  have hcanon := source_canonical_first_monotone i m G hfloor g hg margin
  have hsmono : Monotone s := slope_monotone hU hη hS hD
  have hsm : Measurable s := hsmono.measurable
  have hcont := original_ae_continuity i G hvalue (slope_countable_exceptions hU hη hS hD)
  have hQcont : Continuous Q := by
    unfold Q Rank.pureRank Bayes.binomBelow PiBinomial.pmf
    fun_prop
  have hattain : ∀ q ∈ usedSet i m G g margin U, q.1 ≤ entry i →
      F q.1=utility (eta i) S D q.1 q.2 := by
    intro q hq hqe
    have hz := LiteralRankIC.source_floor_zero (i := i) (hqe.trans (by linarith [cutoff_pos i]))
    have hbox := hq.2.2.1
    have hic := hq.2.2.2
    rw [hz] at hbox hic
    exact restricted_IC_attains_common_menu hU hη hS hD hq.1.1 hbox hic
  intro p hp hpK hpe hpM
  have hpB : p.2 ∈ Icc (0:ℝ) K :=
    ⟨hp.2.1.le,(hp.2.2.1.2.trans (min_le_left _ _)).trans hpK.le⟩
  let bound := fun w => 2*Q w+Real.exp (-(9/1000000:ℝ)*m)+canonicalFirst i m G g margin p.2
  let A : Set ℝ := {w | w ∈ Icc (0:ℝ) p.1 → s w ≤ bound w}
  have hbcont : Continuous bound := by dsimp [bound]; fun_prop
  have hA : MeasurableSet A := by
    have he : A=(Icc (0:ℝ) p.1)ᶜ ∪ {w | s w ≤ bound w} := by
      ext w
      simp [A,imp_iff_not_or]
    rw [he]
    exact measurableSet_Icc.compl.union (measurableSet_le hsm hbcont.measurable)
  have hpnull : ∀ᵐ q ∂G, q.1 ≠ p.1 := by
    rw [ae_iff]
    simpa only [not_not] using source_value_level_null i G hvalue p.1
  have hGA : ∀ᵐ q ∂G, q.1 ∈ A := by
    filter_upwards [hcommon,hcont,hpnull] with q hq hqc hqne hqI
    have hqp : q.1 < p.1 := lt_of_le_of_ne hqI.2 hqne
    have hqK : q.1 < K := hqp.trans hpK
    have hqB : q.2 ∈ Icc (0:ℝ) K :=
      ⟨hq.2.1.le,(hq.2.2.1.2.trans (min_le_left _ _)).trans hqK.le⟩
    have horder := hsort q hq hqK p hp hqp
    have hcanonical := hcanon hqB hpB horder
    have hqrank := hrank q hq hqK
    have hpure := PureUnionUpper.source_pure_union_upper i hm (G.map Prod.snd)
      hq.2.1 (hatom q.2) (by rw [hqrank]; exact hqI.2.trans hpM)
    have hs := all_used_success_eq_slope hU hη hS hD hqc
      ⟨hq.2.1.le,hq.2.2.1.2.trans (min_le_right _ _)⟩
      (hattain q hq (hqI.2.trans hpe))
    have hdecomp := source_first_decomposition i m G g hg margin hqB
    rw [hqrank] at hpure
    change s q.1 ≤ bound q.1
    dsimp [bound,canonicalFirst] at ⊢
    change S q.2=s q.1 at hs
    change S q.2=_ at hdecomp
    nlinarith
  have hvol := original_type_predicate i G hvalue hA hGA
  have hae : ∀ᵐ w ∂volume.restrict (Icc (0:ℝ) p.1), s w ≤ bound w := by
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [hvol] with w hw hwI
    exact hw ⟨hwI.1,hwI.2.trans hp.1.2⟩ hwI
  have hsi : IntervalIntegrable s volume 0 p.1 := hsmono.intervalIntegrable
  have hi := intervalIntegral.integral_mono_ae_restrict hp.1.1 hsi (hbcont.intervalIntegrable (μ := volume) 0 p.1) hae
  have hFTC : F p.1=∫ w in (0:ℝ)..p.1,s w := optimized_integral hU hη hS hD hp.1.1
  have he : (∫ w in (0:ℝ)..p.1,bound w)=
      2*(∫ w in (0:ℝ)..p.1,Q w)+p.1*Real.exp (-(9/1000000:ℝ)*m)+
        p.1*canonicalFirst i m G g margin p.2 := by
    have htwo : IntervalIntegrable (fun w => 2*Q w) volume 0 p.1 :=
      (hQcont.const_mul 2).intervalIntegrable 0 p.1
    have hexp : IntervalIntegrable (fun _ : ℝ => Real.exp (-(9/1000000:ℝ)*m)) volume 0 p.1 :=
      intervalIntegrable_const
    have hconst : IntervalIntegrable (fun _ : ℝ => canonicalFirst i m G g margin p.2) volume 0 p.1 :=
      intervalIntegrable_const
    have hsum : IntervalIntegrable (fun w => 2*Q w+Real.exp (-(9/1000000:ℝ)*m)) volume 0 p.1 := by
      convert! htwo.add hexp using 1
    dsimp only [bound]
    rw [intervalIntegral.integral_add hsum hconst,
      intervalIntegral.integral_add htwo hexp,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,
      intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [he,← hFTC,hattain p hp hpe] at hi
  have harea := PureEnvelope.source_rank_area i hm hp.1.1 hpM
  change (∫ w in (0:ℝ)..p.1,Q w) ≤ (20000/(m:ℝ))*Q p.1 at harea
  change Rank.payoff (eta i) p.1 p.2 (S p.2) (D p.2) ≤ _
  dsimp only [utility] at hi
  calc
    _ ≤ 2*(∫ w in (0:ℝ)..p.1,Q w)+p.1*Real.exp (-(9/1000000:ℝ)*m)+
        p.1*canonicalFirst i m G g margin p.2 := hi
    _ ≤ 2*((20000/(m:ℝ))*Q p.1)+p.1*Real.exp (-(9/1000000:ℝ)*m)+
        p.1*canonicalFirst i m G g margin p.2 := by
      gcongr
    _ = _ := by dsimp only [Q]; ring

theorem actual_common_conull_envelope (i : Row) {m : ℕ} (hm : 4 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hatom : ∀ b : ℝ, (G.map Prod.snd) {b}=0)
    (g : GuardData) {K : ℝ} (hg : LiteralPrefixStieltjes.PrefixConditions (xi i) g K)
    (margin : (Fin (m-1) → Fin 4) → ℝ)
    (hmenu : ∀ᵐ p ∂G, p.2 ∈ Icc (LowChernoff.physicalFloor i p.1)
      (min p.1 (ReceiptGap.cap i)))
    (hIC : ∀ᵐ p ∂G, ∀ a ∈ Icc (LowChernoff.physicalFloor i p.1)
      (min p.1 (ReceiptGap.cap i)),
      Rank.payoff (eta i) p.1 a (sourceSuccess i m G g margin a) (sourceDuplicate i m G g margin a) ≤
        Rank.payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2)
          (sourceDuplicate i m G g margin p.2)) :
    ∀ᵐ p ∂G, p.1 < K → p.1 ≤ entry i → p.1 ≤ RankCutoff.Mstar i →
      Rank.payoff (eta i) p.1 p.2 (sourceSuccess i m G g margin p.2)
        (sourceDuplicate i m G g margin p.2) ≤
      (40000/(m:ℝ))*Rank.pureRank (m-1) (capacity m) ((1+cutoff i)/2) p.1+
        p.1*Real.exp (-(9/1000000:ℝ)*m)+p.1*canonicalFirst i m G g margin p.2 := by
  have hc := usedSet_full i m G hvalue hatom g margin (ReceiptGap.cap i) hmenu hIC
  exact hc.mono fun p hp => actual_envelope_on_usedSet i hm G hvalue hatom g
    (ReceiptGap.cap_bounds i).1.le hg margin hc p hp

end FCAppendix.Affine.Uniform06.SourceValueEnvelope
