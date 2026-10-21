import FCAppendix.Affine.Uniform06.RawGoodGeometry
import FCAppendix.Affine.Uniform06.RawCenteredArray

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceCoarseIntegral

open MeasureTheory ProbabilityTheory Set LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment LiteralCoarsePath LiteralCoarseMeasurable
open RawMixedSource RawTiltedSource RawDeficitGeometry RawGoodGeometry
open CoarseIntegralBounds WeightedIntervalLLT

def tiltedC (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b θ : ℝ) : ℝ :=
  ∫ ω : Fin (m-1) → RowRival,
    Real.exp (-θ*deficit i b (capacity m) ω)*
      originalRowMarginal (xi i) (capacity m) g countMargin b ω
        ∂Measure.pi (fun _ => tiltedSource i G b θ)

def tiltedR (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (countMargin : (Fin (m-1) → Fin 4) → ℝ) (b θ : ℝ) : ℝ :=
  ∫ ω : Fin (m-1) → RowRival,
    Real.exp (-θ*deficit i b (capacity m) ω)*
      originalRowDuplicate (xi i) (capacity m) g countMargin b ω
        ∂Measure.pi (fun _ => tiltedSource i G b θ)

def tiltedMoment (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (b θ a : ℝ) (k : ℕ) : ℝ :=
  ∫ ω : Fin (m-1) → RowRival,
    exponentialTest k θ (a*(imbalanceSum ω).natAbs) (deficit i b (capacity m) ω)
      ∂Measure.pi (fun _ => tiltedSource i G b θ)

def equalWindow (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (b θ : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin (m-1) => tiltedSource i G b θ)).real
    {ω | deficit i b (capacity m) ω ∈ Icc (1:ℝ) 2 ∧ imbalanceSum ω=0}

def receiptGap (i : Row) : ℝ := cutoff i/(25*xi i*ReceiptGap.cap i)

theorem receiptGap_pos (i : Row) : 0 < receiptGap i := by
  have hξ := xi_pos i
  have hu := (ReceiptGap.cap_bounds i).1
  exact div_pos (cutoff_pos i) (by positivity)

theorem original_retained_bid_cap (i : Row) (G : Measure (ℝ × ℝ)) {U : ℝ}
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    ∀ᵐ r ∂source i G,r.1=0 → r.2 ≤ U := by
  have hbids : ∀ᵐ z ∂G.map Prod.snd,z ≤ U :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Iic).mpr hcap
  unfold source rivalLaw
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero,ae_add_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    filter_upwards [hbids] with z hz
    exact fun _ => hz
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]

theorem tilted_raw_row_support (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b U : ℝ} (hb : 0 < b) (hU : 0 ≤ U) (hbU : b ≤ U) (θ : ℝ) (N : ℕ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ),
      (∀ k,rowBids b ω k ≤ U) ∧ (∀ j,(ω j).1 ≠ 1) := by
  letI := tiltedSource_probability i G hb θ
  have hraw : ∀ᵐ r ∂tiltedSource i G b θ,r.1=0 → r.2 ≤ U :=
    (tilted_absolutelyContinuous _ _).ae_le (original_retained_bid_cap i G hcap)
  have hno : ∀ᵐ r ∂tiltedSource i G b θ,r.1 ≠ 1 :=
    TiltedGood.tilted_no_active_tag i G b θ
  have hp (j : Fin N) :=
    (measurePreserving_eval (fun _ : Fin N => tiltedSource i G b θ) j).quasiMeasurePreserving.ae
      (hraw.and hno)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  refine ⟨?_,fun j => (hω j).2⟩
  intro k
  refine Fin.cases hbU (fun j => ?_) k
  by_cases hj : (ω j).1=0
  · simpa only [rowBids,Fin.cons_succ,if_pos hj] using (hω j).1 hj
  · simpa only [rowBids,Fin.cons_succ,if_neg hj] using hU

theorem deficit_bounded (i : Row) {b : ℝ} (hb : 0 < b) (c N : ℕ)
    (ω : Fin N → RowRival) : |deficit i b c ω| ≤ (c:ℝ)+(N:ℝ) := by
  have h0 : 0 ≤ FCAppendix.ExponentialTilt.iidSum (demand (xi i) b) N ω :=
    Finset.sum_nonneg (fun j _ => (demand_bounds (xi_pos i) hb (ω j)).1)
  have h1 : FCAppendix.ExponentialTilt.iidSum (demand (xi i) b) N ω ≤ (N:ℝ) := by
    calc
      _ ≤ ∑ _j : Fin N,(1:ℝ) := Finset.sum_le_sum (fun j _ => (demand_bounds (xi_pos i) hb (ω j)).2)
      _ = _ := by simp
  rw [abs_le]
  dsimp [deficit]
  constructor <;> linarith [show (0:ℝ) ≤ c from Nat.cast_nonneg c,show (0:ℝ) ≤ N from Nat.cast_nonneg N]

theorem capacity_centered_error {m : ℕ} (hm : 2 ≤ m) :
    |(capacity m:ℝ)-((m-1:ℕ):ℝ)*rho| ≤ 1 := by
  have hn : 0 < ((m-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
  have hh := PhysicalRates.rival_capacity_density_error hm
  have he : (capacity m:ℝ)/((m-1:ℕ):ℝ)-rho=
      ((capacity m:ℝ)-((m-1:ℕ):ℝ)*rho)/((m-1:ℕ):ℝ) := by field_simp [hn.ne']
  rw [he,abs_div,abs_of_pos hn] at hh
  exact (div_le_div_iff_of_pos_right hn).mp hh

theorem actual_finite_bounds (i : Row) {m : ℕ} (hm : 2 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (countMargin : (Fin (m-1) → Fin 4) → ℝ)
    {b θ lo s ε q : ℝ} (hb : 0 < b) (hθ : 0 < θ) (hlo : 0 < lo)
    (hε : 0 < ε) (hq : 0 < q)
    (hεg : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    (hroot : entry i-cutoff i/200 ≤ g.multiplier) (hradius : g.radius ≤ cutoff i/100)
    (hguardLower : 0 < g.multiplier-g.radius)
    (hlb : lo < b) (hbs : b < s) (hbL : b ≤ g.multiplier)
    (hbU : b ≤ ReceiptGap.cap i)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ ReceiptGap.cap i)
    (hloGuard : (1-xi i)*ReceiptGap.cap i ≤ lo)
    (hpos : ε*((m-1:ℕ):ℝ)+2 < ((m-1:ℕ):ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*((m-1:ℕ):ℝ)+3 ≤ ((m-1:ℕ):ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hstrip : q ≤ (TiltedGood.law i G b θ).real (CostAmplification.activeStrip s (ReceiptGap.cap i)))
    (hεq : 12*ε ≤ q) (hNq : 4 ≤ q*((m-1:ℕ):ℝ))
    (hwindow : 2/((b-lo)*(q*((m-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i)) <
      (b-lo)/(xi i*b)) :
    let A := (b-lo)*(q*((m-1:ℕ):ℝ)/2)/(xi i*ReceiptGap.cap i)
    let bad := 8*Real.exp (-2*((m-1:ℕ):ℝ)*ε^2)
    tiltedC i m G g countMargin b θ ≤ tiltedMoment i m G b θ (receiptGap i) 1/A+bad ∧
    tiltedR i m G g countMargin b θ ≤ tiltedMoment i m G b θ (receiptGap i) 2/A^2+bad ∧
    Real.exp (-2*θ)/(1+b*(m:ℝ)/lo)*(equalWindow i m G b θ-bad) ≤
      tiltedC i m G g countMargin b θ ∧
    sourceCanonicalMarginal i m G g countMargin b=
      Real.exp (-ExactUntilting.cost (source i G) (demand (xi i) b) θ (capacity m) (m-1))*
        tiltedC i m G g countMargin b θ ∧
    sourceCanonicalDuplicate i m G g countMargin b=
      Real.exp (-ExactUntilting.cost (source i G) (demand (xi i) b) θ (capacity m) (m-1))*
        tiltedR i m G g countMargin b θ := by
  let N := m-1
  let μ := Measure.pi (fun _ : Fin N => tiltedSource i G b θ)
  let W := deficit (N := N) i b (capacity m)
  let Y := @imbalanceSum N
  let p := originalRowMarginal (xi i) (capacity m) g countMargin b
  let r := originalRowDuplicate (xi i) (capacity m) g countMargin b
  let Good := RivalGood.good (TiltedGood.law i G b θ) (TiltedGood.statistics s (ReceiptGap.cap i)) N ε
  let A := (b-lo)*(q*(N:ℝ)/2)/(xi i*ReceiptGap.cap i)
  let bad := 8*Real.exp (-2*(N:ℝ)*ε^2)
  have hN : 0 < N := by dsimp [N]; omega
  have hNR : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hξ := xi_pos i
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hU := (ReceiptGap.cap_bounds i).1
  have hA : 0 < A := by dsimp [A]; positivity
  have ha := receiptGap_pos i
  letI := tiltedSource_probability i G hb θ
  letI : IsProbabilityMeasure μ := inferInstance
  have hW : Measurable W := measurable_deficit i b _
  have hY : Measurable Y := measurable_imbalanceSum
  have hmeas := measurable_original_moments hξ hξ1 (capacity m) g countMargin b hεg hM hr hbL
  have hpmeas : Measurable p := hmeas.1
  have hrmeas : Measurable r := hmeas.2
  have hGood : MeasurableSet Good := RivalGood.measurable_good _ _
    (TiltedGood.statistics_measurable s (ReceiptGap.cap i)) N ε
  have hbad : μ.real Goodᶜ ≤ bad := TiltedGood.source_good_complement i G hb θ s
    (ReceiptGap.cap i) hN hε.le
  have hsupport := tilted_raw_row_support i G hb hU.le hbU θ N hcap
  have hpb : ∀ᵐ ω ∂μ,p ω ∈ Icc (0:ℝ) 1 := ae_of_all _ fun ω =>
    (numeric_unit_and_duplicate_le hξ hξ1
      {g with countMargin := countMargin (fun j => (ω j).1)}
      (patternTemplate (capacity m) (fun j => (ω j).1)) (rowBids b ω) 0 hεg hM hr
      (by simpa only [rowBids,Fin.cons_zero] using hbL)).1
  have hrb : ∀ᵐ ω ∂μ,r ω ∈ Icc (0:ℝ) 1 := ae_of_all _ fun ω =>
    (numeric_unit_and_duplicate_le hξ hξ1
      {g with countMargin := countMargin (fun j => (ω j).1)}
      (patternTemplate (capacity m) (fun j => (ω j).1)) (rowBids b ω) 0 hεg hM hr
      (by simpa only [rowBids,Fin.cons_zero] using hbL)).2.1
  have hppos : ∀ᵐ ω ∂μ,0 < p ω → 0 ≤ W ω := by
    filter_upwards [hsupport] with ω hω
    intro hp
    exact (original_positive_implies_raw_deficit i (capacity m) g countMargin hb hbL
      hεg hM hr hroot hradius hguardLower ω hω.1 hp).le
  have hrpos : ∀ᵐ ω ∂μ,0 < r ω → 0 ≤ W ω := by
    filter_upwards [hsupport] with ω hω
    intro hp
    exact (original_duplicate_positive_implies_raw_deficit i (capacity m) g countMargin hb hbL
      hεg hM hr hroot hradius hguardLower ω hω.1 hp).le
  have hgoodBounds : ∀ᵐ ω ∂μ,ω ∈ Good →
      p ω ≤ max 0 (W ω-receiptGap i*((Y ω).natAbs:ℝ))/A ∧
      r ω ≤ (max 0 (W ω-receiptGap i*((Y ω).natAbs:ℝ)))^2/A^2 := by
    filter_upwards [hsupport] with ω hω
    intro hg
    have hgeom := source_good_geometry i G hb θ s (ReceiptGap.cap i) hN hε.le hq
      (capacity_centered_error hm) hpos hroom hstrip hεq hNq ω hω.2 hg
    have hh := numeric_moments_from_active_strip i
      {g with countMargin := countMargin (fun j => (ω j).1)}
      (patternTemplate (capacity m) (fun j => (ω j).1)) (rowBids b ω)
      (stripSet s (ReceiptGap.cap i) ω) 0 hlo (by positivity : 0 < q*(N:ℝ)/2)
      hεg hM hr hroot hradius hguardLower (focal_mem_patternTemplate _ _)
      (by simpa only [rowBids,Fin.cons_zero] using hlb)
      (by simpa only [rowBids,Fin.cons_zero] using hbL) hω.1
      (rowBids_outside _ _ _) hloGuard
      (by simpa only [rowBids,Fin.cons_zero] using stripSet_bids hbs ω) hgeom.2.2.2
    rw [hgeom.2.1,hgeom.2.2.1] at hh
    simpa only [receiptGap,A,W,Y,p,r,originalRowMarginal,
      originalRowDuplicate,rowBids,Fin.cons_zero] using hh
  have hwb : ∀ᵐ ω ∂μ,|W ω| ≤ (capacity m:ℝ)+(N:ℝ) :=
    ae_of_all _ fun ω => deficit_bounded i hb (capacity m) N ω
  have hfirst := tilted_kernel_upper μ hW hY hpmeas hθ ha.le hA
    (by positivity : 0 ≤ (capacity m:ℝ)+(N:ℝ)) hwb hpb hppos Good hGood 1 (by norm_num)
    (hgoodBounds.mono fun ω hh hg => by simpa only [pow_one] using (hh hg).1)
  have hsecond := tilted_kernel_upper μ hW hY hrmeas hθ ha.le (sq_pos_of_pos hA)
    (by positivity : 0 ≤ (capacity m:ℝ)+(N:ℝ)) hwb hrb hrpos Good hGood 2 (by norm_num)
    (hgoodBounds.mono fun ω hh hg => (hh hg).2)
  have hden : 0 < 1+b*(m:ℝ)/lo := by positivity
  have hlower := tilted_kernel_lower_window μ hW hY hpmeas hθ.le
    (by positivity : 0 ≤ 1/(1+b*(m:ℝ)/lo)) hpb hppos Good hGood (by
      filter_upwards [hsupport] with ω hω
      intro hg hy hw
      have hgeom := source_good_geometry i G hb θ s (ReceiptGap.cap i) hN hε.le hq
        (capacity_centered_error hm) hpos hroom hstrip hεq hNq ω hω.2 hg
      have hequal := equal_residuals_of_zero_sign (capacity m) ω hy
      have hd0 : imbalance (patternTemplate (capacity m) (fun j => (ω j).1))=0 := by
        simp [imbalance,small,hequal]
      have hh := equal_window_lower_from_strip hξ hξ1 hlo hU
        (by positivity : 0 < q*(N:ℝ)/2)
        {g with countMargin := countMargin (fun j => (ω j).1)}
        (patternTemplate (capacity m) (fun j => (ω j).1)) (rowBids b ω)
        (stripSet s (ReceiptGap.cap i) ω) 0 hequal (focal_mem_patternTemplate _ _)
        (by simpa only [rowBids,Fin.cons_zero] using hlb) hω.1 (rowBids_outside _ _ _)
        hloGuard (by simpa only [rowBids,Fin.cons_zero] using stripSet_bids hbs ω)
        (by simpa only [hd0,Nat.cast_zero,sub_zero] using hgeom.2.2.2)
        (by rwa [hgeom.2.1])
        (by simpa only [rowBids,Fin.cons_zero] using hwindow)
      have hNm : N+1=m := by dsimp [N]; omega
      simpa only [Fintype.card_fin,hNm,rowBids,Fin.cons_zero,p,originalRowMarginal] using hh)
  have hlower' : Real.exp (-2*θ)/(1+b*(m:ℝ)/lo)*
      (equalWindow i m G b θ-bad) ≤ tiltedC i m G g countMargin b θ := by
    have hm1 : 0 ≤ Real.exp (-2*θ)/(1+b*(m:ℝ)/lo) := by positivity
    have he : Real.exp (-θ*(2:ℝ))*(1/(1+b*(m:ℝ)/lo))=
        Real.exp (-2*θ)/(1+b*(m:ℝ)/lo) := by rw [show -θ*2=-2*θ by ring]; ring
    rw [he] at hlower
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hbad _) hm1).trans hlower
  refine ⟨hfirst.trans (add_le_add le_rfl hbad),
    hsecond.trans (add_le_add le_rfl hbad),hlower',?_,?_⟩
  · exact source_canonical_marginal_untilt i m G g countMargin hb θ
  · exact source_canonical_duplicate_untilt i m G g countMargin hb θ

end FCAppendix.Affine.Uniform06.SourceCoarseIntegral
