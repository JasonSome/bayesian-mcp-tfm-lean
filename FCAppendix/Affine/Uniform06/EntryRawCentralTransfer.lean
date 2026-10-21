import FCAppendix.Affine.Uniform06.EntryRawGoodMoments
import FCAppendix.Affine.Uniform06.EntryResponseTransfer

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawCentralTransfer

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open EntryRawCentral EntryRawGoodMoments EntryEarlySourceLimits
open scoped BigOperators

lemma finite_root_displacement {N : ℕ} {ξ b K D p Λ c : ℝ}
    (hN : 0 < N) (hξ : 0 < ξ) (hb : 0 < b) (hc : 0 < c)
    (hK : c*(N:ℝ) ≤ K) (hp : p=max D 0/(1+b*K))
    (hprice : Λ=b*(1-ξ*p)) :
    0 ≤ b-Λ ∧ b-Λ ≤ (ξ/c)*max D 0/(N:ℝ) := by
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  have hKp : 0 < K := (mul_pos hc hNr).trans_le hK
  have hd : 0 < 1+b*K := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hdisp : b-Λ=ξ*b*(max D 0)/(1+b*K) := by rw [hprice,hp]; ring
  rw [hdisp]
  constructor
  · positivity
  · have hfirst : ξ*b*(max D 0)/(1+b*K) ≤ ξ*(max D 0)/K := by
      apply (div_le_div_iff₀ hd hKp).mpr
      nlinarith [mul_nonneg hξ.le (le_max_right D 0)]
    have hsecond := div_le_div_of_nonneg_left (mul_nonneg hξ.le (le_max_right D 0))
      (mul_pos hc hNr) hK
    exact hfirst.trans (hsecond.trans_eq (by ring))

theorem raw_deficit_memLp (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {N : ℕ} (hN : 0 < N) (C : ℕ) {b : ℝ} (hb : 0 < b) (l c hstar : ℝ)
    (hhstar : 0 ≤ hstar) (k : ENNReal) :
    MemLp (fun x => max (deficit i C b l c hstar x) 0/Real.sqrt (N:ℝ)) k
      (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) := by
  have hr := Real.sqrt_pos.mpr (show (0:ℝ)< N by exact_mod_cast hN)
  apply MemLp.of_bound
    (((measurable_deficit i N C b l c hstar).max measurable_const).div_const _).aestronglyMeasurable
    ((C:ℝ)/Real.sqrt (N:ℝ))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (le_max_right _ _) hr.le)]
    exact div_le_div_of_nonneg_right
      (max_le (deficit_le_capacity i C hb l c hhstar x) (Nat.cast_nonneg C)) hr.le

theorem raw_deficit_fourth (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {N : ℕ} (hN : 0 < N) (C : ℕ) {b : ℝ} (hb : 0 < b) (l c hstar : ℝ)
    (hhstar : 0 ≤ hstar) :
    (∫ x, (max (deficit i C b l c hstar x) 0/Real.sqrt (N:ℝ))^4
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) ≤
      8*(center i G N C b)^4+16*FCAppendix.Probability.gaussianMomentConstant 4 2 := by
  let μ := RawMixedSource.source i G
  let P := EntryIIDCentral.rowLaw μ N
  let C0 := RawMixedSource.centered i G b
  let A := fun j : Fin N => EntryIIDCentral.array N C0 j 0
  let S := fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
    selected i b l c hstar x/Real.sqrt (N:ℝ)
  have hCm := RawMixedSource.centered_measurable i G b
  have hA j : Measurable (A j) := EntryIIDCentral.measurable_array hCm j 0
  have hAb j : ∀ᵐ x ∂P, |A j x| ≤ 1 :=
    (EntryIIDCentral.eval_preserving μ N j).quasiMeasurePreserving.ae
      (Eventually.of_forall ((RawMixedSource.centered_bounds_and_mean i G hb).1 0))
  have hAz j : (∫ x, A j x ∂P)=0 := EntryIIDCentral.array_mean_zero μ hCm
    (RawMixedSource.centered_bounds_and_mean i G hb).2 j 0
  have hAi : iIndepFun A P := EntryIIDCentral.scalar_array_independent μ hCm 0
  have hSm : Measurable S := (measurable_selected i N b l c hstar).div_const _
  have hSn : ∀ᵐ x ∂P, 0 ≤ S x := Eventually.of_forall fun x =>
    div_nonneg (selected_nonneg i hb l c hhstar x) (Real.sqrt_nonneg _)
  have hh := EntryUI.actual_normalized_deficit_fourth_bound P hN A hA hAb hAz hAi
    S hSm hSn (center i G N C b)
  have he x : max (center i G N C b-EntryUI.normalizedSum A x-S x) 0=
      max (deficit i C b l c hstar x) 0/Real.sqrt (N:ℝ) := by
    have hp := positive_deficit_identity i G hN C b l c hstar x
    have hstat : EntryIIDCentral.statistic (RawMixedSource.centered i G b) (rawWeight i l) (rawH i b)
        (focalWeight i b l) (1/2) c hstar (focalWeight_bounds i b l) (rawWeight_bounds i l)
        RawMixedSource.draws x=EntryUI.normalizedSum A x+S x := by rfl
    rw [hstat] at hp
    convert! hp using 1
    congr 1
    ring
  simpa only [he] using hh.2

section Source
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem central_deficit_per_rival (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hbt : ∀ m, b m ≤ cutoff i)
    (hlp : ∀ m, 0 < l m) (hb : Tendsto b atTop (𝓝 (entry i)))
    (hl : Tendsto l atTop (𝓝 (entry i)))
    (N C : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m)) (N m) (C m) (b m)) atTop (𝓝 z)) :
    Tendsto (fun m => ∫ x, max (deficit i (C m) (b m) (l m)
      (eligibleMass μ i V/2) (eligibleHMean μ i V) x) 0/(N m:ℝ)
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)) atTop (𝓝 0) := by
  have hfirst := (raw_central_moments μ i V B hV hB hvalue hadmissible hactive b l hbp hbt hlp
    hb hl N C hNp hN hcentral).2.1
  have hNr : Tendsto (fun m => (N m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hsi := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hNr)
  have hh := hfirst.mul hsi
  have hid (m : ℕ) (x : EntryIIDCentral.Row (Ω := RowRival) (N m)) :
      max (deficit i (C m) (b m) (l m) (eligibleMass μ i V/2) (eligibleHMean μ i V) x) 0/(N m:ℝ)=
      (max (deficit i (C m) (b m) (l m) (eligibleMass μ i V/2) (eligibleHMean μ i V) x) 0/
        Real.sqrt (N m:ℝ))*(Real.sqrt (N m:ℝ))⁻¹ := by
    have hr := Real.sqrt_pos.mpr (show (0:ℝ)< N m by exact_mod_cast hNp m)
    field_simp [hr.ne',(show (N m:ℝ)≠0 by exact_mod_cast Nat.ne_of_gt (hNp m))]
    rw [Real.sq_sqrt (Nat.cast_nonneg (N m))]
  simp_rw [hid,integral_mul_const]
  simpa only [mul_zero,Function.comp_def,eligibleHMean] using! hh

theorem central_root_displacement (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hbt : ∀ m, b m ≤ cutoff i)
    (hlp : ∀ m, 0 < l m) (hb : Tendsto b atTop (𝓝 (entry i)))
    (hl : Tendsto l atTop (𝓝 (entry i)))
    (N C : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m)) (N m) (C m) (b m)) atTop (𝓝 z))
    (Λ : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ)
    (hΛm : ∀ m, Measurable (Λ m)) {A : ℝ} (_hA : 0 ≤ A)
    (hfinite : ∀ m x, 0 ≤ b m-Λ m x ∧ b m-Λ m x ≤ A*
      max (deficit i (C m) (b m) (l m) (eligibleMass μ i V/2) (eligibleHMean μ i V) x) 0/(N m:ℝ)) :
    Tendsto (fun m => ∫ x, b m-Λ m x
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)) atTop (𝓝 0) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) := Measure.isProbabilityMeasure_map
    (hV.prodMk (hB m)).aemeasurable
  have hh := (central_deficit_per_rival μ i V B hV hB hvalue hadmissible hactive
    b l hbp hbt hlp hb hl N C hNp hN hcentral).const_mul A
  apply squeeze_zero (fun m => integral_nonneg fun x => (hfinite m x).1) (fun m => ?_)
    (by simpa only [mul_zero] using hh)
  let D := fun x : EntryIIDCentral.Row (Ω := RowRival) (N m) => max (deficit i (C m) (b m) (l m) (eligibleMass μ i V/2)
    (eligibleHMean μ i V) x) 0
  have hDp := eligibleHMean_positive μ i V hV hvalue
  have hDm : Measurable D := (measurable_deficit i (N m) (C m) (b m) (l m)
    (eligibleMass μ i V/2) (eligibleHMean μ i V)).max measurable_const
  have hDi : Integrable D (EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)) :=
    Integrable.of_mem_Icc 0 (C m:ℝ) hDm.aemeasurable (Eventually.of_forall fun x =>
      ⟨le_max_right _ _,max_le (deficit_le_capacity i (C m) (hbp m) (l m)
        (eligibleMass μ i V/2) hDp.le x) (Nat.cast_nonneg _)⟩)
  have hLi : Integrable (fun x => b m-Λ m x)
      (EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)) := by
    apply Integrable.mono' ((hDi.const_mul A).div_const (N m:ℝ))
      (measurable_const.sub (hΛm m)).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (hfinite m x).1]
      exact (hfinite m x).2
  have hi := integral_mono hLi ((hDi.const_mul A).div_const (N m:ℝ)) (fun x => (hfinite m x).2)
  simpa only [integral_div,integral_const_mul,mul_div_assoc] using hi

end Source
end FCAppendix.Affine.Uniform06.EntryRawCentralTransfer
