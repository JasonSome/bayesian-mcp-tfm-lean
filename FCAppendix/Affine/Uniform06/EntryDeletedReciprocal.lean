import FCAppendix.Affine.Uniform06.EntryReciprocalLimit
import FCAppendix.Affine.Uniform06.EntryRawGoodMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryDeletedReciprocal

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.WeightedSampling
open EntryReciprocalLimit EntryEarlySourceLimits ReciprocalSecantBounds
open scoped BigOperators

def listBids {N : ℕ} (focal : ℝ) (r : Fin N → RowRival) : Fin (N+1) → ℝ :=
  Fin.cons focal (fun j => maskedRawBid (r j))

lemma measurable_listBids (N : ℕ) (focal : ℝ) : Measurable (listBids (N := N) focal) := by
  have hm : Measurable maskedRawBid := by
    exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_snd measurable_const
  apply measurable_pi_lambda
  intro j
  refine Fin.cases measurable_const (fun j => ?_) j
  exact hm.comp (measurable_pi_apply j)

lemma measurable_reciprocalSum {Ξ ι : Type*} [MeasurableSpace Ξ] [Fintype ι] [DecidableEq ι]
    {B : Ξ → ι → ℝ} {E : Ξ → Finset ι} (hB : Measurable B) (hE : Measurable E) (z : ℝ) :
    Measurable (fun x => reciprocalSum (B x) (E x) z) := by
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite ((Set.to_countable {s : Finset ι | j ∈ s}).measurableSet.preimage hE)
    measurable_const (measurable_reciprocalTerm ((measurable_pi_apply j).comp hB) z)

def normalized {N : ℕ} (focal z : ℝ) (w : (Fin N → RowRival) → Weights (Fin (N+1)))
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  reciprocalSum (listBids focal x.1) (removed w RawMixedSource.draws x) z/(N:ℝ)

lemma measurable_normalized {N : ℕ} (focal z : ℝ)
    {w : (Fin N → RowRival) → Weights (Fin (N+1))} (hw : Measurable w) :
    Measurable (normalized focal z w) :=
  (measurable_reciprocalSum ((measurable_listBids N focal).comp measurable_fst)
    (measurable_removed hw (RawMixedSource.measurable_draws N)) z).div_const _

lemma normalized_bounds {N : ℕ} (hN : 0 < N) (focal z : ℝ)
    (w : (Fin N → RowRival) → Weights (Fin (N+1))) {lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    normalized focal z w x ∈ Icc (0:ℝ) (2/lo) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hzp := hlo.trans_le hz
  constructor
  · exact div_nonneg (reciprocalSum_nonneg _ _ hzp) hNp.le
  · have hs := reciprocalSum_le (listBids focal x.1) (removed w RawMixedSource.draws x) hzp
    simp only [Fintype.card_fin,Nat.cast_add_one] at hs
    have hh := div_le_div_of_nonneg_right hs hNp.le
    change normalized focal z w x ≤ ((N:ℝ)+1)/z/(N:ℝ) at hh
    apply hh.trans
    have hi := div_le_div_of_nonneg_left (show 0 ≤ (N:ℝ)+1 by positivity) hlo hz
    apply (div_le_div_of_nonneg_right hi hNp.le).trans
    apply (div_le_iff₀ hNp).mpr
    apply (div_le_iff₀ hlo).mpr
    have he : (2/lo)*(N:ℝ)*lo=2*(N:ℝ) := by
      field_simp [hlo.ne']
    rw [he]
    linarith

theorem normalized_error_bound {N : ℕ} (hN : 0 < N) (focal z κ : ℝ)
    (w : (Fin N → RowRival) → Weights (Fin (N+1))) {lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    |normalized focal z w x-κ| ≤
      |EntryEmpiricalRatio.empirical (rawReciprocal z) N x.1-κ|+
        ((RawMixedSource.draws x.1:ℝ)+1)/(lo*(N:ℝ)) :=
  focal_deletion_empirical_bound hN x.1 focal z lo κ hlo hz
    (removed w RawMixedSource.draws x) (removed_card_le w RawMixedSource.draws x)

theorem normalized_integral_error (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {N : ℕ} (hN : 0 < N) (focal z κ : ℝ)
    (w : (Fin N → RowRival) → Weights (Fin (N+1))) (hw : Measurable w)
    {lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) :
    (∫ x, |normalized focal z w x-κ| ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) ≤
      (∫ r, |EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ|
        ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G))+
      (1/lo)*((∫ r, (RawMixedSource.draws r:ℝ)/(N:ℝ)
        ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G))+1/(N:ℝ)) := by
  let Q := Measure.pi (fun _ : Fin N => RawMixedSource.source i G)
  let P := EntryIIDCentral.rowLaw (RawMixedSource.source i G) N
  have hproj : MeasurePreserving Prod.fst P Q := measurePreserving_fst
  have hF : Integrable (fun x => |normalized focal z w x-κ|) P := by
    apply Integrable.of_bound (f := fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      |normalized focal z w x-κ|) (μ := P)
      ((measurable_normalized focal z hw).sub_const κ).abs.aestronglyMeasurable
      (2/lo+|κ|)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have hb : |normalized focal z w x| ≤ 2/lo := by
        rw [abs_of_nonneg (normalized_bounds hN focal z w hlo hz x).1]
        exact (normalized_bounds hN focal z w hlo hz x).2
      exact (abs_sub _ _).trans (add_le_add hb le_rfl)
  have hEi := (EntryEmpiricalRatio.integrable_empirical (RawMixedSource.source i G)
    (measurable_rawReciprocal z) (inv_nonneg.mpr hlo.le)
    (Eventually.of_forall (rawReciprocal_bound hlo hz)) N).sub (integrable_const κ)
  have hDm : Measurable (fun r : Fin N → RowRival => (RawMixedSource.draws r:ℝ)/(N:ℝ)) :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      (RawMixedSource.measurable_draws N)).div_const _
  have hDi : Integrable (fun r : Fin N → RowRival => (RawMixedSource.draws r:ℝ)/(N:ℝ)) Q := by
    apply Integrable.of_mem_Icc 0 1 hDm.aemeasurable
    exact Eventually.of_forall fun r => ⟨by positivity,(div_le_one (by exact_mod_cast hN)).mpr
      (by exact_mod_cast RawMixedSource.draws_le r)⟩
  have hEm : Measurable (fun r : Fin N → RowRival =>
      |EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ|) :=
    ((EntryEmpiricalRatio.measurable_empirical (measurable_rawReciprocal z) N).sub_const κ).abs
  have hRi : Integrable (fun r : Fin N → RowRival =>
      (1/lo)*((RawMixedSource.draws r:ℝ)/(N:ℝ)+1/(N:ℝ))) Q := by
    simpa only [one_div, Pi.add_apply] using
      (hDi.add (integrable_const ((N:ℝ)⁻¹))).const_mul (1/lo)
  have hRm : Measurable (fun r : Fin N → RowRival =>
      (1/lo)*((RawMixedSource.draws r:ℝ)/(N:ℝ)+1/(N:ℝ))) :=
    (hDm.add_const _).const_mul _
  have hEip : Integrable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      |EntryEmpiricalRatio.empirical (rawReciprocal z) N x.1-κ|) P := by
    simpa only [Function.comp_def, Pi.sub_apply] using hproj.integrable_comp_of_integrable hEi.abs
  have hRip : Integrable (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      (1/lo)*((RawMixedSource.draws x.1:ℝ)/(N:ℝ)+1/(N:ℝ))) P := by
    exact hproj.integrable_comp_of_integrable hRi
  have hb := integral_mono hF (hEip.add hRip) (fun x => by
      have hh := normalized_error_bound hN focal z κ w hlo hz x
      dsimp only [Pi.add_apply]
      convert! hh using 1
      ring)
  have he : (∫ x, |EntryEmpiricalRatio.empirical (rawReciprocal z) N x.1-κ| ∂P) =
      ∫ r, |EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ| ∂Q := by
    have hh := integral_map (μ := P) hproj.measurable.aemeasurable hEm.aestronglyMeasurable
    rw [hproj.map_eq] at hh
    exact hh.symm
  have hr : (∫ x, (1/lo)*((RawMixedSource.draws x.1:ℝ)/(N:ℝ)+1/(N:ℝ)) ∂P) =
      ∫ r, (1/lo)*((RawMixedSource.draws r:ℝ)/(N:ℝ)+1/(N:ℝ)) ∂Q := by
    have hh := integral_map (μ := P) hproj.measurable.aemeasurable hRm.aestronglyMeasurable
    rw [hproj.map_eq] at hh
    exact hh.symm
  change (∫ x, |normalized focal z w x-κ| ∂P) ≤
    (∫ x, |EntryEmpiricalRatio.empirical (rawReciprocal z) N x.1-κ|+
      (1/lo)*((RawMixedSource.draws x.1:ℝ)/(N:ℝ)+1/(N:ℝ)) ∂P) at hb
  rw [integral_add hEip hRip,he,hr,
    integral_const_mul,integral_add hDi (integrable_const _),integral_const] at hb
  simpa only [probReal_univ,one_smul,one_div] using hb

theorem actual_deleted_reciprocal_L1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    {lo : ℝ} (hlo : 0 < lo) (z : ℕ → ℝ) (hzlo : ∀ m, lo ≤ z m)
    (hz : Tendsto z atTop (𝓝 (entry i)))
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (focal : ℕ → ℝ)
    (w : (m : ℕ) → (Fin (N m) → RowRival) → Weights (Fin (N m+1)))
    (hw : ∀ m, Measurable (w m)) :
    Tendsto (fun m => ∫ x, |normalized (focal m) (z m) (w m) x-reciprocalMean μ i V|
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)) atTop (𝓝 0) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) := Measure.isProbabilityMeasure_map
    (hV.prodMk (hB m)).aemeasurable
  have hEmp := actual_raw_reciprocal_empirical_L1 μ i V B hV hB hvalue hadmissible hactive
    hlo z hzlo hz N hN
  have hD := actual_draw_fraction_L1 i G N hN
  have hNR : Tendsto (fun m => (N m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hInv : Tendsto (fun m => 1/(N m:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hNR
  have hR := hEmp.add ((hD.add hInv).const_mul (1/lo))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun m => normalized_integral_error i (G m) (hNp m) (focal m) (z m)
      (reciprocalMean μ i V) (w m) (hw m) hlo (hzlo m))
  simpa using hR

theorem omitted_focal_identity {N : ℕ} (focal z : ℝ) (hz : 0 < z)
    (r : Fin N → RowRival) (E : Finset (Fin (N+1))) :
    reciprocalSum (listBids focal r) (insert 0 E) z=
      reciprocalSum (listBids 0 r) E z := by
  unfold reciprocalSum
  apply Finset.sum_congr rfl
  intro j _
  refine Fin.cases ?_ (fun j => ?_) j
  · by_cases h0 : (0 : Fin (N+1)) ∈ E <;>
      simp [listBids,h0,reciprocalTerm,not_lt.mpr hz.le]
  · simp only [listBids,Fin.cons_succ,Finset.mem_insert,Fin.succ_ne_zero,false_or]

end FCAppendix.Affine.Uniform06.EntryDeletedReciprocal
