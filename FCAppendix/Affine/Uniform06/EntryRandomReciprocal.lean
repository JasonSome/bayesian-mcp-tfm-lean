import FCAppendix.Affine.Uniform06.EntryDeletedReciprocal

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRandomReciprocal

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.WeightedSampling
open EntryReciprocalLimit EntryEarlySourceLimits ReciprocalSecantBounds
open scoped BigOperators

lemma reciprocalTerm_antitone {B z z' : ℝ} (hz : 0 < z) (hzz' : z ≤ z') :
    reciprocalTerm B z' ≤ reciprocalTerm B z := by
  by_cases h : z' < B
  · simp only [reciprocalTerm,if_pos h,if_pos (hzz'.trans_lt h),le_refl]
  · rw [reciprocalTerm,if_neg h]
    exact reciprocalTerm_nonneg hz

lemma reciprocalSum_antitone {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ) (E : Finset ι) {z z' : ℝ} (hz : 0 < z) (hzz' : z ≤ z') :
    reciprocalSum B E z' ≤ reciprocalSum B E z := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ E
  · simp only [hj,if_true,le_refl]
  · simp only [hj,if_false]
    exact reciprocalTerm_antitone hz hzz'

lemma absolute_interval_bound {l u z κ : ℝ} (hl : l ≤ z) (hu : z ≤ u) :
    |z-κ| ≤ |l-κ|+|u-κ| := by
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le (l-κ)
    linarith [abs_nonneg (u-κ)]
  · have h := le_abs_self (u-κ)
    linarith [abs_nonneg (l-κ)]

theorem secant_error_bound {N : ℕ} (hN : 0 < N) (b Λ K κ ε lo : ℝ)
    (hlo : 0 < lo) (hε : 0 < ε) (hΛ : lo ≤ Λ) (hΛb : Λ ≤ b)
    (r : Fin N → RowRival) (E : Finset (Fin (N+1)))
    (hKlo : reciprocalSum (EntryDeletedReciprocal.listBids 0 r) E b ≤ K)
    (hKhi : K ≤ reciprocalSum (EntryDeletedReciprocal.listBids 0 r) E Λ) :
    |K/(N:ℝ)-κ| ≤
      |reciprocalSum (EntryDeletedReciprocal.listBids 0 r) E b/(N:ℝ)-κ|+
      |reciprocalSum (EntryDeletedReciprocal.listBids 0 r) E (max lo (b-ε))/(N:ℝ)-κ|+
      (2/lo+|κ|)*(b-Λ)/ε := by
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N from hN)
  have hb : 0 < b := hlo.trans_le (hΛ.trans hΛb)
  have hKn : 0 ≤ K/(N:ℝ) := div_nonneg
    ((reciprocalSum_nonneg _ _ hb).trans hKlo) hNr.le
  have hKu : K/(N:ℝ) ≤ 2/lo := by
    have hs := hKhi.trans (reciprocalSum_le _ _ (hlo.trans_le hΛ))
    simp only [Fintype.card_fin,Nat.cast_add_one] at hs
    have hq := (div_le_div_of_nonneg_right hs hNr.le).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_left
        (show 0≤(N:ℝ)+1 by positivity) hlo hΛ) hNr.le)
    apply hq.trans
    apply (div_le_iff₀ hNr).mpr
    apply (div_le_iff₀ hlo).mpr
    have he : (2/lo)*(N:ℝ)*lo=2*(N:ℝ) := by field_simp [hlo.ne']
    rw [he]
    linarith
  have hC : 0 ≤ 2/lo+|κ| := by positivity
  by_cases hclose : b-Λ ≤ ε
  · have hz : max lo (b-ε) ≤ Λ := max_le hΛ (by linarith)
    have hu := div_le_div_of_nonneg_right
      (hKhi.trans (reciprocalSum_antitone _ _ (hlo.trans_le (le_max_left _ _)) hz)) hNr.le
    have hl := div_le_div_of_nonneg_right hKlo hNr.le
    exact (absolute_interval_bound hl hu).trans
      (le_add_of_nonneg_right (div_nonneg (mul_nonneg hC (sub_nonneg.mpr hΛb)) hε.le))
  · have hd : ε < b-Λ := lt_of_not_ge hclose
    have hbound : |K/(N:ℝ)-κ| ≤ 2/lo+|κ| := by
      exact (abs_sub _ _).trans (add_le_add (by simpa only [abs_of_nonneg hKn] using hKu) le_rfl)
    have hscale : 2/lo+|κ| ≤ (2/lo+|κ|)*(b-Λ)/ε := by
      apply (le_div_iff₀ hε).mpr
      exact mul_le_mul_of_nonneg_left hd.le hC
    exact hbound.trans (hscale.trans (le_add_of_nonneg_left (by positivity)))

def radius (N : ℕ) (r : ℝ) : ℝ := Real.sqrt r+1/(N:ℝ)

lemma radius_pos {N : ℕ} (hN : 0 < N) (r : ℝ) : 0 < radius N r := by
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (one_div_pos.mpr hNr)

lemma mean_div_radius {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    r/radius N r ≤ Real.sqrt r := by
  apply (div_le_iff₀ (radius_pos hN r)).mpr
  unfold radius
  nlinarith [Real.sq_sqrt hr,Real.sqrt_nonneg r,
    mul_nonneg (Real.sqrt_nonneg r) (one_div_nonneg.mpr (Nat.cast_nonneg N))]

lemma radius_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun m => radius (N m) (r m)) atTop (𝓝 0) := by
  have hNr : Tendsto (fun m => (N m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have hinv := tendsto_inv_atTop_zero.comp hNr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  simpa only [radius,Real.sqrt_zero,one_div,zero_add,Function.comp_def] using! hs.add hinv

theorem actual_random_reciprocal_L1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    {lo : ℝ} (hlo : 0 < lo) (hloEntry : lo < entry i)
    (b : ℕ → ℝ) (hblo : ∀ m, lo ≤ b m) (hb : Tendsto b atTop (𝓝 (entry i)))
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (w : (m : ℕ) → (Fin (N m) → RowRival) → Weights (Fin (N m+1)))
    (hw : ∀ m, Measurable (w m))
    (Λ K : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ)
    (hΛm : ∀ m, Measurable (Λ m)) (hKm : ∀ m, Measurable (K m))
    (hΛ : ∀ m x, lo ≤ Λ m x ∧ Λ m x ≤ b m)
    (hK : ∀ m x,
      reciprocalSum (EntryDeletedReciprocal.listBids 0 x.1)
        (removed (w m) RawMixedSource.draws x) (b m) ≤ K m x ∧
      K m x ≤ reciprocalSum (EntryDeletedReciprocal.listBids 0 x.1)
        (removed (w m) RawMixedSource.draws x) (Λ m x))
    (hmove : Tendsto (fun m => ∫ x, b m-Λ m x
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, |K m x/(N m:ℝ)-reciprocalMean μ i V|
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)) atTop (𝓝 0) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) := Measure.isProbabilityMeasure_map
    (hV.prodMk (hB m)).aemeasurable
  let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
  let κ := reciprocalMean μ i V
  let r := fun m => ∫ x, b m-Λ m x ∂P m
  let ε := fun m => radius (N m) (r m)
  let z := fun m => max lo (b m-ε m)
  have hr0 : ∀ m, 0 ≤ r m := fun m => integral_nonneg fun x => sub_nonneg.mpr (hΛ m x).2
  have hr : Tendsto r atTop (𝓝 0) := hmove
  have hε : Tendsto ε atTop (𝓝 0) := radius_tendsto N hN r hr
  have hz : Tendsto z atTop (𝓝 (entry i)) := by
    simpa only [z,sub_zero,max_eq_right hloEntry.le] using! (tendsto_const_nhds : Tendsto (fun _ : ℕ => lo) atTop (𝓝 lo)).max (hb.sub hε)
  have hEb := EntryDeletedReciprocal.actual_deleted_reciprocal_L1 μ i V B hV hB hvalue
    hadmissible hactive hlo b hblo hb N hNp hN (fun _ => 0) w hw
  have hEz := EntryDeletedReciprocal.actual_deleted_reciprocal_L1 μ i V B hV hB hvalue
    hadmissible hactive hlo z (fun _ => le_max_left _ _) hz N hNp hN (fun _ => 0) w hw
  have hsqrt : Tendsto (fun m => Real.sqrt (r m)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,Function.comp_def] using! Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have htotal := (hEb.add hEz).add (hsqrt.const_mul (2/lo+|κ|))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
    (fun m => ?_) (by simpa only [add_zero,mul_zero] using htotal)
  have hNr : (0:ℝ)< N m := by exact_mod_cast hNp m
  have hCb (x) : |K m x/(N m:ℝ)-κ| ≤ 2/lo+|κ| := by
    have hKn : 0 ≤ K m x/(N m:ℝ) := div_nonneg
      ((reciprocalSum_nonneg _ _ (hlo.trans_le (hblo m))).trans (hK m x).1) hNr.le
    have hKu : K m x/(N m:ℝ) ≤ 2/lo := by
      have hs := (hK m x).2.trans (reciprocalSum_le _ _ (hlo.trans_le (hΛ m x).1))
      simp only [Fintype.card_fin,Nat.cast_add_one] at hs
      apply ((div_le_div_of_nonneg_right hs hNr.le).trans
        (div_le_div_of_nonneg_right (div_le_div_of_nonneg_left
          (show 0≤(N m:ℝ)+1 by positivity) hlo (hΛ m x).1) hNr.le)).trans
      apply (div_le_iff₀ hNr).mpr
      apply (div_le_iff₀ hlo).mpr
      have he : (2/lo)*(N m:ℝ)*lo=2*(N m:ℝ) := by field_simp [hlo.ne']
      rw [he]
      have hN1 : (1:ℝ)≤ N m := by exact_mod_cast (show 1≤ N m from hNp m)
      linarith
    exact (abs_sub _ _).trans (add_le_add (by simpa only [abs_of_nonneg hKn] using hKu) le_rfl)
  have hKi : Integrable (fun x => |K m x/(N m:ℝ)-κ|) (P m) :=
    Integrable.of_bound (((hKm m).div_const _).sub_const κ).abs.aestronglyMeasurable _
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hCb x)
  have hRi : Integrable (fun x => b m-Λ m x) (P m) :=
    Integrable.of_mem_Icc 0 (b m-lo) (measurable_const.sub (hΛm m)).aemeasurable
      (Eventually.of_forall fun x => ⟨by linarith [(hΛ m x).2],by linarith [(hΛ m x).1]⟩)
  have hEi (p : ℝ) (hp : lo ≤ p) :
      Integrable (fun x => |EntryDeletedReciprocal.normalized 0 p (w m) x-κ|) (P m) := by
    apply Integrable.of_bound
      (((EntryDeletedReciprocal.measurable_normalized 0 p (hw m)).sub_const κ).abs).aestronglyMeasurable
      (2/lo+|κ|)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have hbnds := EntryDeletedReciprocal.normalized_bounds (hNp m) 0 p (w m) hlo hp x
      exact (abs_sub _ _).trans (add_le_add (by simpa only [abs_of_nonneg hbnds.1] using hbnds.2) le_rfl)
  have hi := ((hEi (b m) (hblo m)).add (hEi (z m) (le_max_left _ _))).add
    ((hRi.const_mul (2/lo+|κ|)).div_const (ε m))
  have hineq := integral_mono hKi hi (fun x =>
    secant_error_bound (hNp m) (b m) (Λ m x) (K m x) κ (ε m) lo hlo
      (radius_pos (hNp m) (r m)) (hΛ m x).1 (hΛ m x).2 x.1
      (removed (w m) RawMixedSource.draws x) (hK m x).1 (hK m x).2)
  simp only [Pi.add_apply] at hineq
  have hsum : Integrable (fun x => |EntryDeletedReciprocal.normalized 0 (b m) (w m) x-κ|+
      |EntryDeletedReciprocal.normalized 0 (z m) (w m) x-κ|) (P m) :=
    (hEi (b m) (hblo m)).add (hEi (z m) (le_max_left _ _))
  have htail : Integrable (fun x => (2/lo+|κ|)*(b m-Λ m x)/(ε m)) (P m) :=
    (hRi.const_mul _).div_const _
  rw [integral_add hsum htail,integral_add (hEi (b m) (hblo m))
    (hEi (z m) (le_max_left _ _)),integral_div,integral_const_mul] at hineq
  refine hineq.trans (add_le_add le_rfl ?_)
  have hh := mul_le_mul_of_nonneg_left (mean_div_radius (hNp m) (hr0 m))
    (show 0≤2/lo+|κ| by positivity)
  simpa only [r,ε,mul_div_assoc] using hh

end FCAppendix.Affine.Uniform06.EntryRandomReciprocal
