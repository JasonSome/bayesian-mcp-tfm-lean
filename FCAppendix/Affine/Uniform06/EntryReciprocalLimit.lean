import FCAppendix.Affine.Uniform06.EntryEmpiricalRatio
import FCAppendix.Affine.Uniform06.ReciprocalSecantBounds
import FCAppendix.Affine.Uniform06.RawMixedSource
import FCAppendix.Affine.Uniform06.EntryEarlySourceLimits
import FCAppendix.Affine.Uniform06.EntrySamplingLaw

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryReciprocalLimit

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.ReciprocalSecantBounds
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def activeReciprocal (lam : ℝ) (B0 : ℝ → ℝ) (v : ℝ) : ℝ :=
  if lam < v then (B0 v)⁻¹ else 0

lemma measurable_reciprocalTerm {B : Ω → ℝ} (hB : Measurable B) (z : ℝ) :
    Measurable (fun ω => reciprocalTerm (B ω) z) :=
  Measurable.ite (measurableSet_lt measurable_const hB) hB.inv measurable_const

lemma measurable_activeReciprocal (lam : ℝ) {B0 : ℝ → ℝ} (hB0 : Measurable B0) :
    Measurable (activeReciprocal lam B0) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) hB0.inv measurable_const

theorem entry_lt_activeBid (i : Row) {v : ℝ} (hv : entry i < v) :
    entry i < ActiveGraphComponent.activeBid i v := by
  have hlam := EarlyMean.entry_pos i
  have hv0 := hlam.trans hv
  have hξ := xi_pos i
  have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
  have hsum : kappa i+xi i=1 := by cases i <;> norm_num [kappa,kappaQ,xi,xiQ,etaQ]
  have hden : 0 < kappa i*v+xi i*entry i :=
    add_pos (mul_pos hκ hv0) (mul_pos hξ hlam)
  unfold ActiveGraphComponent.activeBid
  apply (lt_div_iff₀ hden).mpr
  have hp := mul_pos (mul_pos hlam hξ) (sub_pos.mpr hv)
  nlinarith [mul_nonneg hlam.le hv0.le,congrArg (fun q : ℝ => entry i*v*q) hsum]

theorem reciprocal_tendsto_ae (μ : Measure Ω) (V : Ω → ℝ)
    (B : ℕ → Ω → ℝ) (B0 : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 lam))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ lam)
    (hactive : ∀ᵐ ω ∂μ, lam < V ω →
      Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω))))
    (hstrict : ∀ v, lam < v → lam < B0 v) :
    ∀ᵐ ω ∂μ, Tendsto (fun m => reciprocalTerm (B m ω) (b m)) atTop
      (𝓝 (activeReciprocal lam B0 (V ω))) := by
  filter_upwards [ae_all_iff.mpr hadmissible,hthreshold,hactive] with ω hB hne ha
  by_cases hv : lam < V ω
  · have hB0 := hstrict (V ω) hv
    have hBlim := ha hv
    have hsep : ∀ᶠ m in atTop, b m < B m ω := by
      filter_upwards [hb.eventually (eventually_lt_nhds (show lam < (lam+B0 (V ω))/2 by linarith)),
        hBlim.eventually (eventually_gt_nhds (show (lam+B0 (V ω))/2 < B0 (V ω) by linarith))] with m hm hm'
      exact hm.trans hm'
    have hi := hBlim.inv₀ (hlam.trans hB0).ne'
    simp only [activeReciprocal,if_pos hv]
    apply hi.congr'
    filter_upwards [hsep] with m hm
    simp only [reciprocalTerm,if_pos hm]
  · have hvlt : V ω < lam := lt_of_le_of_ne (le_of_not_gt hv) hne
    apply tendsto_const_nhds.congr'
    filter_upwards [hb.eventually (eventually_gt_nhds hvlt)] with m hm
    have hnot : ¬ b m < B m ω := not_lt.mpr ((hB m).trans hm.le)
    simp only [activeReciprocal,if_neg hv,reciprocalTerm,if_neg hnot]

theorem reciprocal_abs_bound {B z lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) :
    |reciprocalTerm B z| ≤ lo⁻¹ := by
  rw [abs_of_nonneg (reciprocalTerm_nonneg (hlo.trans_le hz))]
  exact (reciprocalTerm_le (hlo.trans_le hz)).trans
    (by simpa only [one_div] using one_div_le_one_div_of_le hlo hz)

theorem population_reciprocal_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (B0 : ℝ → ℝ)
    (_hV : Measurable V) (hB : ∀ m, Measurable (B m)) (_hB0 : Measurable B0)
    {lam lo : ℝ} (hlam : 0 < lam) (hlo : 0 < lo)
    (b : ℕ → ℝ) (hbl : ∀ m, lo ≤ b m) (hb : Tendsto b atTop (𝓝 lam))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ lam)
    (hactive : ∀ᵐ ω ∂μ, lam < V ω →
      Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω))))
    (hstrict : ∀ v, lam < v → lam < B0 v) :
    Tendsto (fun m => ∫ ω, reciprocalTerm (B m ω) (b m) ∂μ) atTop
      (𝓝 (∫ ω, activeReciprocal lam B0 (V ω) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => lo⁻¹)
  · intro m
    exact (measurable_reciprocalTerm (hB m) (b m)).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact Eventually.of_forall fun _ => by
      simpa only [Real.norm_eq_abs] using reciprocal_abs_bound hlo (hbl m)
  · exact reciprocal_tendsto_ae μ V B B0 hlam b hb hadmissible hthreshold hactive hstrict

theorem tilted_population_reciprocal_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → ℝ) (B X : ℕ → Ω → ℝ) (B0 : ℝ → ℝ)
    (hB : ∀ m, Measurable (B m)) (hX : ∀ m, Measurable (X m))
    (hXb : ∀ m, ∀ᵐ ω ∂μ, X m ω ∈ Icc (0:ℝ) 1)
    {lam lo : ℝ} (hlam : 0 < lam) (hlo : 0 < lo)
    (b : ℕ → ℝ) (hbl : ∀ m, lo ≤ b m) (hb : Tendsto b atTop (𝓝 lam))
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hthreshold : ∀ᵐ ω ∂μ, V ω ≠ lam)
    (hactive : ∀ᵐ ω ∂μ, lam < V ω → Tendsto (fun m => B m ω) atTop (𝓝 (B0 (V ω))))
    (hstrict : ∀ v, lam < v → lam < B0 v)
    (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun m => ∫ ω, reciprocalTerm (B m ω) (b m)
      ∂μ.tilted (fun ω => u m*X m ω)) atTop
        (𝓝 (∫ ω, activeReciprocal lam B0 (V ω) ∂μ)) := by
  exact EntryActiveLimit.tilted_integral_tendsto_fixed_carrier μ X
    (fun m ω => reciprocalTerm (B m ω) (b m))
    (fun ω => activeReciprocal lam B0 (V ω)) hX
    (fun m => measurable_reciprocalTerm (hB m) (b m)) hXb (inv_nonneg.mpr hlo.le)
    (fun m => Eventually.of_forall fun _ => reciprocal_abs_bound hlo (hbl m))
    (reciprocal_tendsto_ae μ V B B0 hlam b hb hadmissible hthreshold hactive hstrict) u hu

section Deletion
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem reciprocal_deletion_identity (B : ι → ℝ) (E : Finset ι) (z : ℝ) :
    (∑ j, reciprocalTerm (B j) z)-reciprocalSum B E z=
      ∑ j ∈ E, reciprocalTerm (B j) z := by
  unfold reciprocalSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : ι, if j ∈ E then reciprocalTerm (B j) z else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ E <;> simp [hj]
    _ = _ := by simp

theorem reciprocal_deletion_bound (B : ι → ℝ) (E : Finset ι)
    {z lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) :
    |reciprocalSum B E z-(∑ j, reciprocalTerm (B j) z)| ≤ E.card/lo := by
  rw [abs_sub_comm,reciprocal_deletion_identity]
  calc
    |∑ j ∈ E, reciprocalTerm (B j) z| ≤ ∑ j ∈ E, |reciprocalTerm (B j) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ E, lo⁻¹ := Finset.sum_le_sum fun _ _ => reciprocal_abs_bound hlo hz
    _ = _ := by simp [div_eq_mul_inv]

omit [Fintype ι] in

theorem finalSet_card_le (n : ℕ) (S : Finset ι) (p : Path ι n) :
    (finalSet n S p).card ≤ S.card+n := by
  induction n generalizing S with
  | zero => simp [finalSet]
  | succ n ih =>
    have hrec := ih (insert p.1 S) p.2
    have hi := Finset.card_insert_le p.1 S
    simpa only [finalSet] using (hrec.trans (by omega))

theorem actual_path_reciprocal_deletion {n : ℕ} (B : ι → ℝ) (p : Path ι n)
    {z lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) :
    |reciprocalSum B (finalSet n ∅ p) z-(∑ j, reciprocalTerm (B j) z)| ≤ n/lo := by
  have hh := reciprocal_deletion_bound B (finalSet n ∅ p) hlo hz
  have hc : ((finalSet n ∅ p).card : ℝ) ≤ n := by
    exact_mod_cast (by simpa using finalSet_card_le n (∅ : Finset ι) p)
  exact hh.trans (div_le_div_of_nonneg_right hc hlo.le)

end Deletion

def rawReciprocal (z : ℝ) : LowBody.RowRival → ℝ :=
  RivalGood.lowerTest (fun B => reciprocalTerm B z)

lemma measurable_rawReciprocal (z : ℝ) : Measurable (rawReciprocal z) :=
  RivalGood.measurable_lowerTest (measurable_reciprocalTerm measurable_id z)

lemma rawReciprocal_bound {z lo : ℝ} (hlo : 0 < lo) (hz : lo ≤ z) (r : LowBody.RowRival) :
    |rawReciprocal z r| ≤ lo⁻¹ := by
  unfold rawReciprocal RivalGood.lowerTest
  split_ifs
  · exact reciprocal_abs_bound hlo hz
  · simp only [abs_zero]
    positivity

theorem raw_reciprocal_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Row) (V B : Ω → ℝ) (hV : Measurable V) (hB : Measurable B)
    {z : ℝ} (hz : 0 < z) :
    (∫ r, rawReciprocal z r ∂ RawMixedSource.source i (EntryEarlySourceLimits.joint μ V B))=
      cutoff i*(∫ ω, reciprocalTerm (B ω) z ∂μ) := by
  let G := EntryEarlySourceLimits.joint μ V B
  letI : IsProbabilityMeasure G := Measure.isProbabilityMeasure_map (hV.prodMk hB).aemeasurable
  have hf : Measurable (fun B : ℝ => reciprocalTerm B z) := measurable_reciprocalTerm measurable_id z
  have hi : Integrable (fun p : ℝ × ℝ => reciprocalTerm p.2 z) G :=
    Integrable.of_bound (hf.comp measurable_snd).aestronglyMeasurable z⁻¹
      (Eventually.of_forall fun _ => by simpa only [Real.norm_eq_abs] using reciprocal_abs_bound hz le_rfl)
  change (∫ r, RivalGood.lowerTest (fun B => reciprocalTerm B z) r ∂ RawMixedSource.source i G) = _
  rw [RawMixedSource.integral_lower_statistic i G _ hf hi]
  dsimp only [G,EntryEarlySourceLimits.joint]
  rw [integral_map (f := fun p : ℝ × ℝ => reciprocalTerm p.2 z)
    (hV.prodMk hB).aemeasurable (hf.comp measurable_snd).aestronglyMeasurable]

def reciprocalMean (μ : Measure Ω) (i : Row) (V : Ω → ℝ) : ℝ :=
  cutoff i*(∫ ω, activeReciprocal (entry i) (ActiveGraphComponent.activeBid i) (V ω) ∂μ)

lemma activeReciprocal_bounds (i : Row) (v : ℝ) :
    activeReciprocal (entry i) (ActiveGraphComponent.activeBid i) v ∈
      Icc (0:ℝ) (entry i)⁻¹ := by
  by_cases hv : entry i < v
  · have hB := entry_lt_activeBid i hv
    rw [activeReciprocal,if_pos hv]
    exact ⟨inv_nonneg.mpr ((EarlyMean.entry_pos i).trans hB).le,
      by simpa only [one_div] using one_div_le_one_div_of_le (EarlyMean.entry_pos i) hB.le⟩
  · simp only [activeReciprocal,if_neg hv,mem_Icc,le_refl,true_and]
    exact inv_nonneg.mpr (EarlyMean.entry_pos i).le

theorem reciprocalMean_positive (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Row) (V : Ω → ℝ) (hV : Measurable V)
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i) :
    0 < reciprocalMean μ i V := by
  let f := fun ω => activeReciprocal (entry i) (ActiveGraphComponent.activeBid i) (V ω)
  have hBm : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  have hfm : Measurable f := (measurable_activeReciprocal _ hBm).comp hV
  have hfi : Integrable f μ := Integrable.of_mem_Icc 0 ((entry i)⁻¹) hfm.aemeasurable
    (Eventually.of_forall fun ω => activeReciprocal_bounds i (V ω))
  have hm : μ.real {ω | V ω ∈ Ioc (entry i) (cutoff i)}=1-x i := by
    have hmap : μ.real {ω | V ω ∈ Ioc (entry i) (cutoff i)}=
        (μ.map V).real (Ioc (entry i) (cutoff i)) := by
      rw [Measure.real,Measure.real,Measure.map_apply hV measurableSet_Ioc]
      rfl
    rw [hmap,hvalue,EarlyMean.conditional_interval_mass i (EarlyMean.entry_pos i).le
      (EarlyMean.entry_lt_cutoff i).le le_rfl]
    unfold entry
    field_simp [(cutoff_pos i).ne']
  have hmass : 0 < μ {ω | V ω ∈ Ioc (entry i) (cutoff i)} := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hr : μ.real {ω | V ω ∈ Ioc (entry i) (cutoff i)}=0 := by
      simp only [Measure.real,hz,ENNReal.toReal_zero]
    rw [hm] at hr
    cases i <;> norm_num [x,xQ] at hr
  have hs : {ω | V ω ∈ Ioc (entry i) (cutoff i)} ⊆ Function.support f := by
    intro ω hω
    change f ω ≠ 0
    dsimp [f]
    rw [activeReciprocal,if_pos hω.1]
    exact inv_ne_zero ((EarlyMean.entry_pos i).trans (entry_lt_activeBid i hω.1)).ne'
  exact mul_pos (cutoff_pos i)
    ((integral_pos_iff_support_of_nonneg (fun ω => (activeReciprocal_bounds i (V ω)).1)
      hfi).mpr (hmass.trans_le (measure_mono hs)))

theorem raw_reciprocal_population_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    {lo : ℝ} (hlo : 0 < lo) (z : ℕ → ℝ) (hzlo : ∀ m, lo ≤ z m)
    (hz : Tendsto z atTop (𝓝 (entry i))) :
    Tendsto (fun m => ∫ r, rawReciprocal (z m) r
      ∂ RawMixedSource.source i (EntryEarlySourceLimits.joint μ V (B m)))
      atTop (𝓝 (reciprocalMean μ i V)) := by
  simp_rw [raw_reciprocal_integral μ i V (B _) hV (hB _) (hlo.trans_le (hzlo _))]
  have hB0 : Measurable (ActiveGraphComponent.activeBid i) := by
    unfold ActiveGraphComponent.activeBid
    fun_prop
  exact (population_reciprocal_tendsto μ V B (ActiveGraphComponent.activeBid i) hV hB hB0
    (EarlyMean.entry_pos i) hlo z hzlo hz hadmissible
    (EntryEarlySourceLimits.fixed_value_null μ i V hV hvalue (entry i)) hactive
    (fun v hv => entry_lt_activeBid i hv)).const_mul (cutoff i)

theorem actual_raw_reciprocal_empirical_L1 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    {lo : ℝ} (hlo : 0 < lo) (z : ℕ → ℝ) (hzlo : ∀ m, lo ≤ z m)
    (hz : Tendsto z atTop (𝓝 (entry i)))
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun m => ∫ r,
      |EntryEmpiricalRatio.empirical (rawReciprocal (z m)) (N m) r-reciprocalMean μ i V|
      ∂Measure.pi (fun _ : Fin (N m) => RawMixedSource.source i (EntryEarlySourceLimits.joint μ V (B m))))
      atTop (𝓝 0) := by
  let G := fun m => EntryEarlySourceLimits.joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) := Measure.isProbabilityMeasure_map
    (hV.prodMk (hB m)).aemeasurable
  exact EntryEmpiricalRatio.empirical_L1_tendsto
    (fun m => RawMixedSource.source i (G m)) (fun m => rawReciprocal (z m))
    (fun m => measurable_rawReciprocal (z m)) (inv_nonneg.mpr hlo.le)
    (fun m => Eventually.of_forall (rawReciprocal_bound hlo (hzlo m))) N hN
    (raw_reciprocal_population_tendsto μ i V B hV hB hvalue hadmissible hactive hlo z hzlo hz)

theorem actual_draw_fraction_L1 (i : Row) (G : ℕ → Measure (ℝ × ℝ))
    [∀ m, IsProbabilityMeasure (G m)] (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun m => ∫ r, (RawMixedSource.draws r:ℝ)/(N m:ℝ)
      ∂Measure.pi (fun _ : Fin (N m) => RawMixedSource.source i (G m))) atTop (𝓝 0) := by
  have he := EntryEmpiricalRatio.empirical_L1_tendsto
    (fun m => RawMixedSource.source i (G m)) (fun _ => RawMixedSource.sign)
    (fun _ => RawMixedSource.measurable_sign) (by norm_num : (0:ℝ)≤1)
    (fun _ => Eventually.of_forall RawMixedSource.sign_bounds) N hN
    (show Tendsto (fun m => ∫ r, RawMixedSource.sign r ∂ RawMixedSource.source i (G m)) atTop (𝓝 0) from by
      simp_rw [RawMixedSource.sign_mean i (G _) (EarlyMean.entry_pos i)]
      exact tendsto_const_nhds)
  simpa only [sub_zero,EntryEmpiricalRatio.empirical,abs_div,
    abs_of_nonneg (show (0:ℝ) ≤ N _ from Nat.cast_nonneg _),RawMixedSource.draws_eq_abs] using he

section ActualRemoval
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def removed (w : Ω → Weights ι) (d : Ω → ℕ) (x : Ω × unitInterval) : Finset ι :=
  finalSet (d x.1) ∅ (EntrySamplingLaw.sampler (d x.1) (w x.1) x.2)

lemma measurable_removed {w : Ω → Weights ι} {d : Ω → ℕ}
    (hw : Measurable w) (hd : Measurable d) : Measurable (removed w d) := by
  have hm (n : ℕ) : Measurable (fun x : Ω × unitInterval =>
      finalSet n ∅ (EntrySamplingLaw.sampler n (w x.1) x.2)) :=
    (measurable_of_countable (finalSet n (∅ : Finset ι))).comp
      ((EntrySamplingLaw.measurable_sampler n).comp ((hw.comp measurable_fst).prodMk measurable_snd))
  exact (measurable_from_prod_countable_right (f := fun x : ℕ × (Ω × unitInterval) =>
    finalSet x.1 ∅ (EntrySamplingLaw.sampler x.1 (w x.2.1) x.2.2)) hm).comp
    ((hd.comp measurable_fst).prodMk measurable_id)

omit [MeasurableSpace Ω] in
lemma removed_card_le (w : Ω → Weights ι) (d : Ω → ℕ) (x : Ω × unitInterval) :
    (removed w d x).card ≤ d x.1 := by
  simpa only [removed,Finset.card_empty,zero_add] using
    finalSet_card_le (d x.1) (∅ : Finset ι) (EntrySamplingLaw.sampler (d x.1) (w x.1) x.2)

end ActualRemoval

def maskedRawBid (r : LowBody.RowRival) : ℝ := if r.1=0 then r.2 else 0

lemma reciprocal_mask (r : LowBody.RowRival) {z : ℝ} (hz : 0 < z) :
    reciprocalTerm (maskedRawBid r) z=rawReciprocal z r := by
  unfold maskedRawBid rawReciprocal RivalGood.lowerTest
  split_ifs
  · rfl
  · simp [reciprocalTerm,not_lt.mpr hz.le]

theorem focal_deletion_empirical_bound {N : ℕ} (hN : 0 < N)
    (r : Fin N → LowBody.RowRival) (focal z lo κ : ℝ) (hlo : 0 < lo) (hz : lo ≤ z)
    (E : Finset (Fin (N+1))) (hE : E.card ≤ RawMixedSource.draws r) :
    |reciprocalSum (Fin.cons focal (fun j => maskedRawBid (r j))) E z/(N:ℝ)-κ| ≤
      |EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ|+
        ((RawMixedSource.draws r:ℝ)+1)/(lo*(N:ℝ)) := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let B : Fin (N+1) → ℝ := Fin.cons focal (fun j => maskedRawBid (r j))
  have hs : (∑ j, reciprocalTerm (B j) z)=reciprocalTerm focal z+∑ j, rawReciprocal z (r j) := by
    rw [Fin.sum_univ_succ]
    simp only [B,Fin.cons_zero,Fin.cons_succ,reciprocal_mask _ (hlo.trans_le hz)]
  have hdel := reciprocal_deletion_bound B E hlo hz
  have hER : (E.card:ℝ) ≤ RawMixedSource.draws r := by exact_mod_cast hE
  have hdel' : |reciprocalSum B E z-(∑ j, reciprocalTerm (B j) z)| ≤
      (RawMixedSource.draws r:ℝ)/lo :=
    hdel.trans (div_le_div_of_nonneg_right hER hlo.le)
  have hsplit : reciprocalSum B E z/(N:ℝ)-κ=
      (reciprocalSum B E z-(∑ j, reciprocalTerm (B j) z))/(N:ℝ)+
        reciprocalTerm focal z/(N:ℝ)+(EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ) := by
    rw [hs,EntryEmpiricalRatio.empirical]
    ring
  rw [hsplit]
  have habs := (abs_add_le
    ((reciprocalSum B E z-(∑ j, reciprocalTerm (B j) z))/(N:ℝ)+reciprocalTerm focal z/(N:ℝ))
    (EntryEmpiricalRatio.empirical (rawReciprocal z) N r-κ)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_div,abs_div,abs_of_pos hNp] at habs
  have h1 := div_le_div_of_nonneg_right hdel' hNp.le
  have h2 := div_le_div_of_nonneg_right (reciprocal_abs_bound hlo hz (B := focal)) hNp.le
  have halg : ((RawMixedSource.draws r:ℝ)/lo)/(N:ℝ)+lo⁻¹/(N:ℝ)=
      ((RawMixedSource.draws r:ℝ)+1)/(lo*(N:ℝ)) := by
    field_simp [hlo.ne',hNp.ne']
  linarith

end FCAppendix.Affine.Uniform06.EntryReciprocalLimit
