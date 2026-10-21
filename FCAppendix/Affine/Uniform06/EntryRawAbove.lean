import FCAppendix.Affine.Uniform06.EntryRawGoodMoments
import FCAppendix.Affine.Uniform06.AboveEntry

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawAbove

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open EntryRawCentral EntryRawGoodMoments EntryEarlySourceLimits EntryCentralSampling EntryProfileMean
open scoped BigOperators

section Iid
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem iid_centered_sum_second {X : Ω → ℝ} (hX : Measurable X)
    (hb : ∀ᵐ ω ∂μ, |X ω| ≤ 1) (hz : ∫ ω, X ω ∂μ=0) (N : ℕ) :
    (∫ r : EntryIIDCentral.Row (Ω := Ω) N, (∑ j, X (r.1 j))^2
      ∂EntryIIDCentral.rowLaw μ N) ≤ N := by
  let P := Measure.pi (fun _ : Fin N => μ)
  let S := fun r : Fin N → Ω => ∑ j, X (r j)
  have hLp : MemLp X 2 μ := MemLp.of_bound hX.aestronglyMeasurable 1
    (hb.mono fun _ hh => by simpa only [Real.norm_eq_abs] using hh)
  have hLpS : MemLp S 2 P := memLp_finsetSum _ (fun j _ =>
    hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) j))
  have hSmeas : Measurable S := Finset.measurable_sum _
    (fun j _ => hX.comp (measurable_pi_apply j))
  have hSmean : (∫ r, S r ∂P)=0 := by
    change (∫ r : Fin N → Ω, ∑ j, X (r j) ∂Measure.pi (fun _ : Fin N => μ))=0
    have hIj (j : Fin N) : Integrable (fun r : Fin N → Ω => X (r j)) (Measure.pi (fun _ : Fin N => μ)) :=
      (hLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) j)).integrable (by norm_num)
    rw [integral_finsetSum Finset.univ (fun j _ => hIj j)]
    simp only [integral_comp_eval (μ := fun _ : Fin N => μ) hX.aestronglyMeasurable,hz,
      Finset.sum_const_zero]
  have hvar : variance S P=(N:ℝ)*variance X μ := by
    have he : (∑ j : Fin N, fun r : Fin N → Ω => X (r j))=S := by
      funext r
      simp [S]
    have hv := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => X) (fun _ => hLp)
    rw [he] at hv
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hv
  have hvariance : variance X μ ≤ 1 := by
    apply (variance_le_expectation_sq hX.aestronglyMeasurable).trans
    have hh : (∫ ω, (X ω)^2 ∂μ) ≤ ∫ _ω, (1:ℝ) ∂μ := by
      apply integral_mono_ae hLp.integrable_sq (integrable_const _)
      filter_upwards [hb] with ω hω
      nlinarith [sq_abs (X ω),abs_nonneg (X ω)]
    simpa using hh
  have he := integral_map (f := fun r : Fin N → Ω => (S r)^2)
    (μ := P.prod (volume : Measure unitInterval)) measurable_fst.aemeasurable
    (hSmeas.pow_const 2).aestronglyMeasurable
  rw [(measurePreserving_fst (μ := P) (ν := (volume : Measure unitInterval))).map_eq] at he
  have he := he.symm
  change (∫ r : EntryIIDCentral.Row (Ω := Ω) N, (∑ j, X (r.1 j))^2
      ∂EntryIIDCentral.rowLaw μ N)=(∫ r, (S r)^2 ∂P) at he
  rw [he]
  have hvarianceS := variance_eq_sub hLpS
  simp only [hSmean,zero_pow (by decide : (2:ℕ)≠0),sub_zero,Pi.pow_apply] at hvarianceS
  rw [← hvarianceS,hvar]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hvariance (Nat.cast_nonneg N)

end Iid

def delta (i : Row) (G : Measure (ℝ × ℝ)) (N C : ℕ) (b : ℝ) : ℝ :=
  (C:ℝ)-(N:ℝ)*RawMixedSource.mean i G b

def balanced {N : ℕ} (i : Row) (C : ℕ) (b : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  (C:ℝ)-∑ j, RawMixedSource.demand (xi i) b (x.1 j)

theorem centered_balanced_identity (i : Row) (G : Measure (ℝ × ℝ)) (N C : ℕ)
    (b : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    balanced i C b x-delta i G N C b= -∑ j, RawMixedSource.centered i G b 0 (x.1 j) := by
  simp only [balanced,delta,RawMixedSource.centered,Matrix.cons_val_zero,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem selected_le_half_sign (i : Row) {N : ℕ} {b : ℝ} (hb : 0 < b) (l c : ℝ)
    {hstar : ℝ} (hhstar : hstar ∈ Icc (0:ℝ) (1/2))
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    selected i b l c hstar x ≤ (1/2)*|∑ j, RawMixedSource.sign (x.1 j)| := by
  have hh := EntryCentralReplacement.guardedSample_abs_le (c := c*(N:ℝ))
    (profileWeights (focalWeight i b l) (rawWeight i l) (focalWeight_bounds i b l) (rawWeight_bounds i l))
    (profileH (1/2) (rawH i b)) RawMixedSource.draws (by norm_num : (0:ℝ)≤1/2)
    (fun r j => profileH_abs_le (by norm_num : |(1/2:ℝ)|≤1/2)
      (fun q => by rw [abs_of_nonneg (rawH_bounds i hb q).1]; exact (rawH_bounds i hb q).2) r j)
    (by rw [abs_of_nonneg hhstar.1]; exact hhstar.2) x
  have hh : |selected i b l c hstar x| ≤ (1/2)*(RawMixedSource.draws x.1:ℝ) := by
    exact hh
  rw [RawMixedSource.draws_eq_abs] at hh
  exact (le_abs_self _).trans hh

theorem raw_normalized_deficit_error (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (N C : ℕ) {b : ℝ} (hb : 0 < b) (l c : ℝ)
    {hstar : ℝ} (hhstar : hstar ∈ Icc (0:ℝ) (1/2))
    (hδ : 0 < delta i G N C b) :
    (∫ x, (max (deficit i C b l c hstar x) 0/delta i G N C b-1)^2
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) ≤
      4*(N:ℝ)/(delta i G N C b)^2 := by
  let P := EntryIIDCentral.rowLaw (RawMixedSource.source i G) N
  let W := balanced (N := N) i C b
  let S := selected (N := N) i b l c hstar
  let Y := fun x : EntryIIDCentral.Row (Ω := RowRival) N => ∑ j, RawMixedSource.sign (x.1 j)
  have hWm : Measurable W := measurable_const.sub (Finset.measurable_sum _ (fun j _ =>
    (RawMixedSource.measurable_demand (xi i) b).comp ((measurable_pi_apply j).comp measurable_fst)))
  have hYm : Measurable Y := Finset.measurable_sum _ (fun j _ =>
    RawMixedSource.measurable_sign.comp ((measurable_pi_apply j).comp measurable_fst))
  have hW : MemLp W 2 P := by
    apply MemLp.of_bound hWm.aestronglyMeasurable ((C:ℝ)+N)
    exact Eventually.of_forall fun x => by
      have hsum : (∑ j, RawMixedSource.demand (xi i) b (x.1 j)) ∈ Icc (0:ℝ) N := by
        constructor
        · exact Finset.sum_nonneg fun j _ => (RawMixedSource.demand_bounds (xi_pos i) hb _).1
        · simpa using! Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
            (RawMixedSource.demand_bounds (xi_pos i) hb (x.1 j)).2)
      rw [Real.norm_eq_abs,abs_le]
      dsimp [W,balanced]
      constructor <;> linarith [(show (0:ℝ) ≤ C from Nat.cast_nonneg C),hsum.1,hsum.2]
  have hS : MemLp S 2 P := by
    apply MemLp.of_bound (measurable_selected i N b l c hstar).aestronglyMeasurable ((N:ℝ)/2)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (selected_nonneg i hb l c hhstar.1 x)]
      have hh := selected_le_half_sign i hb l c hhstar x
      rw [← RawMixedSource.draws_eq_abs] at hh
      have hd : (RawMixedSource.draws x.1:ℝ) ≤ N := by exact_mod_cast RawMixedSource.draws_le x.1
      nlinarith
  have hY : MemLp Y 2 P := by
    apply MemLp.of_bound hYm.aestronglyMeasurable (N:ℝ)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,← RawMixedSource.draws_eq_abs]
      exact_mod_cast RawMixedSource.draws_le x.1
  have hVW : (∫ x, (W x-delta i G N C b)^2 ∂P) ≤ (4*(N:ℝ))/4 := by
    simp_rw [W,centered_balanced_identity,neg_sq]
    simpa using iid_centered_sum_second (RawMixedSource.source i G)
      (RawMixedSource.centered_measurable i G b 0)
      (Eventually.of_forall ((RawMixedSource.centered_bounds_and_mean i G hb).1 0))
      ((RawMixedSource.centered_bounds_and_mean i G hb).2 0) N
  have hVY : (∫ x, (Y x)^2 ∂P) ≤ 4*(N:ℝ) := by
    have hh := iid_centered_sum_second (RawMixedSource.source i G)
      RawMixedSource.measurable_sign (Eventually.of_forall RawMixedSource.sign_bounds)
      (RawMixedSource.sign_mean i G hb) N
    exact hh.trans (by change (N : ℝ) ≤ 4*N; nlinarith only [Nat.cast_nonneg (α := ℝ) N])
  have hh := AboveEntry.normalized_deficit_error P W S Y hδ (by norm_num : (0:ℝ)≤1/2)
    hW hS hY (Eventually.of_forall (selected_nonneg i hb l c hhstar.1))
    (Eventually.of_forall (selected_le_half_sign i hb l c hhstar)) hVW hVY
  norm_num only [one_div,inv_pow] at hh
  convert! hh using 1
  ring

theorem raw_above_moments (i : Row) (G : ℕ → Measure (ℝ × ℝ))
    [∀ m, IsProbabilityMeasure (G m)] (N C : ℕ → ℕ)
    (_hNp : ∀ m, 0 < N m) (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m)
    (c hstar : ℝ) (hhstar : hstar ∈ Icc (0:ℝ) (1/2))
    (hδ : ∀ m, 0 < delta i (G m) (N m) (C m) (b m))
    (habove : Tendsto (fun m => delta i (G m) (N m) (C m) (b m)/Real.sqrt (N m:ℝ)) atTop atTop) :
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
    let Z := fun m (x : EntryIIDCentral.Row (Ω := RowRival) (N m)) => max (deficit i (C m) (b m) (l m) c hstar x) 0/
      delta i (G m) (N m) (C m) (b m)
    Tendsto (fun m => ∫ x, Z m x ∂P m) atTop (𝓝 1) ∧
    Tendsto (fun m => (P m).real {x | 0 < Z m x}) atTop (𝓝 1) ∧
    Tendsto (fun m => ∫ x, (Z m x)^2 ∂P m) atTop (𝓝 1) ∧
    Tendsto (fun m => (∫ x, Z m x ∂P m)^2/
      ((P m).real {x | 0 < Z m x}*(∫ x, (Z m x)^2 ∂P m))) atTop (𝓝 1) := by
  let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
  let Z := fun m (x : EntryIIDCentral.Row (Ω := RowRival) (N m)) => max (deficit i (C m) (b m) (l m) c hstar x) 0/
    delta i (G m) (N m) (C m) (b m)
  have hm (m : ℕ) : Measurable (Z m) :=
    ((measurable_deficit i (N m) (C m) (b m) (l m) c hstar).max measurable_const).div_const _
  have hlp (m : ℕ) : MemLp (Z m) 2 (P m) := by
    apply MemLp.of_bound (hm m).aestronglyMeasurable
      ((C m:ℝ)/delta i (G m) (N m) (C m) (b m))
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (le_max_right _ _) (hδ m).le)]
      apply div_le_div_of_nonneg_right _ (hδ m).le
      exact max_le (deficit_le_capacity i (C m) (hbp m) (l m) c hhstar.1 x) (Nat.cast_nonneg _)
  have hinv := (tendsto_inv_atTop_zero.comp habove).pow 2
  have hrhs : Tendsto (fun m => 4*(N m:ℝ)/(delta i (G m) (N m) (C m) (b m))^2)
      atTop (𝓝 0) := by
    have he (m : ℕ) : 4*(N m:ℝ)/(delta i (G m) (N m) (C m) (b m))^2=
        4*((delta i (G m) (N m) (C m) (b m)/Real.sqrt (N m:ℝ))⁻¹)^2 := by
      rw [inv_div,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    simp_rw [he]
    simpa using hinv.const_mul 4
  have herr : Tendsto (fun m => ∫ x, (Z m x-1)^2 ∂P m) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _)
      (fun m => raw_normalized_deficit_error i (G m) (N m) (C m) (hbp m) (l m) c hhstar (hδ m)) hrhs
  exact AboveEntry.ratio_tendsto_one_of_L2 P Z hm hlp
    (fun m => Eventually.of_forall fun _ => div_nonneg (le_max_right _ _) (hδ m).le) herr

end FCAppendix.Affine.Uniform06.EntryRawAbove
