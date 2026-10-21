import FCAppendix.Affine.Uniform06.EntryIIDCentral
import FCAppendix.Affine.Uniform06.EntryEarlySourceLimits
import FCAppendix.Affine.Uniform06.CapacityFloor

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawCentral

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.Uniform06.EntryEarlySourceLimits
open FCAppendix.Affine.Uniform06.EntryCentralSampling
open FCAppendix.Affine.Uniform06.EntryProfileMean
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def focalWeight (i : Row) (b l : ℝ) : ℝ :=
  FiniteGuards.eligibility (xi i) l (PrefixRoot.requiredDemand i) b

lemma focalWeight_bounds (i : Row) (b l : ℝ) : focalWeight i b l ∈ Icc (0:ℝ) 1 :=
  FiniteGuards.eligibility_bounds _ _ _ _

def selected {N : ℕ} (i : Row) (b l c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  guardedSample
    (profileWeights (focalWeight i b l) (rawWeight i l)
      (focalWeight_bounds i b l) (rawWeight_bounds i l))
    (profileH (1/2) (rawH i b)) RawMixedSource.draws (c*N) hstar x

def deficit {N : ℕ} (i : Row) (C : ℕ) (b l c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  (C:ℝ)-(∑ j, RawMixedSource.demand (xi i) b (x.1 j))-selected i b l c hstar x

def center (i : Row) (G : Measure (ℝ × ℝ)) (N C : ℕ) (b : ℝ) : ℝ :=
  ((C:ℝ)-(N:ℝ)*RawMixedSource.mean i G b)/Real.sqrt (N:ℝ)

theorem centered_deficit_identity (i : Row) (G : Measure (ℝ × ℝ))
    {N : ℕ} (C : ℕ) (b l c hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    center i G N C b-
      EntryIIDCentral.statistic (RawMixedSource.centered i G b)
        (rawWeight i l) (rawH i b) (focalWeight i b l) (1/2) c hstar
        (focalWeight_bounds i b l) (rawWeight_bounds i l) RawMixedSource.draws x=
      deficit i C b l c hstar x/Real.sqrt (N:ℝ) := by
  unfold center EntryIIDCentral.statistic EntryUI.normalizedSum EntryIIDCentral.array
  simp only [RawMixedSource.centered,Matrix.cons_val_zero,Finset.sum_sub_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold deficit selected
  ring

theorem positive_deficit_identity (i : Row) (G : Measure (ℝ × ℝ))
    {N : ℕ} (_hN : 0 < N) (C : ℕ) (b l c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    max (center i G N C b-
      EntryIIDCentral.statistic (RawMixedSource.centered i G b)
        (rawWeight i l) (rawH i b) (focalWeight i b l) (1/2) c hstar
        (focalWeight_bounds i b l) (rawWeight_bounds i l) RawMixedSource.draws x) 0=
      max (deficit i C b l c hstar x) 0/Real.sqrt (N:ℝ) := by
  rw [centered_deficit_identity]
  simpa only [zero_div] using
    (max_div_div_right (Real.sqrt_nonneg (N:ℝ)) (deficit i C b l c hstar x) 0)

theorem success_event_identity (i : Row) (G : Measure (ℝ × ℝ))
    {N : ℕ} (hN : 0 < N) (C : ℕ) (b l c hstar : ℝ) :
    {x | EntryIIDCentral.statistic (RawMixedSource.centered i G b)
      (rawWeight i l) (rawH i b) (focalWeight i b l) (1/2) c hstar
      (focalWeight_bounds i b l) (rawWeight_bounds i l) RawMixedSource.draws x < center i G N C b}=
      {x : EntryIIDCentral.Row (Ω := RowRival) N | 0 < deficit i C b l c hstar x} := by
  ext x
  simp only [mem_setOf_eq]
  rw [← sub_pos,centered_deficit_identity]
  exact div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (by exact_mod_cast hN))

theorem raw_central_moments (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
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
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (N m)
    let D := fun m => deficit i (C m) (b m) (l m) (eligibleMass μ i V/2) (eligibleHMass μ i V/eligibleMass μ i V)
    let α := Real.sqrt (limitingVariance μ i V)
    let β := eligibleHMean μ i V*Real.sqrt (1-cutoff i)
    Tendsto (fun m => (P m).real {x | 0 < D m x}) atTop (𝓝 (EntryCentralRatio.success α β z)) ∧
    Tendsto (fun m => ∫ x, max (D m x) 0/Real.sqrt (N m:ℝ) ∂P m) atTop
      (𝓝 (EntryCentralRatio.firstMoment α β z)) ∧
    Tendsto (fun m => ∫ x, (max (D m x) 0/Real.sqrt (N m:ℝ))^2 ∂P m) atTop
      (𝓝 (EntryCentralRatio.secondMoment α β z)) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let v := fun m => RawMixedSource.variances i (G m) (b m)
  let v0 : Fin 2 → ℝ := ![limitingVariance μ i V,1-cutoff i]
  have hvl := raw_variance_tendsto μ i V B hV hB hvalue hadmissible hactive b hbp hb
  have hv0p := limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb
  have hvp (m : ℕ) (j : Fin 2) : 0 < v m j := by
    fin_cases j
    · have hlow := raw_variance_lower μ i V (B m) hV (hB m) hvalue (hadmissible m) (hbp m) (hbt m)
      have hp : 0 < (1-cutoff i)/2 := by linarith [cutoff_lt_one i]
      exact (mul_pos (hbp m) (sq_pos_of_pos hp)).trans_le hlow
    · exact sub_pos.mpr (cutoff_lt_one i)
  have hv0 (j : Fin 2) : 0 < v0 j := by
    fin_cases j
    · exact hv0p
    · exact sub_pos.mpr (cutoff_lt_one i)
  have hvlim (j : Fin 2) : Tendsto (fun m => v m j) atTop (𝓝 (v0 j)) := by
    fin_cases j
    · exact hvl
    · exact tendsto_const_nhds
  have hd := eligibleMass_positive μ i V hV hvalue
  have hh := eligibleHMean_bounds μ i V hV hvalue
  have hh0 : 0 ≤ eligibleHMean μ i V := (eligibleHMean_positive μ i V hV hvalue).le
  have hprof := raw_profile_limits μ i V B hV hB hvalue hadmissible hactive b l hbp hlp hb hl
  have hmain := EntryIIDCentral.primitive_central_moments
    (fun m => RawMixedSource.source i (G m)) N hNp hN
    (fun m => RawMixedSource.centered i (G m) (b m))
    (fun m => RawMixedSource.centered_measurable i (G m) (b m))
    (fun m j => Eventually.of_forall ((RawMixedSource.centered_bounds_and_mean i (G m) (hbp m)).1 j))
    (fun m => (RawMixedSource.centered_bounds_and_mean i (G m) (hbp m)).2)
    v v0 hvp hv0 (fun m => RawMixedSource.centered_covariance i (G m) (hbp m)) hvlim
    (fun m => rawWeight i (l m)) (fun m => rawH i (b m))
    (fun m => measurable_rawWeight i (l m)) (fun m => measurable_rawH i (b m))
    (fun _ => RawMixedSource.draws) (fun m => RawMixedSource.measurable_draws (N m))
    (fun _ => RawMixedSource.draws_le)
    (fun m r => by simpa only [RawMixedSource.centered,Matrix.cons_val_one,Matrix.head_cons,Matrix.cons_val_zero]
      using RawMixedSource.draws_eq_abs r)
    (fun m => focalWeight i (b m) (l m)) (fun _ => (1/2:ℝ))
    (A := 1/2) (c := eligibleMass μ i V/2) (dbar := eligibleMass μ i V) (a := eligibleHMass μ i V)
    (by norm_num) (by positivity) (by linarith)
    (fun m => focalWeight_bounds i (b m) (l m)) (fun _ => by norm_num)
    (fun m => rawWeight_bounds i (l m)) (fun m => rawH_bounds i (hbp m))
    ⟨hh0,hh.2⟩ hprof.1 hprof.2
    (fun m => center i (G m) (N m) (C m) (b m)) hcentral
  dsimp only at hmain ⊢
  constructor
  · simpa only [success_event_identity i _ (hNp _) (C _) (b _) (l _)
      (eligibleMass μ i V/2) (eligibleHMass μ i V/eligibleMass μ i V),G,v0,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.head_cons,eligibleHMean] using! hmain.1
  · constructor
    · simpa only [positive_deficit_identity i _ (hNp _) (C _) (b _) (l _)
        (eligibleMass μ i V/2) (eligibleHMass μ i V/eligibleMass μ i V),G,v0,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,eligibleHMean] using! hmain.2.1
    · simpa only [positive_deficit_identity i _ (hNp _) (C _) (b _) (l _)
        (eligibleMass μ i V/2) (eligibleHMass μ i V/eligibleMass μ i V),G,v0,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.head_cons,eligibleHMean] using! hmain.2.2

theorem literal_central_ratio (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hbt : ∀ m, b m ≤ cutoff i)
    (hlp : ∀ m, 0 < l m) (hb : Tendsto b atTop (𝓝 (entry i)))
    (hl : Tendsto l atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m, 2 ≤ n m) (hn : Tendsto n atTop atTop)
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m))
      (n m-1) (capacity (n m)) (b m)) atTop (𝓝 z)) :
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (n m-1)
    let D := fun m => deficit i (capacity (n m)) (b m) (l m)
      (eligibleMass μ i V/2) (eligibleHMass μ i V/eligibleMass μ i V)
    let p := fun m => (P m).real {x | 0 < D m x}
    let a := fun m => ∫ x, max (D m x) 0/Real.sqrt ((n m-1:ℕ):ℝ) ∂P m
    let b₂ := fun m => ∫ x, (max (D m x) 0/Real.sqrt ((n m-1:ℕ):ℝ))^2 ∂P m
    (∀ᶠ m in atTop, 0 < p m ∧ 0 < a m ∧ 0 < b₂ m) ∧
    ∃ R ≥ (1/2:ℝ), Tendsto (fun m => (a m)^2/(p m*b₂ m)) atTop (𝓝 R) := by
  have hN : Tendsto (fun m => n m-1) atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hNp (m : ℕ) : 0 < n m-1 := by have := hnp m; omega
  have hm := raw_central_moments μ i V B hV hB hvalue hadmissible hactive b l hbp hbt hlp hb hl
    (fun m => n m-1) (fun m => capacity (n m)) hNp hN hcentral
  have ha : 0 < Real.sqrt (limitingVariance μ i V) := Real.sqrt_pos.mpr
    (limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb)
  have hb' : 0 ≤ eligibleHMean μ i V*Real.sqrt (1-cutoff i) :=
    mul_nonneg (eligibleHMean_positive μ i V hV hvalue).le (Real.sqrt_nonneg _)
  have hratio := EntryCentralPassage.central_ratio_of_moments _ _ _ ha hb' hm.1 hm.2.1 hm.2.2
  exact ⟨hratio.1,_,hratio.2.2,hratio.2.1⟩

end FCAppendix.Affine.Uniform06.EntryRawCentral
