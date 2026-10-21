import FCAppendix.Affine.Uniform06.EntryLiteralResponseGeometry

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralResponseMoments

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open EntryLiteralResponseGeometry EntryRawCentral EntryRawGoodMoments
open EntryEarlySourceLimits EntryReciprocalLimit EntryResponseTransfer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {N C : ℕ}

theorem raw_no_tag_one (i : Row) (G : Measure (ℝ × ℝ)) :
    ∀ᵐ r ∂ RawMixedSource.source i G,r.1 ≠ 1 := by
  unfold RawMixedSource.source rivalLaw
  simp only [ENNReal.ofReal_zero,zero_smul,add_zero,ae_add_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (by fun_prop) (by measurability)).mpr
    exact ae_of_all _ fun r => by norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff (by measurability)).mpr
    norm_num [Fin.ext_iff]

theorem raw_lower_cap (i : Row) (G : Measure (ℝ × ℝ)) {U : ℝ}
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    ∀ᵐ r ∂ RawMixedSource.source i G,r.1=0 → r.2 ≤ U := by
  have hbids : ∀ᵐ z ∂G.map Prod.snd,z ≤ U :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Iic).mpr hcap
  unfold RawMixedSource.source rivalLaw
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

theorem rawConditions_ae (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) (b U : ℝ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    ∀ᵐ x ∂ EntryIIDCentral.rowLaw (RawMixedSource.source i G) N,
      x ∈ rawConditions i g b U := by
  have hc := raw_lower_cap i G hcap
  have hn := raw_no_tag_one i G
  have hp (j : Fin N) := (EntryIIDCentral.eval_preserving (RawMixedSource.source i G) N j).quasiMeasurePreserving.ae (hn.and hc)
  have hs := EntryLiteralCentral.actual_sampler_positive_ae
    (Measure.pi (fun _ : Fin N => RawMixedSource.source i G))
    (profile i g b) RawMixedSource.draws (measurable_profile i g b) (RawMixedSource.measurable_draws N)
  filter_upwards [ae_all_iff.mpr hp,hs] with x hx hxs
  exact ⟨fun j => (hx j).1,fun j => (hx j).2,hxs⟩

theorem usable_ae_good (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) (b A U ε : ℝ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    usable (N := N) (RawMixedSource.source i G) i g b A U ε =ᵐ[
      EntryIIDCentral.rowLaw (RawMixedSource.source i G) N]
      goodEvent i G g N ε A U := by
  filter_upwards [rawConditions_ae i G g b U hcap] with x hx
  apply propext
  change ((x.1 ∈ RivalGood.good (RawMixedSource.source i G)
    (ActualEntryGoodGeometry.tests (xi i) g A U) N ε) ∧ x ∈ rawConditions i g b U) ↔ _
  exact and_iff_left hx

def normalizedGoodDeficit (μ : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  if x ∈ usable μ i g b A U ε then
    max (deficit i C b g.multiplier c hstar x) 0/Real.sqrt (N:ℝ) else 0

lemma measurable_normalizedGoodDeficit (μ : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε c hstar : ℝ) :
    Measurable (normalizedGoodDeficit (N := N) μ i C g b A U ε c hstar) :=
  Measurable.ite (measurable_usable μ i g b A U ε)
    (((measurable_deficit i N C b g.multiplier c hstar).max measurable_const).div_const _) measurable_const

lemma normalizedGoodDeficit_nonneg (μ : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    0 ≤ normalizedGoodDeficit μ i C g b A U ε c hstar x := by
  unfold normalizedGoodDeficit
  split_ifs <;> positivity

lemma normalizedGoodDeficit_le (μ : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε c hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    normalizedGoodDeficit μ i C g b A U ε c hstar x ≤
      max (deficit i C b g.multiplier c hstar x) 0/Real.sqrt (N:ℝ) := by
  unfold normalizedGoodDeficit
  split_ifs
  · exact le_rfl
  · positivity

lemma normalizedGoodDeficit_memLp (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) {b : ℝ} (hb : 0 < b) (A U ε c hstar : ℝ)
    (hhstar : 0 ≤ hstar) (hN : 0 < N) (C : ℕ) (k : ENNReal) :
    MemLp (normalizedGoodDeficit (N := N) (RawMixedSource.source i G) i C g b A U ε c hstar) k
      (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) := by
  exact (EntryRawCentralTransfer.raw_deficit_memLp i G hN C hb g.multiplier c hstar hhstar k).indicator
    (measurable_usable _ i g b A U ε)

theorem normalizedGoodDeficit_moment_eq (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) (b A U ε c hstar : ℝ)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (k : ℕ) (hk : 0 < k) :
    (∫ x, (normalizedGoodDeficit (N := N) (RawMixedSource.source i G) i C g b A U ε c hstar x)^k
      ∂ EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      ∫ x in goodEvent i G g N ε A U, normalizedMoment k N
        (deficit i C b g.multiplier c hstar x) ∂ EntryIIDCentral.rowLaw (RawMixedSource.source i G) N := by
  rw [← integral_indicator (measurable_goodEvent i G g N ε A U)]
  apply integral_congr_ae
  filter_upwards [usable_ae_good i G g b A U ε hcap] with x hx
  by_cases he : x ∈ usable (RawMixedSource.source i G) i g b A U ε
  · have hg : x ∈ goodEvent i G g N ε A U := hx.mp he
    simp [normalizedGoodDeficit,normalizedMoment,he,hg,Nat.ne_of_gt hk,Set.indicator]
  · have hg : x ∉ goodEvent i G g N ε A U := fun hh => he (hx.mpr hh)
    simp [normalizedGoodDeficit,he,hg,Nat.ne_of_gt hk,Set.indicator]

theorem finite_displacement (μ : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    0 ≤ b-price μ i C g b A U ε x ∧
      b-price μ i C g b A U ε x ≤ (xi i/(q/(2*U)))*
        max (deficit i C b g.multiplier c hstar x) 0/(N:ℝ) := by
  have hf := total_finite_geometry μ i g h hstar x
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hc : 0 < q/(2*U) := div_pos h.strip_pos (by have := h.cap_pos; positivity)
  by_cases hp : 0 < response μ i C g b A U ε x
  · have hx := (hf.2.2.2.2.2.2.mp hp).1
    have hK : (q/(2*U))*(N:ℝ) ≤ slope μ i C g b A U ε x := by
      convert! hf.2.2.2.2.2.1 hp using 1; ring
    exact EntryRawCentralTransfer.finite_root_displacement h.rivals_pos (xi_pos i) hb hc hK
      (hf.2.2.2.2.1 hx) rfl
  · have hq : response μ i C g b A U ε x=0 := by
      apply le_antisymm (le_of_not_gt hp)
      unfold response
      split_ifs
      · exact (EntryLiteralResponseGeometry.complement_bounds i C g b x).1
      · exact le_rfl
    simp only [price,hq,mul_zero,sub_zero,mul_one,sub_self,le_refl,true_and]
    have hξ := xi_pos i
    positivity

theorem slope_normalized_bounds (μ : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    slope μ i C g b A U ε x/(N:ℝ) ∈ Icc (0:ℝ) (2/lo) := by
  have hf := total_finite_geometry μ i g h hstar x
  have hn : (0:ℝ)< N := by exact_mod_cast h.rivals_pos
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hk0 : 0 ≤ slope μ i C g b A U ε x :=
    (ReciprocalSecantBounds.reciprocalSum_nonneg _ _ hb).trans hf.2.2.1
  refine ⟨div_nonneg hk0 hn.le,?_⟩
  have hr := hf.2.2.2.1.trans
    (ReciprocalSecantBounds.reciprocalSum_le _ _ (h.lo_pos.trans_le hf.1))
  simp only [Fintype.card_fin,Nat.cast_add_one] at hr
  have hupper : slope μ i C g b A U ε x ≤ ((N:ℝ)+1)/lo := hr.trans
    (div_le_div_of_nonneg_left (by positivity) h.lo_pos hf.1)
  apply (div_le_iff₀ hn).mpr
  apply hupper.trans
  apply (div_le_iff₀ h.lo_pos).mpr
  have hid : (2/lo)*(N:ℝ)*lo=2*(N:ℝ) := by field_simp [h.lo_pos.ne']
  rw [hid]
  have hN1 : (1:ℝ)≤ N := by exact_mod_cast (show 1≤ N from h.rivals_pos)
  linarith

theorem response_coefficient_exact (μ : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s d : ℝ} (h : Inputs μ i g N C b A U ε c q lo γ w s)
    (_hd : 0 < d) (hdq : d ≤ q/(2*U)) (hstar : ℝ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    Real.sqrt (N:ℝ)*response μ i C g b A U ε x=
      coefficient N b d (slope μ i C g b A U ε x/(N:ℝ))*
        normalizedGoodDeficit μ i C g b A U ε c hstar x := by
  have hf := total_finite_geometry μ i g h hstar x
  have hn : (0:ℝ)< N := by exact_mod_cast h.rivals_pos
  have hr : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hn
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hK0 := (slope_normalized_bounds μ i g h hstar x).1
  have hKn : 0 ≤ slope μ i C g b A U ε x := by
    have hh := mul_nonneg hK0 hn.le
    rwa [div_mul_cancel₀ _ hn.ne'] at hh
  have hden : 0 < 1+b*slope μ i C g b A U ε x := by positivity
  by_cases hp : 0 < response μ i C g b A U ε x
  · have hx := (hf.2.2.2.2.2.2.mp hp).1
    have hbound : d ≤ slope μ i C g b A U ε x/(N:ℝ) := by
      apply (le_div_iff₀ hn).mpr
      have hh := mul_le_mul_of_nonneg_right hdq hn.le
      have hid : (q/(2*U))*(N:ℝ)=q*(N:ℝ)/(2*U) := by ring
      rw [hid] at hh
      exact hh.trans (hf.2.2.2.2.2.1 hp)
    rw [hf.2.2.2.2.1 hx,normalizedGoodDeficit,if_pos hx,coefficient,max_eq_right hbound]
    have hden' : 1/(N:ℝ)+b*(slope μ i C g b A U ε x/(N:ℝ))=
        (1+b*slope μ i C g b A U ε x)/(N:ℝ) := by ring
    rw [hden']
    field_simp [hn.ne',hr.ne',hden.ne']
    rw [Real.sq_sqrt hn.le]
    ring
  · have hq0 : response μ i C g b A U ε x=0 := by
      apply le_antisymm (le_of_not_gt hp)
      unfold response
      split_ifs
      · exact (EntryLiteralResponseGeometry.complement_bounds i C g b x).1
      · exact le_rfl
    have hZ : normalizedGoodDeficit μ i C g b A U ε c hstar x=0 := by
      unfold normalizedGoodDeficit
      split_ifs with hx
      · have hnot : ¬ 0 < deficit i C b g.multiplier c hstar x :=
          fun hh => hp (hf.2.2.2.2.2.2.mpr ⟨hx,hh⟩)
        rw [max_eq_right (le_of_not_gt hnot),zero_div]
      · rfl
    rw [hq0,hZ,mul_zero,mul_zero]

theorem response_success_eq (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) {b A U ε c q lo γ w s : ℝ}
    (h : Inputs (RawMixedSource.source i G) i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (hcap : ∀ᵐ p ∂G,p.2 ≤ U) :
    (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N).real
      {x | 0 < response (RawMixedSource.source i G) i C g b A U ε x}=
      ∫ x in goodEvent i G g N ε A U,
        normalizedMoment 0 N (deficit i C b g.multiplier c hstar x)
        ∂ EntryIIDCentral.rowLaw (RawMixedSource.source i G) N := by
  let P := EntryIIDCentral.rowLaw (RawMixedSource.source i G) N
  let S := {x : EntryIIDCentral.Row (Ω := RowRival) N |
    0 < response (RawMixedSource.source i G) i C g b A U ε x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const
    (measurable_response _ i C g b A U ε)
  have hI : (∫ x, S.indicator (fun _ => (1:ℝ)) x ∂P)=P.real S := by
    rw [integral_indicator_const _ hS,smul_eq_mul,mul_one]
  rw [← hI,← integral_indicator (measurable_goodEvent i G g N ε A U)]
  apply integral_congr_ae
  filter_upwards [usable_ae_good i G g b A U ε hcap] with x hx
  have hf := (total_finite_geometry (RawMixedSource.source i G) i g h hstar x).2.2.2.2.2.2
  by_cases he : x ∈ goodEvent i G g N ε A U <;>
    by_cases hd : 0 < deficit i C b g.multiplier c hstar x
  · have hp := hf.mpr ⟨hx.mpr he,hd⟩
    simp [S,Set.indicator,he,hd,hp,normalizedMoment]
  · have hp : ¬ 0 < response (RawMixedSource.source i G) i C g b A U ε x :=
      fun hh => hd (hf.mp hh).2
    simp [S,Set.indicator,he,hd,hp,normalizedMoment]
  · have hp : ¬ 0 < response (RawMixedSource.source i G) i C g b A U ε x :=
      fun hh => he (hx.mp (hf.mp hh).1)
    simp [S,Set.indicator,he,hp]
  · have hp : ¬ 0 < response (RawMixedSource.source i G) i C g b A U ε x :=
      fun hh => he (hx.mp (hf.mp hh).1)
    simp [S,Set.indicator,he,hp]

section OriginalCentral
variable {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem original_central_response_moments
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbt : ∀ m, b m ≤ cutoff i) (hb : Tendsto b atTop (𝓝 (entry i)))
    (g : ℕ → LiteralExperiment.GuardData)
    (hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m, 4 ≤ n m) (hn : Tendsto n atTop atTop)
    {ε q U lo : ℝ} (hε : 0 < ε) (hloLam : lo < entry i)
    (A γ w s : ℕ → ℝ)
    (hcap : ∀ m, ∀ᵐ p ∂joint μ V (B m),p.2 ≤ U)
    (hfinite : ∀ m, Inputs (RawMixedSource.source i (joint μ V (B m))) i (g m)
      (n m-1) (capacity (n m)) (b m) (A m) U ε (eligibleMass μ i V/2) q lo (γ m) (w m) (s m))
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m))
      (n m-1) (capacity (n m)) (b m)) atTop (𝓝 z)) :
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (n m-1)
    let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (n m-1) → ℝ := fun m => response (RawMixedSource.source i (joint μ V (B m))) i
      (capacity (n m)) (g m) (b m) (A m) U ε
    let α := Real.sqrt (limitingVariance μ i V)
    let β := eligibleHMean μ i V*Real.sqrt (1-cutoff i)
    let κ := reciprocalMean μ i V
    Tendsto (fun m => (P m).real {x | 0 < p m x}) atTop
      (𝓝 (EntryCentralRatio.success α β z)) ∧
    Tendsto (fun m => ∫ x, Real.sqrt ((n m-1:ℕ):ℝ)*p m x ∂P m) atTop
      (𝓝 (EntryCentralRatio.firstMoment α β z/(entry i*κ))) ∧
    Tendsto (fun m => ∫ x, (Real.sqrt ((n m-1:ℕ):ℝ)*p m x)^2 ∂P m) atTop
      (𝓝 (EntryCentralRatio.secondMoment α β z/(entry i*κ)^2)) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let C := fun m => capacity (n m)
  let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
  let κ := reciprocalMean μ i V
  let d := min (q/(2*U)) (κ/2)
  let a0 := 1/(entry i*κ)
  let D : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => deficit i (C m) (b m) ((g m).multiplier)
    (eligibleMass μ i V/2) (eligibleHMean μ i V)
  let Z : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => normalizedGoodDeficit (RawMixedSource.source i (G m)) i (C m) (g m)
    (b m) (A m) U ε (eligibleMass μ i V/2) (eligibleHMean μ i V)
  let p : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => response (RawMixedSource.source i (G m)) i (C m) (g m) (b m) (A m) U ε
  let Λ : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => price (RawMixedSource.source i (G m)) i (C m) (g m) (b m) (A m) U ε
  let K : (m : ℕ) → EntryIIDCentral.Row (Ω := RowRival) (N m) → ℝ := fun m => slope (RawMixedSource.source i (G m)) i (C m) (g m) (b m) (A m) U ε
  let a := fun m x => coefficient (N m) (b m) d (K m x/(N m:ℝ))
  let X := fun m x => Real.sqrt (N m:ℝ)*p m x
  let Y := fun m x => a0*Z m x
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hNp (m) : 0 < N m := (hfinite m).rivals_pos
  have hC (m) : C m ≤ N m := (PhysicalRates.capacity_strictly_below_rivals (hnp m)).le
  have hlo : 0 < lo := (hfinite 0).lo_pos
  have hU : 0 < U := (hfinite 0).cap_pos
  have hq : 0 < q := (hfinite 0).strip_pos
  have hLam := EarlyMean.entry_pos i
  have hκ : 0 < κ := reciprocalMean_positive μ i V hV hvalue
  have hd : 0 < d := lt_min (div_pos hq (by positivity)) (by positivity)
  have hdq : d ≤ q/(2*U) := min_le_left _ _
  have hdκ : d ≤ κ := (min_le_right _ _).trans (by linarith)
  have hhstar := (eligibleHMean_positive μ i V hV hvalue).le
  have hblo (m) : lo ≤ b m := (hfinite m).lower_price.trans (hfinite m).bid_window.1
  have hbp (m) : 0 < b m := hlo.trans_le (hblo m)
  have hlp (m) : 0 < (g m).multiplier := by
    linarith [(hfinite m).prefix.lower_pos,(hfinite m).radius_pos]
  have hLo (m) : 0 < (g m).multiplier-(g m).radius := (hfinite m).prefix.lower_pos
  have hHi (m) : 0 < (g m).multiplier+(g m).radius := by
    linarith [hLo m,(hfinite m).radius_pos]
  have hscale (m) : 0 < (g m).rejectionScale := (hfinite m).prefix.rejectionScale_pos
  have hraw := raw_central_moments μ i V B hV hB hvalue hadmissible hactive b
    (fun m => (g m).multiplier) hbp hbt hlp hb hl N C hNp hN hcentral
  have he (k : ℕ) := raw_good_moment_error i G g hLo hHi hscale N C hNp hN hC
    b (fun m => (g m).multiplier) hbp (eligibleMass μ i V/2) (eligibleHMean μ i V)
    hhstar hε A (fun _ => U) k
  have hPgood := he 0
  simp_rw [zeroth_integral] at hPgood
  have hpLim := tendsto_of_abs_sub_tendsto hraw.1 hPgood
  have hP : Tendsto (fun m => (P m).real {x | 0 < p m x}) atTop
      (𝓝 (EntryCentralRatio.success (Real.sqrt (limitingVariance μ i V))
        (eligibleHMean μ i V*Real.sqrt (1-cutoff i)) z)) := by
    convert! hpLim using 1
    funext m
    exact response_success_eq i (G m) (g m) (hfinite m) (eligibleHMean μ i V) (hcap m)
  have he1 := he 1
  simp only [normalizedMoment,show (1:ℕ)≠0 by decide,if_false,pow_one] at he1
  have he2 := he 2
  simp only [normalizedMoment,show (2:ℕ)≠0 by decide,if_false] at he2
  have hZA : Tendsto (fun m => ∫ x, Z m x ∂P m) atTop
      (𝓝 (EntryCentralRatio.firstMoment (Real.sqrt (limitingVariance μ i V))
        (eligibleHMean μ i V*Real.sqrt (1-cutoff i)) z)) := by
    have hh := tendsto_of_abs_sub_tendsto hraw.2.1 he1
    convert! hh using 1
    funext m
    simpa only [pow_one,normalizedMoment,show (1:ℕ)≠0 by decide,if_false] using
      normalizedGoodDeficit_moment_eq (N := N m) (C := C m) i (G m) (g m) (b m) (A m) U ε
        (eligibleMass μ i V/2) (eligibleHMean μ i V) (hcap m) 1 (by norm_num)
  have hZB : Tendsto (fun m => ∫ x, (Z m x)^2 ∂P m) atTop
      (𝓝 (EntryCentralRatio.secondMoment (Real.sqrt (limitingVariance μ i V))
        (eligibleHMean μ i V*Real.sqrt (1-cutoff i)) z)) := by
    have hh := tendsto_of_abs_sub_tendsto hraw.2.2 he2
    convert! hh using 1
    funext m
    simpa only [normalizedMoment,show (2:ℕ)≠0 by decide,if_false] using
      normalizedGoodDeficit_moment_eq (N := N m) (C := C m) i (G m) (g m) (b m) (A m) U ε
        (eligibleMass μ i V/2) (eligibleHMean μ i V) (hcap m) 2 (by norm_num)
  have hZm (m) : Measurable (Z m) := measurable_normalizedGoodDeficit _ i _ _ _ _ _ _ _ _
  have hZlp (m) (k : ENNReal) : MemLp (Z m) k (P m) := normalizedGoodDeficit_memLp i (G m)
    (g m) (hbp m) (A m) U ε (eligibleMass μ i V/2) (eligibleHMean μ i V) hhstar (hNp m) (C m) k
  have hZb (m) (x) : |Z m x| ≤ (N m:ℝ) := by
    rw [abs_of_nonneg (normalizedGoodDeficit_nonneg _ i _ _ _ _ _ _ _ _ x)]
    have hh := normalizedMoment_bound i (hNp m) (C m) (hC m) (hbp m)
      ((g m).multiplier) (eligibleMass μ i V/2) hhstar 1 x
    simp only [normalizedMoment,show (1:ℕ)≠0 by decide,if_false,pow_one] at hh
    exact (normalizedGoodDeficit_le _ i _ _ _ _ _ _ _ _ x).trans
      ((le_abs_self _).trans hh)
  have hLm (m) : Measurable (Λ m) := measurable_price _ i _ _ _ _ _ _
  have hKm (m) : Measurable (K m) := measurable_slope _ i _ _ _ _ _ _
  have hgeom (m) (x) := total_finite_geometry (RawMixedSource.source i (G m)) i (g m)
    (hfinite m) (eligibleHMean μ i V) x
  have hmove := EntryRawCentralTransfer.central_root_displacement μ i V B hV hB hvalue
    hadmissible hactive b (fun m => (g m).multiplier) hbp hbt hlp hb hl N C hNp hN hcentral
    Λ hLm (A := xi i/(q/(2*U))) (by have := xi_pos i; positivity)
    (fun m x => finite_displacement _ i (g m) (hfinite m) (eligibleHMean μ i V) x)
  have hKlim := EntryRandomReciprocal.actual_random_reciprocal_L1 μ i V B hV hB hvalue
    hadmissible hactive hlo hloLam b hblo hb N hNp hN
    (fun m => profile i (g m) (b m)) (fun m => measurable_profile i (g m) (b m))
    Λ K hLm hKm (fun m x => ⟨(hgeom m x).1,(hgeom m x).2.1⟩)
    (fun m x => ⟨(hgeom m x).2.2.1,(hgeom m x).2.2.2.1⟩) hmove
  have hKi (m) : Integrable (fun x => |K m x/(N m:ℝ)-κ|) (P m) := by
    apply Integrable.of_bound (((hKm m).div_const _).sub_const κ).abs.aestronglyMeasurable (2/lo+|κ|)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      have hh := slope_normalized_bounds _ i (g m) (hfinite m) (eligibleHMean μ i V) x
      calc
        |K m x/(N m:ℝ)-κ| ≤ |K m x/(N m:ℝ)|+|κ| := abs_sub _ _
        _ ≤ 2/lo+|κ| := add_le_add (by
          rw [abs_of_nonneg (show 0 ≤ K m x/(N m:ℝ) from hh.1)]
          exact hh.2) le_rfl
  have haLim := coefficient_L1 P N hN b hlo hLam hblo hb hd hκ hdκ
    (fun m x => K m x/(N m:ℝ)) (fun m => (hKm m).div_const _) hKi hKlim
  have ham (m) : Measurable (a m) := by
    dsimp only [a,coefficient]
    fun_prop
  let e := fun m x => a m x-a0
  have hem (m) : Measurable (e m) := (ham m).sub_const _
  have heb (m) (x) : |e m x| ≤ 1/(lo*d)+|a0| := by
    have ha := coefficient_bounds hlo (hblo m) hd (N := N m) (k := K m x/(N m:ℝ))
    calc
      |e m x| ≤ |a m x|+|a0| := abs_sub _ _
      _ ≤ 1/(lo*d)+|a0| := add_le_add (by
        rw [abs_of_pos (show 0 < a m x from ha.1)]
        exact ha.2) le_rfl
  let M := 8*(|z|+1)^4+16*|FCAppendix.Probability.gaussianMomentConstant 4 2|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hZ4 : ∀ᶠ m in atTop, (∫ x, (Z m x)^4 ∂P m) ≤ M := by
    have hcent := hcentral.abs.eventually_lt_const (show (|z| : ℝ) < |z|+1 by linarith)
    filter_upwards [hcent] with m hm
    have hraw4 := EntryRawCentralTransfer.raw_deficit_fourth i (G m) (hNp m) (C m) (hbp m)
      ((g m).multiplier) (eligibleMass μ i V/2) (eligibleHMean μ i V) hhstar
    have hRlp := EntryRawCentralTransfer.raw_deficit_memLp i (G m) (hNp m) (C m) (hbp m)
      ((g m).multiplier) (eligibleMass μ i V/2) (eligibleHMean μ i V) hhstar 4
    have hZi : Integrable (fun x => (Z m x)^4) (P m) := by
      simpa only [Real.norm_eq_abs,show (4:ℕ)=2*2 by norm_num,pow_mul,sq_abs] using
        (hZlp m 4).integrable_norm_pow (by norm_num : (4:ℕ)≠0)
    have hRi : Integrable (fun x => (max (D m x) 0/Real.sqrt (N m:ℝ))^4) (P m) := by
      simpa only [Real.norm_eq_abs,show (4:ℕ)=2*2 by norm_num,pow_mul,sq_abs] using!
        hRlp.integrable_norm_pow (by norm_num : (4:ℕ)≠0)
    have hmon := integral_mono hZi hRi (fun x => pow_le_pow_left₀
      (normalizedGoodDeficit_nonneg _ i _ _ _ _ _ _ _ _ x)
      (normalizedGoodDeficit_le _ i _ _ _ _ _ _ _ _ x) 4)
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hm.le 4
    have hceq : |center i (G m) (N m) (C m) (b m)|^4=
        (center i (G m) (N m) (C m) (b m))^4 := by
      rw [show (4:ℕ)=2*2 by norm_num,pow_mul,pow_mul,sq_abs]
    rw [hceq] at hpow
    exact hmon.trans (hraw4.trans (by dsimp [M]; nlinarith [le_abs_self (FCAppendix.Probability.gaussianMomentConstant 4 2)]))
  have heL2 := dependent_coefficient_L2 P Z e hZm hem (fun m => (N m:ℝ)) hZb
    (show 0 ≤ 1/(lo*d)+|a0| by positivity) heb hM hZ4 haLim
  have hXeq (m) (x) : X m x=a m x*Z m x :=
    response_coefficient_exact _ i (g m) (hfinite m) hd hdq (eligibleHMean μ i V) x
  have hXlp (m) : MemLp (X m) 2 (P m) := by
    apply MemLp.of_bound ((measurable_response _ i _ _ _ _ _ _).const_mul _).aestronglyMeasurable
      (Real.sqrt (N m:ℝ))
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      have hp : p m x ∈ Icc (0:ℝ) 1 := by
        dsimp [p,response]
        split_ifs
        · exact EntryLiteralResponseGeometry.complement_bounds i (C m) (g m) (b m) x
        · norm_num
      rw [abs_of_nonneg hp.1]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp.2 (Real.sqrt_nonneg _)
  have hYlp (m) : MemLp (Y m) 2 (P m) := (hZlp m 2).const_mul a0
  have herr : Tendsto (fun m => ∫ x, (X m x-Y m x)^2 ∂P m) atTop (𝓝 0) := by
    convert! heL2 using 1
    funext m
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change (X m x-Y m x)^2=(Z m x*e m x)^2
      rw [hXeq]
      dsimp only [Y,e]
      ring
  have hYA : Tendsto (fun m => ∫ x, Y m x ∂P m) atTop
      (𝓝 (a0*EntryCentralRatio.firstMoment (Real.sqrt (limitingVariance μ i V))
        (eligibleHMean μ i V*Real.sqrt (1-cutoff i)) z)) := by
    simpa only [Y,integral_const_mul] using hZA.const_mul a0
  have hYB : Tendsto (fun m => ∫ x, (Y m x)^2 ∂P m) atTop
      (𝓝 (a0^2*EntryCentralRatio.secondMoment (Real.sqrt (limitingVariance μ i V))
        (eligibleHMean μ i V*Real.sqrt (1-cutoff i)) z)) := by
    simpa only [Y,mul_pow,integral_const_mul] using hZB.const_mul (a0^2)
  have hout := moments_of_L2 P X Y hXlp hYlp hYA hYB herr
  refine ⟨hP,?_,?_⟩
  · simpa only [X,p,G,P,N,a0,κ,div_eq_mul_inv,mul_pow,mul_inv_rev,inv_pow,mul_assoc,mul_comm,mul_left_comm,one_mul,one_pow] using! hout.1
  · simpa only [X,p,G,P,N,a0,κ,div_eq_mul_inv,mul_pow,mul_inv_rev,inv_pow,mul_assoc,mul_comm,mul_left_comm,one_mul,one_pow] using! hout.2

end OriginalCentral

end FCAppendix.Affine.Uniform06.EntryLiteralResponseMoments
