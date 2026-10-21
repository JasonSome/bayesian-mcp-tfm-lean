import FCAppendix.Affine.Uniform06.EntryRawCentral
import FCAppendix.Affine.Uniform06.EntryGoodEvent

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryRawGoodMoments

open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.LowBody
open EntryRawCentral EntryEarlySourceLimits EntryCentralSampling EntryProfileMean
open scoped BigOperators

def normalizedMoment (k N : ℕ) (D : ℝ) : ℝ :=
  if k=0 then (if 0< D then 1 else 0) else (max D 0/Real.sqrt (N:ℝ))^k

lemma normalizedMoment_nonneg (k N : ℕ) (D : ℝ) : 0 ≤ normalizedMoment k N D := by
  unfold normalizedMoment
  split_ifs <;> positivity

lemma measurable_normalizedMoment {Ξ : Type*} [MeasurableSpace Ξ]
    {D : Ξ → ℝ} (hD : Measurable D) (k N : ℕ) : Measurable (fun x => normalizedMoment k N (D x)) := by
  by_cases hk : k=0
  · subst k
    change Measurable (fun x => if 0 < D x then (1 : ℝ) else 0)
    exact Measurable.ite (measurableSet_lt measurable_const hD) measurable_const measurable_const
  · simp only [normalizedMoment,if_neg hk]
    exact ((hD.max measurable_const).div_const _).pow_const k

lemma measurable_selected (i : Row) (N : ℕ) (b l c hstar : ℝ) :
    Measurable (selected (N := N) i b l c hstar) := by
  exact measurable_guardedSample _ _ _
    (measurable_profileWeights _ _ _ _ (measurable_rawWeight i l) N)
    (measurable_profileH _ (measurable_rawH i b) N) (RawMixedSource.measurable_draws N) _ _

lemma measurable_deficit (i : Row) (N C : ℕ) (b l c hstar : ℝ) :
    Measurable (deficit (N := N) i C b l c hstar) :=
  (measurable_const.sub (Finset.measurable_sum _ (fun j _ =>
    (RawMixedSource.measurable_demand (xi i) b).comp
      ((measurable_pi_apply j).comp measurable_fst)))).sub (measurable_selected i N b l c hstar)

lemma selected_nonneg (i : Row) {N : ℕ} {b : ℝ} (hb : 0 < b) (l c : ℝ)
    {hstar : ℝ} (hhstar : 0 ≤ hstar) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    0 ≤ selected i b l c hstar x := by
  exact EntryIIDCentral.guardedSample_nonneg
    (fun r j => Fin.cases (by change (0 : ℝ) ≤ 1/2; norm_num)
      (fun j => (rawH_bounds i hb (r j)).1) j) hhstar x

lemma deficit_le_capacity (i : Row) {N : ℕ} (C : ℕ) {b : ℝ} (hb : 0 < b) (l c : ℝ)
    {hstar : ℝ} (hhstar : 0 ≤ hstar) (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    deficit i C b l c hstar x ≤ C := by
  have hsum : 0 ≤ ∑ j, RawMixedSource.demand (xi i) b (x.1 j) :=
    Finset.sum_nonneg fun j _ => (RawMixedSource.demand_bounds (xi_pos i) hb (x.1 j)).1
  have hsel := selected_nonneg i hb l c hhstar x
  unfold deficit
  linarith

theorem normalizedMoment_bound (i : Row) {N : ℕ} (hN : 0 < N)
    (C : ℕ) (hC : C ≤ N) {b : ℝ} (hb : 0 < b) (l c : ℝ)
    {hstar : ℝ} (hhstar : 0 ≤ hstar) (k : ℕ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    |normalizedMoment k N (deficit i C b l c hstar x)| ≤ (N:ℝ)^k := by
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hR : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hNp
  have hR1 : 1 ≤ Real.sqrt (N:ℝ) := by
    nlinarith [Real.sq_sqrt hNp.le,Real.sqrt_nonneg (N:ℝ)]
  have hCN : (C:ℝ) ≤ N := by exact_mod_cast hC
  have hmax : max (deficit i C b l c hstar x) 0 ≤ (N:ℝ) :=
    max_le ((deficit_le_capacity i C hb l c hhstar x).trans hCN) hNp.le
  have hnorm : max (deficit i C b l c hstar x) 0/Real.sqrt (N:ℝ) ≤ (N:ℝ) := by
    apply (div_le_iff₀ hR).mpr
    exact hmax.trans (by nlinarith [mul_le_mul_of_nonneg_left hR1 hNp.le])
  rw [abs_of_nonneg (normalizedMoment_nonneg _ _ _)]
  by_cases hk : k=0
  · subst k
    simp only [normalizedMoment,ite_true,pow_zero]
    split_ifs <;> norm_num
  · simp only [normalizedMoment,if_neg hk]
    exact pow_le_pow_left₀ (div_nonneg (le_max_right _ _) hR.le) hnorm k

def goodEvent (i : Row) (G : Measure (ℝ × ℝ)) (g : LiteralExperiment.GuardData)
    (N : ℕ) (ε activeLo U : ℝ) : Set (EntryIIDCentral.Row (Ω := RowRival) N) :=
  Prod.fst ⁻¹' RivalGood.good (RawMixedSource.source i G)
    (RivalGood.statistics (xi i) g.multiplier g.radius g.requiredDemand g.rejectionScale
      g.rejectionRoot g.seedCutoff activeLo U) N ε

lemma measurable_goodEvent (i : Row) (G : Measure (ℝ × ℝ)) (g : LiteralExperiment.GuardData)
    (N : ℕ) (ε activeLo U : ℝ) : MeasurableSet (goodEvent i G g N ε activeLo U) :=
  (RivalGood.measurable_good _ _
    (RivalGood.statistics_measurable (xi i) g.multiplier g.radius g.requiredDemand g.rejectionScale
      g.rejectionRoot g.seedCutoff activeLo U) N ε).preimage measurable_fst

theorem goodEvent_complement_le (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (g : LiteralExperiment.GuardData) (N : ℕ) (hN : 0 < N)
    (hlo : 0 < g.multiplier-g.radius) (hhi : 0 < g.multiplier+g.radius)
    (hd : 0 < g.rejectionScale) {ε : ℝ} (hε : 0 ≤ ε) (activeLo U : ℝ) :
    (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N).real
      (goodEvent i G g N ε activeLo U)ᶜ ≤ 18*Real.exp (-2*(N:ℝ)*ε^2) := by
  let f := RivalGood.statistics (xi i) g.multiplier g.radius g.requiredDemand g.rejectionScale
    g.rejectionRoot g.seedCutoff activeLo U
  let S := RivalGood.good (RawMixedSource.source i G) f N ε
  have hS := RivalGood.measurable_good (RawMixedSource.source i G) f (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _) N ε
  have hmap : (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N).real
      (goodEvent i G g N ε activeLo U)ᶜ=
      (Measure.pi (fun _ : Fin N => RawMixedSource.source i G)).real Sᶜ := by
    change ((EntryIIDCentral.rowLaw (RawMixedSource.source i G) N) (Prod.fst ⁻¹' Sᶜ)).toReal=_
    rw [← Measure.map_apply measurable_fst hS.compl]
    unfold EntryIIDCentral.rowLaw
    rw [(measurePreserving_fst (μ := Measure.pi (fun _ : Fin N => RawMixedSource.source i G))
      (ν := (volume : Measure unitInterval))).map_eq]
    rfl
  rw [hmap]
  simpa only [S,Fintype.card_fin,Nat.cast_ofNat,show (2:ℝ)*9=18 by norm_num] using! RivalGood.good_complement_le (RawMixedSource.source i G) f
    (fun k => (RivalGood.statistics_measurable _ _ _ _ _ _ _ _ _ k).aemeasurable)
    (fun k => Eventually.of_forall fun x => RivalGood.statistics_unit (xi_pos i) hlo hhi hd k x)
    N hN hε

theorem raw_good_moment_error (i : Row) (G : ℕ → Measure (ℝ × ℝ))
    [∀ m, IsProbabilityMeasure (G m)] (g : ℕ → LiteralExperiment.GuardData)
    (hlo : ∀ m, 0 < (g m).multiplier-(g m).radius)
    (hhi : ∀ m, 0 < (g m).multiplier+(g m).radius)
    (hd : ∀ m, 0 < (g m).rejectionScale)
    (N C : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (hC : ∀ m, C m ≤ N m) (b l : ℕ → ℝ) (hbp : ∀ m, 0 < b m)
    (c hstar : ℝ) (hhstar : 0 ≤ hstar) {ε : ℝ} (hε : 0 < ε)
    (activeLo U : ℕ → ℝ) (k : ℕ) :
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
    let E := fun m => goodEvent i (G m) (g m) (N m) ε (activeLo m) (U m)
    let F := fun m x => normalizedMoment k (N m) (deficit i (C m) (b m) (l m) c hstar x)
    Tendsto (fun m => |(∫ x in E m, F m x ∂P m)-(∫ x, F m x ∂P m)|) atTop (𝓝 0) := by
  dsimp only
  have hI (m : ℕ) : Integrable (fun x => normalizedMoment k (N m)
      (deficit i (C m) (b m) (l m) c hstar x))
      (EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)) :=
    Integrable.of_bound
      (measurable_normalizedMoment (measurable_deficit i (N m) (C m) (b m) (l m) c hstar) k (N m)).aestronglyMeasurable
      ((N m:ℝ)^k) (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using normalizedMoment_bound i (hNp m) (C m) (hC m)
          (hbp m) (l m) c hhstar k x)
  have hh := EntryGoodEvent.restricted_moment_relative_error_tendsto_zero
    (fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)) N hN
    (fun m => goodEvent i (G m) (g m) (N m) ε (activeLo m) (U m))
    (fun m => measurable_goodEvent i (G m) (g m) (N m) ε (activeLo m) (U m))
    (fun m x => normalizedMoment k (N m) (deficit i (C m) (b m) (l m) c hstar x)) hI
    (fun _ => 0) (fun _ => 1) tendsto_const_nhds
    (c := 2*ε^2) (C := 18) (by positivity) (by norm_num)
    (Eventually.of_forall fun _ => by norm_num)
    (Eventually.of_forall fun m => by
      simpa only [mul_assoc,mul_left_comm,mul_comm,neg_mul,mul_neg] using!
        goodEvent_complement_le i (G m) (g m) (N m) (hNp m) (hlo m) (hhi m) (hd m)
          hε.le (activeLo m) (U m)) k 0
    (fun m => Eventually.of_forall fun x => normalizedMoment_bound i (hNp m) (C m) (hC m)
      (hbp m) (l m) c hhstar k x)
  simpa using hh

lemma tendsto_of_abs_sub_tendsto {A B : ℕ → ℝ} {a : ℝ}
    (hB : Tendsto B atTop (𝓝 a)) (herror : Tendsto (fun m => |A m-B m|) atTop (𝓝 0)) :
    Tendsto A atTop (𝓝 a) := by
  have hdiff : Tendsto (fun m => A m-B m) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using herror.neg) herror
      (fun m => neg_abs_le (A m-B m)) (fun m => le_abs_self (A m-B m))
  simpa using hdiff.add hB

lemma zeroth_integral (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (N C : ℕ) (b l c hstar : ℝ) :
    (∫ x, normalizedMoment 0 N (deficit i C b l c hstar x)
      ∂EntryIIDCentral.rowLaw (RawMixedSource.source i G) N)=
      (EntryIIDCentral.rowLaw (RawMixedSource.source i G) N).real
        {x | 0 < deficit i C b l c hstar x} := by
  have hS : MeasurableSet {x : EntryIIDCentral.Row (Ω := RowRival) N |
      0 < deficit i C b l c hstar x} :=
    measurableSet_lt measurable_const (measurable_deficit i N C b l c hstar)
  have he : (fun x : EntryIIDCentral.Row (Ω := RowRival) N =>
      normalizedMoment 0 N (deficit i C b l c hstar x))=
      ({x : EntryIIDCentral.Row (Ω := RowRival) N | 0 < deficit i C b l c hstar x}).indicator (fun _ => (1:ℝ)) := by
    funext x
    simp [normalizedMoment,Set.indicator]
  rw [he,integral_indicator_const _ hS]
  simp only [smul_eq_mul,mul_one]

theorem literal_central_good_ratio {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m, Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m, ∀ᵐ ω ∂μ, B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ, entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (b : ℕ → ℝ) (hbp : ∀ m, 0 < b m) (hbt : ∀ m, b m ≤ cutoff i)
    (g : ℕ → LiteralExperiment.GuardData)
    (hlp : ∀ m, 0 < (g m).multiplier)
    (hlo : ∀ m, 0 < (g m).multiplier-(g m).radius)
    (hhi : ∀ m, 0 < (g m).multiplier+(g m).radius)
    (hd : ∀ m, 0 < (g m).rejectionScale)
    (hb : Tendsto b atTop (𝓝 (entry i)))
    (hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m, 4 ≤ n m) (hn : Tendsto n atTop atTop)
    {ε : ℝ} (hε : 0 < ε) (activeLo U : ℕ → ℝ)
    {z : ℝ} (hcentral : Tendsto (fun m => center i (joint μ V (B m))
      (n m-1) (capacity (n m)) (b m)) atTop (𝓝 z)) :
    let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (n m-1)
    let E := fun m => goodEvent i (joint μ V (B m)) (g m) (n m-1) ε (activeLo m) (U m)
    let D := fun m => deficit i (capacity (n m)) (b m) ((g m).multiplier)
      (eligibleMass μ i V/2) (eligibleHMean μ i V)
    let M := fun k m => ∫ x in E m, normalizedMoment k (n m-1) (D m x) ∂P m
    (∀ᶠ m in atTop, 0 < M 0 m ∧ 0 < M 1 m ∧ 0 < M 2 m) ∧
      ∃ R ≥ (1/2:ℝ), Tendsto (fun m => (M 1 m)^2/(M 0 m*M 2 m)) atTop (𝓝 R) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hNp (m : ℕ) : 0 < N m := by have := hnp m; dsimp [N]; omega
  have hC (m : ℕ) : capacity (n m) ≤ N m := (PhysicalRates.capacity_strictly_below_rivals (hnp m)).le
  have hhstar : 0 ≤ eligibleHMean μ i V := (eligibleHMean_positive μ i V hV hvalue).le
  have hmain := raw_central_moments μ i V B hV hB hvalue hadmissible hactive b
    (fun m => (g m).multiplier) hbp hbt hlp hb hl N (fun m => capacity (n m)) hNp hN hcentral
  have he (k : ℕ) := raw_good_moment_error i G g hlo hhi hd N (fun m => capacity (n m))
    hNp hN hC b (fun m => (g m).multiplier) hbp
    (eligibleMass μ i V/2) (eligibleHMean μ i V) hhstar hε activeLo U k
  have hfull0 := hmain.1
  have hfull1 := hmain.2.1
  have hfull2 := hmain.2.2
  have he0 := he 0
  simp_rw [zeroth_integral] at he0
  have he1 := he 1
  simp only [normalizedMoment,show (1:ℕ)≠0 by decide,if_false,pow_one] at he1
  have he2 := he 2
  simp only [normalizedMoment,show (2:ℕ)≠0 by decide,if_false] at he2
  have hp := tendsto_of_abs_sub_tendsto hfull0 he0
  have ha := tendsto_of_abs_sub_tendsto hfull1 he1
  have hb₂ := tendsto_of_abs_sub_tendsto hfull2 he2
  have hα : 0 < Real.sqrt (limitingVariance μ i V) := Real.sqrt_pos.mpr
    (limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb)
  have hβ : 0 ≤ eligibleHMean μ i V*Real.sqrt (1-cutoff i) := mul_nonneg hhstar (Real.sqrt_nonneg _)
  have hr := EntryCentralPassage.central_ratio_of_moments _ _ _ hα hβ hp ha hb₂
  refine ⟨?_,_,hr.2.2,?_⟩
  · simpa only [normalizedMoment,show (1:ℕ)≠0 by decide,show (2:ℕ)≠0 by decide,
      ite_true,if_false,pow_one,G,N] using hr.1
  · simpa only [normalizedMoment,show (1:ℕ)≠0 by decide,show (2:ℕ)≠0 by decide,
      ite_true,if_false,pow_one,G,N] using hr.2.1

end FCAppendix.Affine.Uniform06.EntryRawGoodMoments
