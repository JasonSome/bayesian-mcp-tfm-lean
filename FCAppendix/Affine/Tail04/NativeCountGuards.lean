import FCAppendix.Affine.Tail04.SourceRoleMasses
import FCAppendix.Affine.Hybrid.TypicalCounts
import FCAppendix.Game.CommonListSeeds

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeCountGuards
open MeasureTheory ProbabilityTheory Set Game Bayes
open Affine.Hybrid Affine.LowBody
open OriginalValues
open scoped BigOperators

theorem prob_ofMeasure {X A : Type*} [MeasurableSpace X] [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → A) (hf : Measurable f)
    (P : A → Prop) :
    (FiniteLaw.ofMeasure μ f hf).prob P = μ.real {x | P (f x)} := by
  classical
  rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_ofMeasure]
  have hP : MeasurableSet {a | P a} := (Set.to_countable _).measurableSet
  change (∫ ω,(f ⁻¹' {a | P a}).indicator (1 : X → ℝ) ω ∂μ) = _
  rw [integral_indicator_one (hP.preimage hf)]
  rfl

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (E : Observable.Regions)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hrow : (userLaw Γ).map (E.nativeRow Γ) = rivalLaw s a h G)

include hrow in
theorem one_native_category_law :
    FiniteLaw.ofMeasure (userLaw Γ) E.coarseTag E.measurable_coarseTag =
      categoryLaw s a h hs ha hh hsum G := by
  letI : IsProbabilityMeasure (rivalLaw s a h G) :=
    rivalLaw_isProbability s a h hs ha hh hsum G
  apply FiniteLaw.ofMeasure_eq_of_map_eq (userLaw Γ) (rivalLaw s a h G)
    E.coarseTag E.measurable_coarseTag Prod.fst measurable_fst
  calc
    _ = ((userLaw Γ).map (E.nativeRow Γ)).map Prod.fst := by
      rw [Measure.map_map measurable_fst (E.measurable_nativeRow Γ)]
      rfl
    _ = _ := by rw [hrow]

include hrow in
theorem original_row_category_law (N : ℕ) :
    FiniteLaw.ofMeasure (Measure.pi (fun _ : Fin N => userLaw Γ))
      (fun row i => E.coarseTag (row i))
      (measurable_pi_lambda _ fun i => E.measurable_coarseTag.comp (measurable_pi_apply i)) =
      CommonList.iid (categoryLaw s a h hs ha hh hsum G) N :=
  FiniteLaw.ofMeasure_pi_eq_iid (userLaw Γ) N (fun _ => E.coarseTag)
    (fun _ => E.measurable_coarseTag) _
    (fun _ => one_native_category_law Γ E s a h hs ha hh hsum G hrow)

include hrow in
theorem original_category_event (N : ℕ) (P : (Fin N → Fin 4) → Prop) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | P (fun i => E.coarseTag (row i))} =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob P := by
  rw [← original_row_category_law Γ E s a h hs ha hh hsum G hrow N,
    prob_ofMeasure]

include s a hs ha hh hsum G hrow in
theorem original_private_difference_le (N : ℕ) (hN : 0 < N)
    (hhpos : 0 < h) (hh1 : h ≤ 1) (offset : ℤ) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | upperDifference (fun i => E.coarseTag (row i)) = offset} ≤
      upperTieError h N := by
  rw [original_category_event Γ E s a h hs ha hh hsum G hrow N (fun row => upperDifference row=offset)]
  exact upperDifference_probability_le s a h hs ha hhpos hh1 hsum G N hN offset

include s a hs ha hh hsum G hrow in
theorem original_equal_private_prefix_le {r : ℕ} (fixed : Fin r → Fin 4)
    (N : ℕ) (hN : 0 < N) (hhpos : 0 < h) (hh1 : h ≤ 1) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | fullCategoryCount fixed (fun i => E.coarseTag (row i)) 2 =
        fullCategoryCount fixed (fun i => E.coarseTag (row i)) 3} ≤
      (6/h)/Real.sqrt N := by
  rw [original_category_event Γ E s a h hs ha hh hsum G hrow N (fun row => fullCategoryCount fixed row 2=fullCategoryCount fixed row 3)]
  have he : (fun row : Fin N → Fin 4 =>
      fullCategoryCount fixed row 2 = fullCategoryCount fixed row 3) =
      (fun row => upperDifference fixed+upperDifference row=0) := by
    funext row
    exact propext (full_upper_counts_equal_iff fixed row)
  rw [he]
  exact (forced_upperDifference_probability_le s a h hs ha hhpos hh1 hsum G
    fixed N hN 0).trans (upperTieError_le_six_div_sqrt hhpos hh1 N hN)

include s a hs ha hh hsum G hrow in
theorem original_equal_private_prefix_uniform {r : ℕ} (fixed : Fin r → Fin 4)
    (N : ℕ) (hN : 0 < N) (hbase : ℝ) (hb : 0 < hbase) (hbh : hbase ≤ h)
    (hh1 : h ≤ 1) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | fullCategoryCount fixed (fun i => E.coarseTag (row i)) 2 =
        fullCategoryCount fixed (fun i => E.coarseTag (row i)) 3} ≤
      (6/hbase)/Real.sqrt N := by
  apply (original_equal_private_prefix_le Γ E s a h hs ha hh hsum G hrow
    fixed N hN (hb.trans_le hbh) hh1).trans
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_left (by norm_num) hb hbh) (Real.sqrt_nonneg _)

include hrow in
theorem original_category_guard_le {r : ℕ} (fixed : Fin r → Fin 4)
    (N : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hroom : (r:ℝ) ≤ N*δ/2) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | ∃ k : Fin 4, (N+r:ℕ)*δ ≤
        |(categoryCount k fixed:ℝ)+
          (categoryCount k (fun i => E.coarseTag (row i)):ℝ)-
          (N+r:ℕ)*(categoryLaw s a h hs ha hh hsum G).mass k|} ≤
      8*Real.exp (-(N:ℝ)*δ^2/2) := by
  rw [original_category_event Γ E s a h hs ha hh hsum G hrow N (fun row => ∃ k : Fin 4,(N+r:ℕ)*δ ≤
    |(categoryCount k fixed:ℝ)+(categoryCount k row:ℝ)-(N+r:ℕ)*(categoryLaw s a h hs ha hh hsum G).mass k|)]
  exact forced_fractional_count_exception_le _ fixed N hδ hroom

theorem source_private_tie_bound (P : ValueParameters)
    (hF : Γ.F = valueLaw P) (t : ℝ) (ht : P.M ≤ t)
    (hlow : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ E.d ↔ x.1 ≤ P.d0)
    (hprivate : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ,
      x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t)
    {r : ℕ} (fixed : Fin r → Fin 4) (N : ℕ) (hN : 0 < N) :
    (Measure.pi (fun _ : Fin N => userLaw Γ)).real
      {row | fullCategoryCount fixed (fun i => E.coarseTag (row i)) 2 =
        fullCategoryCount fixed (fun i => E.coarseTag (row i)) 3} ≤
      (75/4:ℝ)/Real.sqrt N := by
  let hm := activeMass P.theta*P.zeta*powerTail P.M 10 t
  have hm0 : 0 ≤ hm := P.tailMass_nonneg t ht
  obtain ⟨hslow, hactive, hpriv⟩ :=
    P.native_source_category_masses E Γ hF t ht hlow hprivate
  have hsn : nativeActionLaw Γ E.lowActions ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hslow
    linarith [P.low_mass_pos]
  letI : IsProbabilityMeasure (cond (nativeActionLaw Γ) E.lowActions) :=
    cond_isProbabilityMeasure hsn
  let Glow : Measure ℝ := (cond (nativeActionLaw Γ) E.lowActions).map (fun a => a.bid)
  letI : IsProbabilityMeasure Glow :=
    Measure.isProbabilityMeasure_map (measurable_bid 2).aemeasurable
  have ha0 : 0 ≤ activeMass P.theta-hm := by
    rw [← hactive]
    exact measureReal_nonneg
  have hh0 : 0 ≤ partialMass+hm := by norm_num [partialMass]; linarith
  have hh1 : partialMass+hm ≤ 1 := by
    rw [← hpriv]
    exact measureReal_le_one
  have hsum : lowMass P.theta+(activeMass P.theta-hm)+(partialMass+hm)=1 := by
    have h := mass_sum P.theta
    linarith
  have hrow' : (userLaw Γ).map (E.nativeRow Γ) =
      rivalLaw (lowMass P.theta) (activeMass P.theta-hm) (partialMass+hm) Glow :=
    P.native_source_row E Γ hF t ht hlow hprivate
  have hb := original_equal_private_prefix_uniform Γ E
    (lowMass P.theta) (activeMass P.theta-hm) (partialMass+hm)
    P.low_mass_pos.le ha0 hh0 hsum Glow hrow' fixed N hN partialMass
    (by norm_num [partialMass]) (by linarith) hh1
  norm_num [partialMass] at hb
  exact hb

end FCAppendix.Affine.Tail04.NativeCountGuards
