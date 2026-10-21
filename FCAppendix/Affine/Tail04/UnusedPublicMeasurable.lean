import FCAppendix.Affine.Tail04.NativeUnusedReference

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedPublicMeasurable
open MeasureTheory ProbabilityTheory Set Classical
open PublicScenario EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open MenuError UnusedPublicLaw UnusedPublicPrices UnusedFiniteCountError
open UnusedFocalCountError FocalInsertion
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

lemma measurable_listMinimum {I X : Type*} [MeasurableSpace X]
    (xs : List I) (f : X→ I→ℝ) (hf : ∀i∈xs,Measurable (fun x=> f x i)) :
    Measurable (fun x=> TypicalGuard.listMinimum xs (f x)) := by
  induction xs with
  | nil => exact measurable_const
  | cons i xs ih =>
    exact (hf i (by simp)).min (ih (fun j hj=> hf j (by simp [hj])))

lemma measurable_finiteMinimum {I X : Type*} [Fintype I] [MeasurableSpace X]
    (f : X→ I→ℝ) (hf : ∀i,Measurable (fun x=> f x i)) :
    Measurable (fun x=> TypicalGuard.finiteMinimum (f x)) :=
  measurable_listMinimum _ _ (fun i _=> hf i)

lemma measurable_realizationMargin (A H c : ℕ) (ξ B : ℝ) (reg : Bool)
    (O I : Finset (Fin A)) : Measurable (fun b : Fin A→ℝ=>
      TypicalGuard.realizationMargin A H c ξ B reg O I b) := by
  apply measurable_finiteMinimum
  intro z
  exact ((measurable_baseline_realization A H c ξ reg O I z).sub measurable_const).min
    (measurable_const.sub (measurable_baseline_realization A H c ξ reg O I z))

lemma measurable_partialMargin (A H0 H1 c : ℕ) (ξ R Rp : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin A)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (fun b : Fin A→ℝ=>
      TypicalGuard.partialMargin A H0 H1 c ξ R Rp reg I O0 O1 b ν0 ν1) := by
  cases reg
  · exact (measurable_const.sub (measurable_baseline A H0 c ξ false O0 I ν0)).min
      (measurable_const.sub (measurable_baseline A H1 c ξ false O1 I ν1))
  · exact ((measurable_baseline A H0 c ξ true O0 I ν0).sub measurable_const).min
      ((measurable_baseline A H1 c ξ true O1 I ν1).sub measurable_const)

lemma measurable_margin (A H0 H1 c : ℕ) (ξ B R Rp : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin A)) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) :
    Measurable (fun b : Fin A→ℝ=>
      TypicalGuard.margin A H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1) :=
  ((measurable_realizationMargin A H0 c ξ B reg O0 I).min
    (measurable_realizationMargin A H1 c ξ B reg O1 I)).min
      (measurable_partialMargin A H0 H1 c ξ R Rp reg I O0 O1 ν0 ν1)

lemma measurable_weight (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B R Rp width : ℝ) (s : Scenario A) :
    Measurable (fun b : Fin A→ℝ=> PublicWeightLaw.weight Q A H B R Rp width b s) := by
  unfold PublicWeightLaw.weight TypicalGuard.weight
  split_ifs
  · exact measurable_const.min (measurable_const.max
      ((measurable_margin A H.1 H.2 Q.c Q.ξ B R Rp (regime s)
        (mixed s) (owner0 s) (owner1 s) (Q.marksLaw H.1) (Q.marksLaw H.2)).div_const width))
  · exact measurable_const

lemma measurable_price0 (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (s : Scenario A) :
    Measurable (fun b : Fin A→ℝ=> price0 Q A H b s) := by
  unfold price0 WeightedFlagBound.meanMixedPrice
  exact measurable_const.div (measurable_reciprocal A (mixed s))

lemma measurable_price1 (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ) (s : Scenario A) :
    Measurable (fun b : Fin A→ℝ=> price1 Q A H b s) := by
  unfold price1 WeightedFlagBound.meanMixedPrice
  exact measurable_const.div (measurable_reciprocal A (mixed s))

lemma measurableSet_safe (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ : ℝ) (s : Scenario A) :
    MeasurableSet {b : Fin A→ℝ | Safe Q A H B B0 R Rp width γ b s} :=
  (FocalInsertion.measurableSet_guard A H.1 H.2 Q.c Q.ξ B R Rp (regime s)
    (mixed s) (owner0 s) (owner1 s) (Q.marksLaw H.1) (Q.marksLaw H.2)).inter
      ((measurableSet_eq_fun (measurable_weight Q A H B R Rp width s) measurable_const).inter
        (measurableSet_le measurable_const (measurable_margin A H.1 H.2 Q.c Q.ξ B0 R Rp
          (regime s) (mixed s) (owner0 s) (owner1 s) (Q.marksLaw H.1) (Q.marksLaw H.2))))

lemma measurableSet_strongSafe (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) (s : Scenario A) :
    MeasurableSet {b : Fin A→ℝ | StrongSafe Q A H B B0 R Rp width γ a b s} := by
  have hc : MeasurableSet {b : Fin A→ℝ |
      |NativeTypicalCount.privateMean H.2 (regime s) (Q.marksLaw H.2)-
        NativeTypicalCount.privateMean H.1 (regime s) (Q.marksLaw H.1)|≤(A-(mixed s).card:ℕ)} :=
    measurableSet_le measurable_const measurable_const
  exact (measurableSet_safe Q A H B B0 R Rp width γ s).inter
    (hc.inter ((measurableSet_le (measurable_price0 Q A H s) measurable_const).inter
      (measurableSet_le (measurable_price1 Q A H s) measurable_const)))

lemma measurable_failure (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (B B0 R Rp width γ a : ℝ) :
    Measurable (fun b : Fin A→ℝ=>(scenarioLaw Q A H b).prob
      (fun s=>¬StrongSafe Q A H B B0 R Rp width γ a b s)) := by
  unfold FiniteLaw.prob FiniteLaw.expect
  apply Finset.measurable_sum
  intro s _
  exact (measurable_scenarioLaw_mass_fixed Q A H s).mul
    (Measurable.ite (measurableSet_strongSafe Q A H B B0 R Rp width γ a s).compl
      measurable_const measurable_const)

lemma measurable_scenario_expect (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (y : ℝ) (s : Scenario A) (f : Fin 3→ℝ) :
    Measurable (fun b : Fin A→ℝ=>(scenarioCount Q A H b y s).expect f) := by
  have hW:=measurable_reciprocal A (mixed s)
  have h0:=measurable_price0 Q A H s
  have h1:=measurable_price1 Q A H s
  have hD : Measurable (fun b : Fin A→ℝ=>
      FocalResponse.denominator Q.ξ y (mixedReciprocalSum (mixed s) b)) :=
    measurable_const.mul (measurable_const.add (measurable_const.div hW))
  have hp:=((measurable_const (a:=y)).sub h0 |>.div hD).prodMk
    ((measurable_const (a:=y)).sub h1 |>.div hD)
  have hleft:=FocalResponse.measurable_solution_left.comp hp
  have hright:=FocalResponse.measurable_solution_right.comp hp
  simp_rw [scenarioCount,actualCount_expect]
  unfold coinMoment
  exact (((measurable_const.sub hleft).mul (measurable_const.sub hright)).mul_const (f 0)).add
    (((hleft.mul (measurable_const.sub hright)).add
      ((measurable_const.sub hleft).mul hright)).mul_const (f 1)) |>.add
        ((hleft.mul hright).mul_const (f 2))

lemma measurable_public_expect (Q : PublicScenario.Data) (A : ℕ) (H : ℕ×ℕ)
    (y : ℝ) (f : Fin 3→ℝ) :
    Measurable (fun b : Fin A→ℝ=>(publicCount Q A H b y).expect f) := by
  simp_rw [publicCount,FiniteLaw.expect_finiteMix]
  unfold FiniteLaw.expect
  apply Finset.measurable_sum
  intro s _
  exact (measurable_scenarioLaw_mass_fixed Q A H s).mul
    (measurable_scenario_expect Q A H y s f)

lemma measurable_sorted_real {A : ℕ} {B : ℝ} :
    Measurable (fun b : Fin A→ Icc (1:ℝ) B=> TypicalGuard.bids (SortedAllNoise.sortedBox b)) :=
  TypicalGuard.continuous_bids.measurable.comp SortedAllNoise.continuous_sortedBox.measurable

end FCAppendix.Affine.Tail04.UnusedPublicMeasurable
