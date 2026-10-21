import FCAppendix.Affine.Tail04.SumBorel
import FCAppendix.Affine.Tail04.EqualPrivateMeasurable
import FCAppendix.Finite.ReceiptOrder

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualPrivateSignal
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators

abbrev Signal (H : ℕ) (R Rp : ℝ) := Fin H → (Unit ⊕ Icc R Rp)
abbrev Marks (H : ℕ) := Fin H → Bool
abbrev Target (N H : ℕ) := Fin N ⊕ Fin H

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

instance (H : ℕ) (R Rp : ℝ) : PolishSpace (Signal H R Rp) := by
  letI : PolishSpace (Icc R Rp) := isClosed_Icc.polishSpace
  letI : PolishSpace (Unit ⊕ Icc R Rp) := inferInstance
  infer_instance

def isUpper {R Rp : ℝ} : Unit ⊕ Icc R Rp → Bool
  | .inl _ => true
  | .inr _ => false

def partialBid {R Rp : ℝ} : Unit ⊕ Icc R Rp → ℝ
  | .inl _ => 0
  | .inr b => b.1

lemma continuous_isUpper {R Rp : ℝ} : Continuous (@isUpper R Rp) :=
  continuous_sum_dom.mpr ⟨continuous_const,continuous_const⟩

lemma continuous_partialBid {R Rp : ℝ} : Continuous (@partialBid R Rp) :=
  continuous_sum_dom.mpr ⟨continuous_const,continuous_subtype_val⟩

def marks {H : ℕ} {R Rp : ℝ} (s : Signal H R Rp) : Marks H :=
  fun j => isUpper (s j)

lemma continuous_marks {H : ℕ} {R Rp : ℝ} :
    Continuous (marks : Signal H R Rp → Marks H) :=
  continuous_pi fun j => continuous_isUpper.comp (continuous_apply j)

def upperCount {H : ℕ} (z : Marks H) : ℕ :=
  (Finset.univ.filter fun j => z j = true).card

def Feasible (N H c : ℕ) (z : Marks H) (S : Finset (Target N H)) : Prop :=
  S.card ≤ c-upperCount z ∧ ∀ j, Sum.inr j ∈ S → z j = false

abbrev Action (N H c : ℕ) := ∀ z : Marks H, {S : Finset (Target N H) // Feasible N H c z S}

lemma empty_feasible (N H c : ℕ) (z : Marks H) : Feasible N H c z ∅ := by
  simp [Feasible]

instance actionNonempty (N H c : ℕ) : Nonempty (Action N H c) :=
  ⟨fun z => ⟨∅,empty_feasible N H c z⟩⟩

def selected {N H c : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (a : Action N H c) : Finset (Target N H) := (a (marks s)).1

lemma selected_feasible {N H c : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (a : Action N H c) : Feasible N H c (marks s) (selected s a) :=
  (a (marks s)).2

lemma restored_capacity {N H c : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (a : Action N H c) :
    min c (upperCount (marks s)) + (selected s a).card ≤ c := by
  have hh := (selected_feasible s a).1
  omega

lemma continuous_selected {N H c : ℕ} {R Rp : ℝ} :
    Continuous (fun p : Signal H R Rp × Action N H c => selected p.1 p.2) := by
  let f : Marks H × Action N H c → Finset (Target N H) := fun p => (p.2 p.1).1
  exact (continuous_of_discreteTopology (f := f)).comp
    ((continuous_marks.comp continuous_fst).prodMk continuous_snd)

def activeIndicator (N H c : ℕ) (R Rp : ℝ) (i : Fin N) :
    C(Signal H R Rp × Action N H c, ℝ) :=
  ⟨fun p => if Sum.inl i ∈ selected p.1 p.2 then 1 else 0,
    (continuous_of_discreteTopology
      (f := fun S : Finset (Target N H) => if Sum.inl i ∈ S then (1:ℝ) else 0)).comp
      continuous_selected⟩

lemma activeIndicator_bounds {N H c : ℕ} {R Rp : ℝ} (i : Fin N)
    (p : Signal H R Rp × Action N H c) :
    0 ≤ activeIndicator N H c R Rp i p ∧ activeIndicator N H c R Rp i p ≤ 1 := by
  dsimp [activeIndicator]
  split <;> norm_num

def privateReceipt (N H c : ℕ) (R Rp : ℝ) :
    C(Signal H R Rp × Action N H c, ℝ) :=
  ⟨fun p => ∑ j, partialBid (p.1 j) *
      (if Sum.inr j ∈ selected p.1 p.2 then 1 else 0), by
    apply continuous_finsetSum
    intro j _
    exact (continuous_partialBid.comp ((continuous_apply j).comp continuous_fst)).mul
      ((continuous_of_discreteTopology
        (f := fun S : Finset (Target N H) => if Sum.inr j ∈ S then (1:ℝ) else 0)).comp
          continuous_selected)⟩

def revenue {N H : ℕ} {R Rp : ℝ} (b q : Fin N → ℝ) (ξ : ℝ)
    (s : Signal H R Rp) (S : Finset (Target N H)) : ℝ :=
  (∑ j, partialBid (s j) * (if Sum.inr j ∈ S then 1 else 0)) +
    ∑ i, b i*(1-ξ*q i)*(if Sum.inl i ∈ S then 1 else 0)

lemma score_eq_revenue {N H c : ℕ} {R Rp : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (s : Signal H R Rp) (a : Action N H c) :
    EqualPrivateFrontier.score (activeIndicator N H c R Rp)
      (privateReceipt N H c R Rp) b q ξ (s,a) = revenue b q ξ s (selected s a) := by
  simp only [EqualPrivateFrontier.score,ContinuousMap.add_apply,
    ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    privateReceipt,activeIndicator,revenue,ContinuousMap.coe_mk]

def actionFor (N H c : ℕ) (z : Marks H) (S : Finset (Target N H))
    (hS : Feasible N H c z S) : Action N H c :=
  fun z' => if h : z' = z then ⟨S, by simpa only [h] using hS⟩
    else ⟨∅,empty_feasible N H c z'⟩

lemma selected_actionFor {N H c : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (S : Finset (Target N H)) (hS : Feasible N H c (marks s) S) :
    selected s (actionFor N H c (marks s) S hS) = S := by
  simp [selected,actionFor]

theorem exists_private_signal_continuation (N H c : ℕ) (R Rp : ℝ)
    (μ : Measure (Signal H R Rp)) [IsProbabilityMeasure μ]
    (b : Fin N → ℝ) (ξ : ℝ) :
    ∃ (π : EqualPrivateFrontier.Plan (A := Action N H c) μ)
      (σ : Kernel (Signal H R Rp) (Action N H c)),
      IsMarkovKernel σ ∧ μ ⊗ₘ σ = (π.1 : Measure _) ∧
      (∀ (s : Signal H R Rp) (a : Action N H c),
        min c (upperCount (marks s)) + (selected s a).card ≤ c) ∧
      (∀ᵐ s ∂μ, ∀ᵐ a ∂σ s, ∀ S : Finset (Target N H),
        Feasible N H c (marks s) S →
        revenue b (EqualPrivateFrontier.marginal (activeIndicator N H c R Rp) π) ξ s S ≤
        revenue b (EqualPrivateFrontier.marginal (activeIndicator N H c R Rp) π) ξ
          s (selected s a)) ∧
      Existence.Distributional.IntegralOptimal π
        (EqualPrivateFrontier.score (activeIndicator N H c R Rp)
          (privateReceipt N H c R Rp) b
          (EqualPrivateFrontier.marginal (activeIndicator N H c R Rp) π) ξ) := by
  obtain ⟨π,σ,hσ,hdis,_hmax,hopt,_hall,hlocal⟩ :=
    EqualPrivateFrontier.exists_equal_private_continuation μ
      (activeIndicator N H c R Rp) (privateReceipt N H c R Rp) b ξ
  refine ⟨π,σ,hσ,hdis,fun s a => restored_capacity s a,?_,hopt⟩
  filter_upwards [hlocal] with s hs
  filter_upwards [hs] with a ha
  intro S hS
  have hh := ha (actionFor N H c (marks s) S hS)
  rw [score_eq_revenue,score_eq_revenue,selected_actionFor] at hh
  exact hh

abbrev PolicyParameters (N H : ℕ) (R Rp lo hi : ℝ) :=
  EqualPrivateMeasurable.Parameters (Fin N) (Signal H R Rp) lo hi

def policyMean (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (p : PolicyParameters N H R Rp lo hi) : Fin N → ℝ :=
  EqualPrivateMeasurable.q (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi p

def policyLaw (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (p : PolicyParameters N H R Rp lo hi) :
    WeakProbability.Law (Signal H R Rp × Action N H c) :=
  EqualPrivateMeasurable.planLaw (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi p

def residualKernel (N H c : ℕ) (R Rp ξ lo hi : ℝ) :
    Kernel (PolicyParameters N H R Rp lo hi × Signal H R Rp) (Action N H c) :=
  EqualPrivateMeasurable.policyKernel (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi

instance (N H c : ℕ) (R Rp ξ lo hi : ℝ) :
    IsMarkovKernel (residualKernel N H c R Rp ξ lo hi) := by
  unfold residualKernel
  infer_instance

theorem continuous_policyMean (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (hξ : 0 < ξ) (hlo : 0 < lo) :
    Continuous (policyMean N H c R Rp ξ lo hi) :=
  EqualPrivateMeasurable.continuous_q (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi hξ hlo

theorem residualKernel_jointLaw (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (p : PolicyParameters N H R Rp lo hi) :
    WeakProbability.toMeasure p.2 ⊗ₘ
      EqualPrivateMeasurable.fiber (residualKernel N H c R Rp ξ lo hi) p =
      WeakProbability.toMeasure (policyLaw N H c R Rp ξ lo hi p) :=
  EqualPrivateMeasurable.policyKernel_disintegrates (activeIndicator N H c R Rp)
    (privateReceipt N H c R Rp) ξ lo hi p

theorem exists_jointly_borel_residual_policy (N H c : ℕ) (R Rp ξ lo hi : ℝ) :
    ∃ f : (PolicyParameters N H R Rp lo hi × Signal H R Rp) →
        unitInterval → Action N H c,
      Measurable (Function.uncurry f) ∧
      (∀ p s, volume.map (f (p,s)) = residualKernel N H c R Rp ξ lo hi (p,s)) ∧
      (Measurable (fun z : (PolicyParameters N H R Rp lo hi × Signal H R Rp) ×
          unitInterval => selected z.1.2 (f z.1 z.2))) ∧
      (∀ p s u, Feasible N H c (marks s) (selected s (f (p,s) u))) ∧
      (∀ p s u, min c (upperCount (marks s)) + (selected s (f (p,s) u)).card ≤ c) ∧
      (∀ p s u S, Feasible N H c (marks s) S →
        revenue (EqualPrivateMeasurable.bids p) (policyMean N H c R Rp ξ lo hi p) ξ s S ≤
        revenue (EqualPrivateMeasurable.bids p) (policyMean N H c R Rp ξ lo hi p) ξ
          s (selected s (f (p,s) u))) := by
  obtain ⟨f,hf,hlaw,hbest⟩ := EqualPrivateMeasurable.exists_pointwise_sampler
    (activeIndicator N H c R Rp) (privateReceipt N H c R Rp) ξ lo hi
  refine ⟨f,hf,(fun p s => hlaw (p,s)),?_,fun p s u => selected_feasible s _,
    fun p s u => restored_capacity s _,?_⟩
  · exact continuous_selected.measurable.comp
      ((measurable_snd.comp measurable_fst).prodMk hf)
  · intro p s u S hS
    have hh := hbest (p,s) u (actionFor N H c (marks s) S hS)
    change EqualPrivateFrontier.score (activeIndicator N H c R Rp)
        (privateReceipt N H c R Rp) (EqualPrivateMeasurable.bids p)
        (policyMean N H c R Rp ξ lo hi p) ξ
        (s,actionFor N H c (marks s) S hS) ≤
      EqualPrivateFrontier.score (activeIndicator N H c R Rp)
        (privateReceipt N H c R Rp) (EqualPrivateMeasurable.bids p)
        (policyMean N H c R Rp ξ lo hi p) ξ (s,f (p,s) u) at hh
    rw [score_eq_revenue,score_eq_revenue,selected_actionFor] at hh
    exact hh

def privateIndicator (N H c : ℕ) (R Rp : ℝ) (j : Fin H) :
    C(Signal H R Rp × Action N H c,ℝ) :=
  ⟨fun p => if Sum.inr j ∈ selected p.1 p.2 then 1 else 0,
    (continuous_of_discreteTopology
      (f := fun S : Finset (Target N H) => if Sum.inr j ∈ S then (1:ℝ) else 0)).comp
      continuous_selected⟩

def itemReceipt {N H : ℕ} {R Rp : ℝ} (b q : Fin N → ℝ) (ξ : ℝ)
    (s : Signal H R Rp) : Target N H → ℝ
  | .inl i => b i*(1-ξ*q i)
  | .inr j => partialBid (s j)

lemma revenue_eq_sum {N H : ℕ} {R Rp : ℝ} (b q : Fin N → ℝ) (ξ : ℝ)
    (s : Signal H R Rp) (S : Finset (Target N H)) :
    revenue b q ξ s S = ∑ t ∈ S, itemReceipt b q ξ s t := by
  have he : (∑ t ∈ S, itemReceipt b q ξ s t) =
      ∑ t : Target N H, if t ∈ S then itemReceipt b q ξ s t else 0 := by
    simp
  rw [he,Fintype.sum_sum_type]
  simp only [itemReceipt,revenue,mul_ite,mul_one,mul_zero]
  ring

def residualEligible {N H : ℕ} {R Rp : ℝ} (s : Signal H R Rp) : Target N H → Prop
  | .inl _ => True
  | .inr j => isUpper (s j)=false

def eraseUppers {N H : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (S : Finset (Target N H)) : Finset (Target N H) :=
  S.filter (residualEligible s)

lemma eraseUppers_feasible {N H c : ℕ} {R Rp : ℝ} (s : Signal H R Rp)
    (S : Finset (Target N H)) (hS : S.card ≤ c-upperCount (marks s)) :
    Feasible N H c (marks s) (eraseUppers s S) := by
  refine ⟨(Finset.card_filter_le S _).trans hS,?_⟩
  intro j hj
  exact (Finset.mem_filter.mp hj).2

lemma eraseUppers_sum {N H : ℕ} {R Rp : ℝ} (b q : Fin N → ℝ) (ξ : ℝ)
    (s : Signal H R Rp) (S : Finset (Target N H)) :
    (∑ t ∈ eraseUppers s S, itemReceipt b q ξ s t) =
      ∑ t ∈ S, itemReceipt b q ξ s t := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro t ht hnot
  have hineligible : ¬residualEligible s t := by
    intro heligible
    exact hnot (Finset.mem_filter.mpr ⟨ht,heligible⟩)
  cases t with
  | inl i => exact (hineligible trivial).elim
  | inr j =>
    cases hs : s j with
    | inl u => simp [itemReceipt,hs,partialBid]
    | inr v => exact (hineligible (by simp [residualEligible,hs,isUpper])).elim

theorem finiteOptimal_of_residualOptimal {N H c : ℕ} {R Rp : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (s : Signal H R Rp) (S : Finset (Target N H))
    (hS : Feasible N H c (marks s) S)
    (hopt : ∀ T, Feasible N H c (marks s) T → revenue b q ξ s T ≤ revenue b q ξ s S) :
    Finite.Optimal (c-upperCount (marks s)) (itemReceipt b q ξ s) S := by
  refine ⟨hS.1,?_⟩
  intro T hT
  calc
    (∑ t ∈ T, itemReceipt b q ξ s t) =
        ∑ t ∈ eraseUppers s T, itemReceipt b q ξ s t :=
      (eraseUppers_sum b q ξ s T).symm
    _ ≤ ∑ t ∈ S, itemReceipt b q ξ s t := by
      rw [← revenue_eq_sum,← revenue_eq_sum]
      exact hopt _ (eraseUppers_feasible s T hT)

theorem membership_iff_strictRank_of_noTie {J : Type*} [Fintype J]
    (c : ℕ) (r : J → ℝ) (S : Finset J) (hS : Finite.Optimal c r S)
    (j : J) (hjpos : 0 < r j) (hnotie : ∀ i, i ≠ j → r i ≠ r j) :
    j ∈ S ↔ (Finset.univ.filter fun i => r j < r i).card < c := by
  constructor
  · intro hj
    by_contra h
    exact Finite.excluded_of_many_better c r S hS j (le_of_not_gt h) hj
  · intro hcount
    apply Finite.included_of_few_competitors c r S hS j hjpos
    have he : (Finset.univ.filter fun i => i ≠ j ∧ r j ≤ r i) =
        Finset.univ.filter fun i => r j < r i := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨hij,hji⟩
        exact lt_of_le_of_ne hji (Ne.symm (hnotie i hij))
      · intro hji
        exact ⟨fun hij => by subst i; exact (lt_irrefl _ hji),hji.le⟩
    simpa only [he] using hcount

theorem private_membership_unique {N H c : ℕ} {R Rp : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (s : Signal H R Rp)
    (S T : Finset (Target N H)) (j : Fin H)
    (hS : Feasible N H c (marks s) S) (hT : Feasible N H c (marks s) T)
    (hoptS : ∀ L, Feasible N H c (marks s) L → revenue b q ξ s L ≤ revenue b q ξ s S)
    (hoptT : ∀ L, Feasible N H c (marks s) L → revenue b q ξ s L ≤ revenue b q ξ s T)
    (hj : 0 < partialBid (s j))
    (htie : ∀ i : Target N H, i ≠ Sum.inr j →
      itemReceipt b q ξ s i ≠ partialBid (s j)) :
    Sum.inr j ∈ S ↔ Sum.inr j ∈ T := by
  have hp : 0 < itemReceipt b q ξ s (Sum.inr j) := hj
  have ht : ∀ i : Target N H, i ≠ Sum.inr j →
      itemReceipt b q ξ s i ≠ itemReceipt b q ξ s (Sum.inr j) := htie
  rw [membership_iff_strictRank_of_noTie _ _ S
    (finiteOptimal_of_residualOptimal b q ξ s S hS hoptS) (Sum.inr j) hp ht,
    membership_iff_strictRank_of_noTie _ _ T
    (finiteOptimal_of_residualOptimal b q ξ s T hT hoptT) (Sum.inr j) hp ht]

lemma policyMean_bounds (N H c : ℕ) (R Rp ξ lo hi : ℝ)
    (p : PolicyParameters N H R Rp lo hi) (i : Fin N) :
    policyMean N H c R Rp ξ lo hi p i ∈ Icc (0:ℝ) 1 := by
  have hfst : ((policyLaw N H c R Rp ξ lo hi p).val :
      Measure (Signal H R Rp × Action N H c)).map Prod.fst = WeakProbability.toMeasure p.2 :=
    congrArg (fun μ : ProbabilityMeasure (Signal H R Rp) =>
      (μ : Measure (Signal H R Rp)))
      (EqualPrivateMeasurable.planLaw_spec (activeIndicator N H c R Rp)
        (privateReceipt N H c R Rp) ξ lo hi p).1
  let π : EqualPrivateFrontier.Plan (A := Action N H c) (WeakProbability.toMeasure p.2) :=
    ⟨(policyLaw N H c R Rp ξ lo hi p).val,hfst⟩
  exact EqualPrivateFrontier.marginal_mem_Icc (WeakProbability.toMeasure p.2)
    (activeIndicator N H c R Rp) activeIndicator_bounds π i

end FCAppendix.Affine.Tail04.EqualPrivateSignal
