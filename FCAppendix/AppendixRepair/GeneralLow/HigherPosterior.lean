import FCAppendix.AppendixRepair.GeneralLow.HigherPolicy
import FCAppendix.Affine.Hybrid.ClassifiedReceipts

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.HigherPosterior
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open scoped BigOperators Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def BidCompatible (C : Information.Classifier) (d κ b : ℝ) : Prop :=
  (C.label b = 0 → b ≤ d) ∧ (C.label b = 1 → d < κ*b) ∧
    (C.label b = 2 → d < b)

theorem measurableSet_bidCompatible (C : Information.Classifier) (d κ : ℝ) :
    MeasurableSet {b | BidCompatible C d κ b} := by
  unfold BidCompatible
  simp only [imp_iff_not_or]
  exact (((measurableSet_eq_fun C.measurable_label measurable_const).compl.union
    measurableSet_Iic).inter
    (((measurableSet_eq_fun C.measurable_label measurable_const).compl.union
      (measurableSet_lt measurable_const (measurable_const.mul measurable_id))).inter
    ((measurableSet_eq_fun C.measurable_label measurable_const).compl.union
      measurableSet_Ioi)))

def CompatibleList (C : Information.Classifier) (d κ : ℝ) (L : LocalList m) : Prop :=
  NonnegativeList L ∧ ∀ i, L i = none ∨ BidCompatible C d κ (entryBid (L i))

theorem compatibleList_iff (C : Information.Classifier) (d κ : ℝ) (L : LocalList m)
    (hnonneg : NonnegativeList L) :
    CompatibleList C d κ L ↔
      ∀ i b, L i = some b → BidCompatible C d κ b := by
  constructor
  · intro h i b hi
    rcases h.2 i with hnone | hbid
    · cases hi.symm.trans hnone
    · simpa only [hi, entryBid] using hbid
  · intro h
    refine ⟨hnonneg, ?_⟩
    intro i
    cases hi : L i with
    | none => exact Or.inl rfl
    | some b => exact Or.inr (by simpa only [entryBid] using h i b hi)

theorem measurableSet_compatibleList (C : Information.Classifier) (d κ : ℝ) :
    MeasurableSet {L : LocalList m | CompatibleList C d κ L} := by
  simp only [CompatibleList, setOf_and, setOf_forall]
  apply (measurableSet_nonnegativeList m).inter
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun (measurable_pi_apply i) measurable_const).union
    ((measurableSet_bidCompatible C d κ).preimage
      (measurable_entryBid.comp (measurable_pi_apply i)))

def ActionCompatible (C : Information.Classifier) (d κ : ℝ) (a : JointAction 2) : Prop :=
  BidCompatible C d κ a.bid ∧
    a.routeCount = if C.label a.bid = 2 then 1 else 2

def profiles (C : Information.Classifier) (d κ : ℝ) : Set (UserProfile m 2) :=
  {x | ∀ i, ActionCompatible C d κ (x i).1.2}

theorem measurableSet_profiles (C : Information.Classifier) (d κ : ℝ) :
    MeasurableSet (profiles (m := m) C d κ) := by
  simp only [profiles, ActionCompatible, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  have ha : Measurable (fun x : UserProfile m 2 => (x i).1.2) :=
    (measurable_pi_apply i).fst.snd
  have hb := (measurable_bid 2).comp ha
  have hr := (measurable_routeCount 2).comp ha
  exact ((measurableSet_bidCompatible C d κ).preimage hb).inter
    (measurableSet_eq_fun hr
      (Measurable.ite
        (measurableSet_eq_fun (C.measurable_label.comp hb) measurable_const)
        measurable_const measurable_const))

theorem observe_compatible (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ) (j : Fin 2) :
    CompatibleList C d κ (observe (drawsRealization x) j) := by
  refine ⟨(feasibleObservedList_iff_nonnegative j _).mp ⟨x, rfl⟩, ?_⟩
  intro i
  unfold observe
  split
  · exact Or.inr (hx i).1
  · exact Or.inl rfl

def kind (C : Information.Classifier) (x : UserProfile m 2) : Fin m → Fin 3 :=
  fun i => C.label (x i).1.2.bid

theorem correct_kind (C : Information.Classifier) (x : UserProfile m 2) :
    Information.Correct C (kind C x) (drawsRealization x) := fun _ => rfl

theorem routes_kind (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ) :
    Information.Routes (kind C x) (drawsRealization x) := by
  constructor
  · intro i hi
    change C.label (x i).1.2.bid ≠ 2 at hi
    have hr : (x i).1.2.routeCount = 2 := by
      simpa only [if_neg hi] using (hx i).2
    simp [drawsRealization, hr, Affine.Hybrid.firstK_full_two]
  · intro i hi
    change C.label (x i).1.2.bid = 2 at hi
    have hr : (x i).1.2.routeCount = 1 := by
      simpa only [if_pos hi] using (hx i).2
    change (firstK (x i).2 (x i).1.2.routeCount).card = 1
    rw [hr, card_firstK _ _ (by omega)]

def completionAction (C : Information.Classifier) (R : ℝ) : Option ℝ → JointAction 2
  | none => ⟨max R 0, le_max_right _ _, 1, by omega⟩
  | some b => ⟨max b 0, le_max_right _ _, if C.label b = 2 then 1 else 2,
      by split_ifs <;> omega⟩

theorem measurable_completionAction (C : Information.Classifier) (R : ℝ) :
    Measurable (completionAction C R) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ =>
    (max b 0, if C.label b = 2 then (1 : ℕ) else 2)) ⁻¹' S)
  exact (((measurable_id.max measurable_const).prodMk
    (Measurable.ite (measurableSet_eq_fun C.measurable_label measurable_const)
      measurable_const measurable_const))) hS

def completionProfile (C : Information.Classifier) (R : ℝ)
    (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  fun i => ((0, completionAction C R (L i)), Affine.Hybrid.classifiedOrdering j (L i))

theorem measurable_completionProfile (C : Information.Classifier) (R : ℝ) (j : Fin 2) :
    Measurable (completionProfile (m := m) C R j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.prodMk
    ((measurable_completionAction C R).comp (measurable_pi_apply i))).prodMk
      ((Affine.Hybrid.measurable_classifiedOrdering j).comp (measurable_pi_apply i))

theorem observe_completionProfile (C : Information.Classifier) (R : ℝ)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    observe (drawsRealization (completionProfile C R j L)) j = L := by
  funext i
  cases hi : L i with
  | none =>
      simp [observe, drawsRealization, completionProfile, completionAction,
        Affine.Hybrid.classifiedOrdering, hi, Affine.Hybrid.firstK_routeTo]
  | some b =>
      have hb : 0 ≤ b := by simpa only [NonnegativeList, hi, entryBid] using hL i
      by_cases hc : C.label b = 2
      · simp [observe, drawsRealization, completionProfile, completionAction,
          Affine.Hybrid.classifiedOrdering, hi, hc, Affine.Hybrid.firstK_routeTo,
          max_eq_left hb]
      · simp [observe, drawsRealization, completionProfile, completionAction,
          Affine.Hybrid.classifiedOrdering, hi, hc, Affine.Hybrid.firstK_full_two,
          max_eq_left hb]

theorem completionProfile_mem (C : Information.Classifier) (d κ R : ℝ)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L)
    (hcomp : CompatibleList C d κ L) :
    completionProfile C R j L ∈ profiles C d κ := by
  intro i
  cases hi : L i with
  | none =>
      simp [ActionCompatible, BidCompatible, completionProfile, completionAction,
        hi, max_eq_left hR, hRC, hdR]
  | some b =>
      have hb : 0 ≤ b := by simpa only [NonnegativeList, hi, entryBid] using hL i
      have hbc := (compatibleList_iff C d κ L hL).mp hcomp i b hi
      simpa [ActionCompatible, completionProfile, completionAction, hi, max_eq_left hb]
        using hbc

def privateAction : Option ℝ → JointAction 2
  | none => Interim.abstain 2
  | some b => ⟨max b 0, le_max_right _ _, 1, by omega⟩

theorem measurable_privateAction : Measurable privateAction := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  intro S hS
  change MeasurableSet ((fun b : ℝ => (max b 0, (1 : ℕ))) ⁻¹' S)
  exact ((measurable_id.max measurable_const).prodMk measurable_const) hS

def privateProfile (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  fun i => ((0, privateAction (L i)), Affine.Hybrid.routeTo j)

theorem measurable_privateProfile (j : Fin 2) :
    Measurable (privateProfile (m := m) j) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_const.prodMk
    (measurable_privateAction.comp (measurable_pi_apply i))).prodMk measurable_const

theorem observe_privateProfile (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) :
    observe (drawsRealization (privateProfile j L)) j = L := by
  funext i
  cases hi : L i with
  | none => simp [observe, drawsRealization, privateProfile, privateAction, hi,
      Interim.abstain, mem_firstK]
  | some b =>
      have hb : 0 ≤ b := by simpa only [NonnegativeList, hi, entryBid] using hL i
      simp [observe, drawsRealization, privateProfile, privateAction, hi,
        Affine.Hybrid.firstK_routeTo, max_eq_left hb]

theorem privateProfile_other_absent (j : Fin 2) (L : LocalList m) (i : Fin m) :
    observe (drawsRealization (privateProfile j L)) (Affine.Hybrid.otherProposer j) i = none := by
  cases hi : L i <;>
    simp [observe, drawsRealization, privateProfile, privateAction, hi,
      Interim.abstain, mem_firstK, Affine.Hybrid.firstK_routeTo]

def fallbackProfile (C : Information.Classifier) (d κ R : ℝ)
    (j : Fin 2) (L : LocalList m) : UserProfile m 2 :=
  if CompatibleList C d κ L then completionProfile C R j L else privateProfile j L

theorem measurable_fallbackProfile (C : Information.Classifier) (d κ R : ℝ) (j : Fin 2) :
    Measurable (fallbackProfile (m := m) C d κ R j) :=
  Measurable.ite (measurableSet_compatibleList C d κ)
    (measurable_completionProfile C R j) (measurable_privateProfile j)

def fallback (C : Information.Classifier) (d κ R : ℝ) (j : Fin 2) :
    Kernel (LocalList m) (UserProfile m 2) :=
  Kernel.deterministic (fallbackProfile C d κ R j)
    (measurable_fallbackProfile C d κ R j)

instance (C : Information.Classifier) (d κ R : ℝ) (j : Fin 2) :
    IsMarkovKernel (fallback (m := m) C d κ R j) := by
  unfold fallback
  infer_instance

theorem fallback_feasible (C : Information.Classifier) (d κ R : ℝ)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L) :
    ∀ᵐ x ∂fallback C d κ R j L, observe (drawsRealization x) j = L := by
  rw [fallback, Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  unfold fallbackProfile
  split_ifs
  · exact observe_completionProfile C R j L ((feasibleObservedList_iff_nonnegative j L).mp hL)
  · exact observe_privateProfile j L ((feasibleObservedList_iff_nonnegative j L).mp hL)

def posterior (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier) (d κ R : ℝ)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ) : PosteriorSystem Γ :=
  posteriorWithFallback Γ (measurableSet_profiles C d κ) hfull
    (fallback C d κ R) (fallback_feasible C d κ R)

theorem posterior_support (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d κ L) :
    ∀ᵐ x ∂(posterior Γ C d κ R hfull).posterior j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d κ := by
  classical
  change ∀ᵐ x ∂posteriorWithFallbackKernel Γ (measurableSet_profiles C d κ)
    (fallback C d κ R) j L, _
  by_cases hg : L ∈ goodPosteriorLists Γ (profiles C d κ) j
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hg]
    exact ae_iff.mpr hg
  · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_neg hg,
      fallback, Kernel.deterministic_apply]
    apply (ae_dirac_iff ((measurableSet_eq_lists (measurable_observe_draws j) measurable_const).inter
      (measurableSet_profiles C d κ))).mpr
    simp only [fallbackProfile, if_pos hcomp]
    have hnonneg := (feasibleObservedList_iff_nonnegative j L).mp hL
    exact ⟨observe_completionProfile C R j L hnonneg,
      completionProfile_mem C d κ R hR hRC hdR j L hnonneg hcomp⟩

theorem not_good_of_incompatible (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ : ℝ) (j : Fin 2) (L : LocalList m) (hcomp : ¬ CompatibleList C d κ L) :
    L ∉ goodPosteriorLists Γ (profiles C d κ) j := by
  intro hg
  have ha : ∀ᵐ x ∂regularUserPosterior Γ j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d κ := ae_iff.mpr hg
  obtain ⟨x, hx⟩ := ha.exists
  exact hcomp (hx.1 ▸ observe_compatible C d κ x hx.2 j)

theorem posterior_incompatible (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (j : Fin 2) (L : LocalList m) (hcomp : ¬ CompatibleList C d κ L) :
    (posterior Γ C d κ R hfull).posterior j L = Measure.dirac (privateProfile j L) := by
  have hg := not_good_of_incompatible Γ C d κ j L hcomp
  simp only [posterior, posteriorWithFallback, posteriorWithFallbackKernel,
    Kernel.piecewise_apply, if_neg hg, fallback, Kernel.deterministic_apply,
    fallbackProfile, if_neg hcomp]

end FCAppendix.Appendix08.GeneralLow.HigherPosterior
