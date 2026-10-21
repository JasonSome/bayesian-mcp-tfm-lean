import FCAppendix.Affine.Hybrid.ObservedSeed
import FCAppendix.Affine.Hybrid.Native02.GuardedSampler

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02

open MeasureTheory ProbabilityTheory Bayes Game Set Classical

variable {m : ℕ}

def lowOnlyList (d : ℝ) (L : LocalList m) : LocalList m :=
  TaggedLocal.lowList d d L

lemma lowOnlyList_eq_tagged (d U : ℝ) (L : LocalList m) :
    lowOnlyList d L = TaggedLocal.lowList d U L := by
  funext i
  cases h : L i with
  | none => simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag, h]
  | some b =>
    by_cases hb : b ≤ d
    · simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag, h, hb]
    · by_cases hU : b ≤ U <;>
        simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag, h, hb, hU]

lemma lowOnlyList_some (d : ℝ) (L : LocalList m) (i : Fin m) (b : ℝ)
    (hi : L i = some b) (hb : b ≤ d) : lowOnlyList d L i = some b := by
  simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag, hi, hb]

lemma lowOnlyList_above (d : ℝ) (L : LocalList m) (i : Fin m) (b : ℝ)
    (hi : L i = some b) (hb : d < b) : lowOnlyList d L i = none := by
  simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag, hi, not_le.mpr hb]

lemma measurable_lowOnlyList (d : ℝ) : Measurable (lowOnlyList (m := m) d) :=
  TaggedLocal.measurable_lowList d d

def observedLowMinimumSeed (d : ℝ) (μ : Measure ℝ) (L : LocalList m) :
    Option unitInterval := seedOnList μ (lowOnlyList d L)

lemma measurable_observedLowMinimumSeed (d : ℝ) (μ : Measure ℝ) :
    Measurable (observedLowMinimumSeed (m := m) d μ) :=
  (measurable_seedOnList μ).comp (measurable_lowOnlyList d)

lemma observedLowMinimumSeed_eq_tagged (d U : ℝ) (μ : Measure ℝ) (L : LocalList m) :
    observedLowMinimumSeed d μ L = observedLowSeed d U μ L := by
  rw [observedLowMinimumSeed, observedLowSeed, lowOnlyList_eq_tagged d U]

@[simp] lemma observedLowMinimumSeed_empty (d : ℝ) (μ : Measure ℝ) :
    observedLowMinimumSeed d μ (fun _ : Fin m => none) = none := by
  have he : lowOnlyList d (fun _ : Fin m => none) = fun _ => none := by
    funext i
    simp [lowOnlyList, TaggedLocal.lowList, TaggedLocal.tag]
  rw [observedLowMinimumSeed, he, seedOnList_empty]

def seedUseAllowed (A d₀ d₁ : ℕ) : Prop := d₀ < A ∧ d₁ < A

def safeObservedLowMinimumSeed (d : ℝ) (μ : Measure ℝ) (A d₀ d₁ : ℕ)
    (L : LocalList m) : Option unitInterval :=
  if seedUseAllowed A d₀ d₁ then observedLowMinimumSeed d μ L else none

lemma safeObservedLowMinimumSeed_allowed (d : ℝ) (μ : Measure ℝ) (A d₀ d₁ : ℕ)
    (L : LocalList m) (h : seedUseAllowed A d₀ d₁) :
    safeObservedLowMinimumSeed d μ A d₀ d₁ L = observedLowMinimumSeed d μ L := by
  simp only [safeObservedLowMinimumSeed, if_pos h]

lemma safeObservedLowMinimumSeed_disallowed (d : ℝ) (μ : Measure ℝ) (A d₀ d₁ : ℕ)
    (L : LocalList m) (h : ¬seedUseAllowed A d₀ d₁) :
    safeObservedLowMinimumSeed d μ A d₀ d₁ L = none := by
  simp only [safeObservedLowMinimumSeed, if_neg h]

lemma measurable_safeObservedLowMinimumSeed (d : ℝ) (μ : Measure ℝ) :
    Measurable (fun x : (ℕ × ℕ × ℕ) × LocalList m =>
      safeObservedLowMinimumSeed d μ x.1.1 x.1.2.1 x.1.2.2 x.2) :=
  measurable_from_prod_countable_right (fun t => by
    unfold safeObservedLowMinimumSeed
    dsimp only
    split_ifs
    · exact measurable_observedLowMinimumSeed d μ
    · exact measurable_const)

theorem activePatternGuarded_seedUseAllowed {N : ℕ} {xi L U : ℝ} (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) (hg : typicalCountTest xi L U c z kind) :
    seedUseAllowed (Fintype.card (ActivePatternIndex kind))
      (activePatternCapacity c kind 0) (activePatternCapacity c kind 1) :=
  ⟨activePatternGuarded_capacity_lt c z kind hg 0,
    activePatternGuarded_capacity_lt c z kind hg 1⟩

theorem observedLowMinimumSeed_actual {n : ℕ} {d U : ℝ} (μ : Measure ℝ)
    (kind : Fin m → Fin 3) (x : Realization m 2) (hdU : d ≤ U)
    (hb : TaggedLocal.BidBoxes kind x d U) (hr : TaggedLocal.ClassRoutes kind x)
    (e : Fin (n+1) ≃ {i : Fin m // kind i = 0}) (j : Fin 2) :
    observedLowMinimumSeed d μ (observe x j) =
      some (conditionalMinimumSeed μ n (fun l => (x.action (e l)).bid)) := by
  rw [observedLowMinimumSeed_eq_tagged d U]
  exact observedLowSeed_actual μ kind x hdU hb hr e j

theorem observedLowMinimumSeed_formula {n : ℕ} {d U : ℝ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (kind : Fin m → Fin 3)
    (x : Realization m 2) (hdU : d ≤ U)
    (hb : TaggedLocal.BidBoxes kind x d U) (hr : TaggedLocal.ClassRoutes kind x)
    (e : Fin (n+1) ≃ {i : Fin m // kind i = 0}) (j : Fin 2) :
    (observedLowMinimumSeed d μ (observe x j)).map Subtype.val =
      some (1 - (1 - cdf μ (minBid n (fun l => (x.action (e l)).bid)))^(n+1)) := by
  rw [observedLowMinimumSeed_actual μ kind x hdU hb hr e j]
  simp only [Option.map_some]
  exact congrArg some (conditionalMinimumSeed_formula μ n _)

theorem observedLowMinimumSeed_native_joint {c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (tag : UserDraw 2 → Fin 3) (htag : Measurable tag)
    (k : Fin m → Fin 3) (hmass : ∀ i, userLaw Γ (tag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i = 0})
    (hnoatoms : ∀ b : ℝ,
      ((cond (userLaw Γ) (tag ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0)
    {d U : ℝ} (hdU : d ≤ U)
    (hshape : ∀ᵐ x ∂cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ),
      TaggedLocal.BidBoxes k (drawsRealization x.1) d U ∧
        TaggedLocal.ClassRoutes k (drawsRealization x.1)) (j : Fin 2) :
    (cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
      (fun x => (observedLowMinimumSeed d
          ((cond (userLaw Γ) (tag ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid))
          (observe (drawsRealization x.1) j),
        ((fun i : {i : Fin m // k i ≠ 0} => x.1 i), x.2))) =
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun i : {i : Fin m // k i ≠ 0} =>
          cond (userLaw Γ) (tag ⁻¹' {k i}))).prod
            (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))) := by
  simp_rw [observedLowMinimumSeed_eq_tagged d U]
  exact observedLowSeed_native_joint Γ tag htag k hmass n e hnoatoms hdU hshape j

theorem observedLowMinimumSeed_native_four_category_joint {c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed)
    (tag : UserDraw 2 → Fin 4) (htag : Measurable tag)
    (k : Fin m → Fin 4) (hmass : ∀ i, userLaw Γ (tag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i = 0})
    (hnoatoms : ∀ b : ℝ,
      ((cond (userLaw Γ) (tag ⁻¹' {0})).map
        (fun u : UserDraw 2 => u.1.2.bid)) {b} = 0)
    (d : ℝ) (j : Fin 2)
    (hobs : ∀ᵐ x ∂cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ),
      ∀ i, lowOnlyList d (observe (drawsRealization x.1) j) i =
        if k i = 0 then some ((x.1 i).1.2.bid) else none) :
    (cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
      (fun x => (observedLowMinimumSeed d
          ((cond (userLaw Γ) (tag ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid))
          (observe (drawsRealization x.1) j),
        ((fun i : {i : Fin m // k i ≠ 0} => x.1 i), x.2))) =
      ((volume : Measure unitInterval).map some).prod
        ((Measure.pi (fun i : {i : Fin m // k i ≠ 0} =>
          cond (userLaw Γ) (tag ⁻¹' {k i}))).prod
            (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))) := by
  let μB := (cond (userLaw Γ) (tag ⁻¹' {0})).map (fun u : UserDraw 2 => u.1.2.bid)
  let ν := (Measure.pi (fun i : {i : Fin m // k i ≠ 0} =>
    cond (userLaw Γ) (tag ⁻¹' {k i}))).prod (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))
  let f : Background m 2 Seed → unitInterval ×
      (({i : Fin m // k i ≠ 0} → UserDraw 2) × (Fin 2 → Seed)) :=
    fun x => (conditionalMinimumSeed μB n (fun l => (x.1 (e l)).1.2.bid),
      ((fun i => x.1 i), x.2))
  have hf : Measurable f :=
    ((measurable_conditionalMinimumSeed μB n).comp (measurable_pi_lambda _
      (fun l => ((Game.measurable_bid 2).comp
        ((measurable_pi_apply ((e l) : Fin m)).comp measurable_fst).fst.snd)))).prodMk
      ((measurable_pi_lambda _
        (fun i : {i : Fin m // k i ≠ 0} => (measurable_pi_apply (i : Fin m)).comp
          measurable_fst)).prodMk measurable_snd)
  have hlaw := native_background_minimum_seed Γ tag htag k 0 hmass n e hnoatoms
  change (cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map _ =
    ((volume : Measure unitInterval).map some).prod ν
  calc
    _ = (cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
        ((Prod.map some id) ∘ f) := by
      apply Measure.map_congr
      filter_upwards [hobs] with x hx
      apply Prod.ext
      · exact seedOnList_enumeration μB (fun i => k i = 0) e
          (fun i => (x.1 i).1.2.bid)
          (lowOnlyList d (observe (drawsRealization x.1) j)) hx
      · rfl
    _ = ((cond (backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map f).map
        (Prod.map some id) :=
      (Measure.map_map (measurable_some.prodMap measurable_id) hf).symm
    _ = ((volume : Measure unitInterval).prod ν).map (Prod.map some id) := by rw [hlaw]
    _ = _ := by rw [←Measure.map_prod_map _ _ measurable_some measurable_id, Measure.map_id]

def wholeLowList (n : ℕ) (b : Fin (n+1) → ℝ) : LocalList (n+1) := fun i => some (b i)

lemma seedOnList_wholeLowList (μ : Measure ℝ) (n : ℕ) (b : Fin (n+1) → ℝ) :
    seedOnList μ (wholeLowList n b) = some (conditionalMinimumSeed μ n b) := by
  let e : Fin (n+1) ≃ {i : Fin (n+1) // True} :=
    ⟨fun i => ⟨i, trivial⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
  convert! seedOnList_enumeration μ (fun _ : Fin (n+1) => True) e b (wholeLowList n b)
      (fun _ => by simp [wholeLowList]) using 1

theorem observedSeed_fixed_external_joint {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀ b, μ {b} = 0)
    (n : ℕ) (ν : Measure X) [IsProbabilityMeasure ν] :
    ((lowVectorLaw μ n).prod ν).map
      (fun x => (seedOnList μ (wholeLowList n x.1), x.2)) =
      ((volume : Measure unitInterval).map some).prod ν := by
  simp_rw [seedOnList_wholeLowList]
  let f : (Fin (n+1) → ℝ) × X → unitInterval × X :=
    fun x => (conditionalMinimumSeed μ n x.1, x.2)
  have hf : Measurable f := (measurable_conditionalMinimumSeed μ n).prodMap measurable_id
  calc
    _ = (((lowVectorLaw μ n).prod ν).map f).map (Prod.map some id) :=
      (Measure.map_map (measurable_some.prodMap measurable_id) hf).symm
    _ = ((volume : Measure unitInterval).prod ν).map (Prod.map some id) := by
      rw [conditionalMinimumSeed_joint μ hnoatoms n ν]
    _ = _ := by rw [←Measure.map_prod_map _ _ measurable_some measurable_id, Measure.map_id]

theorem rejected_low_seed_payoff_unchanged (eta v b b' : ℝ) {K K' : ℕ}
    (hK : K = 0) (hK' : K' = 0) :
    realizedPayoff eta v b K = realizedPayoff eta v b' K' :=
  rejected_seed_user_invariance eta v b b' hK hK'

end FCAppendix.Affine.Hybrid.Native02
