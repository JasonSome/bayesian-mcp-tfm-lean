import FCAppendix.Affine.Hybrid.Native02.NativePhysicalRows
import FCAppendix.Affine.Hybrid.Native02.ObservedSeed

set_option maxRecDepth 3000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open scoped BigOperators

section ProductProjection
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

theorem pi_subtype_map (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    (Measure.pi μ).map (fun x : ι → X => fun i : Subtype p => x i) =
      Measure.pi (fun i : Subtype p => μ i) := by
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p
  have hsplit := (measurePreserving_piEquivPiSubtypeProd μ p).map_eq
  calc
    _ = ((Measure.pi μ).map E).map Prod.fst :=
      (Measure.map_map measurable_fst E.measurable).symm
    _ = ((Measure.pi (fun i : Subtype p => μ i)).prod
        (Measure.pi (fun i : {i : ι // ¬p i} => μ i))).map Prod.fst := by rw [hsplit]
    _ = _ := (measurePreserving_fst (μ := Measure.pi (fun i : Subtype p => μ i))
      (ν := Measure.pi (fun i : {i : ι // ¬p i} => μ i))).map_eq

end ProductProjection

section LowSeed
variable {N : ℕ}

def maskedLowList (kind : Fin N → Fin 4) (low : Fin N → ℝ) : LocalList (N+1) :=
  Fin.cons none (fun j => if kind j = 0 then some (low j) else none)

def lowPatternPred (kind : Fin N → Fin 4) : Fin (N+1) → Prop :=
  Fin.cases False (fun j => kind j = 0)

lemma maskedLowList_entry (kind : Fin N → Fin 4) (low : Fin N → ℝ)
    (i : Fin (N+1)) :
    maskedLowList kind low i =
      if lowPatternPred kind i then some (Fin.cons (α := fun _ => ℝ) 0 low i) else none := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [maskedLowList, lowPatternPred]
  · simp [maskedLowList, lowPatternPred]

def subtypePrecompEquiv {α : Type*} (p : α → Prop) (e : Equiv.Perm α) :
    {i : α // p (e i)} ≃ Subtype p where
  toFun i := ⟨e i, i.property⟩
  invFun i := ⟨e.symm i, by simpa only [Equiv.apply_symm_apply] using i.property⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i)
  right_inv i := Subtype.ext (e.apply_symm_apply i)

def lowSuccEquiv (kind : Fin N → Fin 4) :
    {j : Fin N // kind j = 0} ≃ {i : Fin (N+1) // lowPatternPred kind i} where
  toFun j := ⟨j.val.succ, j.property⟩
  invFun i := Fin.cases (fun h : False => False.elim h)
    (fun j (h : kind j = 0) => (⟨j, h⟩ : {j : Fin N // kind j = 0})) i.val i.property
  left_inv j := rfl
  right_inv i := by
    apply Subtype.ext
    rcases Fin.eq_zero_or_eq_succ i.val with hi | ⟨j, hj⟩
    · exact False.elim (by simpa only [lowPatternPred, hi, Fin.cases_zero] using i.property)
    · rcases i with ⟨i, hi⟩
      dsimp only at hj
      subst i
      rfl

lemma lowPattern_card (kind : Fin N → Fin 4) :
    Fintype.card {j : Fin N // kind j = 0} = classCount 0 (patternRow kind) := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    classCount, patternRow]
  rfl

def lowEnumeration (kind : Fin N → Fin 4)
    (h : 0 < classCount 0 (patternRow kind)) :
    Fin (Fintype.card {j : Fin N // kind j = 0}-1+1) ≃ {j : Fin N // kind j = 0} :=
  Fintype.equivOfCardEq (by
    have hp : 0 < Fintype.card {j : Fin N // kind j = 0} := by
      rw [lowPattern_card]
      exact h
    simp only [Fintype.card_fin]
    omega)

theorem maskedLowSeed_formula (μ : Measure ℝ) (kind : Fin N → Fin 4)
    (h : 0 < classCount 0 (patternRow kind)) (e : Equiv.Perm (Fin (N+1)))
    (low : Fin N → ℝ) :
    seedOnList μ (maskedLowList kind low ∘ e) =
      some (conditionalMinimumSeed μ (Fintype.card {j : Fin N // kind j = 0}-1)
        (fun k => low (lowEnumeration kind h k))) := by
  let el := lowEnumeration kind h
  let E := (el.trans (lowSuccEquiv kind)).trans
    (subtypePrecompEquiv (lowPatternPred kind) e).symm
  have hh := seedOnList_enumeration μ (fun i => lowPatternPred kind (e i)) E
    (Fin.cons (α := fun _ => ℝ) 0 low ∘ e) (maskedLowList kind low ∘ e)
    (fun i => maskedLowList_entry kind low (e i))
  have harray : (fun k => (Fin.cons (α := fun _ => ℝ) (0:ℝ) low ∘ e) (E k)) =
      (fun k => low (el k)) := by
    funext k
    change Fin.cons (α := fun _ => ℝ) (0:ℝ) low (e (e.symm ((el k : Fin N).succ))) = _
    rw [Equiv.apply_symm_apply, Fin.cons_succ]
  rw [harray] at hh
  exact hh

def maskedLowSeed (μ : Measure ℝ) (kind : Fin N → Fin 4)
    (h : 0 < classCount 0 (patternRow kind)) (low : Fin N → ℝ) : unitInterval :=
  conditionalMinimumSeed μ (Fintype.card {j : Fin N // kind j = 0}-1)
    (fun k => low (lowEnumeration kind h k))

lemma measurable_maskedLowSeed (μ : Measure ℝ) (kind : Fin N → Fin 4)
    (h : 0 < classCount 0 (patternRow kind)) : Measurable (maskedLowSeed μ kind h) :=
  (measurable_conditionalMinimumSeed μ _).comp (measurable_pi_lambda _
    (fun k => measurable_pi_apply ((lowEnumeration kind h k) : Fin N)))

theorem maskedLowSeed_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnoatoms : ∀ b, μ {b} = 0) (kind : Fin N → Fin 4)
    (h : 0 < classCount 0 (patternRow kind)) :
    (Measure.pi (fun _ : Fin N => μ)).map (maskedLowSeed μ kind h) =
      (volume : Measure unitInterval) := by
  let n := Fintype.card {j : Fin N // kind j = 0}-1
  let e := lowEnumeration kind h
  let split := bidBlockSplit (fun j : Fin N => kind j = 0) n e (id : ℝ → ℝ)
  have hs := bidBlockSplit_law (fun _ : Fin N => μ) (fun j => kind j = 0) n e
    (id : ℝ → ℝ) measurable_id μ (fun _ => Measure.map_id)
  have hm := measurable_bidBlockSplit (fun j : Fin N => kind j = 0) n e
    (id : ℝ → ℝ) measurable_id
  have hproj : (Measure.pi (fun _ : Fin N => μ)).map (fun x => (split x).1) =
      lowVectorLaw μ n := by
    calc
      _ = ((Measure.pi (fun _ : Fin N => μ)).map split).map Prod.fst :=
        (Measure.map_map measurable_fst hm).symm
      _ = ((lowVectorLaw μ n).prod
          (Measure.pi (fun _ : {j : Fin N // kind j ≠ 0} => μ))).map Prod.fst := by rw [hs]
      _ = _ := (measurePreserving_fst (μ := lowVectorLaw μ n)
        (ν := Measure.pi (fun _ : {j : Fin N // kind j ≠ 0} => μ))).map_eq
  calc
    _ = ((Measure.pi (fun _ : Fin N => μ)).map (fun x => (split x).1)).map
        (conditionalMinimumSeed μ n) :=
      (Measure.map_map (measurable_conditionalMinimumSeed μ n) hm.fst).symm
    _ = _ := by rw [hproj, conditionalMinimumSeed_uniform μ hnoatoms n]

theorem maskedLowSeed_joint {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀ b, μ {b} = 0)
    (kind : Fin N → Fin 4) (h : 0 < classCount 0 (patternRow kind))
    (e : Equiv.Perm (Fin (N+1))) (ν : Measure X) [IsProbabilityMeasure ν] :
    ((Measure.pi (fun _ : Fin N => μ)).prod ν).map
      (fun t => ((seedOnList μ (maskedLowList kind t.1 ∘ e)).getD 0, t.2)) =
      (volume : Measure unitInterval).prod ν := by
  simp_rw [maskedLowSeed_formula μ kind h e, Option.getD_some]
  change ((Measure.pi (fun _ : Fin N => μ)).prod ν).map
    (Prod.map (maskedLowSeed μ kind h) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_maskedLowSeed μ kind h) measurable_id,
    maskedLowSeed_law μ hnoatoms kind h, Measure.map_id]

theorem observedLowSeed_joint_of_lowList {X : Type*} [MeasurableSpace X]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀ b, μ {b} = 0)
    (kind : Fin N → Fin 4) (h : 0 < classCount 0 (patternRow kind))
    (e : Equiv.Perm (Fin (N+1))) (ν : Measure X) [IsProbabilityMeasure ν]
    (d : ℝ) (L : (Fin N → ℝ) × X → LocalList (N+1))
    (hL : ∀ᵐ t ∂(Measure.pi (fun _ : Fin N => μ)).prod ν,
      lowOnlyList d (L t) = maskedLowList kind t.1 ∘ e) :
    ((Measure.pi (fun _ : Fin N => μ)).prod ν).map
      (fun t => ((observedLowMinimumSeed d μ (L t)).getD 0, t.2)) =
      (volume : Measure unitInterval).prod ν := by
  calc
    _ = ((Measure.pi (fun _ : Fin N => μ)).prod ν).map
        (fun t => ((seedOnList μ (maskedLowList kind t.1 ∘ e)).getD 0, t.2)) := by
      apply Measure.map_congr
      filter_upwards [hL] with t ht
      simp only [observedLowMinimumSeed, ht]
    _ = _ := maskedLowSeed_joint μ hnoatoms kind h e ν

end LowSeed

section ActiveProjection
variable {N : ℕ}

lemma measurable_physicalActiveArray (kind : Fin N → Fin 4) (v b : ℝ) :
    Measurable (fun active : Fin N → ℝ =>
      activePhysicalActiveBids kind (v, b, (fun _ => 0), active)) := by
  exact (continuous_activePhysicalActiveBids kind).measurable.comp
    (measurable_const.prodMk (measurable_const.prodMk
      (measurable_const.prodMk measurable_id)))

theorem physicalActiveBids_law (B : Measure ℝ) [IsProbabilityMeasure B]
    (kind : Fin N → Fin 4) (v b : ℝ) :
    (Measure.pi (fun _ : Fin N => B)).map
      (fun active => activePhysicalActiveBids kind (v, b, (fun _ => 0), active)) =
      (Measure.pi (fun _ : ActivePatternIndex kind => B)).map
        (fun x => Function.update x (activePatternFocal kind) b) := by
  let proj : (Fin (N+1) → ℝ) → (ActivePatternIndex kind → ℝ) :=
    fun x i => x i
  let del : (Fin (N+1) → ℝ) → (Fin N → ℝ) := fun x j => x ((0 : Fin (N+1)).succAbove j)
  let update : (ActivePatternIndex kind → ℝ) → (ActivePatternIndex kind → ℝ) :=
    fun x => Function.update x (activePatternFocal kind) b
  let physical : (Fin N → ℝ) → (ActivePatternIndex kind → ℝ) :=
    fun active => activePhysicalActiveBids kind (v, b, (fun _ => 0), active)
  have hproj : Measurable proj := measurable_pi_lambda _
    (fun i => measurable_pi_apply (i : Fin (N+1)))
  have hup : Measurable update := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = activePatternFocal kind
    · subst i
      simp only [update, Function.update_self]
      exact measurable_const
    · simp only [update, Function.update_of_ne hi]
      exact measurable_pi_apply i
  have hdel : MeasurePreserving del (Measure.pi (fun _ : Fin (N+1) => B))
      (Measure.pi (fun _ : Fin N => B)) :=
    (measurePreserving_snd (μ := B) (ν := Measure.pi (fun _ : Fin N => B))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => B) 0)
  have hfun : physical ∘ del = update ∘ proj := by
    funext x i
    have hh : ∀ (k : Fin (N+1)) (hk : activePatternPred kind k),
        physical (del x) ⟨k, hk⟩ = update (proj x) ⟨k, hk⟩ := by
      intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · intro hk
        have he : (⟨0, hk⟩ : ActivePatternIndex kind) = activePatternFocal kind := rfl
        simp only [update, Function.update_self, physical,
          activePhysicalActiveBids, activePatternFocal, Fin.cases_zero]
      · intro hk
        have hi : (⟨j.succ, hk⟩ : ActivePatternIndex kind) ≠ activePatternFocal kind := by
          intro he
          have hz := congrArg Subtype.val he
          exact Fin.succ_ne_zero j hz
        have hz : (0 : Fin (N+1)).succAbove j = j.succ := by simp
        simp only [update, Function.update_of_ne hi, proj, physical,
          activePhysicalActiveBids, Fin.cases_succ, del, hz]
    exact hh i.val i.property
  calc
    _ = ((Measure.pi (fun _ : Fin (N+1) => B)).map del).map physical := by rw [hdel.map_eq]
    _ = (Measure.pi (fun _ : Fin (N+1) => B)).map (update ∘ proj) := by
      rw [Measure.map_map (measurable_physicalActiveArray kind v b) hdel.measurable, hfun]
    _ = ((Measure.pi (fun _ : Fin (N+1) => B)).map proj).map update :=
      (Measure.map_map hup hproj).symm
    _ = _ := by rw [pi_subtype_map (fun _ : Fin (N+1) => B) (activePatternPred kind)]

theorem integral_physicalActiveBids (B : Measure ℝ) [IsProbabilityMeasure B]
    (kind : Fin N → Fin 4) (v b : ℝ)
    (f : (ActivePatternIndex kind → ℝ) → ℝ) (hf : Measurable f) :
    (∫ active : Fin N → ℝ,
      f (activePhysicalActiveBids kind (v, b, (fun _ => 0), active))
      ∂Measure.pi (fun _ : Fin N => B)) =
      ∫ x : ActivePatternIndex kind → ℝ, f (Function.update x (activePatternFocal kind) b)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => B) := by
  have hup : Measurable (fun x : ActivePatternIndex kind → ℝ =>
      Function.update x (activePatternFocal kind) b) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = activePatternFocal kind
    · subst i
      simp only [Function.update_self]
      exact measurable_const
    · simp only [Function.update_of_ne hi]
      exact measurable_pi_apply i
  rw [← integral_map (measurable_physicalActiveArray kind v b).aemeasurable
    hf.aestronglyMeasurable, physicalActiveBids_law B kind v b,
    integral_map hup.aemeasurable hf.aestronglyMeasurable]

end ActiveProjection
end FCAppendix.Affine.Hybrid.Native02
