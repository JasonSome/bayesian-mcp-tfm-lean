import FCAppendix.Affine.EqualCapacityBoundary

noncomputable section
namespace FCAppendix.Affine.EqualCapacity
open Set MeasureTheory ProbabilityTheory Game Classical
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

def chosenPolicy (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    LocalPolicy m c unitInterval := (exists_affine_localPolicy m ξ c hξ hξ1).choose

theorem measurable_chosenPolicy (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) :
    Measurable (fun z : LocalList m×unitInterval=>(chosenPolicy m ξ c hξ hξ1 z.1 z.2).val) :=
  (exists_affine_localPolicy m ξ c hξ hξ1).choose_spec.choose

theorem chosenPolicy_law (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1) (L : LocalList m) :
    FiniteLaw.ofMeasure volume (fun s=>(chosenPolicy m ξ c hξ hξ1 L s).val)
      ((measurable_chosenPolicy m ξ c hξ hξ1).comp (measurable_const.prodMk measurable_id))=
        canonicalLottery ξ c (listBids L) :=
  (exists_affine_localPolicy m ξ c hξ hξ1).choose_spec.choose_spec L

def variablePolicy (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (R : LocalList m→ℕ) (hR : ∀L,R L≤c) : LocalPolicy m c unitInterval := fun L s=>
  ⟨(chosenPolicy m ξ (R L) hξ hξ1 L s).val,
    (chosenPolicy m ξ (R L) hξ hξ1 L s).property.1.trans (hR L),
    (chosenPolicy m ξ (R L) hξ hξ1 L s).property.2⟩

theorem measurable_variablePolicy (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (R : LocalList m→ℕ) (hR : ∀L,R L≤c) (hmR : Measurable R) :
    Measurable (fun z : LocalList m×unitInterval=>(variablePolicy m ξ c hξ hξ1 R hR z.1 z.2).val) := by
  apply measurable_to_countable'
  intro S
  have he : (fun z : LocalList m×unitInterval=>(variablePolicy m ξ c hξ hξ1 R hR z.1 z.2).val) ⁻¹' {S}=
      ⋃r : ℕ,{z | R z.1=r} ∩ {z | (chosenPolicy m ξ r hξ hξ1 z.1 z.2).val=S} := by
    ext z
    simp only [mem_preimage,mem_singleton_iff,mem_iUnion,mem_inter_iff,mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨R z.1,rfl,hz⟩
    · rintro ⟨r,hr,hS⟩
      change (chosenPolicy m ξ (R z.1) hξ hξ1 z.1 z.2).val=S
      rw [hr]
      exact hS
  rw [he]
  apply MeasurableSet.iUnion
  intro r
  exact (measurableSet_eq_fun (hmR.comp measurable_fst) measurable_const).inter
    (measurableSet_eq_fun (measurable_chosenPolicy m ξ r hξ hξ1) measurable_const)

theorem variablePolicy_law (m : ℕ) (ξ : ℝ) (c : ℕ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (R : LocalList m→ℕ) (hR : ∀L,R L≤c) (hmR : Measurable R) (L : LocalList m) :
    FiniteLaw.ofMeasure volume (fun s=>(variablePolicy m ξ c hξ hξ1 R hR L s).val)
      ((measurable_variablePolicy m ξ c hξ hξ1 R hR hmR).comp
        (measurable_const.prodMk measurable_id))=
      canonicalLottery ξ (R L) (listBids L) := chosenPolicy_law m ξ (R L) hξ hξ1 L
end FCAppendix.Affine.EqualCapacity
