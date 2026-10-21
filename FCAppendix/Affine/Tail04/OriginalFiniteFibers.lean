import FCAppendix.Affine.Hybrid.CategoryFibers
import FCAppendix.Affine.Hybrid.NativeRows
import FCAppendix.Affine.Tail04.NativeFlagTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalFiniteFibers
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open scoped BigOperators

lemma measure_sum_apply {X K : Type*} [MeasurableSpace X] [DecidableEq K]
    (μ : K → Measure X) (S : Finset K) (B : Set X) :
    (∑ k∈S,μ k) B=∑ k∈S,μ k B := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih => rw [Finset.sum_insert hk,Measure.add_apply,ih,Finset.sum_insert hk]

section Partition
variable {X K : Type*} [MeasurableSpace X] [Fintype K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

lemma restrict_partition (μ : Measure X) (tag : X → K) (htag : Measurable tag) :
    (∑ k,μ.restrict (tag ⁻¹' {k}))=μ := by
  apply Measure.ext
  intro B hB
  rw [measure_sum_apply]
  simp only [Measure.restrict_apply hB]
  have hd : Pairwise (fun k l : K => Disjoint (B∩tag ⁻¹' {k}) (B∩tag ⁻¹' {l})) := by
    intro k l hkl
    apply disjoint_left.mpr
    rintro x ⟨_,hk⟩ ⟨_,hl⟩
    exact hkl (hk.symm.trans hl)
  have hm (k : K) : MeasurableSet (B∩tag ⁻¹' {k}) := hB.inter (htag (measurableSet_singleton k))
  have hu : (⋃ k : K,B∩tag ⁻¹' {k})=B := by
    ext x
    simp
  have hmeasure := measure_iUnion (μ := μ) hd hm
  rw [hu, tsum_fintype] at hmeasure
  exact hmeasure.symm

theorem finite_disintegration (μ : Measure X) [IsFiniteMeasure μ]
    (tag : X → K) (htag : Measurable tag) :
    μ=∑ k,μ (tag ⁻¹' {k}) • cond μ (tag ⁻¹' {k}) := by
  simp_rw [measure_smul_cond]
  exact (restrict_partition μ tag htag).symm

variable {ι : Type*} [Fintype ι]

omit [MeasurableSpace X] [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] [Fintype ι] in
lemma assignment_preimage (tag : X → K) (k : ι → K) :
    (fun x : ι → X => tag ∘ x) ⁻¹' {k}=categoryFiber tag k := by
  ext x
  simp only [mem_preimage,mem_singleton_iff,categoryFiber,mem_univ_pi]
  exact ⟨fun h i => congrFun h i,fun h => funext h⟩

theorem iid_finite_disintegration (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (htag : Measurable tag) :
    Measure.pi (fun _ : ι => μ)=
      ∑ k : ι → K,(∏ i,μ (tag ⁻¹' {k i})) •
        Measure.pi (fun i => cond μ (tag ⁻¹' {k i})) := by
  have ht : Measurable (fun x : ι → X => tag ∘ x) :=
    measurable_pi_lambda _ (fun i => htag.comp (measurable_pi_apply i))
  rw [finite_disintegration (Measure.pi (fun _ : ι => μ)) _ ht]
  apply Finset.sum_congr rfl
  intro k _
  rw [assignment_preimage,categoryFiber_mass,conditional_categoryFiber μ tag htag k]

end Partition

section Operations
variable {X Y K : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype K]

omit [Fintype K] in
lemma map_finsetSum (μ : K → Measure X) (S : Finset K) (f : X → Y) (hf : Measurable f) :
    (∑ k∈S,μ k).map f=∑ k∈S,(μ k).map f := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih => rw [Finset.sum_insert hk,Measure.map_add _ _ hf,ih,Finset.sum_insert hk]

omit [Fintype K] in
lemma sfinite_finsetSum (μ : K → Measure X) [∀ k, SFinite (μ k)] (S : Finset K) :
    SFinite (∑ k∈S, μ k) := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | @insert k S hk ih =>
    rw [Finset.sum_insert hk]
    letI := ih
    infer_instance

omit [Fintype K] in
lemma prod_finsetSum (μ : K → Measure X) [∀ k, SFinite (μ k)] (S : Finset K) (ν : Measure Y) [SFinite ν] :
    (∑ k∈S,μ k).prod ν=∑ k∈S,(μ k).prod ν := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih =>
    letI := sfinite_finsetSum μ S
    rw [Finset.sum_insert hk,Measure.add_prod,ih,Finset.sum_insert hk]

end Operations

section Native
variable {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame (N+1) 2 c Seed)
  {K : Type*} [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K]
  (tag : UserDraw 2 → K) (htag : Measurable tag)

abbrev DeletedSample (N : ℕ) (Seed : Type*) :=
  ((Fin N → UserDraw 2) × (Fin 2 → Seed)) × Equiv.Perm (Fin 2)

def deleteSample (i : Fin (N+1)) (ω : Sample (N+1) 2 Seed) : DeletedSample N Seed :=
  ((NativeFlag.deletedUsers i ω.1.1,ω.1.2),ω.2)

def deletedSampleLaw : Measure (DeletedSample N Seed) :=
  ((Measure.pi (fun _ : Fin N => userLaw Γ)).prod
    (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)

instance : IsProbabilityMeasure (deletedSampleLaw Γ) := by unfold deletedSampleLaw;infer_instance

include Γ in
lemma deleteSample_preserves (i : Fin (N+1)) :
    MeasurePreserving (deleteSample (Seed:=Seed) i) (sampleLaw Γ) (deletedSampleLaw Γ) :=
  ((NativeFlag.deletedUsers_measurePreserving Γ i).prod
    (MeasurePreserving.id (Measure.pi (fun _ : Fin 2 => Γ.seedLaw)))).prod
      (MeasurePreserving.id (permLaw 2))

include htag in
theorem deletedSample_finite_disintegration :
    deletedSampleLaw Γ=
      ∑ k : Fin N → K,(∏ i,userLaw Γ (tag ⁻¹' {k i})) •
        (((Measure.pi (fun i => cond (userLaw Γ) (tag ⁻¹' {k i}))).prod
          (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)) := by
  unfold deletedSampleLaw
  rw [iid_finite_disintegration (userLaw Γ) tag htag]
  rw [prod_finsetSum,prod_finsetSum]
  simp_rw [Measure.prod_smul_left]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_univ]
  · intro x _
    rfl

include htag in
theorem deletedSample_map_fibers {Y : Type*} [MeasurableSpace Y]
    (f : DeletedSample N Seed → Y) (hf : Measurable f) :
    (deletedSampleLaw Γ).map f=
      ∑ k : Fin N → K,(∏ i,userLaw Γ (tag ⁻¹' {k i})) •
        ((((Measure.pi (fun i => cond (userLaw Γ) (tag ⁻¹' {k i}))).prod
          (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2)).map f) := by
  rw [deletedSample_finite_disintegration Γ tag htag,map_finsetSum _ _ f hf]
  simp only [Measure.map_smul]

end Native
end FCAppendix.Affine.Tail04.OriginalFiniteFibers
