import FCAppendix.Affine.Tail04.FocalInsertionSampling
import FCAppendix.Affine.Tail04.SortedCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.FocalIdentity
open MeasureTheory ProbabilityTheory Set Classical
open SortedCoordinates
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m : ℕ}

lemma old_embedding_mem (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (x : EqualPrivateSignal.Target A.card P.card) :
    targetEmbedding A P hAP b k x∈A∪P := by
  cases x with
  | inl i => exact Finset.mem_union_left _ (enumerate A b i).2
  | inr j => exact Finset.mem_union_right _ (enumerate P k j).2

def embedding (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) : FocalInsertion.Target A.card P.card ↪ Fin m where
  toFun := fun x => Option.elim x i (targetEmbedding A P hAP b k)
  inj' := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        change i = targetEmbedding A P hAP b k y at h
        exact (hi (h.symm ▸ old_embedding_mem A P hAP b k y)).elim
    | some x =>
      cases y with
      | none =>
        change targetEmbedding A P hAP b k x = i at h
        exact (hi (h ▸ old_embedding_mem A P hAP b k x)).elim
      | some y => exact congrArg some ((targetEmbedding A P hAP b k).injective h)

@[simp] lemma embedding_none (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) : embedding i A P hAP hi b k none=i := rfl

@[simp] lemma embedding_some (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (x : EqualPrivateSignal.Target A.card P.card) :
    embedding i A P hAP hi b k (some x)=targetEmbedding A P hAP b k x := rfl

lemma embedding_range (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (j : Fin m) :
    j∈Set.range (embedding i A P hAP hi b k) ↔ j=i ∨ j∈A∪P := by
  constructor
  · rintro ⟨x,rfl⟩
    cases x with
    | none => exact Or.inl rfl
    | some x => exact Or.inr (old_embedding_mem A P hAP b k x)
  · rintro (rfl | hj)
    · exact ⟨none,rfl⟩
    · have ht : j∈SortedCoordinates.transport A P hAP b k Finset.univ := by
        rw [transport_univ]
        exact hj
      obtain ⟨x,hx,hxj⟩ := Finset.mem_map.mp ht
      exact ⟨some x,hxj⟩

def transport (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (S : Finset (FocalInsertion.Target A.card P.card)) :
    Finset (Fin m) := S.map (embedding i A P hAP hi b k)

@[simp] lemma transport_card (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (S : Finset (FocalInsertion.Target A.card P.card)) :
    (transport i A P hAP hi b k S).card=S.card := by simp [transport]

lemma transport_subset (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (S : Finset (FocalInsertion.Target A.card P.card)) :
    transport i A P hAP hi b k S⊆insert i (A∪P) := by
  intro j hj
  obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hj
  cases x with
  | none => simp
  | some x => exact Finset.mem_insert_of_mem (old_embedding_mem A P hAP b k x)

@[simp] lemma focal_mem_transport (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (S : Finset (FocalInsertion.Target A.card P.card)) :
    i∈transport i A P hAP hi b k S ↔ none∈S := by
  change embedding i A P hAP hi b k none∈S.map _ ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hh : a=none := (embedding i A P hAP hi b k).injective he
    exact hh ▸ ha
  · intro h
    exact ⟨none,h,rfl⟩

lemma measurable_transport {Ω : Type*} [MeasurableSpace Ω]
    (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P) (hi : i∉A∪P)
    (b k : Ω → Fin m → ℝ) (hb : ∀ j,Measurable (fun ω => b ω j))
    (hk : ∀ j,Measurable (fun ω => k ω j))
    (S : Ω → Finset (FocalInsertion.Target A.card P.card)) (hS : Measurable S) :
    Measurable (fun ω => transport i A P hAP hi (b ω) (k ω) (S ω)) := by
  have he : Measurable (fun ω x => embedding i A P hAP hi (b ω) (k ω) x) := by
    apply measurable_pi_iff.mpr
    intro x
    cases x with
    | none => exact measurable_const
    | some x =>
      cases x with
      | inl j => exact measurable_subtype_coe.comp (measurable_enumerate A b hb j)
      | inr j => exact measurable_subtype_coe.comp (measurable_enumerate P k hk j)
  have hm := (measurable_of_countable (fun z :
      (FocalInsertion.Target A.card P.card → Fin m) × Finset (FocalInsertion.Target A.card P.card) =>
      z.2.image z.1)).comp (he.prodMk hS)
  simpa only [Function.comp_def,transport,Finset.map_eq_image] using hm

def receipt (i : Fin m) (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : FocalInsertion.Target A.card P.card → ℝ) (low : Fin m → ℝ) (j : Fin m) : ℝ :=
  if j=i then r none else if j∈A∪P then
    SortedCoordinates.receiptTransport A P b k (fun x => r (some x)) j else low j

lemma receipt_embedding (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ)
    (r : FocalInsertion.Target A.card P.card → ℝ) (low : Fin m → ℝ)
    (x : FocalInsertion.Target A.card P.card) :
    receipt i A P b k r low (embedding i A P hAP hi b k x)=r x := by
  cases x with
  | none => simp [receipt]
  | some x =>
    have hx := old_embedding_mem A P hAP b k x
    have hn : targetEmbedding A P hAP b k x≠i := fun he => hi (he ▸ hx)
    simp only [embedding_some,receipt,if_neg hn,if_pos hx]
    exact SortedCoordinates.receiptTransport_embedding A P hAP b k (fun x => r (some x)) x

lemma receipt_outside (i : Fin m) (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : FocalInsertion.Target A.card P.card → ℝ) (low : Fin m → ℝ)
    (j : Fin m) (hj : j∉insert i (A∪P)) : receipt i A P b k r low j=low j := by
  have hn : j≠i := fun he => hj (by simp [he])
  have hu : j∉A∪P := fun h => hj (Finset.mem_insert_of_mem h)
  simp [receipt,hn,hu]

theorem all_identity_optimal (i : Fin m) (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (hi : i∉A∪P) (b k : Fin m → ℝ) (c : ℕ)
    (r : FocalInsertion.Target A.card P.card → ℝ) (low : Fin m → ℝ)
    (S : Finset (FocalInsertion.Target A.card P.card)) (τ : ℝ)
    (hS : FocalInsertion.Threshold c r S τ)
    (hlow : ∀ j,j∉insert i (A∪P) → low j≤ τ) :
    Finite.Optimal c (receipt i A P b k r low) (transport i A P hAP hi b k S) := by
  apply FocalCapacity.optimal_of_threshold c _ _ τ
    (by simpa using hS.1) hS.2.1
  · intro j hj
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hj
    rw [receipt_embedding]
    exact hS.2.2.1 x hx
  · intro j hj
    by_cases hr : j∈Set.range (embedding i A P hAP hi b k)
    · obtain ⟨x,rfl⟩ := hr
      rw [receipt_embedding]
      apply hS.2.2.2 x
      intro hx
      exact hj (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
    · have ho : j∉insert i (A∪P) := by
        simpa only [embedding_range,Finset.mem_insert] using hr
      rw [receipt_outside i A P b k r low j ho]
      exact hlow j ho

end FCAppendix.Affine.Tail04.FocalIdentity
