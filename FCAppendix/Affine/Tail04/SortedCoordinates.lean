import FCAppendix.Exclusive.MarkerConstruction
import FCAppendix.Affine.Tail04.LocalHighCommon
import FCAppendix.Affine.Tail04.LocalObservation

noncomputable section
namespace FCAppendix.Affine.Tail04.SortedCoordinates
open MeasureTheory Set Classical Game
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m : ℕ}

def before (b : Fin m → ℝ) (i j : Fin m) : Prop :=
  b j < b i ∨ b i=b j ∧ i< j

lemma before_irrefl (b : Fin m → ℝ) (i : Fin m) : ¬ before b i i := by
  simp [before]

lemma before_trans (b : Fin m → ℝ) {i j k : Fin m}
    (hij : before b i j) (hjk : before b j k) : before b i k := by
  rcases hij with hij | ⟨hij,hij'⟩ <;> rcases hjk with hjk | ⟨hjk,hjk'⟩
  · exact Or.inl (hjk.trans hij)
  · exact Or.inl (by linarith)
  · exact Or.inl (by linarith)
  · exact Or.inr ⟨hij.trans hjk,hij'.trans hjk'⟩

lemma before_total (b : Fin m → ℝ) {i j : Fin m} (hne : i≠j) :
    before b i j ∨ before b j i := by
  rcases lt_trichotomy (b i) (b j) with hl | he | hg
  · exact Or.inr (Or.inl hl)
  · rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl (Or.inr ⟨he,h⟩)
    · exact Or.inr (Or.inr ⟨he.symm,h⟩)
  · exact Or.inl (Or.inl hg)

def preceding (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) : Finset (Fin m) :=
  P.filter fun j => before b j i

def rank (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) : ℕ :=
  (preceding P b i).card

lemma rank_lt_card (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin m) (hi : i∈P) :
    rank P b i < P.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset _ _,?_⟩
  intro he
  have hh : i ∈ preceding P b i := he.symm ▸ hi
  exact before_irrefl b i (Finset.mem_filter.mp hh).2

lemma rank_strict (P : Finset (Fin m)) (b : Fin m → ℝ)
    {i j : Fin m} (hi : i∈P) (hij : before b i j) : rank P b i < rank P b j := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_,?_⟩
  · intro k hk
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,
      before_trans b (Finset.mem_filter.mp hk).2 hij⟩
  · intro he
    have hh : i∈preceding P b j := Finset.mem_filter.mpr ⟨hi,hij⟩
    have hh' : i∈preceding P b i := he.symm ▸ hh
    exact before_irrefl b i (Finset.mem_filter.mp hh').2

lemma rank_injective (P : Finset (Fin m)) (b : Fin m → ℝ) : Set.InjOn (rank P b) P := by
  intro i hi j hj he
  by_contra hn
  rcases before_total b hn with h | h
  · have hh := rank_strict P b hi h
    omega
  · have hh := rank_strict P b hj h
    omega

def rankFin (P : Finset (Fin m)) (b : Fin m → ℝ) (i : {i // i∈P}) : Fin P.card :=
  ⟨rank P b i,rank_lt_card P b i i.2⟩

lemma rankFin_injective (P : Finset (Fin m)) (b : Fin m → ℝ) :
    Function.Injective (rankFin P b) := by
  intro i j he
  apply Subtype.ext
  exact rank_injective P b i.2 j.2 (congrArg Fin.val he)

lemma rankFin_congr (P : Finset (Fin m)) (b d : Fin m → ℝ)
    (h : ∀ i∈P,b i=d i) : rankFin P b=rankFin P d := by
  funext i
  apply Fin.ext
  change (preceding P b i).card = (preceding P d i).card
  apply congrArg Finset.card
  apply Finset.ext
  intro j
  by_cases hj : j∈P
  · simp [preceding,before,h j hj,h i i.2,hj]
  · simp [preceding,hj]

lemma surjective_of_injective_card {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Injective f) (hc : Fintype.card α=Fintype.card β) :
    Function.Surjective f := by
  have he : Finset.univ.image f = (Finset.univ : Finset β) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injective _ hf]
    simpa only [Finset.card_univ] using hc.ge
  intro y
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp (show y∈Finset.univ.image f by rw [he]; simp)
  exact ⟨x,hxy⟩

lemma rankFin_surjective (P : Finset (Fin m)) (b : Fin m → ℝ) :
    Function.Surjective (rankFin P b) :=
  surjective_of_injective_card _ (rankFin_injective P b) (by simp)

def rankEquiv (P : Finset (Fin m)) (b : Fin m → ℝ) : {i // i∈P} ≃ Fin P.card :=
  Equiv.ofBijective (rankFin P b) ⟨rankFin_injective P b,rankFin_surjective P b⟩

def enumerate (P : Finset (Fin m)) (b : Fin m → ℝ) (k : Fin P.card) : {i // i∈P} :=
  (rankEquiv P b).symm k

@[simp] lemma rank_enumerate (P : Finset (Fin m)) (b : Fin m → ℝ) (k : Fin P.card) :
    rankFin P b (enumerate P b k)=k := (rankEquiv P b).apply_symm_apply k

@[simp] lemma enumerate_rank (P : Finset (Fin m)) (b : Fin m → ℝ) (i : {i // i∈P}) :
    enumerate P b (rankFin P b i)=i := (rankEquiv P b).symm_apply_apply i

lemma enumerate_congr (P : Finset (Fin m)) (b d : Fin m → ℝ)
    (h : ∀ i∈P,b i=d i) : enumerate P b=enumerate P d := by
  have he : rankEquiv P b=rankEquiv P d := Equiv.ext (fun i => congrFun (rankFin_congr P b d h) i)
  unfold enumerate
  rw [he]

lemma enumerate_injective (P : Finset (Fin m)) (b : Fin m → ℝ) :
    Function.Injective (enumerate P b) := (rankEquiv P b).symm.injective

lemma measurable_rank {Ω : Type*} [MeasurableSpace Ω] (P : Finset (Fin m))
    (b : Ω → Fin m → ℝ) (hb : ∀ i, Measurable (fun ω => b ω i)) (i : Fin m) :
    Measurable (fun ω => rank P (b ω) i) := by
  have hbefore (j : Fin m) : MeasurableSet {ω | before (b ω) j i} := by
    have horder : MeasurableSet {ω : Ω | j < i} := by
      by_cases h : j < i
      · have he : {ω : Ω | j < i} = Set.univ := by ext ω; simp [h]
        rw [he]
        exact MeasurableSet.univ
      · have he : {ω : Ω | j < i} = ∅ := by ext ω; simp [h]
        rw [he]
        exact MeasurableSet.empty
    exact (measurableSet_lt (hb i) (hb j)).union
      ((measurableSet_eq_fun (hb j) (hb i)).inter horder)
  exact (measurable_of_countable (fun Q : Finset (Fin m) => Q.card)).comp
    (FCAppendix.Exclusive.Marker.measurable_filter P (fun ω j => before (b ω) j i) hbefore)

lemma measurable_rankFin {Ω : Type*} [MeasurableSpace Ω] (P : Finset (Fin m))
    (b : Ω → Fin m → ℝ) (hb : ∀ i, Measurable (fun ω => b ω i)) (i : {i // i∈P}) :
    Measurable (fun ω => rankFin P (b ω) i) := by
  have he : MeasurableEmbedding (Fin.val : Fin P.card → ℕ) :=
    ⟨Fin.val_injective, measurable_of_countable _, fun _ _ => (Set.to_countable _).measurableSet⟩
  apply he.measurable_comp_iff.mp
  change Measurable (fun ω => rank P (b ω) i)
  exact measurable_rank P b hb i

def inverseTable (P : Finset (Fin m)) (r : {i // i∈P} → Fin P.card) (k : Fin P.card) :
    {i // i∈P} :=
  if h : ∃ i, r i=k then Classical.choose h
  else (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm k

lemma inverseTable_rank (P : Finset (Fin m)) (b : Fin m → ℝ) (k : Fin P.card) :
    inverseTable P (rankFin P b) k=enumerate P b k := by
  have hs := rankFin_surjective P b k
  unfold inverseTable
  rw [dif_pos hs]
  apply rankFin_injective P b
  rw [Classical.choose_spec hs,rank_enumerate]

lemma measurable_enumerate {Ω : Type*} [MeasurableSpace Ω] (P : Finset (Fin m))
    (b : Ω → Fin m → ℝ) (hb : ∀ i, Measurable (fun ω => b ω i)) (k : Fin P.card) :
    Measurable (fun ω => enumerate P (b ω) k) := by
  have hr : Measurable (fun ω => rankFin P (b ω)) :=
    measurable_pi_iff.mpr (fun i => measurable_rankFin P b hb i)
  have hh := (measurable_of_countable (fun r : {i // i∈P} → Fin P.card => inverseTable P r k)).comp hr
  simpa only [Function.comp_def,inverseTable_rank] using hh

lemma enumerate_ordered (P : Finset (Fin m)) (b : Fin m → ℝ)
    {k l : Fin P.card} (hkl : k≤ l) : b (enumerate P b l) ≤ b (enumerate P b k) := by
  by_contra hn
  have hb : before b (enumerate P b l) (enumerate P b k) := Or.inl (lt_of_not_ge hn)
  have hr := rank_strict P b (enumerate P b l).2 hb
  have hk := congrArg Fin.val (rank_enumerate P b k)
  have hl := congrArg Fin.val (rank_enumerate P b l)
  change rank P b (enumerate P b k)=k.val at hk
  change rank P b (enumerate P b l)=l.val at hl
  omega

lemma preceding_eq_higher (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hdist : Set.InjOn b P) (i : Fin m) (hi : i∈P) :
    preceding P b i=P.filter fun j => b i< b j := by
  ext j
  simp only [preceding,Finset.mem_filter,before]
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    rcases h.2 with hl | ⟨he,hle⟩
    · exact hl
    · have hij := hdist h.1 hi he
      subst j
      exact (lt_irrefl i hle).elim
  · exact fun h => ⟨h.1,Or.inl h.2⟩

lemma rank_relabel (e : Equiv.Perm (Fin m)) (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hdist : Set.InjOn b P) (i : Fin m) (hi : i∈P) :
    rank (P.map e.toEmbedding) (fun j => b (e.symm j)) (e i)=rank P b i := by
  have hdist' : Set.InjOn (fun j => b (e.symm j)) (P.map e.toEmbedding) := by
    intro j hj k hk he
    obtain ⟨j0,hj0,rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨k0,hk0,rfl⟩ := Finset.mem_map.mp hk
    exact congrArg e (hdist hj0 hk0 (by simpa using he))
  unfold rank
  rw [preceding_eq_higher _ _ hdist' (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩),
    preceding_eq_higher _ _ hdist i hi]
  have hfilter : (P.map e.toEmbedding).filter (fun j => b i < b (e.symm j)) =
      (P.filter fun j => b i< b j).map e.toEmbedding := by
    ext j
    simp
  simp only [Equiv.symm_apply_apply,hfilter,Finset.card_map]

theorem enumerate_relabel (e : Equiv.Perm (Fin m)) (P : Finset (Fin m)) (b : Fin m → ℝ)
    (hdist : Set.InjOn b P) (k : Fin P.card) :
    (enumerate (P.map e.toEmbedding) (fun j => b (e.symm j))
      (Fin.cast (Finset.card_map e.toEmbedding).symm k)).val = e (enumerate P b k) := by
  let i := enumerate P b k
  let i' : {i // i∈P.map e.toEmbedding} := ⟨e i,Finset.mem_map.mpr ⟨i,i.2,rfl⟩⟩
  have hr : rankFin (P.map e.toEmbedding) (fun j => b (e.symm j)) i' =
      Fin.cast (Finset.card_map e.toEmbedding).symm k := by
    apply Fin.ext
    change rank (P.map e.toEmbedding) (fun j => b (e.symm j)) (e i)=k.val
    rw [rank_relabel e P b hdist i i.2]
    exact congrArg Fin.val (rank_enumerate P b k)
  rw [←hr,enumerate_rank]

def targetEmbedding (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ) :
    EqualPrivateSignal.Target A.card P.card ↪ Fin m where
  toFun := Sum.elim (fun i => (enumerate A b i).val) (fun j => (enumerate P k j).val)
  inj' := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (enumerate_injective A b (Subtype.ext he))
      | inr j =>
        change (enumerate A b i).val = (enumerate P k j).val at he
        exact False.elim ((Finset.disjoint_left.mp hAP) (enumerate A b i).2
          (he.symm ▸ (enumerate P k j).2))
    | inr i =>
      cases j with
      | inl j =>
        change (enumerate P k i).val = (enumerate A b j).val at he
        exact False.elim ((Finset.disjoint_left.mp hAP) (he.symm ▸ (enumerate A b j).2)
          (enumerate P k i).2)
      | inr j => exact congrArg Sum.inr (enumerate_injective P k (Subtype.ext he))

def transport (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card)) : Finset (Fin m) :=
  S.map (targetEmbedding A P hAP b k)

@[simp] lemma transport_card (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card)) :
    (transport A P hAP b k S).card=S.card := Finset.card_map _

lemma transport_subset (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card)) : transport A P hAP b k S ⊆ A∪P := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
  cases j with
  | inl j => exact Finset.mem_union_left _ (enumerate A b j).2
  | inr j => exact Finset.mem_union_right _ (enumerate P k j).2

@[simp] lemma mem_transport (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card))
    (i : EqualPrivateSignal.Target A.card P.card) :
    targetEmbedding A P hAP b k i∈transport A P hAP b k S ↔ i∈S := by
  simp [transport]

lemma sum_transport (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card)) (r : Fin m → ℝ) :
    (∑ i∈transport A P hAP b k S,r i)=∑ i∈S,r (targetEmbedding A P hAP b k i) := by
  simp [transport,Finset.sum_map]

lemma measurable_transport {Ω : Type*} [MeasurableSpace Ω]
    (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Ω → Fin m → ℝ) (hb : ∀ i,Measurable (fun ω => b ω i))
    (hk : ∀ i,Measurable (fun ω => k ω i))
    (S : Ω → Finset (EqualPrivateSignal.Target A.card P.card)) (hS : Measurable S) :
    Measurable (fun ω => transport A P hAP (b ω) (k ω) (S ω)) := by
  have he : Measurable (fun ω i => targetEmbedding A P hAP (b ω) (k ω) i) := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | inl i => exact measurable_subtype_coe.comp (measurable_enumerate A b hb i)
    | inr i => exact measurable_subtype_coe.comp (measurable_enumerate P k hk i)
  have hmap := (measurable_of_countable (fun z :
      (EqualPrivateSignal.Target A.card P.card → Fin m) ×
        Finset (EqualPrivateSignal.Target A.card P.card) => z.2.image z.1)).comp (he.prodMk hS)
  simpa only [transport,Finset.map_eq_image,Function.comp_def] using hmap

lemma transport_univ (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ) :
    transport A P hAP b k Finset.univ=A∪P := by
  apply Finset.Subset.antisymm (transport_subset A P hAP b k _)
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · apply Finset.mem_map.mpr
    refine ⟨Sum.inl (rankFin A b ⟨i,hi⟩),Finset.mem_univ _,?_⟩
    simp only [targetEmbedding,Function.Embedding.coeFn_mk,Sum.elim_inl,enumerate_rank]
  · apply Finset.mem_map.mpr
    refine ⟨Sum.inr (rankFin P k ⟨i,hi⟩),Finset.mem_univ _,?_⟩
    simp only [targetEmbedding,Function.Embedding.coeFn_mk,Sum.elim_inr,enumerate_rank]

theorem transport_optimal (A P : Finset (Fin m)) (hAP : Disjoint A P) (b k : Fin m → ℝ)
    (c : ℕ) (r : Fin m → ℝ) (S : Finset (EqualPrivateSignal.Target A.card P.card))
    (hS : Finite.Optimal c (fun i => r (targetEmbedding A P hAP b k i)) S) :
    Finite.Optimal c (fun i => if i∈A∪P then r i else 0) (transport A P hAP b k S) := by
  let e := targetEmbedding A P hAP b k
  refine ⟨by simpa using hS.1,?_⟩
  intro T hT
  let T' : Finset (EqualPrivateSignal.Target A.card P.card) := Finset.univ.filter fun i => e i∈T
  have hmap : transport A P hAP b k T'=T∩(A∪P) := by
    ext i
    simp only [transport,Finset.mem_map,Finset.mem_inter,T',Finset.mem_filter,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact ⟨hj,transport_subset A P hAP b k Finset.univ
        (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,rfl⟩)⟩
    · intro hi
      have hh : i∈transport A P hAP b k Finset.univ := by
        rw [transport_univ]
        exact hi.2
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hh
      exact ⟨j,hji.symm ▸ hi.1,hji⟩
  have hc : T'.card≤ c := by
    rw [←transport_card A P hAP b k T',hmap]
    exact (Finset.card_le_card Finset.inter_subset_left).trans hT
  have hs : (∑ i∈transport A P hAP b k S, if i∈A∪P then r i else 0)=
      ∑ i∈S,r (e i) := by
    rw [sum_transport]
    apply Finset.sum_congr rfl
    intro i hi
    have hm : e i∈A∪P := transport_subset A P hAP b k Finset.univ
      (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    change (if e i ∈ A∪P then r (e i) else 0) = r (e i)
    exact if_pos hm
  have ht : (∑ i∈T, if i∈A∪P then r i else 0)=∑ i∈T',r (e i) := by
    rw [←sum_transport A P hAP b k T' r,hmap]
    exact Finset.sum_ite_mem T (A∪P) r
  rw [hs,ht]
  exact hS.2 T' hc

def receiptTransport (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : EqualPrivateSignal.Target A.card P.card → ℝ) (i : Fin m) : ℝ :=
  if hA : i∈A then r (Sum.inl (rankFin A b ⟨i,hA⟩))
  else if hP : i∈P then r (Sum.inr (rankFin P k ⟨i,hP⟩)) else 0

lemma receiptTransport_embedding (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (r : EqualPrivateSignal.Target A.card P.card → ℝ)
    (i : EqualPrivateSignal.Target A.card P.card) :
    receiptTransport A P b k r (targetEmbedding A P hAP b k i)=r i := by
  cases i with
  | inl i => simp [targetEmbedding,receiptTransport,(enumerate A b i).2,rank_enumerate]
  | inr j =>
    have hn : (enumerate P k j).val∉A := fun h =>
      (Finset.disjoint_left.mp hAP) h (enumerate P k j).2
    simp [targetEmbedding,receiptTransport,hn,(enumerate P k j).2,rank_enumerate]

lemma receiptTransport_zero (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : EqualPrivateSignal.Target A.card P.card → ℝ) (i : Fin m) (hi : i∉A∪P) :
    receiptTransport A P b k r i=0 := by
  have ha : i∉A := fun h => hi (Finset.mem_union_left _ h)
  have hp : i∉P := fun h => hi (Finset.mem_union_right _ h)
  simp [receiptTransport,ha,hp]

lemma receiptTransport_lower (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : EqualPrivateSignal.Target A.card P.card → ℝ) (a : ℝ) (hr : ∀ i,a≤ r i)
    (i : Fin m) (hi : i∈A∪P) : a≤ receiptTransport A P b k r i := by
  unfold receiptTransport
  split_ifs with hA hP
  · exact hr _
  · exact hr _
  · simp [hA,hP] at hi

lemma receiptTransport_nonneg (A P : Finset (Fin m)) (b k : Fin m → ℝ)
    (r : EqualPrivateSignal.Target A.card P.card → ℝ) (hr : ∀ i,0≤ r i) :
    ∀ i,0≤ receiptTransport A P b k r i := by
  intro i
  unfold receiptTransport
  split_ifs <;> first | exact hr _ | exact le_rfl

theorem receiptTransport_optimal (A P : Finset (Fin m)) (hAP : Disjoint A P)
    (b k : Fin m → ℝ) (c : ℕ) (r : EqualPrivateSignal.Target A.card P.card → ℝ)
    (S : Finset (EqualPrivateSignal.Target A.card P.card)) (hS : Finite.Optimal c r S) :
    Finite.Optimal c (receiptTransport A P b k r) (transport A P hAP b k S) := by
  have he : (fun i => receiptTransport A P b k r (targetEmbedding A P hAP b k i))=r :=
    funext (receiptTransport_embedding A P hAP b k r)
  have hh := transport_optimal A P hAP b k c (receiptTransport A P b k r) S (he.symm ▸ hS)
  have hm : (fun i => if i∈A∪P then receiptTransport A P b k r i else 0)=
      receiptTransport A P b k r := by
    funext i
    by_cases hi : i∈A∪P
    · simp [hi]
    · simp [hi,receiptTransport_zero A P b k r i hi]
  rwa [hm] at hh

end FCAppendix.Affine.Tail04.SortedCoordinates
