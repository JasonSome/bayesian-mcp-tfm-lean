import FCAppendix.Affine.Tail04.SortedCoordinates
import FCAppendix.Affine.Tail04.TypicalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.LocalCoordinates
open MeasureTheory Set Classical Game Bayes
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper SortedCoordinates

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable (E : Observable.Regions) {m : ℕ}

def ids (k : Fin 4) (L : LocalList m) : Finset (Fin m) :=
  Finset.univ.filter fun i => E.localTag (L i)=k

lemma measurable_ids (k : Fin 4) : Measurable (ids E (m:=m) k) :=
  FCAppendix.Exclusive.Marker.measurable_filter Finset.univ _ (fun i =>
    measurableSet_eq_fun (E.measurable_localTag.comp (measurable_pi_apply i)) measurable_const)

lemma ids_card (k : Fin 4) (L : LocalList m) : (ids E k L).card=E.localCount L k := by
  unfold ids Observable.Regions.localCount
  rw [Finset.card_filter]

lemma ids_disjoint {k l : Fin 4} (hkl : k≠l) (L : LocalList m) :
    Disjoint (ids E k L) (ids E l L) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact hkl ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

lemma ids_present (k : Fin 4) (hk : k≠3) (L : LocalList m) (i : Fin m)
    (hi : i∈ids E k L) : L i≠none := by
  intro hn
  have ht := (Finset.mem_filter.mp hi).2
  simp only [hn,Observable.Regions.localTag] at ht
  exact hk ht.symm

lemma private_ids_band (L : LocalList m) (i : Fin m) (hi : i∈ids E 2 L) :
    entryBid (L i)∈E.privateBids := by
  have hp := ids_present E 2 (by decide) L i hi
  cases he : L i with
  | none => exact (hp he).elim
  | some b =>
    have hh := (Finset.mem_filter.mp hi).2
    by_cases hl : b≤ E.d
    · simp [he,Observable.Regions.localTag,hl] at hh
    · by_cases hb : b∈E.privateBids
      · simpa [he,entryBid] using hb
      · simp [he,Observable.Regions.localTag,hl,hb] at hh

def signalKey : Unit ⊕ Icc E.R E.Rp → ℝ
  | .inl _ => E.Rp+1
  | .inr b => b.1

lemma continuous_signalKey : Continuous (signalKey E) :=
  continuous_sum_dom.mpr ⟨continuous_const,continuous_subtype_val⟩

lemma signalKey_injective : Function.Injective (signalKey E) := by
  intro x y he
  cases x with
  | inl x =>
    cases y with
    | inl y => congr
    | inr y => have hy:=y.2.2; simp only [signalKey] at he;linarith
  | inr x =>
    cases y with
    | inl y => have hx:=x.2.2; simp only [signalKey] at he;linarith
    | inr y => exact congrArg Sum.inr (Subtype.ext he)

def clamp (a b x : ℝ) : ℝ := max a (min b x)

lemma clamp_mem {a b x : ℝ} (hab : a≤ b) : clamp a b x∈Icc a b :=
  ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

lemma clamp_eq {a b x : ℝ} (hx : x∈Icc a b) : clamp a b x=x := by
  simp [clamp,min_eq_right hx.2,max_eq_right hx.1]

lemma continuous_clamp (a b : ℝ) : Continuous (clamp a b) :=
  continuous_const.max (continuous_const.min continuous_id)

def decode (b : ℝ) : Ici E.H ⊕ Icc E.R E.Rp :=
  if E.H≤ b then Sum.inl ⟨max E.H b,(show E.H ≤ max E.H b from le_max_left _ _)⟩
  else Sum.inr ⟨clamp E.R E.Rp b,clamp_mem E.R_le_Rp⟩

lemma measurable_decode : Measurable (decode E) := by
  apply Measurable.ite measurableSet_Ici
  · exact measurable_inl.comp ((continuous_const.max continuous_id).measurable.subtype_mk)
  · exact measurable_inr.comp ((continuous_clamp E.R E.Rp).measurable.subtype_mk)

lemma numerical_decode {b : ℝ} (hb : b∈E.privateBids) : numericalEntry (decode E b)=b := by
  by_cases hu : E.H≤ b
  · simp [decode,hu,numericalEntry]
  · have hp : b∈Icc E.R E.Rp := hb.resolve_right hu
    simp [decode,hu,numericalEntry,clamp_eq hp]

lemma decode_upper_iff {b : ℝ} (_hb : b∈E.privateBids) :
    isUpper (signalEntry (decode E b))=true ↔ E.H≤ b := by
  by_cases hu : E.H≤ b <;> simp [decode,hu,signalEntry,isUpper]

def bidVector (L : LocalList m) : Fin m → ℝ := fun i => entryBid (L i)

lemma measurable_bidVector : Measurable (bidVector (m:=m)) :=
  measurable_pi_iff.mpr (fun i => (measurable_entryBid).comp (measurable_pi_apply i))

def privateKey (L : LocalList m) : Fin m → ℝ :=
  fun i => signalKey E (signalEntry (decode E (entryBid (L i))))

lemma measurable_privateKey : Measurable (privateKey E (m:=m)) :=
  measurable_pi_iff.mpr (fun i => (continuous_signalKey E).measurable.comp
    (continuous_signalEntry.measurable.comp ((measurable_decode E).comp
      (measurable_entryBid.comp (measurable_pi_apply i)))))

lemma measurable_finite_eval {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (i : Ω → α) (f : Ω → α → β) (hi : Measurable i) (hf : ∀ a,Measurable (fun ω => f ω a)) :
    Measurable (fun ω => f ω (i ω)) := by
  have he : Measurable (fun z : α×Ω => f z.2 z.1) :=
    measurable_from_prod_countable_right hf
  exact he.comp (hi.prodMk measurable_id)

def activeBids (A : Finset (Fin m)) (L : LocalList m) : TypicalGuard.BidBox A.card E.U :=
  fun i => ⟨clamp 1 E.U (entryBid (L (enumerate A (bidVector L) i))),clamp_mem E.one_le_U⟩

lemma measurable_activeBids (A : Finset (Fin m)) : Measurable (activeBids E A) := by
  apply measurable_pi_iff.mpr
  intro i
  have hi := measurable_subtype_coe.comp
    (measurable_enumerate A bidVector (fun k => measurable_entryBid.comp (measurable_pi_apply k)) i)
  have he := measurable_finite_eval _ _ hi
    (fun k => measurable_entryBid.comp (measurable_pi_apply k))
  exact ((continuous_clamp 1 E.U).measurable.comp he).subtype_mk

lemma activeBids_exact (A : Finset (Fin m)) (L : LocalList m)
    (hA : ∀ i∈A,entryBid (L i)∈Icc (1:ℝ) E.U) (i : Fin A.card) :
    (activeBids E A L i).val=entryBid (L (enumerate A (bidVector L) i)) :=
  clamp_eq (hA _ (enumerate A (bidVector L) i).2)

def privateRow (P : Finset (Fin m)) (L : LocalList m) : Row P.card E.R E.Rp E.H :=
  fun j => decode E (entryBid (L (enumerate P (privateKey E L) j)))

lemma measurable_privateRow (P : Finset (Fin m)) : Measurable (privateRow E P) := by
  apply measurable_pi_iff.mpr
  intro j
  have hi := measurable_subtype_coe.comp
    (measurable_enumerate P (privateKey E) (fun k =>
      (measurable_pi_apply k).comp (measurable_privateKey E)) j)
  have he : Measurable (fun L : LocalList m =>
      entryBid (L (enumerate P (privateKey E L) j).val)) :=
    measurable_finite_eval (fun L : LocalList m => (enumerate P (privateKey E L) j).val)
      (fun L k => entryBid (L k)) hi
      (fun k => measurable_entryBid.comp (measurable_pi_apply k))
  exact (measurable_decode E).comp he

lemma privateRow_exact (P : Finset (Fin m)) (L : LocalList m)
    (hP : ∀ i∈P,entryBid (L i)∈E.privateBids) (j : Fin P.card) :
    numericalEntry (privateRow E P L j)=entryBid (L (enumerate P (privateKey E L) j)) :=
  numerical_decode E (hP _ (enumerate P (privateKey E L) j).2)

lemma decoded_bid_exact (A P : Finset (Fin m)) (hAP : Disjoint A P) (L : LocalList m)
    (hA : ∀ i∈A,entryBid (L i)∈Icc (1:ℝ) E.U)
    (hP : ∀ i∈P,entryBid (L i)∈E.privateBids)
    (i : Target A.card P.card) :
    LocalHighCommon.numericalBid (TypicalGuard.bids (activeBids E A L)) (privateRow E P L) i=
      entryBid (L (targetEmbedding A P hAP (bidVector L) (privateKey E L) i)) := by
  cases i with
  | inl i => exact activeBids_exact E A L hA i
  | inr j => exact privateRow_exact E P L hP j

abbrev Key (m : ℕ) := (Finset (Fin m)×Finset (Fin m))×Fin (m+1)

def key (L : LocalList m) : Key m :=
  ((ids E 1 L,ids E 2 L),⟨E.otherPrivateCount L,by
    unfold Observable.Regions.otherPrivateCount
    omega⟩)

lemma measurable_key : Measurable (key E (m:=m)) := by
  have hfin : Measurable (fun L : LocalList m => (key E L).2) := by
    apply measurable_to_countable'
    intro j
    have he : (fun L : LocalList m => (key E L).2) ⁻¹' {j} =
        {L | E.otherPrivateCount L=j.val} := by
      ext L
      simp only [mem_preimage,mem_singleton_iff,Fin.ext_iff,key,mem_setOf_eq]
    rw [he]
    exact measurableSet_eq_fun E.measurable_otherPrivateCount measurable_const
  exact ((measurable_ids E 1).prodMk (measurable_ids E 2)).prodMk hfin

end FCAppendix.Affine.Tail04.LocalCoordinates
