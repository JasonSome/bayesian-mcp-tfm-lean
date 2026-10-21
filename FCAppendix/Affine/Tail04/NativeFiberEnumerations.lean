import FCAppendix.Affine.Tail04.NativeFocalCoordinates
import FCAppendix.Affine.Tail04.PartialNativeCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFiberEnumerations
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open LocalCoordinates SortedCoordinates PrivateIdentitySort PrivateRowSorting
open NativeCountCoordinates NativeFocalCoordinates EqualPrivateSignal EqualPrivateUpper
open SortedAllNoise PartialNativeCoordinates

def castEquiv {a b : ℕ} (h : a=b) : Fin a ≃ Fin b where
  toFun:=Fin.cast h
  invFun:=Fin.cast h.symm
  left_inv i:=by apply Fin.ext;rfl
  right_inv i:=by apply Fin.ext;rfl

section FiniteInsert
variable {m : ℕ} (P : Finset (Fin m)) (i : Fin m) (hi : i∉P)

def insertEquiv : Fin (P.card+1) ≃ {l : Fin m // l∈insert i P} where
  toFun:=Fin.cases ⟨i,Finset.mem_insert_self _ _⟩
    (fun k => ⟨baselineEmbedding P k,Finset.mem_insert_of_mem (baseline P k).2⟩)
  invFun l:=if h : l.val=i then 0 else
    ((baseline P).symm ⟨l.val,(Finset.mem_insert.mp l.property).resolve_left h⟩).succ
  left_inv k:=by
    refine Fin.cases ?_ (fun j => ?_) k
    · simp
    · have hj : baselineEmbedding P j≠i :=
        fun he => hi (he ▸ (baseline P j).2)
      simp only [Fin.cases_succ,dif_neg hj]
      congr 1
      exact (baseline P).symm_apply_apply j
  right_inv l:=by
    by_cases h : l.val=i
    · apply Subtype.ext
      simp only [dif_pos h,Fin.cases_zero]
      exact h.symm
    · apply Subtype.ext
      simp only [dif_neg h,Fin.cases_succ,baselineEmbedding]
      exact congrArg Subtype.val ((baseline P).apply_symm_apply
        ⟨l.val,(Finset.mem_insert.mp l.property).resolve_left h⟩)

include hi in
lemma insert_card : (insert i P).card=P.card+1 := Finset.card_insert_of_notMem hi

def focalFirst : Fin (insert i P).card ≃ {l : Fin m // l∈insert i P} :=
  (castEquiv (insert_card P i hi)).trans (insertEquiv P i hi)

lemma focalFirst_zero :
    focalFirst P i hi (Fin.cast (insert_card P i hi).symm 0)=⟨i,Finset.mem_insert_self _ _⟩ := by
  change insertEquiv P i hi
    (Fin.cast (insert_card P i hi) (Fin.cast (insert_card P i hi).symm 0))=_
  have he : Fin.cast (insert_card P i hi) (Fin.cast (insert_card P i hi).symm 0)=0 := by
    apply Fin.ext
    rfl
  rw [he]
  rfl

lemma focalFirst_symm :
    (focalFirst P i hi).symm ⟨i,Finset.mem_insert_self _ _⟩=
      Fin.cast (insert_card P i hi).symm 0 := by
  apply (focalFirst P i hi).injective
  rw [Equiv.apply_symm_apply,focalFirst_zero]

lemma focalFirst_row {X : Type*} (f : Fin m → X) :
    (fun k => f (focalFirst P i hi k))=
      (Fin.cons (f i) (fun j => f (baselineEmbedding P j))) ∘
        Fin.cast (insert_card P i hi) := by
  funext k
  change f (insertEquiv P i hi (Fin.cast (insert_card P i hi) k))=
    (show Fin (P.card+1)→X from Fin.cons (f i) (fun j => f (baselineEmbedding P j)))
      (Fin.cast (insert_card P i hi) k)
  generalize Fin.cast (insert_card P i hi) k=l
  exact Fin.cases rfl (fun _ => rfl) l

end FiniteInsert

section Local
variable {m : ℕ} (E : Observable.Regions) (P : Finset (Fin m)) (L : LocalList m)
  (e : Fin P.card ≃ {i : Fin m // i∈P})

def commonRow (hP : ∀ i∈P,entryBid (L i)∈Icc (1:ℝ) E.U) :
    Fin P.card → Icc (1:ℝ) E.U := fun k => ⟨entryBid (L (e k)),hP _ (e k).2⟩

lemma commonRow_baseline (hP : ∀ i∈P,entryBid (L i)∈Icc (1:ℝ) E.U) :
    commonRow E P L e hP=baselineCommon E P L hP ∘ e.trans (baseline P).symm := by
  funext k
  apply Subtype.ext
  change entryBid (L (e k))=entryBid (L ((baseline P) ((baseline P).symm (e k))))
  rw [Equiv.apply_symm_apply]

theorem common_sorted (hP : ∀ i∈P,entryBid (L i)∈Icc (1:ℝ) E.U) :
    activeBids E P L=sortedBox (commonRow E P L e hP) := by
  rw [commonRow_baseline,sortedBox_reindex,activeBids_eq_sorted_baseline]

theorem common_focalRank (hP : ∀ i∈P,entryBid (L i)∈Icc (1:ℝ) E.U)
    (hb : Function.Injective (fun k => (commonRow E P L e hP k:ℝ))) (k : Fin P.card) :
    rankFin P (bidVector L) (e k)=
      focalRank (fun j => (commonRow E P L e hP j:ℝ)) k := by
  let σ : Equiv.Perm (Fin P.card) := e.trans (baseline P).symm
  have hbase : Function.Injective (fun j => (baselineCommon E P L hP j:ℝ)) := by
    intro a b he
    have hh : σ.symm a=σ.symm b := hb (by
      simpa only [commonRow_baseline,Function.comp_apply,σ,Equiv.apply_symm_apply] using he)
    exact σ.symm.injective hh
  have hr := common_rank_eq_focalRank E P L hP (σ k)
  have he : baseline P (σ k)=e k := by simp only [σ,Equiv.trans_apply,Equiv.apply_symm_apply]
  rw [he] at hr
  rw [commonRow_baseline]
  exact hr.trans (focalRank_reindex _ σ hbase k).symm

def privateRaw : Row P.card E.R E.Rp E.H := fun k => LocalCoordinates.decode E (entryBid (L (e k)))

def privatePermutation : Equiv.Perm (Fin P.card) :=
  (rankEquiv P (privateKey E L)).symm.trans e.symm

theorem privateRow_reindex :
    privateRow E P L=PrivatePartialSorting.reindexRow (privatePermutation E P L e)
      (privateRaw E P L e) := by
  funext k
  simp only [privateRow,PrivatePartialSorting.reindexRow,privateRaw,privatePermutation,
    Equiv.trans_apply,Equiv.apply_symm_apply,SortedCoordinates.enumerate]

theorem private_focalRank (k : Fin P.card) :
    rankFin P (privateKey E L) (e k)=(privatePermutation E P L e).symm k := by
  change (rankEquiv P (privateKey E L)) (e k)=_
  rfl

lemma privateRaw_baseline :
    privateRaw E P L (baseline P)=
      (fun k => LocalCoordinates.decode E (entryBid (L (baselineEmbedding P k)))) := rfl

end Local

section Pattern
variable {N : ℕ} (i : Fin (N+1)) (kind : Fin N → Fin 4) (k : Fin 4)

def categoryEnumeration : Fin (rivalSet i kind k).card ≃ {r : Fin N // kind r=k} :=
  (baseline (rivalSet i kind k)).trans (rivalSetEquiv i kind k).symm

lemma categoryEnumeration_identity (j : Fin (rivalSet i kind k).card) :
    i.succAbove (categoryEnumeration i kind k j).val=baselineEmbedding (rivalSet i kind k) j := by
  exact congrArg Subtype.val ((rivalSetEquiv i kind k).apply_symm_apply
    (baseline (rivalSet i kind k) j))

end Pattern
end FCAppendix.Affine.Tail04.NativeFiberEnumerations
