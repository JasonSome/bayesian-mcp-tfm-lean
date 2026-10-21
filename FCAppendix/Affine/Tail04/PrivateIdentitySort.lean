import FCAppendix.Affine.Tail04.PrivateRowSorting

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateIdentitySort
open MeasureTheory Set Classical
open SortedCoordinates PrivateRowSorting LocalCoordinates EqualPrivateSignal EqualPrivateUpper
open scoped BigOperators

variable {m : ℕ}

def baseline (P : Finset (Fin m)) : Fin P.card ≃ {i : Fin m // i∈P} :=
  (rankEquiv P (fun _ => 0)).symm

def baselineEmbedding (P : Finset (Fin m)) : Fin P.card ↪ Fin m where
  toFun k := (baseline P k).val
  inj' := by
    intro i j he
    exact (baseline P).injective (Subtype.ext he)

lemma baseline_strictMono (P : Finset (Fin m)) : StrictMono (baselineEmbedding P) := by
  intro i j hij
  have hne : baselineEmbedding P i≠baselineEmbedding P j :=
    fun he => (ne_of_lt hij) ((baselineEmbedding P).injective he)
  by_contra hn
  have hji : baselineEmbedding P j< baselineEmbedding P i := lt_of_le_of_ne (not_lt.mp hn) hne.symm
  have hb : before (fun _ : Fin m => (0:ℝ)) (baseline P j) (baseline P i) := Or.inr ⟨rfl,hji⟩
  have hr := rank_strict P (fun _ => 0) (baseline P j).2 hb
  have hi := congrArg Fin.val (rank_enumerate P (fun _ => 0) i)
  have hj := congrArg Fin.val (rank_enumerate P (fun _ => 0) j)
  change rank P (fun _ => 0) (baseline P i)=i.val at hi
  change rank P (fun _ => 0) (baseline P j)=j.val at hj
  have hij' : i.val< j.val := hij
  omega

lemma before_baseline (P : Finset (Fin m)) (b : Fin m → ℝ) (i j : Fin P.card) :
    before (fun k => b (baselineEmbedding P k)) i j ↔
      before b (baselineEmbedding P i) (baselineEmbedding P j) := by
  simp only [before,(baseline_strictMono P).lt_iff_lt]

lemma baseline_range (P : Finset (Fin m)) : Finset.univ.map (baselineEmbedding P)=P := by
  ext i
  constructor
  · intro hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
    exact (baseline P k).2
  · intro hi
    obtain ⟨k,hk⟩ := (baseline P).surjective ⟨i,hi⟩
    exact Finset.mem_map.mpr ⟨k,Finset.mem_univ k,congrArg Subtype.val hk⟩

lemma preceding_baseline (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin P.card) :
    (preceding Finset.univ (fun k => b (baselineEmbedding P k)) i).map
      (baselineEmbedding P)=preceding P b (baselineEmbedding P i) := by
  ext j
  constructor
  · intro hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_filter.mpr ⟨(baseline P k).2,
      (before_baseline P b k i).mp (Finset.mem_filter.mp hk).2⟩
  · intro hj
    obtain ⟨hp,hbefore⟩ := Finset.mem_filter.mp hj
    obtain ⟨k,hk⟩ := (baseline P).surjective ⟨j,hp⟩
    have hkj : baselineEmbedding P k=j := congrArg Subtype.val hk
    exact Finset.mem_map.mpr ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ k,
      (before_baseline P b k i).mpr (by simpa only [hkj] using hbefore)⟩,hkj⟩

lemma rank_baseline (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin P.card) :
    rank Finset.univ (fun k => b (baselineEmbedding P k)) i=
      rank P b (baselineEmbedding P i) := by
  unfold rank
  rw [←preceding_baseline,Finset.card_map]

theorem baseline_position (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin P.card) :
    baseline P (permutation (fun k => b (baselineEmbedding P k)) i)=enumerate P b i := by
  apply rankFin_injective P b
  apply Fin.ext
  change rank P b (baselineEmbedding P (permutation (fun k => b (baselineEmbedding P k)) i))=
    (rankFin P b (enumerate P b i)).val
  rw [rank_enumerate,←rank_baseline]
  have h := congrArg Fin.val (rank_enumerate (Finset.univ : Finset (Fin P.card))
    (fun k => b (baselineEmbedding P k)) (Fin.cast (by simp) i))
  simpa only [rankFin,permutation,Equiv.ofBijective_apply,position,Fin.val_cast] using h

theorem baseline_rank (P : Finset (Fin m)) (b : Fin m → ℝ) (i : Fin P.card) :
    rankFin P b (baseline P i)=
      (permutation (fun k => b (baselineEmbedding P k))).symm i := by
  let σ := permutation (fun k => b (baselineEmbedding P k))
  have hp := baseline_position P b (σ.symm i)
  have hh := congrArg (rankFin P b) hp
  simpa only [σ,Equiv.apply_symm_apply,rank_enumerate] using hh

variable (E : Observable.Regions)

theorem native_privateRow_eq_sorted (P : Finset (Fin m)) (L : Game.LocalList m) :
    LocalCoordinates.privateRow E P L=
      PrivateRowSorting.sortRow E P.card
        (fun k => LocalCoordinates.decode E (Bayes.entryBid (L (baselineEmbedding P k)))) := by
  funext i
  have hi := congrArg Subtype.val (baseline_position P (LocalCoordinates.privateKey E L) i)
  change LocalCoordinates.decode E (Bayes.entryBid (L (enumerate P (LocalCoordinates.privateKey E L) i)))=
    LocalCoordinates.decode E (Bayes.entryBid (L (baselineEmbedding P
      (permutation (fun k => LocalCoordinates.signalKey E (signalEntry
        (LocalCoordinates.decode E (Bayes.entryBid (L (baselineEmbedding P k)))))) i))))
  rw [←hi]
  rfl

end FCAppendix.Affine.Tail04.PrivateIdentitySort
