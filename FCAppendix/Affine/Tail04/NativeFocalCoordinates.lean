import FCAppendix.Affine.Tail04.NativeCountCoordinates
import FCAppendix.Affine.Tail04.PrivatePartialSorting
import FCAppendix.Affine.Tail04.PrivateUpdate
import FCAppendix.Affine.Tail04.NativePartialReports

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeFocalCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalCoordinates SortedCoordinates
open PrivateIdentitySort PrivateRowSorting SortedAllNoise NativeLocalPolicy
open NativeCountCoordinates PrivateUpdate PrivatePartialSorting JoinedHighPolicy LocalHighCommon
open scoped BigOperators

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

section Common
variable {N : ℕ}

theorem sorted_reindex (b : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    sorted (b ∘ σ)=sorted b := by
  let τ := (permutation (b ∘ σ)).trans (σ.trans (permutation b).symm)
  have h := antitone_perm_unique (sorted b) (sorted (b ∘ σ)) τ
    (sorted_antitone b) (sorted_antitone (b ∘ σ)) (fun i => by
      simp only [τ,sorted,Function.comp_apply,Equiv.trans_apply,Equiv.apply_symm_apply])
  exact h.symm

theorem sortedBox_reindex {L U : ℝ} (b : Fin N → Icc L U) (σ : Equiv.Perm (Fin N)) :
    sortedBox (b ∘ σ)=sortedBox b := by
  funext i
  apply Subtype.ext
  exact congrFun (sorted_reindex (fun j => (b j:ℝ)) σ) i

theorem focalRank_reindex (b : Fin N → ℝ) (σ : Equiv.Perm (Fin N))
    (hb : Function.Injective b) (i : Fin N) :
    focalRank (b ∘ σ) i=focalRank b (σ i) := by
  apply (hb.comp (permutation b).injective)
  calc
    b (permutation b (focalRank (b ∘ σ) i))=
        sorted (b ∘ σ) (focalRank (b ∘ σ) i) :=
      (congrFun (sorted_reindex b σ) (focalRank (b ∘ σ) i)).symm
    _ = b (σ i) := by simp only [sorted,focalRank,Function.comp_apply,Equiv.apply_symm_apply]
    _ = b (permutation b (focalRank b (σ i))) := by simp only [focalRank,Equiv.apply_symm_apply]

theorem ae_focalRank_reindex {eps : ℝ} (heps : 0< eps) (b : Fin N → ℝ)
    (hb : ∀ i,b i≠0) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ σ : Equiv.Perm (Fin N),∀ i,
        focalRank ((AllNoiseFiniteSelector.noisyBids eps b z) ∘ σ) i=
          focalRank (AllNoiseFiniteSelector.noisyBids eps b z) (σ i) := by
  filter_upwards [AtypicalActiveNoisy.ae_noisyBids_distinct heps.ne' b hb] with z hz
  have hinj : Function.Injective (AllNoiseFiniteSelector.noisyBids eps b z) := by
    intro i j he
    by_contra hn
    exact hz i j hn he
  exact fun σ i => focalRank_reindex _ σ hinj i

end Common

section Private
variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

def rawPrivate (P : Finset (Fin m)) (L : LocalList m) : Row P.card D.E.R D.E.Rp D.E.H :=
  fun k => LocalCoordinates.decode D.E (entryBid (L (baselineEmbedding P k)))

def rawPrivateSlot (P : Finset (Fin m)) (i : Fin m) (hi : i∈P) : Fin P.card :=
  (baseline P).symm ⟨i,hi⟩

lemma rawPrivateSlot_identity (P : Finset (Fin m)) (i : Fin m) (hi : i∈P) :
    baselineEmbedding P (rawPrivateSlot P i hi)=i := by
  change (baseline P ((baseline P).symm ⟨i,hi⟩)).val=i
  simp only [Equiv.apply_symm_apply]

lemma rawPrivateSlot_injective (P : Finset (Fin m)) (i : Fin m) (hi : i∈P)
    (k : Fin P.card) : baselineEmbedding P k=i ↔ k=rawPrivateSlot P i hi := by
  constructor
  · intro h
    apply (baselineEmbedding P).injective
    exact h.trans (rawPrivateSlot_identity P i hi).symm
  · intro h
    exact (congrArg (baselineEmbedding P) h).trans (rawPrivateSlot_identity P i hi)

theorem privateRow_eq_sortRaw (P : Finset (Fin m)) (L : LocalList m) :
    privateRow D.E P L=sortRow D.E P.card (rawPrivate D P L) :=
  native_privateRow_eq_sorted D.E P L

theorem private_rank_rawSlot (P : Finset (Fin m)) (L : LocalList m)
    (i : Fin m) (hi : i∈P) :
    rankFin P (privateKey D.E L) ⟨i,hi⟩=
      (permutation (fun k => LocalCoordinates.signalKey D.E (signal (rawPrivate D P L) k))).symm
        (rawPrivateSlot P i hi) := by
  have h := private_rank_eq_focalRank D.E P L (rawPrivateSlot P i hi)
  simpa only [rawPrivate,rawPrivateSlot,Equiv.apply_symm_apply,signal] using h

lemma rawPrivate_partial (P : Finset (Fin m)) (L : LocalList m) (i : Fin m) (hi : i∈P)
    (b : Icc D.E.R D.E.Rp) (hb : L i=some (b:ℝ)) :
    rawPrivate D P L (rawPrivateSlot P i hi)=Sum.inr b := by
  rw [rawPrivate,rawPrivateSlot_identity P i hi,hb]
  exact NativePartialReports.decode_partial D b

theorem rawPrivate_update (P : Finset (Fin m)) (L : LocalList m)
    (i : Fin m) (hi : i∈P) (b : Icc D.E.R D.E.Rp) :
    rawPrivate D P (Function.update L i (some (b:ℝ)))=
      Function.update (rawPrivate D P L) (rawPrivateSlot P i hi) (Sum.inr b) := by
  funext k
  by_cases hk : k=rawPrivateSlot P i hi
  · subst k
    simp only [rawPrivate,rawPrivateSlot_identity P i hi,Function.update_self,entryBid]
    exact NativePartialReports.decode_partial D b
  · have hki : baselineEmbedding P k≠i := fun he => hk ((rawPrivateSlot_injective P i hi k).mp he)
    simp only [rawPrivate,Function.update_of_ne hki,Function.update_of_ne hk]

theorem completed_zero_private_regular (L : LocalList m) (hmenu : D.offCommon L=∅)
    (hH : D.finiteCount (ids D.E 2 L)=D.finiteCount (ids D.E 3 L))
    (i : Fin m) (hi : i∈ids D.E 2 L) (b : Icc D.E.R D.E.Rp) (hb : L i=some (b:ℝ))
    (hreg : PrivatePayoffContinuity.policyInput (c:=c) (ξ:=D.ξ)
      (equalParameter (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 3 L)) L))
      (signal (rawPrivate D (ids D.E 2 L) L))∈
        PrivatePayoffContinuity.Regular D.ξ (rawPrivateSlot (ids D.E 2 L) i hi))
    (u : Seed) :
    (if i∈(D.completedPolicy 0 L u).val then (1:ℝ) else 0)=
      PrivatePayoffContinuity.privateValue (c:=c) D.ξ (rawPrivateSlot (ids D.E 2 L) i hi)
        (PrivatePayoffContinuity.policyInput (c:=c) (ξ:=D.ξ)
          (equalParameter (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 3 L)) L)) (signal (rawPrivate D (ids D.E 2 L) L))) := by
  rw [D.completed_on_menu 0 L hmenu u]
  simp only [own_zero_private D L i hi u]
  have hs : D.zeroSampler (ids D.E 1 L).card (D.finiteCount (ids D.E 2 L))
      (D.finiteCount (ids D.E 3 L))=D.equalSampler (ids D.E 1 L).card
        (D.finiteCount (ids D.E 2 L)) := by
    rw [←hH,D.zeroSampler_equal]
  rw [hs,privateRow_eq_sortRaw D,private_rank_rawSlot D]
  exact equalBase_sorted_privateValue D.E (ids D.E 1 L).card (ids D.E 2 L).card c
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ _ _ (rawPrivateSlot (ids D.E 2 L) i hi) b
    (rawPrivate_partial D _ L i hi b hb) hreg u.1

theorem completed_one_private_regular (L : LocalList m) (hmenu : D.offCommon L=∅)
    (hH : D.finiteCount (ids D.E 3 L)=D.finiteCount (ids D.E 2 L))
    (i : Fin m) (hi : i∈ids D.E 2 L) (b : Icc D.E.R D.E.Rp) (hb : L i=some (b:ℝ))
    (hreg : PrivatePayoffContinuity.policyInput (c:=c) (ξ:=D.ξ)
      (equalParameter (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
        (D.finiteCount (ids D.E 2 L)) L))
      (signal (rawPrivate D (ids D.E 2 L) L))∈
        PrivatePayoffContinuity.Regular D.ξ (rawPrivateSlot (ids D.E 2 L) i hi))
    (u : Seed) :
    (if i∈(D.completedPolicy 1 L u).val then (1:ℝ) else 0)=
      PrivatePayoffContinuity.privateValue (c:=c) D.ξ (rawPrivateSlot (ids D.E 2 L) i hi)
        (PrivatePayoffContinuity.policyInput (c:=c) (ξ:=D.ξ)
          (equalParameter (D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
            (D.finiteCount (ids D.E 2 L)) L)) (signal (rawPrivate D (ids D.E 2 L) L))) := by
  rw [D.completed_on_menu 1 L hmenu u]
  simp only [own_one_private D L i hi u]
  let f : Fin (m+1)→ℝ := fun H0=>
    if Sum.inr (rankFin (ids D.E 2 L) (privateKey D.E L) ⟨i,hi⟩)∈
      D.oneSampler (ids D.E 1 L).card H0 (D.finiteCount (ids D.E 2 L))
        (D.parameter (ids D.E 1 L) H0 (D.finiteCount (ids D.E 2 L)) L,
          privateRow D.E (ids D.E 2 L) L) u.1 then 1 else 0
  change f (D.finiteCount (ids D.E 3 L))=_
  rw [hH]
  dsimp only [f]
  rw [D.oneSampler_equal,privateRow_eq_sortRaw D,private_rank_rawSlot D]
  exact equalBase_sorted_privateValue D.E (ids D.E 1 L).card (ids D.E 2 L).card c
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ _ _ (rawPrivateSlot (ids D.E 2 L) i hi) b
    (rawPrivate_partial D _ L i hi b hb) hreg u.1

theorem completed_zero_private_unequal (L : LocalList m) (hmenu : D.offCommon L=∅)
    (hH : D.finiteCount (ids D.E 2 L)≠D.finiteCount (ids D.E 3 L))
    (hgap : (1-D.ξ)*D.E.U< D.E.R)
    (i : Fin m) (hi : i∈ids D.E 2 L) (b : Icc D.E.R D.E.Rp) (hb : L i=some (b:ℝ))
    (hno : ∀ k,k≠rawPrivateSlot (ids D.E 2 L) i hi →
      numericalEntry (rawPrivate D (ids D.E 2 L) L k)≠(b:ℝ)) (u : Seed) :
    let p := D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 2 L))
      (D.finiteCount (ids D.E 3 L)) L
    (if i∈(D.completedPolicy 0 L u).val then (1:ℝ) else 0)=
      if UseTypical (ids D.E 1 L).card (ids D.E 2 L).card (ids D.E 3 L).card c
        D.ξ D.E.U D.E.R D.E.Rp D.width
        (D.marksLaw (D.finiteCount (ids D.E 2 L)))
        (D.marksLaw (D.finiteCount (ids D.E 3 L))) p then
          (if regime p.1.1 then 0 else 1)
      else AtypicalPartialNoisy.rankInclusion (ids D.E 1 L).card (ids D.E 2 L).card
        (ids D.E 3 L).card c false (rawPrivateSlot (ids D.E 2 L) i hi)
        ((b:ℝ),signal (rawPrivate D (ids D.E 2 L) L)) := by
  dsimp only
  rw [D.completed_on_menu 0 L hmenu u]
  simp only [own_zero_private D L i hi u]
  rw [D.zeroSampler_unequal _ _ _ hH,privateRow_eq_sortRaw D,private_rank_rawSlot D]
  exact joined_reindexed_rank (ids D.E 1 L).card (ids D.E 2 L).card (ids D.E 3 L).card c
    (D.marksLaw (D.finiteCount (ids D.E 2 L))) (D.marksLaw (D.finiteCount (ids D.E 3 L)))
    false D.xi_pos D.xi_lt_one.le D.width_pos _ (rawPrivate D (ids D.E 2 L) L)
    (permutation (fun k => LocalCoordinates.signalKey D.E (signal (rawPrivate D (ids D.E 2 L) L) k)))
    (D.E.d_nonneg.trans_lt D.E.d_lt_R)
    (D.E.R_le_Rp.trans (D.E.Rp_lt_one.le.trans (D.E.one_le_U.trans D.E.U_lt_H.le)))
    D.E.Rp_lt_one hgap (D.E.Rp_lt_one.trans_le D.E.one_le_U |>.trans D.E.U_lt_H)
    (rawPrivateSlot (ids D.E 2 L) i hi) b (rawPrivate_partial D _ L i hi b hb) hno u.1

theorem completed_one_private_unequal (L : LocalList m) (hmenu : D.offCommon L=∅)
    (hH : D.finiteCount (ids D.E 3 L)≠D.finiteCount (ids D.E 2 L))
    (hgap : (1-D.ξ)*D.E.U< D.E.R)
    (i : Fin m) (hi : i∈ids D.E 2 L) (b : Icc D.E.R D.E.Rp) (hb : L i=some (b:ℝ))
    (hno : ∀ k,k≠rawPrivateSlot (ids D.E 2 L) i hi →
      numericalEntry (rawPrivate D (ids D.E 2 L) L k)≠(b:ℝ)) (u : Seed) :
    let p := D.parameter (ids D.E 1 L) (D.finiteCount (ids D.E 3 L))
      (D.finiteCount (ids D.E 2 L)) L
    (if i∈(D.completedPolicy 1 L u).val then (1:ℝ) else 0)=
      if UseTypical (ids D.E 1 L).card (ids D.E 3 L).card (ids D.E 2 L).card c
        D.ξ D.E.U D.E.R D.E.Rp D.width
        (D.marksLaw (D.finiteCount (ids D.E 3 L)))
        (D.marksLaw (D.finiteCount (ids D.E 2 L))) p then
          (if regime p.1.1 then 0 else 1)
      else AtypicalPartialNoisy.rankInclusion (ids D.E 1 L).card (ids D.E 3 L).card
        (ids D.E 2 L).card c true (rawPrivateSlot (ids D.E 2 L) i hi)
        ((b:ℝ),signal (rawPrivate D (ids D.E 2 L) L)) := by
  dsimp only
  rw [D.completed_on_menu 1 L hmenu u]
  simp only [own_one_private D L i hi u]
  rw [D.oneSampler_unequal _ _ _ hH,privateRow_eq_sortRaw D,private_rank_rawSlot D]
  exact joined_reindexed_rank (ids D.E 1 L).card (ids D.E 3 L).card (ids D.E 2 L).card c
    (D.marksLaw (D.finiteCount (ids D.E 3 L))) (D.marksLaw (D.finiteCount (ids D.E 2 L)))
    true D.xi_pos D.xi_lt_one.le D.width_pos _ (rawPrivate D (ids D.E 2 L) L)
    (permutation (fun k => LocalCoordinates.signalKey D.E (signal (rawPrivate D (ids D.E 2 L) L) k)))
    (D.E.d_nonneg.trans_lt D.E.d_lt_R)
    (D.E.R_le_Rp.trans (D.E.Rp_lt_one.le.trans (D.E.one_le_U.trans D.E.U_lt_H.le)))
    D.E.Rp_lt_one hgap (D.E.Rp_lt_one.trans_le D.E.one_le_U |>.trans D.E.U_lt_H)
    (rawPrivateSlot (ids D.E 2 L) i hi) b (rawPrivate_partial D _ L i hi b hb) hno u.1

end Private
end FCAppendix.Affine.Tail04.NativeFocalCoordinates
