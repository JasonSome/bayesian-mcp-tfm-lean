import FCAppendix.Affine.Tail04.NativeActiveFiberCoordinates
import FCAppendix.Affine.Tail04.JoinedPartialPublicIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialFiberCoordinates
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativeCountCoordinates NativeFocalCoordinates
open NativeFiberEnumerations NativeActiveFiberCoordinates PartialNativeCoordinates
open LocalCoordinates SortedCoordinates PrivateIdentitySort PrivateRowSorting SortedAllNoise
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy OriginalPopulation OriginalValues
open Hybrid NativeFlag

section Coordinates
variable {N : ℕ} (E : Observable.Regions) (i : Fin (N+1)) (kind : Fin N → Fin 4)
  {Seed : Type*} (ω : Background (N+1) 2 Seed)
  (hr : ∀r,NativeMenuReports.MenuAction E (ω.1 (i.succAbove r)).1.2) (hk : rivalKinds E i ω=kind)

lemma decode_partial (b : Icc E.R E.Rp) : LocalCoordinates.decode E b=Sum.inr b := by
  have hn : ¬E.H≤(b:ℝ) := not_le.mpr (b.2.2.trans_lt E.Rp_lt_H)
  simp only [LocalCoordinates.decode,if_neg hn]
  congr 1
  exact Subtype.ext (clamp_eq b.2)

include hr hk in
theorem private_raw_focal (b : Icc E.R E.Rp) (j : Fin 2) :
    NativeFiberEnumerations.privateRaw E
      (insert i (rivalSet i kind (NativeContinuation.upperTag j))) (presentList ω i b j)
      (focalFirst _ i (focal_not_mem_rivalSet i kind _))=
      (Fin.cons (Sum.inr b) (privateRowRaw E i kind (NativeContinuation.upperTag j)
        (fun r => ω.1 (i.succAbove r)))) ∘
          Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind _)) := by
  funext q
  unfold NativeFiberEnumerations.privateRaw
  have he:=congrFun (focalFirst_row (rivalSet i kind (NativeContinuation.upperTag j)) i
    (focal_not_mem_rivalSet i kind _) (fun l => LocalCoordinates.decode E (entryBid (presentList ω i b j l)))) q
  rw [he]
  simp only [Function.comp_apply]
  generalize Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind _)) q=k
  refine Fin.cases ?_ (fun r => ?_) k
  · simp only [Fin.cons_zero,presentList_self,entryBid,decode_partial]
  · simp only [Fin.cons_succ,private_source_entry E i kind ω hr hk j r b,entryBid,
      privateRowRaw]

include hr hk in
theorem private_focal_reindex (b : Icc E.R E.Rp) (j : Fin 2) :
    privateRow E (insert i (rivalSet i kind (NativeContinuation.upperTag j)))
      (presentList ω i b j)=
      PrivatePartialSorting.reindexRow
        (privatePermutation E (insert i (rivalSet i kind (NativeContinuation.upperTag j)))
          (presentList ω i b j) (focalFirst _ i (focal_not_mem_rivalSet i kind _)))
        ((Fin.cons (Sum.inr b) (privateRowRaw E i kind (NativeContinuation.upperTag j)
          (fun r => ω.1 (i.succAbove r)))) ∘
            Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind _))) := by
  rw [privateRow_reindex E _ _ (focalFirst _ i (focal_not_mem_rivalSet i kind _)),
    private_raw_focal E i kind ω hr hk b j]

theorem private_focal_rank (b : Icc E.R E.Rp) (j : Fin 2) :
    rankFin (insert i (rivalSet i kind (NativeContinuation.upperTag j)))
      (privateKey E (presentList ω i b j)) ⟨i,Finset.mem_insert_self _ _⟩=
        (privatePermutation E (insert i (rivalSet i kind (NativeContinuation.upperTag j)))
          (presentList ω i b j) (focalFirst _ i (focal_not_mem_rivalSet i kind _))).symm
          (Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind _)).symm 0) := by
  simpa only [focalFirst_zero] using private_focalRank E
    (insert i (rivalSet i kind (NativeContinuation.upperTag j))) (presentList ω i b j)
    (focalFirst _ i (focal_not_mem_rivalSet i kind _))
    (Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind _)).symm 0)

end Coordinates

section FixedSampler
variable {m c : ℕ} (K : Data m c) (A : ℕ) (H0 H1 : Fin (m+1))
  {Up eps : ℝ} (heps : 0< eps) (hRp : K.E.Rp=Up*(1+eps))

theorem zero_permutation_ae
    (p : Parameters A H0.val K.E.R (Up*(1+eps)) K.E.U)
    (row : Row H0.val K.E.R (Up*(1+eps)) K.E.H)
    (j : Fin H0.val) (b : Icc K.E.R Up)
    (σ τ : unitInterval → Equiv.Perm (Fin H0.val))
    (hgap : (1-K.ξ)*K.E.U< K.E.R) :
    ∀ᵐ z : unitInterval ∂volume,∀ u : unitInterval,
      (if Sum.inr ((σ z).symm j)∈K.zeroSampler A H0 H1
        (hRp.symm ▸ p, hRp.symm ▸ PrivatePartialSorting.reindexRow (σ z)
          (AtypicalPartialNoisy.noisyRow (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps.le j b row z)) u
          then (1:ℝ) else 0)=
      (if Sum.inr ((τ z).symm j)∈K.zeroSampler A H0 H1
        (hRp.symm ▸ p, hRp.symm ▸ PrivatePartialSorting.reindexRow (τ z)
          (AtypicalPartialNoisy.noisyRow (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps.le j b row z)) u
          then (1:ℝ) else 0) := by
  rcases K with ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  let K : Data m c := ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  rcases E with ⟨d,R,Rp,U,H,hd,hdR,hRRp,hRp1,hU,hUH⟩
  change Rp=Up*(1+eps) at hRp
  cases hRp
  by_cases h : H0=H1
  · subst H1
    simp only [Data.zeroSampler_equal,Data.equalSampler,AllCountHighPolicy.equalSample]
    have hσ:=PrivatePartialSorting.ae_equalBase_reindexed_privateValue A H0.val c
      ⟨K.xi_pos.le,K.xi_lt_one.le⟩ (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps
      (K.E.Rp_lt_one.le.trans K.E.one_le_U) K.E.U_lt_H
      (((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H)
      (equalParameter p) row j b σ
    have hτ:=PrivatePartialSorting.ae_equalBase_reindexed_privateValue A H0.val c
      ⟨K.xi_pos.le,K.xi_lt_one.le⟩ (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps
      (K.E.Rp_lt_one.le.trans K.E.one_le_U) K.E.U_lt_H
      (((by norm_num : (0:ℝ)<1).trans_le K.E.one_le_U).trans K.E.U_lt_H)
      (equalParameter p) row j b τ
    exact hσ.and hτ |>.mono fun z hz u => (hz.1 u).trans (hz.2 u).symm
  · rw [K.zeroSampler_unequal A H0 H1 h]
    have hz:=JoinedPartialPublicIntegral.ae_every_public_joined_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) false K.xi_pos K.xi_lt_one.le K.width_pos row
      (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H j b
    exact hz.mono fun z hz u => (hz p (σ z) u).trans (hz p (τ z) u).symm

theorem one_permutation_ae
    (p : Parameters A H0.val K.E.R (Up*(1+eps)) K.E.U)
    (row : Row H1.val K.E.R (Up*(1+eps)) K.E.H)
    (j : Fin H1.val) (b : Icc K.E.R Up)
    (σ τ : unitInterval → Equiv.Perm (Fin H1.val))
    (hgap : (1-K.ξ)*K.E.U< K.E.R) :
    ∀ᵐ z : unitInterval ∂volume,∀ u : unitInterval,
      (if Sum.inr ((σ z).symm j)∈K.oneSampler A H0 H1
        (hRp.symm ▸ p, hRp.symm ▸ PrivatePartialSorting.reindexRow (σ z)
          (AtypicalPartialNoisy.noisyRow (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps.le j b row z)) u
          then (1:ℝ) else 0)=
      (if Sum.inr ((τ z).symm j)∈K.oneSampler A H0 H1
        (hRp.symm ▸ p, hRp.symm ▸ PrivatePartialSorting.reindexRow (τ z)
          (AtypicalPartialNoisy.noisyRow (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps.le j b row z)) u
          then (1:ℝ) else 0) := by
  rcases K with ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  let K : Data m c := ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  rcases E with ⟨d,R,Rp,U,H,hd,hdR,hRRp,hRp1,hU,hUH⟩
  change Rp=Up*(1+eps) at hRp
  cases hRp
  by_cases h : H0=H1
  · subst H1
    rw [K.oneSampler_equal]
    simpa only [K.zeroSampler_equal] using zero_permutation_ae K A H0 H0 heps rfl p row j b σ τ hgap
  · rw [K.oneSampler_unequal A H0 H1 h]
    have hz:=JoinedPartialPublicIntegral.ae_every_public_joined_rank A H0.val H1.val c
      (K.marksLaw H0) (K.marksLaw H1) true K.xi_pos K.xi_lt_one.le K.width_pos row
      (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps
      (K.E.R_le_Rp.trans K.E.Rp_lt_H.le) K.E.Rp_lt_one hgap K.E.Rp_lt_H j b
    exact hz.mono fun z hz u => (hz p (σ z) u).trans (hz p (τ z) u).symm

end FixedSampler
end FCAppendix.Affine.Tail04.NativePartialFiberCoordinates
