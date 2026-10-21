import FCAppendix.Affine.Tail04.NativePartialExperiment

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialTerminal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativeCountCoordinates NativeFocalCoordinates
open NativeFiberEnumerations NativeActiveFiberCoordinates NativePartialFiberCoordinates
open NativePartialExperiment PartialNativeCoordinates LocalCoordinates SortedCoordinates PrivateRowSorting
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy OriginalPopulation OriginalValues
open Hybrid SortedAllNoise

variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (i : Fin (N+1)) (kind : Fin N → Fin 4)

def post0 (side : Bool) : Fin (N+2) :=
  if side then K.finiteCount (rivalSet i kind 2)
  else K.finiteCount (insert i (rivalSet i kind 2))

def post1 (side : Bool) : Fin (N+2) :=
  if side then K.finiteCount (insert i (rivalSet i kind 3))
  else K.finiteCount (rivalSet i kind 3)

def focalIndex (side : Bool) :
    Fin (ownH (post0 K i kind side) (post1 K i kind side) side).val := by
  cases side
  · exact Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 2)).symm 0
  · exact Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 3)).symm 0

lemma post_card (side : Bool) :
    (ownH (post0 K i kind side) (post1 K i kind side) side).val=
      (ownH (K.finiteCount (rivalSet i kind 2)) (K.finiteCount (rivalSet i kind 3)) side).val+1 := by
  cases side
  · exact insert_card _ i (focal_not_mem_rivalSet i kind 2)
  · exact insert_card _ i (focal_not_mem_rivalSet i kind 3)

lemma focalIndex_eq_cast (side : Bool) :
    focalIndex K i kind side=Fin.cast (post_card K i kind side).symm 0 := by
  cases side <;> apply Fin.ext <;> rfl

abbrev Rows := Row (zeroSize i kind) K.E.R K.E.Rp K.E.H ×
  Row (oneSize i kind) K.E.R K.E.Rp K.E.H

def focalRow (side : Bool) (b : Icc K.E.R K.E.Rp) (rows : Rows K i kind) :
    Row (ownH (post0 K i kind side) (post1 K i kind side) side).val K.E.R K.E.Rp K.E.H := by
  cases side
  · exact (Fin.cons (Sum.inr b) rows.1) ∘ Fin.cast
      (insert_card _ i (focal_not_mem_rivalSet i kind 2))
  · exact (Fin.cons (Sum.inr b) rows.2) ∘ Fin.cast
      (insert_card _ i (focal_not_mem_rivalSet i kind 3))

lemma measurable_focalRow (side : Bool) : Measurable (Function.uncurry (focalRow K i kind side)) := by
  cases side
  · have hm : Measurable (fun z : Icc K.E.R K.E.Rp×Rows K i kind =>
        (Fin.cons (Sum.inr z.1) z.2.1 : Fin (zeroSize i kind+1)→Ici K.E.H⊕Icc K.E.R K.E.Rp)) := by
      apply measurable_pi_lambda
      intro j
      refine Fin.cases ?_ (fun q=>?_) j
      · exact measurable_inr.comp measurable_fst
      · exact (measurable_pi_apply q).comp measurable_snd.fst
    exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply (Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 2)) j)).comp hm
  · have hm : Measurable (fun z : Icc K.E.R K.E.Rp×Rows K i kind =>
        (Fin.cons (Sum.inr z.1) z.2.2 : Fin (oneSize i kind+1)→Ici K.E.H⊕Icc K.E.R K.E.Rp)) := by
      apply measurable_pi_lambda
      intro j
      refine Fin.cases ?_ (fun q=>?_) j
      · exact measurable_inr.comp measurable_fst
      · exact (measurable_pi_apply q).comp measurable_snd.snd
    exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply (Fin.cast (insert_card _ i (focal_not_mem_rivalSet i kind 3)) j)).comp hm

def floorPrice : Icc K.E.R K.E.Rp := ⟨K.E.R,le_rfl,K.E.R_le_Rp⟩

lemma focalRow_update (side : Bool) (b : Icc K.E.R K.E.Rp) (rows : Rows K i kind) :
    Function.update (focalRow K i kind side (floorPrice K) rows) (focalIndex K i kind side)
      (Sum.inr b)=focalRow K i kind side b rows := by
  cases side <;> exact update_cast_cons _ _ _ _

def privateAccept (side : Bool) (b : Icc K.E.R K.E.Rp)
    (ω : Background (N+1) 2 Seed) : Bool :=
  if side then privateOneAccept K i b ω else privateZeroAccept K i b ω

def privateSeed (side : Bool) (ω : Background (N+1) 2 Seed) : unitInterval :=
  (ω.2 (if side then 1 else 0)).1

lemma privateAccept_policy (side : Bool) (b : Icc K.E.R K.E.Rp)
    (ω : Background (N+1) 2 Seed) :
    privateAccept K i side b ω=
      decide (i∈(K.policy (if side then 1 else 0)
        (presentList ω i b (if side then 1 else 0)) (ω.2 (if side then 1 else 0))).val) := by
  cases side
  · exact decide_eq_decide.mpr (own_zero_private K _ i
      (partial_present_ids K i b ω 0) (ω.2 0)).symm
  · exact decide_eq_decide.mpr (own_one_private K _ i
      (partial_present_ids K i b ω 1) (ω.2 1)).symm

lemma measurable_presentList_joint (j : Fin 2) :
    Measurable (fun x : ℝ×Background (N+1) 2 Seed => presentList x.2 i x.1 j) := by
  apply measurable_pi_lambda
  intro l
  by_cases hl : l=i
  · subst l
    simpa only [presentList_self,Function.comp_apply] using! measurable_some.comp measurable_fst
  · have he (x : ℝ×Background (N+1) 2 Seed) :
        presentList x.2 i x.1 j l=presentList x.2 i 0 j l := by
      simp only [presentList_other _ _ _ hl]
    simp_rw [he]
    exact ((measurable_pi_apply l).comp (measurable_presentList i 0 j)).comp measurable_snd

attribute [local irreducible] NativeLocalPolicy.Data.policy

lemma measurable_privateAccept (side : Bool) :
    Measurable (Function.uncurry (privateAccept K i side)) := by
  simp only [Function.uncurry_def,privateAccept_policy]
  let j : Fin 2 := if side then 1 else 0
  have hp : Measurable (fun z : Icc K.E.R K.E.Rp×Background (N+1) 2 Seed =>
      (K.policy j (presentList z.2 i z.1 j) (z.2.2 j)).val) := (K.policy_measurable j).comp
    (((measurable_presentList_joint (i:=i) j).comp
      (measurable_fst.subtype_val.prodMk measurable_snd)).prodMk
      ((measurable_pi_apply j).comp measurable_snd.snd))
  exact (measurable_of_countable (fun S : Finset (Fin (N+1)) => decide (i∈S))).comp hp

variable (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀ r,MenuAction K.E (ω.1 (i.succAbove r)).1.2)
  (hk : PartialNativeCoordinates.rivalKinds K.E i ω=kind)

include hQ hr hk in
theorem parameter_eq (b : Icc K.E.R K.E.Rp) (j : Fin 2)
    (H0 H1 : Fin (N+2)) (low : Bool) (u : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i b j))=
      if low then some u else none) :
    K.parameter (rivalSet i kind 1) H0 H1 (presentList ω i b j)=
      publicParameter K (commonSize i kind) H0 H1 Q low
        (commonRow K.E i kind (fun r => ω.1 (i.succAbove r))) u := by
  unfold NativeLocalPolicy.Data.parameter
  rw [common_bids K.E i kind ω hr hk b j,hQ]
  dsimp only [PublicScenario.localChoice]
  rw [hs]
  cases low <;> rfl

include hQ hr hk in
theorem zero_reindexed (b : Icc K.E.R K.E.Rp) (low : Bool) (u : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i b 0))=
      if low then some u else none) :
    (if privateZeroAccept K i b ω then (1:ℝ) else 0)=
      let σ := privatePermutation K.E (insert i (rivalSet i kind 2)) (presentList ω i b 0)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 2))
      let H0 := post0 K i kind false
      let H1 := post1 K i kind false
      if Sum.inr (σ.symm (focalIndex K i kind false))∈K.zeroSampler (commonSize i kind) H0 H1
        (publicParameter K (commonSize i kind) H0 H1 Q low
          (commonRow K.E i kind (fun r => ω.1 (i.succAbove r))) u,
          PrivatePartialSorting.reindexRow σ (focalRow K i kind false b
            (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
              privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))) (ω.2 0).1
        then 1 else 0 := by
  have hi := PartialNativeCoordinates.partial_ids K.E i ω hr b 0
  simp only [hk,show NativeContinuation.upperTag (0:Fin 2)=(2:Fin 4) from rfl,
    show NativeContinuation.upperTag (1:Fin 2)=(3:Fin 4) from rfl,
    show otherProposer (0:Fin 2)=1 from rfl] at hi
  have transport (A Z O : Finset (Fin (N+1))) (him : i∈Z)
      (hA : A=rivalSet i kind 1)
      (hZ : Z=insert i (rivalSet i kind 2)) (hO : O=rivalSet i kind 3) :
      (if Sum.inr (rankFin Z (privateKey K.E (presentList ω i b 0)) ⟨i,him⟩)∈
        K.zeroSampler A.card (K.finiteCount Z) (K.finiteCount O)
          (K.parameter A (K.finiteCount Z) (K.finiteCount O) (presentList ω i b 0),
            privateRow K.E Z (presentList ω i b 0)) (ω.2 0).1 then (1:ℝ) else 0)=
      let σ := privatePermutation K.E (insert i (rivalSet i kind 2)) (presentList ω i b 0)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 2))
      let H0 := post0 K i kind false
      let H1 := post1 K i kind false
      if Sum.inr (σ.symm (focalIndex K i kind false))∈K.zeroSampler (commonSize i kind) H0 H1
        (publicParameter K (commonSize i kind) H0 H1 Q low
          (commonRow K.E i kind (fun r => ω.1 (i.succAbove r))) u,
          PrivatePartialSorting.reindexRow σ (focalRow K i kind false b
            (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
              privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))) (ω.2 0).1
        then 1 else 0 := by
    subst A
    subst Z
    subst O
    erw [parameter_eq K i kind Q μL hQ ω hr hk b 0 _ _ low u hs,
      private_focal_reindex K.E i kind ω hr hk b 0,
      private_focal_rank K.E i kind ω b 0]
    rfl
  simpa only [privateZeroAccept,decide_eq_true_eq] using! transport
    (ids K.E 1 (presentList ω i b 0)) (ids K.E 2 (presentList ω i b 0)) (ids K.E 3 (presentList ω i b 0))
    (partial_present_ids K i b ω 0) hi.2.1 hi.2.2.1 hi.2.2.2

include hQ hr hk in
theorem one_reindexed (b : Icc K.E.R K.E.Rp) (low : Bool) (u : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i b 1))=
      if low then some u else none) :
    (if privateOneAccept K i b ω then (1:ℝ) else 0)=
      let σ := privatePermutation K.E (insert i (rivalSet i kind 3)) (presentList ω i b 1)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 3))
      let H0 := post0 K i kind true
      let H1 := post1 K i kind true
      if Sum.inr (σ.symm (focalIndex K i kind true))∈K.oneSampler (commonSize i kind) H0 H1
        (publicParameter K (commonSize i kind) H0 H1 Q low
          (commonRow K.E i kind (fun r => ω.1 (i.succAbove r))) u,
          PrivatePartialSorting.reindexRow σ (focalRow K i kind true b
            (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
              privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))) (ω.2 1).1
        then 1 else 0 := by
  have hi := PartialNativeCoordinates.partial_ids K.E i ω hr b 1
  simp only [hk,show NativeContinuation.upperTag (0:Fin 2)=(2:Fin 4) from rfl,
    show NativeContinuation.upperTag (1:Fin 2)=(3:Fin 4) from rfl,
    show otherProposer (1:Fin 2)=0 from rfl] at hi
  have transport (A Z O : Finset (Fin (N+1))) (him : i∈O)
      (hA : A=rivalSet i kind 1)
      (hZ : Z=rivalSet i kind 2) (hO : O=insert i (rivalSet i kind 3)) :
      (if Sum.inr (rankFin O (privateKey K.E (presentList ω i b 1)) ⟨i,him⟩)∈
        K.oneSampler A.card (K.finiteCount Z) (K.finiteCount O)
          (K.parameter A (K.finiteCount Z) (K.finiteCount O) (presentList ω i b 1),
            privateRow K.E O (presentList ω i b 1)) (ω.2 1).1 then (1:ℝ) else 0)=
      let σ := privatePermutation K.E (insert i (rivalSet i kind 3)) (presentList ω i b 1)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 3))
      let H0 := post0 K i kind true
      let H1 := post1 K i kind true
      if Sum.inr (σ.symm (focalIndex K i kind true))∈K.oneSampler (commonSize i kind) H0 H1
        (publicParameter K (commonSize i kind) H0 H1 Q low
          (commonRow K.E i kind (fun r => ω.1 (i.succAbove r))) u,
          PrivatePartialSorting.reindexRow σ (focalRow K i kind true b
            (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
              privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))) (ω.2 1).1
        then 1 else 0 := by
    subst A
    subst Z
    subst O
    erw [parameter_eq K i kind Q μL hQ ω hr hk b 1 _ _ low u hs,
      private_focal_reindex K.E i kind ω hr hk b 1,
      private_focal_rank K.E i kind ω b 1]
    rfl
  simpa only [privateOneAccept,decide_eq_true_eq] using! transport
    (ids K.E 1 (presentList ω i b 1)) (ids K.E 3 (presentList ω i b 1)) (ids K.E 2 (presentList ω i b 1))
    (partial_present_ids K i b ω 1) hi.2.1 hi.2.2.2 hi.2.2.1

section Noise
variable {Up eps : ℝ} (heps : 0< eps) (hRp : K.E.Rp=Up*(1+eps))
  (hgap : (1-K.ξ)*K.E.U< K.E.R)

include hQ hr hk hgap in
theorem private_value_ae (side low : Bool) (u : unitInterval)
    (hs : ∀ b : Icc K.E.R K.E.Rp,∀ j : Fin 2,
      seedOnList μL (K.E.roleList 0 (presentList ω i b j))=
        if low then some u else none)
    (v : ℝ) (b : Icc K.E.R Up) :
    ∀ᵐ z : unitInterval ∂volume,
      (v-Hybrid.activeNoisyRealBid eps b z)*
        (if privateAccept K i side (noisyPrice K heps.le hRp b z) ω then 1 else 0)=
      noisyValue K (commonSize i kind) (post0 K i kind side) (post1 K i kind side)
        heps.le hRp Q side low (focalIndex K i kind side) v b
        (commonRow K.E i kind (fun r => ω.1 (i.succAbove r)))
        (focalRow K i kind side (floorPrice K)
          (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
            privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))
        z u (privateSeed side ω) := by
  rcases K with ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  let K : Data (N+1) c := ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  rcases E with ⟨d,R,Rp,U,H,hd,hdR,hRRp,hRp1,hU,hUH⟩
  change Rp=Up*(1+eps) at hRp
  cases hRp
  let rows : Rows K i kind :=
    (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
      privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r)))
  let common := commonRow K.E i kind (fun r => ω.1 (i.succAbove r))
  cases side
  · let p := publicParameter K (commonSize i kind) (post0 K i kind false)
      (post1 K i kind false) Q low common u
    let σ : unitInterval → Equiv.Perm (Fin (insert i (rivalSet i kind 2)).card) := fun z =>
      privatePermutation K.E (insert i (rivalSet i kind 2))
        (presentList ω i (noisyPrice K heps.le rfl b z) 0)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 2))
    have hz := zero_permutation_ae K (commonSize i kind)
      (post0 K i kind false) (post1 K i kind false) heps rfl p
      (focalRow K i kind false (floorPrice K) rows) (focalIndex K i kind false) b σ
      (fun _ => Equiv.refl _) hgap
    filter_upwards [hz] with z hz
    simp only [privateAccept,Bool.false_eq_true,ite_false]
    rw [zero_reindexed K i kind Q μL hQ ω hr hk _ low u (hs _ 0)]
    dsimp only
    have hrow := focalRow_update K i kind false (noisyPrice K heps.le rfl b z) rows
    rw [←hrow]
    have he := hz (ω.2 0).1
    simpa only [NativePartialExperiment.noisyValue,NativePartialExperiment.value,
      NativePartialExperiment.inclusion,AtypicalPartialNoisy.noisyRow,noisyPrice,
      PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply,sampler_false,
      common,p,σ,rows,privateSeed,ite_false] using! congrArg (fun x =>
        (v-Hybrid.activeNoisyRealBid eps b z)*x) he
  · let p := publicParameter K (commonSize i kind) (post0 K i kind true)
      (post1 K i kind true) Q low common u
    let σ : unitInterval → Equiv.Perm (Fin (insert i (rivalSet i kind 3)).card) := fun z =>
      privatePermutation K.E (insert i (rivalSet i kind 3))
        (presentList ω i (noisyPrice K heps.le rfl b z) 1)
        (focalFirst _ i (focal_not_mem_rivalSet i kind 3))
    have hz := one_permutation_ae K (commonSize i kind)
      (post0 K i kind true) (post1 K i kind true) heps rfl p
      (focalRow K i kind true (floorPrice K) rows) (focalIndex K i kind true) b σ
      (fun _ => Equiv.refl _) hgap
    filter_upwards [hz] with z hz
    simp only [privateAccept,ite_true]
    rw [one_reindexed K i kind Q μL hQ ω hr hk _ low u (hs _ 1)]
    dsimp only
    have hrow := focalRow_update K i kind true (noisyPrice K heps.le rfl b z) rows
    rw [←hrow]
    have he := hz (ω.2 1).1
    simpa only [NativePartialExperiment.noisyValue,NativePartialExperiment.value,
      NativePartialExperiment.inclusion,AtypicalPartialNoisy.noisyRow,noisyPrice,
      PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply,sampler_true,
      common,p,σ,rows,privateSeed,ite_true] using! congrArg (fun x =>
        (v-Hybrid.activeNoisyRealBid eps b z)*x) he

end Noise
end FCAppendix.Affine.Tail04.NativePartialTerminal
