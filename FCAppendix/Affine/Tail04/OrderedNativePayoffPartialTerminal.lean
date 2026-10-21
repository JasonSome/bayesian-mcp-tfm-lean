import FCAppendix.Affine.Tail04.OrderedNativePayoffPartialExperiment
import FCAppendix.Affine.Tail04.NativePartialTerminal

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialTerminal
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeMenuReports NativeCountCoordinates NativeFocalCoordinates
open NativeFiberEnumerations NativeActiveFiberCoordinates NativePartialFiberCoordinates
open NativePartialExperiment NativePartialTerminal LocalCoordinates SortedCoordinates
open EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy OriginalPopulation OriginalValues
open Hybrid SortedAllNoise PartialNativeCoordinates PrivateRowSorting

variable {N c : ℕ} (K : NativeLocalPolicy.Data (N+1) c)
  (i : Fin (N+1)) (kind : Fin N→Fin 4)

def physical (side : Bool) : Fin 2 := if side then 1 else 0

def ownTotal (side : Bool) : Fin (N+2) :=
  ownH (post0 K i kind side) (post1 K i kind side) side

def otherTotal (side : Bool) : Fin (N+2) :=
  ownH (post0 K i kind side) (post1 K i kind side) (!side)

def privateAccept (side : Bool) (b : Icc K.E.R K.E.Rp)
    (ω : Background (N+1) 2 Seed) : Bool :=
  decide (i∈(OrderedNativePolicy.policy K (physical side)
    (presentList ω i b (physical side)) (ω.2 (physical side))).val)

attribute [local irreducible] OrderedNativePolicy.policy

lemma measurable_privateAccept (side : Bool) :
    Measurable (Function.uncurry (privateAccept K i side)) := by
  have hp : Measurable (fun x : Icc K.E.R K.E.Rp × Background (N+1) 2 Seed =>
      (OrderedNativePolicy.policy K (physical side)
        (presentList x.2 i x.1 (physical side)) (x.2.2 (physical side))).val) :=
    (OrderedNativePolicy.policy_measurable K (physical side)).comp
    (((NativePartialTerminal.measurable_presentList_joint (i:=i) (physical side)).comp
      (measurable_fst.subtype_val.prodMk measurable_snd)).prodMk
      ((measurable_pi_apply (physical side)).comp measurable_snd.snd))
  exact (measurable_of_countable (fun S : Finset (Fin (N+1)) => decide (i∈S))).comp hp

variable (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hQ : ∀ A,K.publicChoice A=PublicScenario.localChoice K.E Q μL A)
  (ω : Background (N+1) 2 Seed)
  (hr : ∀r,NativeMenuReports.MenuAction K.E (ω.1 (i.succAbove r)).1.2)
  (hk : PartialNativeCoordinates.rivalKinds K.E i ω=kind)

def focalPermutation (side : Bool) (b : Icc K.E.R K.E.Rp) :
    Equiv.Perm (Fin (ownTotal K i kind side).val) := by
  cases side
  · exact privatePermutation K.E (insert i (rivalSet i kind 2)) (presentList ω i b 0)
      (focalFirst _ i (focal_not_mem_rivalSet i kind 2))
  · exact privatePermutation K.E (insert i (rivalSet i kind 3)) (presentList ω i b 1)
      (focalFirst _ i (focal_not_mem_rivalSet i kind 3))

include hr hk in
lemma role_eq (side : Bool) (b : Icc K.E.R K.E.Rp) :
    OrderedNativePolicy.role K.E (physical side) (presentList ω i b (physical side))=
      if OrderedHigherRoles.first (physical side)
        (ownTotal K i kind side).val (otherTotal K i kind side).val then 0 else 1 := by
  have hi := PartialNativeCoordinates.partial_ids K.E i ω hr b (physical side)
  rw [hk] at hi
  unfold OrderedNativePolicy.role
  rw [K.E.otherPrivateCount_eq_missing,←ids_card,hi.2.2.1,hi.2.2.2]
  cases side <;> rfl

include hQ hr hk in

theorem reindexed_inclusion (side : Bool) (b : Icc K.E.R K.E.Rp) (low : Bool)
    (u : unitInterval)
    (hs : seedOnList μL (K.E.roleList 0 (presentList ω i b (physical side)))=
      if low then some u else none) :
    (if privateAccept K i side b ω then (1:ℝ) else 0)=
      let σ := focalPermutation K i kind ω side b
      OrderedNativePayoffPartialExperiment.inclusion K (commonSize i kind)
        (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q low
        (σ.symm (focalIndex K i kind side))
        (commonRow K.E i kind (fun r => ω.1 (i.succAbove r)))
        (PrivatePartialSorting.reindexRow σ (focalRow K i kind side b
          (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
            privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r)))))
        u (privateSeed side ω) := by
  have hi := PartialNativeCoordinates.partial_ids K.E i ω hr b (physical side)
  rw [hk] at hi
  have hm := PartialNativeCoordinates.partial_on_menu K.E i ω hr K rfl b (physical side)
  have hf := NativeMenuReports.partial_present_ids K i b ω (physical side)
  have transport (A Z O : Finset (Fin (N+1))) (him : i∈Z)
      (hA : A=rivalSet i kind 1)
      (hZ : Z=insert i (rivalSet i kind (NativeContinuation.upperTag (physical side))))
      (hO : O=rivalSet i kind (NativeContinuation.upperTag (otherProposer (physical side)))) :
      (if (if OrderedHigherRoles.first (physical side)
          (ownTotal K i kind side).val (otherTotal K i kind side).val then
        decide (Sum.inr (rankFin Z (privateKey K.E (presentList ω i b (physical side))) ⟨i,him⟩)∈
          K.zeroSampler A.card (K.finiteCount Z) (K.finiteCount O)
            (K.parameter A (K.finiteCount Z) (K.finiteCount O) (presentList ω i b (physical side)),
              privateRow K.E Z (presentList ω i b (physical side))) (ω.2 (physical side)).1)
        else decide (Sum.inr (rankFin Z (privateKey K.E (presentList ω i b (physical side))) ⟨i,him⟩)∈
          K.oneSampler A.card (K.finiteCount O) (K.finiteCount Z)
            (K.parameter A (K.finiteCount O) (K.finiteCount Z) (presentList ω i b (physical side)),
              privateRow K.E Z (presentList ω i b (physical side))) (ω.2 (physical side)).1))
        then (1:ℝ) else 0)=
      let σ := focalPermutation K i kind ω side b
      OrderedNativePayoffPartialExperiment.inclusion K (commonSize i kind)
        (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q low
        (σ.symm (focalIndex K i kind side))
        (commonRow K.E i kind (fun r => ω.1 (i.succAbove r)))
        (PrivatePartialSorting.reindexRow σ (focalRow K i kind side b
          (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
            privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r)))))
        u (privateSeed side ω) := by
    subst A
    subst Z
    subst O
    by_cases h : OrderedHigherRoles.first (physical side)
      (ownTotal K i kind side).val (otherTotal K i kind side).val
    all_goals simp only [h,ite_true,ite_false,decide_eq_true_eq,
      OrderedNativePayoffPartialExperiment.inclusion,NativePartialExperiment.inclusion,
      sampler_false,sampler_true]
    all_goals cases side <;>
      erw [NativePartialTerminal.parameter_eq K i kind Q μL hQ ω hr hk _ _ _ _ low u hs,
        private_focal_reindex K.E i kind ω hr hk b _,private_focal_rank K.E i kind ω b _] <;> rfl
  rw [privateAccept,←OrderedNativePrivateCount.privateDecision_eq K (physical side) _ hm i
    (Or.inl hf) (ω.2 (physical side))]
  unfold OrderedNativePrivateCount.privateDecision
  simp only [dif_pos hf,role_eq K i kind ω hr hk side b]
  by_cases h : OrderedHigherRoles.first (physical side)
    (ownTotal K i kind side).val (otherTotal K i kind side).val
  all_goals simpa only [h,ite_true,ite_false,one_ne_zero,↓reduceIte] using! (transport
      (ids K.E 1 (presentList ω i b (physical side)))
      (ids K.E 2 (presentList ω i b (physical side)))
      (ids K.E 3 (presentList ω i b (physical side))) hf hi.2.1 hi.2.2.1 hi.2.2.2)

section Noise
variable {Up eps : ℝ} (heps : 0<eps) (hRp : K.E.Rp=Up*(1+eps))
  (hgap : (1-K.ξ)*K.E.U<K.E.R)

include hQ hr hk hgap in

theorem private_value_ae (side low : Bool) (u : unitInterval)
    (hs : ∀ b : Icc K.E.R K.E.Rp,∀ j : Fin 2,
      seedOnList μL (K.E.roleList 0 (presentList ω i b j))=
        if low then some u else none)
    (v : ℝ) (b : Icc K.E.R Up) :
    ∀ᵐ z : unitInterval ∂volume,
      (v-Hybrid.activeNoisyRealBid eps b z)*
        (if privateAccept K i side (noisyPrice K heps.le hRp b z) ω then 1 else 0)=
      OrderedNativePayoffPartialExperiment.noisyValue K (commonSize i kind)
        (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q heps.le hRp
        low (focalIndex K i kind side) v b
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
  change ∀ᵐ z : unitInterval ∂volume,
      (v-Hybrid.activeNoisyRealBid eps b z)*
        (if privateAccept K i side (noisyPrice K heps.le rfl b z) ω then 1 else 0)=
      OrderedNativePayoffPartialExperiment.noisyValue K (commonSize i kind)
        (ownTotal K i kind side) (otherTotal K i kind side) (physical side) Q heps.le rfl
        low (focalIndex K i kind side) v b
        (commonRow K.E i kind (fun r => ω.1 (i.succAbove r)))
        (focalRow K i kind side (floorPrice K)
          (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
            privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r))))
        z u (privateSeed side ω)
  let rows : Rows K i kind :=
    (privateRowRaw K.E i kind 2 (fun r => ω.1 (i.succAbove r)),
      privateRowRaw K.E i kind 3 (fun r => ω.1 (i.succAbove r)))
  let common := commonRow K.E i kind (fun r => ω.1 (i.succAbove r))
  let own := ownTotal K i kind side
  let other := otherTotal K i kind side
  let σ : unitInterval → Equiv.Perm (Fin own.val) := fun z =>
    focalPermutation K i kind ω side (noisyPrice K heps.le rfl b z)
  by_cases h : OrderedHigherRoles.first (physical side) own.val other.val
  · let p := publicParameter K (commonSize i kind) own other Q low common u
    have hz := zero_permutation_ae K (commonSize i kind) own other heps rfl p
      (focalRow K i kind side (floorPrice K) rows) (focalIndex K i kind side) b σ
      (fun _ => Equiv.refl _) hgap
    filter_upwards [hz] with z hz
    rw [reindexed_inclusion K i kind Q μL hQ ω hr hk side _ low u (hs _ (physical side))]
    have hrow := focalRow_update K i kind side (noisyPrice K heps.le rfl b z) rows
    rw [←hrow]
    have he := hz (privateSeed side ω)
    simpa only [OrderedNativePayoffPartialExperiment.noisyValue,
      OrderedNativePayoffPartialExperiment.value,OrderedNativePayoffPartialExperiment.inclusion,
      h,ite_true,NativePartialExperiment.inclusion,AtypicalPartialNoisy.noisyRow,noisyPrice,
      PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply,sampler_false,
      common,p,σ,rows,own,other] using! congrArg (fun x =>
        (v-Hybrid.activeNoisyRealBid eps b z)*x) he
  · let p := publicParameter K (commonSize i kind) other own Q low common u
    have hz := one_permutation_ae K (commonSize i kind) other own heps rfl p
      (focalRow K i kind side (floorPrice K) rows) (focalIndex K i kind side) b σ
      (fun _ => Equiv.refl _) hgap
    filter_upwards [hz] with z hz
    rw [reindexed_inclusion K i kind Q μL hQ ω hr hk side _ low u (hs _ (physical side))]
    have hrow := focalRow_update K i kind side (noisyPrice K heps.le rfl b z) rows
    rw [←hrow]
    have he := hz (privateSeed side ω)
    simpa only [OrderedNativePayoffPartialExperiment.noisyValue,
      OrderedNativePayoffPartialExperiment.value,OrderedNativePayoffPartialExperiment.inclusion,
      h,ite_false,NativePartialExperiment.inclusion,AtypicalPartialNoisy.noisyRow,noisyPrice,
      PrivatePartialSorting.reindexRow,Equiv.refl_symm,Equiv.refl_apply,sampler_true,
      common,p,σ,rows,own,other] using! congrArg (fun x =>
        (v-Hybrid.activeNoisyRealBid eps b z)*x) he
end Noise
end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialTerminal
