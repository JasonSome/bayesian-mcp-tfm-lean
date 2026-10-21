import FCAppendix.Affine.Tail04.NativeLowSelector
import FCAppendix.Affine.Hybrid.CollapsedRowPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeExactLow
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open FCAppendix.Affine.Hybrid FCAppendix.Affine.LowBody
open NativeContinuation
open Existence.PayOnceBounded (listBids)

variable {m : ℕ}

def seedAveragePayoff (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (w : ℝ) : ℝ :=
  Direct.seedAveragePayoff ξ hξ hξ1 X.1 (residual c 0 X) (residual c 1 X) i w

theorem seedAveragePayoff_eq_reference (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (X : ClassifiedContext m) (hX : NonnegativeList X.1) (i : Fin m) (w : ℝ)
    (hgeneric : ∀ A B,
      (receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).Feasible A →
      (receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).Feasible B →
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) A.1 A.2 =
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) B.1 B.2 →
      focalCopy A i=focalCopy B i) :
    seedAveragePayoff ξ hξ hξ1 c X i w =
      NativeContinuation.seedAveragePayoff ξ hξ hξ1 c X i w := by
  have hb : listBids X.1=ResidualPotential.bid X.1 :=
    FCAppendix.AppendixRepair.GeneralLow.ExactLow.listBids_eq_residualBid X.1 hX
  have he : listBids X.1=(fun k=>entryBid (X.1 k)) := by
    funext k
    cases h : X.1 k <;> simp [listBids,entryBid,h]
  by_cases hcap : residual c 0 X=residual c 1 X
  · rw [NativeContinuation.seedAveragePayoff_equal ξ hξ hξ1 c X i w hcap]
    unfold seedAveragePayoff
    rw [hcap,FCAppendix.AppendixRepair.GeneralLow.ExactLow.seedAveragePayoff_equal]
    exact congrArg (fun r=>equalPayoff ξ r i w (listBids X.1)) hcap.symm
  · rw [NativeContinuation.seedAveragePayoff_pure ξ hξ hξ1 c X i w hcap]
    unfold seedAveragePayoff
    rw [FCAppendix.AppendixRepair.GeneralLow.ExactLow.seedAveragePayoff_pure ξ hξ hξ1
      X.1 (residual c 0 X) (residual c 1 X) i w hcap]
    let A := FCAppendix.AppendixRepair.GeneralLow.ExactLow.purePair (1-ξ) X.1
      (residual c 0 X) (residual c 1 X)
    let B := NativeContinuation.purePair ξ c X
    have hA := FCAppendix.AppendixRepair.GeneralLow.ExactLow.purePair_feasible
      (1-ξ) X.1 (residual c 0 X) (residual c 1 X)
    have hAf : (receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).Feasible A :=
      (receivedTemplate_feasible _ _ _ _).mpr hA
    have hB := purePair_feasible_max ξ hξ1 c X
    have hle := FCAppendix.AppendixRepair.GeneralLow.ExactLow.purePair_max (1-ξ) X.1
      (residual c 0 X) (residual c 1 X) B (by
        change (receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).Feasible B
        exact hB.1)
    rw [hb] at hle
    have hc := hgeneric A B hAf hB.1 (le_antisymm (hB.2 A hAf) hle)
    rw [he]
    exact purePayoff_eq_of_focalCopy_eq (1-ξ) w _ A B i hc

end FCAppendix.Affine.Tail04.NativeExactLow

namespace FCAppendix.Affine.Tail04.NativeLowRowPayoff
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid LowBody NativeContinuation NativeLowCoordinates
open scoped BigOperators

variable {N : ℕ}

lemma rowLowList_nonnegative (b : ℝ) (hb : 0≤ b) (ω : Fin N→ RowRival)
    (hω : ∀ r,(ω r).1=0→0≤(ω r).2) : NonnegativeList (rowLowList b ω) := by
  intro l
  refine Fin.cases ?_ (fun r=>?_) l
  · exact hb
  · by_cases hr : (ω r).1=0
    · simpa [rowLowList,hr,entryBid] using hω r hr
    · simp [rowLowList,hr,entryBid]

lemma rowLowList_bid (b : ℝ) (hb : 0≤ b) (ω : Fin N→ RowRival)
    (hω : ∀ r,(ω r).1=0→0≤(ω r).2) :
    ResidualPotential.bid (rowLowList b ω)=rowBids b ω := by
  funext l
  refine Fin.cases ?_ (fun r=>?_) l
  · exact max_eq_left hb
  · by_cases hr : (ω r).1=0
    · simp [rowLowList,rowBids,hr,ResidualPotential.bid,entryBid,max_eq_left (hω r hr)]
    · simp [rowLowList,rowBids,hr,ResidualPotential.bid,entryBid]

lemma row_template_card (c : ℕ) (b : ℝ) (ω : Fin N→ RowRival) :
    (patternTemplate c (fun r=>(ω r).1)).support.card=1+classCount 0 ω := by
  rw [←received_row_support b ω 0 0 c]
  exact rowLowList_card b ω

lemma actual_template_relabel (c : ℕ) (i : Fin (N+1)) (b : ℝ) (ω : Fin N→ RowRival) :
    let X:=rowContextAt i b ω
    ((receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).clipped).relabel
      (focalIndex i).symm=patternTemplate c (fun r=>(ω r).1) := by
  dsimp only
  let e:=focalIndex i
  let X:=rowContextAt i b ω
  let T:=(receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).clipped
  let S:=patternTemplate c (fun r=>(ω r).1)
  have hs : T.support=S.support.map e.toEmbedding := by
    have hbase:=received_row_support b ω 0 0 c
    change T.support=(patternTemplate c (fun r=>(ω r).1)).support.map e.toEmbedding
    rw [←hbase]
    ext l
    simp [T,PureTemplate.clipped,receivedTemplate,X,rowContextAt,reindexContext,rowContext,e]
  have hcard : T.support.card=1+classCount 0 ω := by
    rw [hs,Finset.card_map]
    exact row_template_card c b ω
  have hext (A B : PureTemplate (Fin (N+1)))
      (hs : A.support=B.support) (h0 : A.residual₀=B.residual₀)
      (h1 : A.residual₁=B.residual₁) : A=B := by
    cases A
    cases B
    simp_all
  apply hext
  · change T.support.map e.symm.toEmbedding=S.support
    rw [hs,Finset.map_map]
    have he : e.toEmbedding.trans e.symm.toEmbedding=Function.Embedding.refl _ := by
      ext l
      exact congrArg Fin.val (e.symm_apply_apply l)
    rw [he,Finset.map_refl]
  · change min T.support.card (c-(classCount 1 ω+classCount 2 ω))=
      rowResidual c 0 (patternRow (fun r=>(ω r).1))
    rw [hcard,rowResidual_tags]
    simp only [rowResidual,Nat.sub_add_eq]
    rfl
  · change min T.support.card (c-(classCount 1 ω+classCount 3 ω))=
      rowResidual c 1 (patternRow (fun r=>(ω r).1))
    rw [hcard,rowResidual_tags]
    simp [rowResidual,Nat.sub_add_eq]

theorem actual_context_positive_payoff (ξ : ℝ) (hξ : 0< ξ) (hξ1 : ξ<1) (c : ℕ)
    (d : ℝ) (hd : 0≤ d) (i : Fin (N+1)) (b : ℝ) (hb : 0< b) (hbd : b≤ d)
    (ω : Fin N→ RowRival) (hω : ∀ r,(ω r).1=0→(ω r).2∈Icc (0:ℝ) d)
    (w : ℝ) (hgeneric : rowCopyGeneric (1-ξ) b ω) :
    NativeExactLow.seedAveragePayoff ξ hξ hξ1 c (rowContextAt i b ω) i w=
      literalRowPayoff ξ c w (b,ω) := by
  let e:=focalIndex i
  let X:=rowContextAt i b ω
  let T:=(receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).clipped
  let S:=patternTemplate c (fun r=>(ω r).1)
  let B:=ResidualPotential.bid X.1
  have hnonneg := rowLowList_nonnegative b hb.le ω (fun r hr=>(hω r hr).1)
  have hX : NonnegativeList X.1 := fun l=> hnonneg (e.symm l)
  have hB : B∘e=rowBids b ω := by
    rw [←rowLowList_bid b hb.le ω (fun r hr=>(hω r hr).1)]
    funext l
    simp [B,X,rowContextAt,reindexContext,rowContext,ResidualPotential.bid,e]
  have hBi : B i=b := by
    change max (entryBid (X.1 i)) 0=b
    rw [rowContextAt_focal]
    exact max_eq_left hb.le
  have hB' : B=rowBids b ω∘e.symm := by
    funext l
    have he:=congrFun hB (e.symm l)
    simpa only [Function.comp_apply,e.apply_symm_apply] using he
  have hT : T=S.relabel e := by
    have ht:=actual_template_relabel c i b ω
    change T.relabel e.symm=S at ht
    rw [←ht]
    exact (T.relabel_symm e.symm).symm
  have hgen : ∀ A A',T.Feasible A→ T.Feasible A'→
      CompleteInformation.potential (1-ξ) B A.1 A.2=
        CompleteInformation.potential (1-ξ) B A'.1 A'.2→ focalCopy A i=focalCopy A' i := by
    intro A A' _ _ he
    have hA:=potential_relabel (1-ξ) B e.symm A
    have hA':=potential_relabel (1-ξ) B e.symm A'
    change CompleteInformation.potential (1-ξ) (B∘e) _ _=_ at hA hA'
    rw [hB] at hA hA'
    have hc:=hgeneric (relabelPair e.symm A) (relabelPair e.symm A')
      (hA.trans (he.trans hA'.symm))
    have hei : e.symm i=0 := by rw [←focalIndex_zero i];exact e.symm_apply_apply _
    have hAc:=focalCopy_relabel e.symm A i
    have hA'c:=focalCopy_relabel e.symm A' i
    rw [hei] at hAc hA'c
    exact hAc.symm.trans (hc.trans hA'c)
  have hlow : ∀ l,entryBid (X.1 l)≤ d := by
    intro l
    change entryBid (rowLowList b ω (e.symm l))≤ d
    refine Fin.cases hbd (fun r=>?_) (e.symm l)
    by_cases hr : (ω r).1=0
    · simpa [rowLowList,hr,entryBid] using (hω r hr).2
    · simpa [rowLowList,hr,entryBid] using hd
  have he : eraseActiveList (∅ : Finset (Fin (N+1))) X.1=X.1 := by
    funext l
    simp [eraseActiveList]
  rw [NativeExactLow.seedAveragePayoff_eq_reference ξ hξ hξ1 c X hX i w]
  swap
  · intro A A' hA hA' hpot
    exact hgen A A' (((receivedTemplate X.1 (residual c 0 X)
      (residual c 1 X)).clipped_feasible A).mpr hA)
      (((receivedTemplate X.1 (residual c 0 X) (residual c 1 X)).clipped_feasible A').mpr hA') hpot
  have hout:=context_low_payoff ξ hξ hξ1 c X hX d hd ∅
    (by simp) (fun l _=> hlow l) i (by simp)
    (by rw [rowContextAt_focal];exact hb) w
  simp only [he,Finset.card_empty,Nat.sub_zero] at hout
  rw [show seedAveragePayoff ξ hξ hξ1 c X i w=T.userPayoff ξ w B i from hout hgen]
  rw [hT,hB',←focalIndex_zero i]
  exact S.userPayoff_relabel e hξ hξ1 w (rowBids b ω) 0
    (fun A A' _ _ he=> hgeneric A A' he)

end FCAppendix.Affine.Tail04.NativeLowRowPayoff
