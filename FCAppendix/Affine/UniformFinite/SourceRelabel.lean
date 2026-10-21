import FCAppendix.Affine.UniformFinite.GuardedPathRelabel
import FCAppendix.Affine.UniformFinite.NativeZeroIndex
import FCAppendix.Affine.Hybrid.EqualRelabel
import FCAppendix.Affine.Hybrid.PureRelabel

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Uniform05 SourceContinuity WeightedSampling
open scoped BigOperators

namespace SourceRelabel
variable {M : ℕ}

def row (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) : Source.CountRow M where
  lower:=r.lower.map e.toEmbedding
  upper0:=r.upper0
  upper1:=r.upper1
  partition:=by simpa only [Finset.card_map] using r.partition

@[simp] lemma lower_mem (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) (a : Fin M) :
    e a∈(row e r).lower↔a∈r.lower := by simp [row]

@[simp] lemma lower_card (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) :
    (row e r).lower.card=r.lower.card := Finset.card_map _

lemma countRowOfKind (e : Equiv.Perm (Fin M)) (k : Fin M→ Fin 3) :
    Source.countRowOfKind (k∘e.symm)=row e (Source.countRowOfKind k) := by
  apply (NativeContext.countRow_eq_iff _ _).mpr
  refine ⟨?_,?_,?_⟩
  · ext a
    simp [Source.countRowOfKind,row]
  · simp only [Source.countRowOfKind,row,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Equiv.sum_comp e.symm (fun a : Fin M=>if k a=1 then (1:ℕ) else 0)
  · simp only [Source.countRowOfKind,row,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Equiv.sum_comp e.symm (fun a : Fin M=>if k a=2 then (1:ℕ) else 0)

@[simp] lemma residual (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) (j : Fin 2) :
    Source.residual (row e r) j=Source.residual r j := by
  simp [Source.residual,Source.upperCount,row]

@[simp] lemma small (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) :
    Source.small (row e r)=Source.small r := by simp [Source.small]

@[simp] lemma imbalance (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) :
    Source.imbalance (row e r)=Source.imbalance r := by simp [Source.imbalance,Source.large]

@[simp] lemma totalResidual (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) :
    Source.totalResidual (row e r)=Source.totalResidual r := by simp [Source.totalResidual]

@[simp] lemma lowerBids (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.lowerBids (row e r) (b∘e.symm)=Source.lowerBids r b∘e.symm := by
  funext a
  simp [Source.lowerBids,row]

@[simp] lemma template (e : Equiv.Perm (Fin M)) (r : Source.CountRow M) :
    Source.lowerTemplate (row e r)=(Source.lowerTemplate r).relabel e := by
  simp only [Source.lowerTemplate,LowBody.PureTemplate.relabel,residual]
  rfl

@[simp] lemma weights (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.sourceWeights i G (row e r) (b∘e.symm)=
      GuardedPathRelabel.relabelWeights e (Source.sourceWeights i G r b) := by
  apply Subtype.ext
  funext a
  simp [Source.sourceWeights,row,GuardedPathRelabel.relabelWeights]

@[simp] lemma lowDemand (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.lowDemand i G (row e r) (b∘e.symm)=Source.lowDemand i G r b := by
  simpa only [Source.lowDemand,lowerBids,Function.comp_apply] using
    Equiv.sum_comp e.symm (fun a : Fin M=> ClippedResidual.exposure (xi i) (Source.rootLo i G)
      (Source.lowerBids r b a))

@[simp] lemma highDemand (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.highDemand i G (row e r) (b∘e.symm)=Source.highDemand i G r b := by
  simpa only [Source.highDemand,lowerBids,Function.comp_apply] using
    Equiv.sum_comp e.symm (fun a : Fin M=> ClippedResidual.exposure (xi i) (Source.rootHi i G)
      (Source.lowerBids r b a))

@[simp] lemma rejectionSum (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.rejectionSum i G (row e r) (b∘e.symm)=Source.rejectionSum i G r b := by
  simpa only [Source.rejectionSum,lowerBids,Function.comp_apply] using
    Equiv.sum_comp e.symm (fun a : Fin M=> rejectionExposure (rejectionScale i) G.rejectionRoot
      (Source.lowerBids r b a))

@[simp] lemma seedCount (e : Equiv.Perm (Fin M)) (i : Row)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.seedCount i (row e r) (b∘e.symm)=Source.seedCount i r b := by
  have he : (row e r).lower.filter (fun a=>(b∘e.symm) a≤ t i/2)=
      (r.lower.filter (fun a=> b a≤ t i/2)).map e.toEmbedding := by
    ext a
    simp [row]
  simp only [Source.seedCount,he,Finset.card_map]

@[simp] lemma slacks (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.sourceSlacks i G (row e r) (b∘e.symm)=Source.sourceSlacks i G r b := by
  simp only [Source.sourceSlacks,lowDemand,highDemand,small,imbalance,weights,
    GuardedPathRelabel.totalWeight_relabel,rejectionSum,totalResidual,lower_card]
  rfl

@[simp] lemma rawAlpha (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.rawAlpha i G (row e r) (b∘e.symm)=Source.rawAlpha i G r b := by
  simp only [Source.rawAlpha,slacks]

@[simp] lemma alpha (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ℝ) :
    Source.guardAlpha i G (row e r) (b∘e.symm)=Source.guardAlpha i G r b := by
  simp only [Source.guardAlpha,seedCount,rawAlpha]

lemma pathPayoff (e : Equiv.Perm (Fin M)) (ξ lo hi η v : ℝ) (b : Fin M→ℝ)
    (d Δ : ℕ) (a : Fin M) (p : Path (Fin M) Δ) :
    Literal.pathPayoff ξ lo hi η v (b∘e.symm) d Δ (e a)
      (GuardedPathRelabel.relabelPath e Δ p)=Literal.pathPayoff ξ lo hi η v b d Δ a p := by
  have hE : finalSet Δ ∅ (GuardedPathRelabel.relabelPath e Δ p)=
      (finalSet Δ ∅ p).map e.toEmbedding := by
    simpa using GuardedPathRelabel.finalSet_relabel e Δ ∅ p
  simp [Literal.pathPayoff,hE,Literal.root_relabel]

variable [NeZero M]

omit [NeZero M] in
lemma equalPayoff (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ Bid i) (v : ℝ) (a : Fin M) :
    (equalLaw i (row e r) (fun j=>(b (e.symm j):ℝ))).expect
      (pairPayoff (eta i) v (b a) (e a))=
      (equalLaw i r (fun j=>(b j:ℝ))).expect (pairPayoff (eta i) v (b a) a) := by
  have hm : equalMarginal i (row e r) (e a) (G,b∘e.symm)=equalMarginal i r a (G,b) := by
    unfold equalMarginal
    have he : bids i (G,b∘e.symm)=bids i (G,b)∘e.symm := rfl
    rw [he,small,lowerBids,EqualCapacity.positiveMarginal_equiv e.symm
      (xi_range i).1 (xi_range i).2]
    simp only [Equiv.symm_apply_apply]
  have hL:=equalPayoff_eq i (row e r) (e a) (v,G,b∘e.symm)
  have hR:=equalPayoff_eq i r a (v,G,b)
  simp only [SourceContinuity.bids,Function.comp_apply,Equiv.symm_apply_apply,hm] at hL hR
  exact hL.trans hR.symm

lemma canonicalPayoff (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ Bid i) (v : ℝ) (a : Fin M) (ha : a∈r.lower)
    (hα : 0< Source.rawAlpha i G r (bids i (G,b))) :
    (canonicalLaw i G (row e r) (fun j=>(b (e.symm j):ℝ))).expect
      (pairPayoff (eta i) v (b a) (e a))=
      (canonicalLaw i G r (fun j=>(b j:ℝ))).expect (pairPayoff (eta i) v (b a) a) := by
  let x : Guarded i r:=⟨(G,b),hα⟩
  let y : Guarded i (row e r):=⟨(G,b∘e.symm),by
    change 0< Source.rawAlpha i G (row e r) (bids i (G,b)∘e.symm)
    rwa [rawAlpha]⟩
  have hL:=canonical_expected_eq_path i (row e r) (e a) ((lower_mem e r a).mpr ha) v y
  have hR:=canonical_expected_eq_path i r a ha v x
  have hW : (Source.imbalance r:ℝ)< totalWeight (Source.sourceWeights i G r (bids i (G,b))) := by
    have h:=guarded_data i r x
    linarith [h.1.2.2.2.1,h.2.2]
  have hb : bids i (G,b∘e.symm)=bids i (G,b)∘e.symm := rfl
  simp only [y,hb,small,lowerBids,weights,
    Function.comp_apply,Equiv.symm_apply_apply] at hL
  simp only [x] at hR
  have hΔ:=congrArg (fun n : ℕ=>
    (pathLaw (GuardedPathRelabel.relabelWeights e
      (Source.sourceWeights i G r (bids i (G,b)))) n ∅).expect
      (Literal.pathPayoff (xi i) (Source.rootLo i G) (Source.rootHi i G)
        (eta i) v (Source.lowerBids r (bids i (G,b))∘e.symm)
        (Source.small r) n (e a))) (imbalance e r)
  have hL':=hL.trans hΔ
  change (canonicalLaw i G (row e r) (fun j=>(b (e.symm j):ℝ))).expect
    (pairPayoff (eta i) v (b a) (e a))=
    (pathLaw (GuardedPathRelabel.relabelWeights e
      (Source.sourceWeights i G r (bids i (G,b))))
      (Source.imbalance r) ∅).expect
      (Literal.pathPayoff (xi i) (Source.rootLo i G) (Source.rootHi i G)
        (eta i) v (Source.lowerBids r (bids i (G,b))∘e.symm)
        (Source.small r) (Source.imbalance r) (e a)) at hL'
  change (canonicalLaw i G r (fun j=>(b j:ℝ))).expect
    (pairPayoff (eta i) v (b a) a)=_ at hR
  rw [hL',hR,GuardedPathRelabel.guarded_empty_path_expect e _ _ hW]
  exact FiniteLaw.expect_congr _ (fun p=> pathPayoff e _ _ _ _ _ _ _ _ _ p)

omit [NeZero M] in

lemma purePayoff (e : Equiv.Perm (Fin M)) (i : Row) (r : Source.CountRow M)
    (b : Fin M→ℝ) (v : ℝ) (a : Fin M) (ha : a∈r.lower)
    (hgeneric : ∀P Q : Allocation M,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids r b) P.1 P.2=
        LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids r b) Q.1 Q.2→
      LowBody.focalCopy P a=LowBody.focalCopy Q a) :
    pairPayoff (eta i) v (b a) (e a)
      ((Source.lowerTemplate (row e r)).selection (kappa i)
        (Source.lowerBids (row e r) (b∘e.symm)))=
      pairPayoff (eta i) v (b a) a
        ((Source.lowerTemplate r).selection (kappa i) (Source.lowerBids r b)) := by
  have h:=(Source.lowerTemplate r).selection_payoff_relabel e (kappa i) v
    (Source.lowerBids r b) a (fun P Q _ _ h=> hgeneric P Q h)
  rw [← ActualAtoms.pairPayoff_eq_purePayoff,← ActualAtoms.pairPayoff_eq_purePayoff] at h
  simpa only [template,lowerBids,Function.comp_apply,Equiv.symm_apply_apply,
    Source.lowerBids_of_mem r b ha] using h

theorem rowPayoff (e : Equiv.Perm (Fin M)) (i : Row) (G : RestrictedLaw i)
    (r : Source.CountRow M) (b : Fin M→ Bid i) (v : ℝ) (a : Fin M) (ha : a∈r.lower)
    (hgeneric : ∀P Q : Allocation M,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids r (bids i (G,b))) P.1 P.2=
        LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids r (bids i (G,b))) Q.1 Q.2→
      LowBody.focalCopy P a=LowBody.focalCopy Q a) :
    UniformFinite.rowPayoff i G (row e r) v (bids i (G,b)∘e.symm) (e a)=
      UniformFinite.rowPayoff i G r v (bids i (G,b)) a := by
  by_cases he : Source.residual r 0=Source.residual r 1
  · rw [UniformFinite.rowPayoff,UniformFinite.rowPayoff,
      continuation_equal i G (row e r) _ (by simpa using he),continuation_equal i G r _ he]
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    convert! equalPayoff e i G r b v a using 1
  · have he' : Source.residual (row e r) 0≠Source.residual (row e r) 1 := by simpa using he
    rw [rowPayoff_unequal i G (row e r) _ _ _ he',rowPayoff_unequal i G r _ _ _ he,
      alpha]
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    rw [purePayoff e i r _ v a ha hgeneric]
    by_cases hα : Source.guardAlpha i G r (bids i (G,b))=0
    · simp only [hα,zero_mul]
    · have hp : 0< Source.guardAlpha i G r (bids i (G,b)) :=
        lt_of_le_of_ne (Source.guardAlpha_bounds i G r _).1 (Ne.symm hα)
      have hraw : 0< Source.rawAlpha i G r (bids i (G,b)) := by
        unfold Source.guardAlpha at hp
        split_ifs at hp
        · exact False.elim ((lt_irrefl 0) hp)
        · exact hp
      have hc : (canonicalLaw i G (row e r) (bids i (G,b)∘e.symm)).expect
          (pairPayoff (eta i) v (bids i (G,b) a) (e a))=
          (canonicalLaw i G r (bids i (G,b))).expect (pairPayoff (eta i) v (bids i (G,b) a) a) := by
        convert! canonicalPayoff e i G r b v a ha hraw using 1
      rw [hc]

end SourceRelabel
end FCAppendix.Affine.UniformFinite
