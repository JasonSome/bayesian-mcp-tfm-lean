import FCAppendix.Affine.Hybrid.NativeResidualPayoff
import FCAppendix.Affine.Hybrid.EqualActiveResidual

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.LowBody
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PureTemplate

def clipped (T : PureTemplate ι) : PureTemplate ι where
  support:=T.support
  residual₀:=min T.support.card T.residual₀
  residual₁:=min T.support.card T.residual₁

omit [Fintype ι] [DecidableEq ι] in
lemma clipped_feasible (T : PureTemplate ι) (P : Finset ι×Finset ι) :
    T.clipped.Feasible P↔T.Feasible P:=by
  simp only [Feasible,clipped,le_min_iff]
  constructor
  · rintro ⟨⟨_,h0⟩,hs,⟨_,h1⟩,ht⟩
    exact ⟨h0,hs,h1,ht⟩
  · rintro ⟨h0,hs,h1,ht⟩
    exact ⟨⟨Finset.card_le_card hs,h0⟩,hs,⟨Finset.card_le_card ht,h1⟩,ht⟩

lemma maximizer_contains_left (T : PureTemplate ι) {κ : ℝ} (hκ:0<κ)
    (b : ι→ℝ) (i : ι) (hi:i∈T.support) (hbi:0<b i)
    (hc:T.support.card ≤ T.residual₀) (P : Finset ι×Finset ι) (hP:T.Feasible P)
    (hm:∀Q,T.Feasible Q → CompleteInformation.potential κ b Q.1 Q.2 ≤
      CompleteInformation.potential κ b P.1 P.2) : i∈P.1:=by
  by_contra hn
  have hsub:insert i P.1⊆T.support:=Finset.insert_subset hi hP.2.1
  have hh:=hm (insert i P.1,P.2) ⟨(Finset.card_le_card hsub).trans hc,hsub,hP.2.2⟩
  rw [CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
  unfold CompleteInformation.revenue at hh
  rw [Finset.sum_insert hn] at hh
  have hp:0<(if i∈P.2 then κ*b i else b i):=by
    split <;> first | exact mul_pos hκ hbi | exact hbi
  linarith

lemma maximizer_contains_right (T : PureTemplate ι) {κ : ℝ} (hκ:0<κ)
    (b : ι→ℝ) (i : ι) (hi:i∈T.support) (hbi:0<b i)
    (hc:T.support.card ≤ T.residual₁) (P : Finset ι×Finset ι) (hP:T.Feasible P)
    (hm:∀Q,T.Feasible Q → CompleteInformation.potential κ b Q.1 Q.2 ≤
      CompleteInformation.potential κ b P.1 P.2) : i∈P.2:=by
  by_contra hn
  have hsub:insert i P.2⊆T.support:=Finset.insert_subset hi hP.2.2.2
  have hh:=hm (P.1,insert i P.2) ⟨hP.1,hP.2.1,(Finset.card_le_card hsub).trans hc,hsub⟩
  rw [CompleteInformation.potential_comm κ b P.1 (insert i P.2),
    CompleteInformation.potential_comm κ b P.1 P.2,
    CompleteInformation.potential_eq_revenue_add,CompleteInformation.potential_eq_revenue_add] at hh
  unfold CompleteInformation.revenue at hh
  rw [Finset.sum_insert hn] at hh
  have hp:0<(if i∈P.1 then κ*b i else b i):=by
    split <;> first | exact mul_pos hκ hbi | exact hbi
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma clipped_equal_of_unequal (T : PureTemplate ι)
    (hne:T.residual₀≠T.residual₁) (he:T.clipped.residual₀=T.clipped.residual₁) :
    T.support.card ≤ T.residual₀ ∧ T.support.card ≤ T.residual₁:=by
  change min T.support.card T.residual₀=min T.support.card T.residual₁ at he
  omega

end PureTemplate
end FCAppendix.Affine.LowBody

namespace FCAppendix.Affine.Hybrid.NativeContinuation
open LowBody EqualCapacity
open Existence.PayOnceBounded (positiveSupport mem_positiveSupport)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_clip_at_positive {ξ : ℝ} (hξ:0<ξ) (hξ1:ξ<1)
    (H : Finset ι) (r : ℕ) (b : ι→ℝ) (hmask:∀i,i∉H → b i=0)
    (i : ι) (hi:0<b i) :
    positiveMarginal ξ r b i=positiveMarginal ξ (min H.card r) b i:=by
  by_cases hr:r ≤ H.card
  · rw [min_eq_right hr]
  · have hc:H.card ≤ r:=le_of_not_ge hr
    have hsupport:(positiveSupport b).card ≤ H.card:=by
      apply Finset.card_le_card
      intro k hk
      by_contra hn
      have hpos:0<b k:=(mem_positiveSupport b k).mp hk
      rw [hmask k hn] at hpos
      exact lt_irrefl 0 hpos
    rw [min_eq_left hc,
      positiveMarginal_one_of_underloaded hξ hξ1 r b (hsupport.trans hc) i hi,
      positiveMarginal_one_of_underloaded hξ hξ1 H.card b hsupport i hi]

end FCAppendix.Affine.Hybrid.NativeContinuation
