import FCAppendix.Affine.Hybrid.PrivateSeedPayoff
import FCAppendix.Affine.Hybrid.PureActiveResidualAllCounts
import FCAppendix.Affine.Hybrid.ResidualCapacityClip

set_option maxHeartbeats 1600000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody EqualCapacity
open Existence.PayOnceBounded (listBids)
open scoped BigOperators
variable {m : ℕ}

lemma erased_bid_focal (L : LocalList m) (hL:NonnegativeList L) (A : Finset (Fin m))
    (i : Fin m) (hi:i∉A) :
    ResidualPotential.bid (eraseActiveList A L) i=entryBid (L i):=by
  simp only [ResidualPotential.bid,eraseActiveList,if_neg hi]
  exact max_eq_left (hL i)

lemma erased_bid_mask (L : LocalList m) (A : Finset (Fin m)) (i : Fin m)
    (hi:i∉(receivedTemplate (eraseActiveList A L) 0 0).support) :
    ResidualPotential.bid (eraseActiveList A L) i=0:=by
  have hh:eraseActiveList A L i=none:=by
    simpa only [receivedTemplate,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hi
  simp [ResidualPotential.bid,hh,entryBid]

lemma acceptance_equal_low_all_counts (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (he:residual c 0 X=residual c 1 X) (d : ℝ) (hd:0 ≤ d) (A : Finset (Fin m))
    (hA:∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow:∀i∉A,entryBid (X.1 i) ≤ d)
    (j : Fin 2) (i : Fin m) (hi:i∉A) :
    acceptance ξ hξ hξ1 c j X i=
      positiveMarginal ξ (residual c 0 X-A.card) (ResidualPotential.bid (eraseActiveList A X.1)) i:=by
  by_cases hfit:A.card ≤ residual c 0 X
  · rw [equal_acceptance_low_residual ξ hξ hξ1 c X hX he d hd A hA hlow hfit j i hi]
    have heq:ResidualPotential.bid X.1=listBids X.1:=by
      funext k
      have hk:listBids X.1 k=entryBid (X.1 k):=by
        cases hv:X.1 k <;> simp [listBids,entryBid,hv]
      change max (entryBid (X.1 k)) 0=listBids X.1 k
      rw [hk]
      exact max_eq_left (hX k)
    rw [bid_eraseActiveList,heq]
  · have hover:residual c j X ≤ A.card:=by
      have hj:residual c j X=residual c 0 X:=by fin_cases j <;> first | rfl | exact he.symm
      rw [hj]
      omega
    have hs (s : unitInterval):i∉select ξ hξ hξ1 c j X s:=fun hh=>
      hi (low_excluded_under_active_overload ξ hξ hξ1 c X hX j s d A hA hlow hover hh)
    have hz:residual c 0 X-A.card=0:=by omega
    rw [hz,positiveMarginal_zero_capacity hξ hξ1]
    simp only [acceptance,if_neg (hs _),integral_zero]

def residualPayoff (ξ : ℝ) (T : PureTemplate (Fin m)) (i : Fin m) (w : ℝ)
    (b : Fin m→ℝ) : ℝ:=
  if T.residual₀=T.residual₁ then equalPayoff ξ T.residual₀ i w b
  else purePayoff (1-ξ) w b (T.selection (1-ξ) b) i

theorem context_low_payoff (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX:NonnegativeList X.1)
    (d : ℝ) (hd:0 ≤ d) (A : Finset (Fin m))
    (hA:∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow:∀i∉A,entryBid (X.1 i) ≤ d)
    (i : Fin m) (hi:i∉A) (hbi:0<entryBid (X.1 i)) (w : ℝ)
    (hgeneric:let low:=eraseActiveList A X.1
      let T:=(receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)).clipped
      ∀P Q,T.Feasible P → T.Feasible Q →
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) P.1 P.2=
          CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) Q.1 Q.2 →
        focalCopy P i=focalCopy Q i) :
    (∫s : Fin 2→unitInterval,purePayoff (1-ξ) w (fun k=>entryBid (X.1 k))
      (select ξ hξ hξ1 c 0 X (s 0),select ξ hξ hξ1 c 1 X (s 1)) i
      ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
    let low:=eraseActiveList A X.1
    let T:=(receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)).clipped
    residualPayoff ξ T i w (ResidualPotential.bid low):=by
  let low:=eraseActiveList A X.1
  let R:=receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)
  let T:=R.clipped
  let b:=ResidualPotential.bid low
  have hbid:b i=entryBid (X.1 i):=erased_bid_focal X.1 hX A i hi
  have hb:0<b i:=by rw [hbid];exact hbi
  have hmask:∀k,k∉R.support → b k=0:=fun k hk=>erased_bid_mask X.1 A k hk
  have his:i∈R.support:=by
    by_contra hn
    have hz:=hmask i hn
    linarith
  by_cases he:residual c 0 X=residual c 1 X
  · have heT:T.residual₀=T.residual₁:=by dsimp [T,R,PureTemplate.clipped,receivedTemplate];rw [he]
    have hm (j : Fin 2):acceptance ξ hξ hξ1 c j X i=positiveMarginal ξ T.residual₀ b i:=by
      rw [acceptance_equal_low_all_counts ξ hξ hξ1 c X hX he d hd A hA hlow j i hi]
      exact positiveMarginal_clip_at_positive hξ hξ1 R.support _ b hmask i hb
    have hf (j : Fin 2):Measurable (select ξ hξ hξ1 c j X):=
      (measurable_select ξ hξ hξ1 c j).comp (measurable_const.prodMk measurable_id)
    rw [private_pair_expected_payoff ξ w (fun k=>entryBid (X.1 k)) i _ _ (hf 0) (hf 1)]
    change w*(acceptance ξ hξ hξ1 c 0 X i+acceptance ξ hξ hξ1 c 1 X i-
      acceptance ξ hξ hξ1 c 0 X i*acceptance ξ hξ hξ1 c 1 X i)-
      entryBid (X.1 i)*(acceptance ξ hξ hξ1 c 0 X i+acceptance ξ hξ hξ1 c 1 X i-
        2*ξ*acceptance ξ hξ hξ1 c 0 X i*acceptance ξ hξ hξ1 c 1 X i)=_
    rw [hm 0,hm 1]
    change _=residualPayoff ξ T i w b
    rw [residualPayoff,if_pos heT]
    unfold equalPayoff
    rw [hbid]
    ring
  · let P:=purePair ξ c X
    let Q:ResidualPotential.Pair m:=(P.1\A,P.2\A)
    obtain ⟨hQ,hmQ⟩:=native_pure_low_maximum_all_counts ξ hξ hξ1 c X hX he d hd A hA hlow
    have hfR:R.Feasible Q:=(receivedTemplate_feasible low _ _ Q).mpr hQ
    have hfT:T.Feasible Q:=(R.clipped_feasible Q).mpr hfR
    have hmT:∀S,T.Feasible S → CompleteInformation.potential (1-ξ) b S.1 S.2 ≤
        CompleteInformation.potential (1-ξ) b Q.1 Q.2:=by
      intro S hS
      exact hmQ S ((receivedTemplate_feasible low _ _ S).mp ((R.clipped_feasible S).mp hS))
    have hcopy:focalCopy P i=focalCopy Q i:=by simp [P,Q,focalCopy,hi]
    have hseed:(∫s : Fin 2→unitInterval,purePayoff (1-ξ) w (fun k=>entryBid (X.1 k))
        (select ξ hξ hξ1 c 0 X (s 0),select ξ hξ hξ1 c 1 X (s 1)) i
        ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval)))=
        purePayoff (1-ξ) w b Q i:=by
      simp only [select,if_neg he,ite_true,if_neg (by decide : (1:Fin 2)≠0),
        integral_const,probReal_univ,smul_eq_mul,one_mul]
      simp only [purePayoff,←hcopy,hbid,P]
    rw [hseed]
    change _=residualPayoff ξ T i w b
    by_cases heT:T.residual₀=T.residual₁
    · have hedge:T.residual₀=0 ∨ T.residual₀=R.support.card:=by
        change min R.support.card (residual c 0 X-A.card)=
          min R.support.card (residual c 1 X-A.card) at heT
        change min R.support.card (residual c 0 X-A.card)=0 ∨
          min R.support.card (residual c 0 X-A.card)=R.support.card
        omega
      rw [residualPayoff,if_pos heT]
      rcases hedge with hz|hfull
      · have hz0:Q.1=∅:=Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (by simpa only [hz] using hfT.1))
        have hz1:Q.2=∅:=Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (by simpa only [←heT,hz] using hfT.2.2.1))
        have hempty:Q=(∅,∅):=Prod.ext hz0 hz1
        rw [hempty,hz]
        simp [purePayoff,focalCopy,equalPayoff,positiveMarginal_zero_capacity hξ hξ1]
      · have hc0:T.support.card ≤ T.residual₀:=by simpa only [T,PureTemplate.clipped] using hfull.ge
        have hc1:T.support.card ≤ T.residual₁:=hc0.trans heT.le
        have h0:=T.maximizer_contains_left (by linarith : 0<1-ξ) b i his hb hc0 Q hfT hmT
        have h1:=T.maximizer_contains_right (by linarith : 0<1-ξ) b i his hb hc1 Q hfT hmT
        have hsupport:(Existence.PayOnceBounded.positiveSupport b).card ≤ R.support.card:=by
          apply Finset.card_le_card
          intro k hk
          by_contra hn
          have hh:0<b k:=(Existence.PayOnceBounded.mem_positiveSupport b k).mp hk
          rw [hmask k hn] at hh
          exact lt_irrefl 0 hh
        have hp:=positiveMarginal_one_of_underloaded hξ hξ1 T.residual₀ b (hsupport.trans hfull.ge) i hb
        simp only [purePayoff,focalCopy,Finset.mem_inter,Finset.mem_union,h0,h1,and_self,if_true,equalPayoff,hp]
        ring
    · rw [residualPayoff,if_neg heT]
      have hc:=T.maximizer_focalCopy_eq_selection (1-ξ) b i Q hfT hmT hgeneric
      exact purePayoff_eq_of_focalCopy_eq (1-ξ) w b Q _ i hc

end FCAppendix.Affine.Hybrid.NativeContinuation
