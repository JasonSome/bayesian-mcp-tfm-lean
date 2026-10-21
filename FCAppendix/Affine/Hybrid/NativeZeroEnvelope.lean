import FCAppendix.Affine.Hybrid.NativeLowContextPayoff

set_option maxHeartbeats 1600000
noncomputable section
namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody EqualCapacity
open Existence.PayOnceBounded (listBids)
variable {m : ℕ}

def seedAveragePayoff (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (w : ℝ) : ℝ:=
  ∫s : Fin 2→unitInterval,purePayoff (1-ξ) w (fun k=>entryBid (X.1 k))
    (select ξ hξ hξ1 c 0 X (s 0),select ξ hξ hξ1 c 1 X (s 1)) i
    ∂Measure.pi (fun _ : Fin 2=>(volume : Measure unitInterval))

def contextAtBid (X : ClassifiedContext m) (i : Fin m) (y : ℝ) : ClassifiedContext m:=
  (Function.update X.1 i (some y),X.2)

lemma seedAveragePayoff_pure (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (w : ℝ) (he:residual c 0 X≠residual c 1 X) :
    seedAveragePayoff ξ hξ hξ1 c X i w=
      purePayoff (1-ξ) w (fun k=>entryBid (X.1 k)) (purePair ξ c X) i:=by
  simp only [seedAveragePayoff,select,if_neg he,ite_true,
    if_neg (by decide : (1:Fin 2)≠0),integral_const,probReal_univ,smul_eq_mul,one_mul]

lemma seedAveragePayoff_equal (ξ : ℝ) (hξ:0<ξ) (hξ1:ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (w : ℝ) (he:residual c 0 X=residual c 1 X) :
    seedAveragePayoff ξ hξ hξ1 c X i w=equalPayoff ξ (residual c 0 X) i w (listBids X.1):=by
  have hf (j : Fin 2):Measurable (select ξ hξ hξ1 c j X):=
    (measurable_select ξ hξ hξ1 c j).comp (measurable_const.prodMk measurable_id)
  unfold seedAveragePayoff
  rw [private_pair_expected_payoff ξ w (fun k=>entryBid (X.1 k)) i _ _ (hf 0) (hf 1)]
  change w*(acceptance ξ hξ hξ1 c 0 X i+acceptance ξ hξ hξ1 c 1 X i-
    acceptance ξ hξ hξ1 c 0 X i*acceptance ξ hξ hξ1 c 1 X i)-
    entryBid (X.1 i)*(acceptance ξ hξ hξ1 c 0 X i+acceptance ξ hξ hξ1 c 1 X i-
      2*ξ*acceptance ξ hξ hξ1 c 0 X i*acceptance ξ hξ hξ1 c 1 X i)=_
  rw [acceptance_equal ξ hξ hξ1 c 0 X he i,acceptance_equal ξ hξ hξ1 c 1 X he i]
  have hb:entryBid (X.1 i)=listBids X.1 i:=by cases hi:X.1 i <;> simp [entryBid,listBids,hi]
  rw [hb]
  unfold equalPayoff
  ring

lemma receivedTemplate_atBid (X : ClassifiedContext m) (i : Fin m) (hi:X.1 i≠none)
    (y : ℝ) (r0 r1 : ℕ) :
    receivedTemplate (contextAtBid X i y).1 r0 r1=receivedTemplate X.1 r0 r1:=by
  have hs:Finset.univ.filter (fun k=>(contextAtBid X i y).1 k≠none)=
      Finset.univ.filter (fun k=>X.1 k≠none):=by
    ext k
    by_cases hk:k=i
    · subst k
      simp [contextAtBid,hi]
    · simp [contextAtBid,Function.update_of_ne hk]
  change PureTemplate.mk _ r0 r1=PureTemplate.mk _ r0 r1
  rw [hs]

lemma bid_contextAtBid (X : ClassifiedContext m) (i : Fin m) (y : ℝ) (hy:0 ≤ y) :
    ResidualPotential.bid (contextAtBid X i y).1=Function.update (ResidualPotential.bid X.1) i y:=by
  funext k
  by_cases hk:k=i
  · subst k
    simp [contextAtBid,ResidualPotential.bid,entryBid,max_eq_left hy]
  · simp [contextAtBid,ResidualPotential.bid,Function.update_of_ne hk]

lemma purePair_feasible_max (ξ : ℝ) (hξ1:ξ<1) (c : ℕ) (X : ClassifiedContext m) :
    let T:=receivedTemplate X.1 (residual c 0 X) (residual c 1 X)
    T.Feasible (purePair ξ c X) ∧
      ∀Q,T.Feasible Q → CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) Q.1 Q.2 ≤
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) (purePair ξ c X).1 (purePair ξ c X).2:=by
  have hf:=ResidualPotential.selection_feasible (1-ξ) (by linarith) X.1 (residual c 0 X) (residual c 1 X)
  refine ⟨(receivedTemplate_feasible _ _ _ _).mpr hf,?_⟩
  intro Q hQ
  have hq:ResidualPotential.Feasible X.1 (residual c 0 X) (residual c 1 X) Q:=
    (receivedTemplate_feasible _ _ _ _).mp hQ
  have hm:=FiniteSelector.select_max
    (ResidualPotential.objective (1-ξ) X.1 (residual c 0 X) (residual c 1 X)) Q
  change ResidualPotential.objective (1-ξ) X.1 (residual c 0 X) (residual c 1 X) Q ≤
    ResidualPotential.objective (1-ξ) X.1 (residual c 0 X) (residual c 1 X) (purePair ξ c X) at hm
  have hfP:ResidualPotential.Feasible X.1 (residual c 0 X) (residual c 1 X) (purePair ξ c X):=hf
  simpa only [ResidualPotential.objective,if_pos hq,if_pos hfP] using hm

lemma zero_pair_payoff_le_new_max (T : PureTemplate (Fin m)) {κ w : ℝ}
    (hκ:1/2 ≤ κ) (hκ1:κ ≤ 1) (hw:0 ≤ w) (b : Fin m→ℝ) (i : Fin m) (hzero:b i=0)
    (P Q : ResidualPotential.Pair m) (hP:T.Feasible P) (hQ:T.Feasible Q)
    (hmP:∀R,T.Feasible R → CompleteInformation.potential κ b R.1 R.2 ≤
      CompleteInformation.potential κ b P.1 P.2)
    (y : ℝ) (hy:0<y)
    (hmQ:∀R,T.Feasible R → CompleteInformation.potential κ (Function.update b i y) R.1 R.2 ≤
      CompleteInformation.potential κ (Function.update b i y) Q.1 Q.2) :
    purePayoff κ w b P i ≤ purePayoff κ w (Function.update b i y) Q i+2*y:=by
  have hc:=T.focalCopy_mono_between_maximizers (by linarith : 0<κ) b i y
    (by simpa only [hzero] using hy) P Q hP hQ hmP hmQ
  have hj:=purePayoff_loss_le_duplicate (κ:=κ) b i (by simpa only [hzero] using hw) P Q hc
  have hp:=purePayoff_price_loss hκ b i y (by simpa only [hzero] using hy.le) Q (w:=w)
  have hfirst:purePayoff κ w b P i-purePayoff κ w b Q i ≤ 0:=by
    simpa only [hzero,mul_zero,ite_self] using hj
  have herr:2*κ*(y-b i) ≤ 2*y:=by rw [hzero];nlinarith
  linarith

theorem context_zero_payoff_le_positive (ξ : ℝ) (hξ:0<ξ) (hξh:ξ ≤ 1/2) (c : ℕ)
    (X : ClassifiedContext m) (i : Fin m) (hzero:X.1 i=some 0) (w : ℝ) (hw:0 ≤ w)
    (y : ℝ) (hy:0<y) :
    let hξ1:ξ<1:=by linarith
    seedAveragePayoff ξ hξ hξ1 c X i w ≤
      seedAveragePayoff ξ hξ hξ1 c (contextAtBid X i y) i w+2*y:=by
  dsimp only
  have hξ1:ξ<1:=by linarith
  let Y:=contextAtBid X i y
  have hr (j : Fin 2):residual c j Y=residual c j X:=rfl
  by_cases he:residual c 0 X=residual c 1 X
  · rw [seedAveragePayoff_equal ξ hξ hξ1 c X i w he,
      seedAveragePayoff_equal ξ hξ hξ1 c Y i w (by rw [hr 0,hr 1];exact he)]
    have hb0:listBids X.1 i=0:=by simp [listBids,hzero]
    have hby:listBids Y.1 i=y:=by simp [Y,contextAtBid,listBids]
    have hp0:positiveMarginal ξ (residual c 0 X) (listBids X.1) i=0:=
      positiveMarginal_zero_of_nonpos ξ _ _ i hb0.le
    have hp:=positiveMarginal_spec ξ (residual c 0 Y) hξ hξ1 (listBids Y.1)
    have hpos:=hp.1 i
    have hone:=hp.2.1 i
    have hserv:0 ≤ 2*positiveMarginal ξ (residual c 0 Y) (listBids Y.1) i-
        (positiveMarginal ξ (residual c 0 Y) (listBids Y.1) i)^2:=by nlinarith
    have hwserv:=mul_nonneg hw hserv
    have hcost:=mul_nonneg (mul_nonneg hξ.le hy.le)
      (sq_nonneg (positiveMarginal ξ (residual c 0 Y) (listBids Y.1) i))
    unfold equalPayoff
    rw [hp0,hb0,hby]
    nlinarith
  · rw [seedAveragePayoff_pure ξ hξ hξ1 c X i w he,
      seedAveragePayoff_pure ξ hξ hξ1 c Y i w (by rw [hr 0,hr 1];exact he)]
    let T:=receivedTemplate X.1 (residual c 0 X) (residual c 1 X)
    obtain ⟨hP,hmP⟩:=purePair_feasible_max ξ hξ1 c X
    obtain ⟨hQ,hmQ⟩:=purePair_feasible_max ξ hξ1 c Y
    have hT:receivedTemplate Y.1 (residual c 0 Y) (residual c 1 Y)=T:=by
      rw [hr 0,hr 1]
      exact receivedTemplate_atBid X i (by rw [hzero];exact Option.some_ne_none 0) y _ _
    rw [hT] at hQ hmQ
    have hb0:ResidualPotential.bid X.1 i=0:=by simp [ResidualPotential.bid,hzero,entryBid]
    have hby:ResidualPotential.bid Y.1=Function.update (ResidualPotential.bid X.1) i y:=bid_contextAtBid X i y hy.le
    rw [hby] at hmQ
    have hh:=zero_pair_payoff_le_new_max T (by linarith : 1/2 ≤ 1-ξ) (by linarith : 1-ξ ≤ 1)
      hw (ResidualPotential.bid X.1) i hb0 (purePair ξ c X) (purePair ξ c Y) hP hQ hmP y hy hmQ
    have hzeroEntry:entryBid (X.1 i)=0:=by rw [hzero];rfl
    have hyEntry:entryBid (Y.1 i)=y:=by simp [Y,contextAtBid,entryBid]
    simpa only [purePayoff,hzeroEntry,hyEntry,hb0,Function.update_self] using hh

end FCAppendix.Affine.Hybrid.NativeContinuation
