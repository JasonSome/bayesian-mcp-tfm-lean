import FCAppendix.Affine.Hybrid.NativeFocalReindex
import FCAppendix.Affine.Hybrid.NativeRealizedContext
import FCAppendix.Affine.Hybrid.NativeLowIncentives

set_option maxHeartbeats 1800000
noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes LowBody Classical
open NativeContinuation
open Existence.Distributional
open scoped BigOperators

variable {N c : ℕ} {d U η : ℝ}

def lowActionGuard (d U κ : ℝ) (a : JointAction 2) : Prop:=
  PopulationGame.actionShape U a ∧ (d<a.bid → a.bid ≤ U → d<κ*a.bid)

lemma measurableSet_lowActionGuard (d U κ : ℝ) :
    MeasurableSet {x : ℝ×JointAction 2|lowActionGuard d U κ x.2}:=by
  have hb:Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
  have hr:Measurable (fun x : ℝ×JointAction 2=>x.2.routeCount):=(measurable_routeCount 2).comp measurable_snd
  simp only [lowActionGuard,PopulationGame.actionShape,imp_iff_not_or,setOf_and,setOf_or]
  exact (((measurableSet_le hb measurable_const).inter (measurableSet_eq_fun hr measurable_const)).union
    ((measurableSet_lt measurable_const hb).inter (measurableSet_eq_fun hr measurable_const))).inter
    (((measurableSet_lt measurable_const hb).compl).union
      ((measurableSet_le hb measurable_const).compl.union
        (measurableSet_lt measurable_const (measurable_const.mul hb))))

theorem population_lowActionGuard {κ : ℝ} (hdU:d ≤ U)
    (s a h : ℝ) (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowValue d) mu) (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<κ*x.2.bid ∧ d<x.2.bid ∧
      x.2.bid ≤ U ∧ x.2.routeCount=2)
    (hupper:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1) :
    ∀ᵐx ∂populationJoint s a h (lowJoint mu pi) PA PH,lowActionGuard d U κ x.2:=by
  have hlo:∀ᵐx ∂(lowJoint mu pi : Measure (ℝ×JointAction 2)),lowActionGuard d U κ x.2:=by
    change ∀ᵐx ∂(pi.1 : Measure (LowValue d×LowValue d)).map
      (fun x=>(x.1.1,lowBroadcast x.2)),lowActionGuard d U κ x.2
    apply (ae_map_iff (show Measurable (fun x : LowValue d×LowValue d=>(x.1.1,lowBroadcast x.2)) from
      measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)).aemeasurable
      (measurableSet_lowActionGuard d U κ)).mpr
    exact ae_of_all _ (fun x=>⟨Or.inl ⟨x.2.property.2.trans hdU,rfl⟩,
      fun hh _=>False.elim (not_lt_of_ge x.2.property.2 hh)⟩)
  have hac:∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),lowActionGuard d U κ x.2:=
    hactive.mono (fun _ hx=>⟨Or.inl ⟨hx.2.2.1,hx.2.2.2⟩,fun _ _=>hx.1⟩)
  have hup:∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),lowActionGuard d U κ x.2:=
    hupper.mono (fun _ hx=>⟨Or.inr hx,fun _ hu=>False.elim (not_le_of_gt hx.1 hu)⟩)
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hlo (ENNReal.ofReal s),Measure.ae_smul_measure hac (ENNReal.ofReal a)⟩,
      Measure.ae_smul_measure hup (ENNReal.ofReal h)⟩

lemma profile_lowActionGuard {κ : ℝ} (P : ProbabilityMeasure (ℝ×JointAction 2))
    (hη0:0 ≤ η) (hη1:η<1)
    (hP:∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),lowActionGuard d U κ x.2) :
    ∀ᵐz ∂userProfileLaw (PopulationGame.game (N+1) c P η hη0 hη1 U),
      ∀i,lowActionGuard d U κ (z i).1.2:=by
  let Gamma:=PopulationGame.game (N+1) c P η hη0 hη1 U
  have hj:∀ᵐx ∂Gamma.F⊗ₘGamma.σ,lowActionGuard d U κ x.2:=by
    simpa only [Gamma,PopulationGame.joint_law] using hP
  have hu:∀ᵐx ∂userLaw Gamma,lowActionGuard d U κ x.1.2:=
    (measurePreserving_fst (μ:=Gamma.F⊗ₘGamma.σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hj
  exact ae_all_iff.mpr (fun i=>
    (measurePreserving_eval (fun _ : Fin (N+1)=>userLaw Gamma) i).quasiMeasurePreserving.ae hu)

lemma inserted_low_guard {κ : ℝ} (hdU:d ≤ U) (z : UserProfile (N+1) 2)
    (hz:∀k,lowActionGuard d U κ (z k).1.2) (i : Fin (N+1)) (v : ℝ) (a : JointAction 2)
    (hk:a.routeCount=2) (ha:a.bid ≤ d) (tau : Equiv.Perm (Fin 2)) :
    ∀k,lowActionGuard d U κ ((Function.update z i ((v,a),tau)) k).1.2:=by
  intro k
  by_cases hki:k=i
  · subst k
    rw [Function.update_self]
    exact ⟨Or.inl ⟨ha.trans hdU,hk⟩,fun hh _=>False.elim (not_lt_of_ge ha hh)⟩
  · rw [Function.update_of_ne hki]
    exact hz k

lemma active_order_of_profile_guard {m : ℕ} {κ : ℝ} (z : UserProfile m 2)
    (hz:∀k,lowActionGuard d U κ (z k).1.2) :
    ∀i∈upperSet d (actualContext U z).1,d<κ*entryBid ((actualContext U z).1 i):=by
  have hc:z∈classifiedProfiles m U:=fun i=>(hz i).1
  intro i hi
  by_cases hu:(z i).1.2.bid ≤ U
  · have hb:=actualContext_entryBid U z hc i hu
    rw [hb]
    exact (hz i).2 (by rw [←hb];exact upperSet_entry_gt _ i hi) hu
  · have he:(actualContext U z).1 i=none:=by
      change broadcastPart U (observe (drawsRealization z) 0) i=none
      rw [broadcastPart_observe z hc 0]
      exact if_neg hu
    exact False.elim (upperSet_present d _ i hi he)

theorem integral_literalRowPayoff_eq_exact {ξ : ℝ} (hξ:0<ξ) (hξ1:ξ<1)
    (s a h : ℝ) (hs:0 ≤ s) (ha:0 ≤ a) (hh:0 ≤ h) (hsum:s+a+h=1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (G : ProbabilityMeasure (LowValue d)) (w b : ℝ) :
    (∫omega,literalRowPayoff ξ c w (b,omega)
      ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h (realLowLaw (G : Measure (LowValue d)))))=
      exactExpectedPayoff N d ξ c (categoryLaw s a h hs ha hh hsum Gref) G (w,b):=by
  have hm:Measurable (fun omega : Fin N→RowRival=>literalRowPayoff ξ c w (b,omega)):=
    (measurable_literalRowPayoff hξ hξ1 c w).comp (measurable_const.prodMk measurable_id)
  rw [integral_lowRowProfile s a h hs ha hh hsum (G : Measure (LowValue d)) N _ hm
    (|w|+(3+2*|1-ξ|)*|b|) (fun omega=>abs_literalRowPayoff_le hξ hξ1 c w b omega)]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum (realLowLaw (G : Measure (LowValue d))) Gref]
  unfold FiniteLaw.expect exactExpectedPayoff patternExpectedPayoff
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  rw [patternActualPayoff_eq_patternPayoff]
  have hb:rowBids b (fun j=>lowRowPoint (kind j,r j))=actualPatternBids kind d b r:=by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · by_cases hj:kind j=0 <;> simp [rowBids,lowRowPoint,actualPatternBids,hj]
  change patternPayoff ξ c (fun j=>(lowRowPoint (kind j,r j)).1) w _=_
  rw [hb]
  rfl

end FCAppendix.Affine.Hybrid
