import FCAppendix.Affine.Hybrid.TaggedResidualList
import FCAppendix.Affine.Hybrid.ResidualIdentity
import FCAppendix.Affine.LowBody.PureFiniteEnvelope

set_option maxHeartbeats 1200000
noncomputable section
namespace FCAppendix.Affine.LowBody
open Set MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace PureTemplate

theorem maximizer_focalCopy_eq_selection (T : PureTemplate ι) (κ : ℝ) (b : ι → ℝ)
    (i : ι) (P : Finset ι×Finset ι) (hP : T.Feasible P)
    (hm : ∀Q,T.Feasible Q → CompleteInformation.potential κ b Q.1 Q.2 ≤
      CompleteInformation.potential κ b P.1 P.2)
    (hgeneric : ∀Q R,T.Feasible Q → T.Feasible R →
      CompleteInformation.potential κ b Q.1 Q.2=CompleteInformation.potential κ b R.1 R.2 →
      focalCopy Q i=focalCopy R i) :
    focalCopy P i=focalCopy (T.selection κ b) i:=by
  apply hgeneric P (T.selection κ b) hP (T.selection_feasible κ b)
  exact le_antisymm (T.selection_max κ b P hP) (hm _ (T.selection_feasible κ b))

theorem focalCopy_mono_between_maximizers (T : PureTemplate ι) {κ : ℝ} (hκ : 0<κ)
    (b : ι → ℝ) (i : ι) (y : ℝ) (hy:b i<y)
    (P Q : Finset ι×Finset ι) (hP:T.Feasible P) (hQ:T.Feasible Q)
    (hmP : ∀R,T.Feasible R → CompleteInformation.potential κ b R.1 R.2 ≤
      CompleteInformation.potential κ b P.1 P.2)
    (hmQ : ∀R,T.Feasible R → CompleteInformation.potential κ (Function.update b i y) R.1 R.2 ≤
      CompleteInformation.potential κ (Function.update b i y) Q.1 Q.2) :
    focalCopy P i ≤ focalCopy Q i:=by
  have h0:=hmP Q hQ
  have h1:=hmQ P hP
  rw [potential_update_focal,potential_update_focal] at h1
  have hc : copyCoefficient κ P i ≤ copyCoefficient κ Q i:=by nlinarith
  exact focalCopy_mono_of_coefficient hκ P Q i hc

theorem zero_maximizer_payoff_le_positive (T : PureTemplate ι) {κ w : ℝ}
    (hκ : 1/2 ≤ κ) (hκ1 : κ ≤ 1) (hw : 0 ≤ w) (b : ι → ℝ) (i : ι) (hzero:b i=0)
    (P : Finset ι×Finset ι) (hP:T.Feasible P)
    (hmP : ∀R,T.Feasible R → CompleteInformation.potential κ b R.1 R.2 ≤
      CompleteInformation.potential κ b P.1 P.2) (y : ℝ) (hy:0<y) :
    purePayoff κ w b P i ≤
      purePayoff κ w (Function.update b i y) (T.selection κ (Function.update b i y)) i+2*y:=by
  let Q:=T.selection κ (Function.update b i y)
  have hQ:=T.selection_feasible κ (Function.update b i y)
  have hc:=T.focalCopy_mono_between_maximizers (by linarith : 0<κ) b i y
    (by simpa only [hzero] using hy) P Q hP hQ hmP
    (fun R hR=>T.selection_max κ (Function.update b i y) R hR)
  have hj:=purePayoff_loss_le_duplicate (κ:=κ) b i (by simpa only [hzero] using hw) P Q hc
  have hp:=purePayoff_price_loss hκ b i y (by simpa only [hzero] using hy.le) Q (w:=w)
  have hfirst : purePayoff κ w b P i-purePayoff κ w b Q i ≤ 0:=by simpa only [hzero,mul_zero,ite_self] using hj
  have herr : 2*κ*(y-b i) ≤ 2*y:=by rw [hzero];nlinarith
  linarith

end PureTemplate

theorem ae_pattern_maximizer_focalCopy {N : ℕ} {d κ b : ℝ} (hκ : 0<κ) (hb:b≠0)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (c : ℕ) (kind : Fin N → Fin 4) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀P : Finset (Fin (N+1))×Finset (Fin (N+1)),
      (patternTemplate c kind).Feasible P →
      (∀Q,(patternTemplate c kind).Feasible Q →
        CompleteInformation.potential κ (actualPatternBids kind d b r) Q.1 Q.2 ≤
          CompleteInformation.potential κ (actualPatternBids kind d b r) P.1 P.2) →
      focalCopy P 0=focalCopy ((patternTemplate c kind).selection κ (actualPatternBids kind d b r)) 0:=by
  filter_upwards [ae_pattern_ties_same_focalCopy hκ hb mu kind] with r hr P hP hm
  exact (patternTemplate c kind).maximizer_focalCopy_eq_selection κ (actualPatternBids kind d b r) 0 P hP hm
    (fun Q R _ _ he=>hr Q R he)

theorem ae_pattern_maximizer_payoff {N : ℕ} {d κ b : ℝ} (hκ : 0<κ) (hb:b≠0)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] [NullSingletonClass mu]
    (c : ℕ) (kind : Fin N → Fin 4) :
    ∀ᵐr ∂Measure.pi (fun _ : Fin N=>mu),∀P : Finset (Fin (N+1))×Finset (Fin (N+1)),
      (patternTemplate c kind).Feasible P →
      (∀Q,(patternTemplate c kind).Feasible Q →
        CompleteInformation.potential κ (actualPatternBids kind d b r) Q.1 Q.2 ≤
          CompleteInformation.potential κ (actualPatternBids kind d b r) P.1 P.2) →
      ∀w : ℝ,purePayoff κ w (actualPatternBids kind d b r) P 0=
        purePayoff κ w (actualPatternBids kind d b r)
          ((patternTemplate c kind).selection κ (actualPatternBids kind d b r)) 0:=by
  filter_upwards [ae_pattern_maximizer_focalCopy hκ hb mu c kind] with r hr P hP hm w
  exact purePayoff_eq_of_focalCopy_eq κ w (actualPatternBids kind d b r) P _ 0 (hr P hP hm)

end FCAppendix.Affine.LowBody

namespace FCAppendix.Affine.Hybrid.NativeContinuation
open MeasureTheory ProbabilityTheory Game Set Classical Bayes LowBody
variable {m : ℕ}

def receivedTemplate (L : LocalList m) (r₀ r₁ : ℕ) : PureTemplate (Fin m) where
  support:=Finset.univ.filter (fun i=>L i≠none)
  residual₀:=r₀
  residual₁:=r₁

lemma receivedTemplate_feasible (L : LocalList m) (r₀ r₁ : ℕ) (P : ResidualPotential.Pair m) :
    (receivedTemplate L r₀ r₁).Feasible P↔ResidualPotential.Feasible L r₀ r₁ P:=by
  simp only [PureTemplate.Feasible,receivedTemplate,ResidualPotential.Feasible,LocallyFeasible]
  have he (S : Finset (Fin m)) : S⊆Finset.univ.filter (fun i=>L i≠none)↔∀i∈S,L i≠none:=by
    constructor
    · intro h i hi
      exact (Finset.mem_filter.mp (h hi)).2
    · intro h i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h i hi⟩
  rw [he,he]
  tauto

theorem native_pure_low_focalCopy (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (he:residual c 0 X≠residual c 1 X) (d : ℝ) (hd:0 ≤ d) (A : Finset (Fin m))
    (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow : ∀i∉A,entryBid (X.1 i) ≤ d)
    (hfit₀:A.card ≤ residual c 0 X) (hfit₁:A.card ≤ residual c 1 X) (i : Fin m) (hi:i∉A)
    (hgeneric : ∀P Q : ResidualPotential.Pair m,
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid (eraseActiveList A X.1)) P.1 P.2=
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid (eraseActiveList A X.1)) Q.1 Q.2 →
      focalCopy P i=focalCopy Q i) :
    let low:=eraseActiveList A X.1
    let T:=receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)
    focalCopy (purePair ξ c X) i=focalCopy (T.selection (1-ξ) (ResidualPotential.bid low)) i:=by
  let P:=purePair ξ c X
  let low:=eraseActiveList A X.1
  let T:=receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)
  let Q:ResidualPotential.Pair m:=(P.1\A,P.2\A)
  obtain ⟨hQ,hmQ⟩:=native_pure_low_maximum ξ hξ hξ1 c X hX he d hd A hA hlow hfit₀ hfit₁
  have hfQ:T.Feasible Q:=(receivedTemplate_feasible low _ _ Q).mpr hQ
  have hm : ∀R,T.Feasible R → CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) R.1 R.2 ≤
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid low) Q.1 Q.2:=
    fun R hR=>hmQ R ((receivedTemplate_feasible low _ _ R).mp hR)
  have hc:=T.maximizer_focalCopy_eq_selection (1-ξ) (ResidualPotential.bid low) i Q hfQ hm
    (fun R S _ _ h=>hgeneric R S h)
  have heCopy:focalCopy P i=focalCopy Q i:=by simp [focalCopy,Q,hi]
  exact heCopy.trans hc

theorem native_pure_low_payoff (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (he:residual c 0 X≠residual c 1 X) (d : ℝ) (hd:0 ≤ d) (A : Finset (Fin m))
    (hA : ∀i∈A,d<(1-ξ)*entryBid (X.1 i)) (hlow : ∀i∉A,entryBid (X.1 i) ≤ d)
    (hfit₀:A.card ≤ residual c 0 X) (hfit₁:A.card ≤ residual c 1 X) (i : Fin m) (hi:i∉A)
    (hgeneric : ∀P Q : ResidualPotential.Pair m,
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid (eraseActiveList A X.1)) P.1 P.2=
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid (eraseActiveList A X.1)) Q.1 Q.2 →
      focalCopy P i=focalCopy Q i) (w : ℝ) :
    let low:=eraseActiveList A X.1
    let T:=receivedTemplate low (residual c 0 X-A.card) (residual c 1 X-A.card)
    purePayoff (1-ξ) w (fun k=>entryBid (X.1 k)) (purePair ξ c X) i=
      purePayoff (1-ξ) w (ResidualPotential.bid low) (T.selection (1-ξ) (ResidualPotential.bid low)) i:=by
  have hc:=native_pure_low_focalCopy ξ hξ hξ1 c X hX he d hd A hA hlow hfit₀ hfit₁ i hi hgeneric
  have hbid:ResidualPotential.bid (eraseActiveList A X.1) i=entryBid (X.1 i):=by
    simp only [ResidualPotential.bid,eraseActiveList,if_neg hi]
    exact max_eq_left (hX i)
  simp only [purePayoff,hc,hbid]

end FCAppendix.Affine.Hybrid.NativeContinuation
