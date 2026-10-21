import FCAppendix.Affine.LowBody.ActualLowBidEquilibrium

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set

namespace ActualAtomlessLowLimit

variable {N : ℕ} {d ξ : ℝ} {c : ℕ} {categories : FiniteLaw (Fin 4)}
  {mu : Measure (LowValue d)} [IsProbabilityMeasure mu]

theorem exists_bid_kernel (L : ActualAtomlessLowLimit N d ξ c categories mu)
    (hξ : 0<ξ) (hξh : ξ≤1/2) :
    ∃sigma : Kernel (LowValue d) (LowValue d),IsMarkovKernel sigma ∧
      mu⊗ₘsigma=(L.joint.1 : Measure (LowValue d×LowValue d)) ∧
      (∀ᵐw ∂mu,∀ᵐb ∂sigma w,0<b.1 ∧ b.1≤w.1 ∧
        w.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤w.1-b.1) ∧
      (∀ᵐw ∂mu,∀ᵐb ∂sigma w,∀b' : ℝ,0≤b'→
        exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (w.1,b')≤
        exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (w.1,b.1)) := by
  letI : Nonempty (LowValue d):=nonempty_of_isProbabilityMeasure mu
  let sigma:=(L.joint.1 : Measure (LowValue d×LowValue d)).condKernel
  have hdis : mu⊗ₘsigma=(L.joint.1 : Measure (LowValue d×LowValue d)) := by
    have hmarg : (L.joint.1 : Measure (LowValue d×LowValue d)).fst=mu:=L.joint.2
    calc
      mu⊗ₘsigma=(L.joint.1 : Measure (LowValue d×LowValue d)).fst⊗ₘsigma:=
        congrArg (fun nu : Measure (LowValue d)=>nu⊗ₘsigma) hmarg.symm
      _=(L.joint.1 : Measure (LowValue d×LowValue d)):=Measure.disintegrate _ _
  refine ⟨sigma,inferInstance,hdis,?_,?_⟩
  · have hs : ∀ᵐx ∂(L.joint.1 : Measure (LowValue d×LowValue d)),
        0<x.2.1 ∧ x.2.1≤x.1.1 ∧
        x.1.1*(CommonList.iid categories N).prob (LocalUnderflow c 0)/4≤x.1.1-x.2.1 := by
      filter_upwards [L.bid_positive,L.bid_le_value,L.value_surplus_gap] with x hx hb hg
      exact ⟨hx,hb,hg⟩
    rw [←hdis] at hs
    exact Measure.ae_ae_of_ae_compProd hs
  · have hIC:=L.all_bid_IC hξ hξh
    have hIC' : ∀ᵐx ∂mu⊗ₘsigma,∀b' : ℝ,0≤b'→
        exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,b')≤
        exactExpectedPayoff N d ξ c categories (L.joint.1.map measurable_snd.aemeasurable) (x.1.1,x.2.1) := by
      simpa only [hdis] using hIC
    exact Measure.ae_ae_of_ae_compProd hIC'

end ActualAtomlessLowLimit
end FCAppendix.Affine.LowBody
