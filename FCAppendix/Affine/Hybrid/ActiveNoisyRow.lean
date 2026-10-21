import FCAppendix.Affine.Hybrid.ActivePatternPayoff
import FCAppendix.Proposer.CommonListGame

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
open scoped BigOperators
variable {N : ℕ}

def activeNoisyExpectedUtility {d vlo vhi L U eps : ℝ} (hL : 0<L) (heps : 0≤eps)
    (xi z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (p : Law (A:=ActiveBaseBid L U) mu × (ActiveValue vlo vhi × ActiveBaseBid L U)) : ℝ :=
  ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
    ∫b : (Fin N→LowBody.LowValue d) × (Fin N→ActivePhysicalBid L U eps),
      activePatternSmoothedPayoff hL heps xi z c kind (p.2,b)
      ∂(productLaw (rowLaw N lowLaw) (rowLaw N (activeImplementedBidLaw hL heps mu p.1)) :
        Measure ((Fin N→LowBody.LowValue d) × (Fin N→ActivePhysicalBid L U eps)))

theorem continuous_activeNoisyExpectedUtility {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (heps : 0<eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    Continuous (activeNoisyExpectedUtility (N:=N) (U:=U) hL heps.le xi z c categories lowLaw mu) := by
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hf:=continuous_activePatternSmoothedPayoff (d:=d) (vlo:=vlo) (vhi:=vhi) (U:=U)
    hL heps hxi hxi1 z c kind
  have hi:=continuous_law_integral (activePatternSmoothedPayoff hL heps.le xi z c kind) hf
  have hp : Continuous (fun p : Law (A:=ActiveBaseBid L U) mu × (ActiveValue vlo vhi × ActiveBaseBid L U)=>
      productLaw (rowLaw N lowLaw) (rowLaw N (activeImplementedBidLaw hL heps.le mu p.1))) :=
    continuous_productLaw.comp (continuous_const.prodMk
      ((continuous_rowLaw N).comp ((continuous_activeImplementedBidLaw hL heps.le mu).comp continuous_fst)))
  exact hi.comp (continuous_snd.prodMk hp)

theorem exists_noisy_active_pattern_law {d vlo vhi L U eps xi : ℝ}
    (hL : 0<L) (hLU : L≤U) (heps : 0<eps) (hxi : 0<xi) (hxi1 : xi<1)
    (z : ℝ) (c : ℕ) (categories : FiniteLaw (Fin 4))
    (lowLaw : ProbabilityMeasure (LowBody.LowValue d))
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu] :
    ∃(pi : Law (A:=ActiveBaseBid L U) mu)(sigma : Kernel (ActiveValue vlo vhi) (ActiveBaseBid L U)),
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=(pi.1 : Measure (ActiveValue vlo vhi × ActiveBaseBid L U)) ∧
      (∀ᵐv ∂mu,∀ᵐB ∂sigma v,∀B' : ActiveBaseBid L U,
        activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,(v,B'))≤
          activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu (pi,(v,B))) := by
  letI : Nonempty (ActiveBaseBid L U):=⟨⟨L,le_rfl,hLU⟩⟩
  obtain ⟨pi,sigma,hmark,hdis,_hjoint,hopt⟩:=exists_symmetric_law (A:=ActiveBaseBid L U) mu
    (activeNoisyExpectedUtility (N:=N) hL heps.le xi z c categories lowLaw mu)
    (continuous_activeNoisyExpectedUtility hL heps hxi hxi1 z c categories lowLaw mu)
  exact ⟨pi,sigma,hmark,hdis,hopt⟩

end FCAppendix.Affine.Hybrid
