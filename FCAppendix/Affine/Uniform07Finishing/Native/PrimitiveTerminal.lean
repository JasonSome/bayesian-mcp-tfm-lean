import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06NativeCrossover
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received06CanonicalOptimizer
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05LowEntry
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Product
import FCAppendix.Affine.Uniform07Finishing.Native.FinalApplication

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Crossover Crossover.Physical Crossover.Received05

def receivedLowerKernels (F : BroadcastLowerFamily) :
    UniformAuxiliaryKernels05_06 F.toAuxiliaryData where
  physical row:={
    crossover:=(F.crossover row).toCrossoverFamily
    low:=F.toReadyLowerFamily.low row
    product:=F.toReadyLowerFamily.product row
    entry:=F.toReadyLowerFamily.entry row
    canonical:=F.toReadyLowerFamily.canonical row }

def uniformSourcePair : UniformNativePair :=
  uniform_native_pair_from_lower_producers auxiliaryData
    (receivedLowerKernels broadcastLowerFamily)

theorem aff_uniform_result :
  ∃ P : UniformNativePair,
    (∀ i v, 0 < v → v ≤ 1 →
      v ≠ Uniform07.entry i → v ≠ Uniform07.cutoff i → ∀ r : Fin 3,
      Tendsto (fun k => (conditionalTypeCountLaw (P.game i k)
        (P.positive k) v).mass r) atTop (𝓝 (sourceLimitMass i v r))) ∧
    (∀ i, Tendsto (fun k => finiteLoad (P.game i k)) atTop (𝓝 (999 / 1000 : ℝ)) ∧
      Tendsto (fun k => finiteLoad (P.game i k) - finiteCoverage (P.game i k))
        atTop (𝓝 (Uniform07.limitDup i)) ∧
      Tendsto (fun k => finiteCoverage (P.game i k)) atTop (𝓝 (Uniform07.limitCoverage i)) ∧
      Tendsto (fun k => finiteMultiplicity (P.game i k)) atTop
        (𝓝 ((999 / 1000 : ℝ) / Uniform07.limitCoverage i))) ∧
    (Tendsto (fun k => (conditionalTypeCountLaw (P.game .first k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 1) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 1) ∧
    Tendsto (fun k => (conditionalTypeCountLaw (P.game .second k)
      (P.positive k) Uniform07.testValue).success) atTop (𝓝 Uniform07.testSuccess) ∧
    Tendsto (fun k => conditionalMultiplicity
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load)
      atTop (𝓝 Uniform07.testMultiplicity)) ∧
    Uniform07.limitDup .first < Uniform07.limitDup .second ∧
    Uniform07.limitCoverage .second < Uniform07.limitCoverage .first ∧
    (49009354366 / 10^11 : ℝ) < Uniform07.testSuccess ∧
    Uniform07.testSuccess < 49009354367 / 10^11 ∧
    (116680848997 / 10^11 : ℝ) < Uniform07.testMultiplicity ∧
    Uniform07.testMultiplicity < 116680848998 / 10^11 ∧
    (∃ K, ∀ k ≥ K,
      0 < finiteCoverage (P.game .first k) ∧
      0 < finiteCoverage (P.game .second k) ∧
      0 < (conditionalTypeCountLaw (P.game .first k)
        (P.positive k) Uniform07.testValue).success ∧
      0 < (conditionalTypeCountLaw (P.game .second k)
        (P.positive k) Uniform07.testValue).success ∧
      finiteLoad (P.game .first k) - finiteCoverage (P.game .first k) <
        finiteLoad (P.game .second k) - finiteCoverage (P.game .second k) ∧
      finiteCoverage (P.game .second k) < finiteCoverage (P.game .first k) ∧
      finiteMultiplicity (P.game .first k) < finiteMultiplicity (P.game .second k) ∧
      (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success <
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success ∧
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .first k) (P.positive k) Uniform07.testValue).load <
      conditionalMultiplicity
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).success
        (conditionalTypeCountLaw (P.game .second k) (P.positive k) Uniform07.testValue).load) :=
  aff_uniform_result_of_native_pair uniformSourcePair

theorem aff_uniform_result_contract : AffUniformResult := aff_uniform_result

theorem uniform_exact_native_families :
    ∃ (N : ℕ) (hN : 2≤ N)
      (Γ : (row : Uniform07.Row)→(k : ℕ)→
        FiniteGame (N+k) 2 (Uniform07.capacity (N+k)) unitInterval),
      (∀row k,(Γ row k).F=Uniform07.uniformLaw ∧
        (Γ row k).A=Schedule.affine 2 (Uniform07.eta row)
          (Uniform07.eta_pos row).le (source_eta_le_one row) ∧
        (Γ row k).G=Schedule.once 2 ∧ (Γ row k).g=0 ∧ (Γ row k).seedLaw=volume) ∧
      (∀row k,IsBayesianEquilibrium (Γ row k)) ∧
      (∀row k j b,visibleBidMeasure (Γ row k) j {b}=0) ∧
      (∀row k,∃B : PosteriorSystem (Γ row k),∀j ℓ s,
        Finite.Optimal (Uniform07.capacity (N+k))
          (beliefReceipts (Γ row k).A (posteriorCountBelief (Γ row k) B j ℓ) ℓ)
          ((Γ row k).policy j ℓ s).val) ∧
      (∀row k,∀ᵐp∂((Γ row k).F⊗ₘ(Γ row k).σ),
        ∀u : Fin (N+k),∀dev : JointAction 2,
          (problem (Γ row k) u).payoff p.1 dev≤(problem (Γ row k) u).payoff p.1 p.2) ∧
      (∀ᵐv∂Uniform07.uniformLaw,∀row k,∀ᵐa∂(Γ row k).σ v,
        ∀u : Fin (N+k),∀dev : JointAction 2,
          (problem (Γ row k) u).payoff v dev≤(problem (Γ row k) u).payoff v a) ∧
      (∀row k v,0< v→ v≤ 1→∀ᵐa∂(Γ row k).σ v,
        ∀u : Fin (N+k),∀dev : JointAction 2,
          (problem (Γ row k) u).payoff v dev≤(problem (Γ row k) u).payoff v a) ∧
      (∀row k v,0< v→ v≤ 1→ v≠Uniform07.cutoff row→∀ᵐa∂(Γ row k).σ v,
        a.routeCount=if v< Uniform07.cutoff row then 2 else 1) ∧
      (∀row v,0< v→ v≤ 1→ v≠Uniform07.entry row→ v≠Uniform07.cutoff row→∀r : Fin 3,
        Tendsto (fun k=>(conditionalTypeCountLaw (Γ row k) (by omega) v).mass r) atTop
          (𝓝 (if v< Uniform07.entry row then if r.val=0 then 1 else 0
            else if v< Uniform07.cutoff row then
              let p:=1-Uniform07.entry row/v
              if r.val=0 then (1-p)^2 else if r.val=1 then 2*p*(1-p) else p^2
            else if r.val=1 then 1 else 0))) := by
  let P:=uniformSourcePair
  refine ⟨P.start,P.start_ge_two,P.game,?_,P.equilibrium,?_,?_,
    P.common_conull_users,P.common_conull_users_all_markets,
    P.fixed_value_best_response,P.fixed_value_routing,?_⟩
  · intro row k
    exact ⟨P.value_law row k,P.bid_schedule row k,P.base_schedule row k,
      P.base_fee row k,P.seed_law row k⟩
  · intro row k j b
    letI:=P.visible_atomless row k j
    exact measure_singleton b
  · intro row k
    exact (P.equilibrium row k).beliefs
  · intro row v hv hv1 hl ht r
    simpa only [sourceLimitMass] using P.conditional_law row v hv hv1 hl ht r

end FCAppendix.Affine.Uniform07Finishing
