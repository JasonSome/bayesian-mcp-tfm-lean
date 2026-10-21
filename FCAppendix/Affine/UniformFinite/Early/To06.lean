import FCAppendix.Affine.UniformFinite.NativeRestrictedIC
import FCAppendix.Affine.UniformFinite.NativeNamedCounts
import FCAppendix.Affine.UniformFinite.NativeStrategyTraces
import FCAppendix.Affine.UniformFinite.LowPrefixGuard

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05

namespace ExactRestrictedLaw
variable {i : Row} {M : ℕ}

theorem marketNeZero (E : ExactRestrictedLaw i M) : NeZero M :=
  ⟨by have h:=E.cluster.market_two_le; omega⟩

variable [NeZero M] {R : ℝ}

theorem actual_common_conull_restricted_IC (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐp∂(E.pi.1 : Measure (Value i×unitInterval)),
      0<(p.1:ℝ) ∧ 0<(baseBid i p:ℝ) ∧
      ∀a : Fin M,∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i p.1) (hiBid i p.1)→
        (problem (OriginalPopulation.game E H) a).payoff p.1 act≤
          (problem (OriginalPopulation.game E H) a).payoff p.1 (OriginalPopulation.lowerAction i p) := by
  cases M with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ N => exact NativeIC.common_broadcast_IC E H hR

theorem actual_conditional_restricted_IC (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐq∂E.sigma v,
      0<(v:ℝ) ∧ 0<(baseBid i (v,q):ℝ) ∧
      ∀a : Fin M,∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i v) (hiBid i v)→
        (problem (OriginalPopulation.game E H) a).payoff v act≤
          (problem (OriginalPopulation.game E H) a).payoff v
            (OriginalPopulation.lowerAction i (v,q)) := by
  have h:=E.actual_common_conull_restricted_IC H hR
  have hdis : lowerMeasure i⊗ₘE.sigma=(E.pi.1 : Measure (Value i×unitInterval)) := E.disintegration
  rw [← hdis] at h
  exact Measure.ae_ae_of_ae_compProd h

theorem actual_kernel_restricted_IC (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐ(v : Value i)∂lowerMeasure i,∀ᵐinc∂(OriginalPopulation.game E H).σ v,
      inc.routeCount=2 ∧ inc.bid∈Icc (floorBid i v) (hiBid i v) ∧
      ∀a : Fin M,∀act : JointAction 2,
        act.routeCount=2→ act.bid∈Icc (floorBid i v) (hiBid i v)→
        (problem (OriginalPopulation.game E H) a).payoff v act≤
          (problem (OriginalPopulation.game E H) a).payoff v inc := by
  cases M with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ N => exact NativeIC.native_kernel_broadcast_IC E H hR

end ExactRestrictedLaw

theorem exists_eventual_uniform_restricted_law (i : Row) :
    ∃M0 : ℕ,∀M : ℕ,M0≤ M→ Nonempty (ExactRestrictedLaw i M) :=
  exists_exact_restricted_family i

end FCAppendix.Affine.UniformFinite
