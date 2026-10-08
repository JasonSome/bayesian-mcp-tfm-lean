import FCAppendix.Finite.EnvelopeIntegral
import FCAppendix.Game.Bayesian

namespace FCAppendix
namespace Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem measurable_observe_deviated_joint (i : Fin m) (j : Fin n) :
    Measurable (fun p : JointAction n × Sample m n Seed => observe (deviated i p.1 p.2) j) := by
  classical
  rw [measurable_pi_iff]
  intro l
  by_cases hl : l = i
  · subst hl
    have hfun : (fun p : JointAction n × Sample m n Seed => observe (deviated l p.1 p.2) j l) =
        fun p => if j ∈ firstK p.2.2 p.1.routeCount then some p.1.bid else none := by
      funext p
      simp only [observe, deviated_recipients_self, deviated_bid_self]
    rw [hfun]
    refine Measurable.ite ?_ ((measurable_some).comp ((measurable_bid n).comp measurable_fst))
      measurable_const
    have hs : {p : JointAction n × Sample m n Seed | j ∈ firstK p.2.2 p.1.routeCount} =
        (fun p : JointAction n × Sample m n Seed => (p.2.2, p.1.routeCount)) ⁻¹'
          {x | j ∈ firstK x.1 x.2} := rfl
    rw [hs]
    exact ((measurable_snd.comp measurable_snd).prodMk
      ((measurable_routeCount n).comp measurable_fst)) (measurableSet_mem_firstK j)
  · have h := measurable_observe_deviated (Seed := Seed) i (Interim.abstain n) j
    have hfun : (fun p : JointAction n × Sample m n Seed => observe (deviated i p.1 p.2) j l) =
        fun p => observe (deviated i (Interim.abstain n) p.2) j l := by
      funext p
      simp only [observe, deviated_recipients_other i l hl, deviated_bid_other i l hl]
    rw [hfun]
    exact ((measurable_pi_apply l).comp h).comp measurable_snd

theorem measurable_focalCount_joint (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun p : JointAction n × Sample m n Seed => focalCount Γ i p.1 p.2) := by
  classical
  have hseed : ∀ j, Measurable (fun p : JointAction n × Sample m n Seed => p.2.1.2 j) :=
    fun j => (measurable_pi_apply j).comp (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have halloc : ∀ j, Measurable (fun p : JointAction n × Sample m n Seed =>
      allocation (deviated i p.1 p.2) Γ.policy p.2.1.2 j) := fun j =>
    (Γ.policy_measurable j).comp ((measurable_observe_deviated_joint i j).prodMk (hseed j))
  have hcount : Measurable (fun p : JointAction n × Sample m n Seed =>
      inclusionCount (deviated i p.1 p.2) Γ.policy p.2.1.2 i) := by
    have he : (fun p : JointAction n × Sample m n Seed =>
        inclusionCount (deviated i p.1 p.2) Γ.policy p.2.1.2 i) =
        fun p => ∑ j, (if i ∈ allocation (deviated i p.1 p.2) Γ.policy p.2.1.2 j
          then 1 else 0) := by
      funext p
      exact inclusionCount_eq_sum _ _ _ _
    rw [he]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (halloc j) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  apply measurable_to_countable'
  intro r
  have hs : (fun p : JointAction n × Sample m n Seed => focalCount Γ i p.1 p.2) ⁻¹' {r} =
      (fun p : JointAction n × Sample m n Seed =>
        inclusionCount (deviated i p.1 p.2) Γ.policy p.2.1.2 i) ⁻¹' {r.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, focalCount, boundedCount]
    exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩
  rw [hs]
  exact hcount (measurableSet_singleton _)

theorem measurable_outcome_expect (Γ : FiniteGame m n c Seed) (i : Fin m)
    (f : Fin (n + 1) → ℝ) :
    Measurable (fun a : JointAction n => ((problem Γ i).outcome a).expect f) := by
  have he : (fun a : JointAction n => ((problem Γ i).outcome a).expect f) =
      fun a => ∫ ω, f (focalCount Γ i a ω) ∂(sampleLaw Γ) := by
    funext a
    rw [problem_outcome, CountLaw.expect_ofMeasure]
  rw [he]
  have hjoint : Measurable (fun p : JointAction n × Sample m n Seed =>
      f (focalCount Γ i p.1 p.2)) :=
    (measurable_of_countable f).comp (measurable_focalCount_joint Γ i)
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_success (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun a : JointAction n => ((problem Γ i).outcome a).success) :=
  measurable_outcome_expect Γ i _

theorem measurable_payoff (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (fun p : ℝ × JointAction n => (problem Γ i).payoff p.1 p.2) := by
  have he : (fun p : ℝ × JointAction n => (problem Γ i).payoff p.1 p.2) =
      fun p => p.1 * ((problem Γ i).outcome p.2).success -
        p.2.bid * ((problem Γ i).outcome p.2).charge Γ.A -
        Γ.g * ((problem Γ i).outcome p.2).charge Γ.G := by
    funext p
    simp only [Interim.Problem.payoff, CountLaw.utility_eq]
    rfl
  rw [he]
  have hs : Measurable (fun p : ℝ × JointAction n => ((problem Γ i).outcome p.2).success) :=
    (measurable_success Γ i).comp measurable_snd
  have hA : Measurable (fun p : ℝ × JointAction n => ((problem Γ i).outcome p.2).charge Γ.A) :=
    (measurable_outcome_expect Γ i (fun r => Γ.A.charge r.val)).comp measurable_snd
  have hG : Measurable (fun p : ℝ × JointAction n => ((problem Γ i).outcome p.2).charge Γ.G) :=
    (measurable_outcome_expect Γ i (fun r => Γ.G.charge r.val)).comp measurable_snd
  have hb : Measurable (fun p : ℝ × JointAction n => p.2.bid) :=
    (measurable_bid n).comp measurable_snd
  exact ((measurable_fst.mul hs).sub (hb.mul hA)).sub (measurable_const.mul hG)

theorem measurableSet_bestResponse (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurableSet {p : ℝ × JointAction n | (problem Γ i).BestResponse p.1 p.2} := by
  have hset : {p : ℝ × JointAction n | (problem Γ i).BestResponse p.1 p.2} =
      {p | (problem Γ i).payoff p.1 p.2 = (problem Γ i).envelope p.1} := by
    ext p
    exact (problem Γ i).bestResponse_iff_attains p.1 p.2
  rw [hset]
  have henv : Measurable (fun p : ℝ × JointAction n => (problem Γ i).envelope p.1) :=
    ((problem Γ i).envelope_lipschitzWith.continuous.measurable).comp measurable_fst
  exact measurableSet_eq_fun (measurable_payoff Γ i) henv

theorem ae_bestResponse_compProd (Γ : FiniteGame m n c Seed) (hΓ : UsersOptimal Γ)
    (i : Fin m) : ∀ᵐ p ∂(Γ.F ⊗ₘ Γ.σ), (problem Γ i).BestResponse p.1 p.2 :=
  Measure.ae_compProd_of_ae_ae (measurableSet_bestResponse Γ i) (hΓ i)

end Bayes
end FCAppendix
