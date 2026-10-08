import FCAppendix.Game.Routing
import FCAppendix.Finite.Envelope
import FCAppendix.Finite.ReceiptOrder
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

namespace FCAppendix
namespace Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory BigOperators

abbrev UserDraw (n : ℕ) := (ℝ × JointAction n) × Equiv.Perm (Fin n)

structure FiniteGame (m n c : ℕ) (Seed : Type*) [MeasurableSpace Seed] where

  F : Measure ℝ
  hF : IsProbabilityMeasure F

  σ : Kernel ℝ (JointAction n)
  hσ : IsMarkovKernel σ

  seedLaw : Measure Seed
  hseed : IsProbabilityMeasure seedLaw

  policy : Fin n → LocalPolicy m c Seed
  policy_measurable : ∀ j, Measurable (fun p : LocalList m × Seed => (policy j p.1 p.2).val)

  A : Schedule n
  G : Schedule n
  g : ℝ
  g_nonneg : 0 ≤ g

attribute [instance] FiniteGame.hF FiniteGame.hσ FiniteGame.hseed

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def userLaw (Γ : FiniteGame m n c Seed) : Measure (UserDraw n) :=
  (Γ.F ⊗ₘ Γ.σ).prod (permLaw n)

instance (Γ : FiniteGame m n c Seed) : IsProbabilityMeasure (userLaw Γ) := by
  unfold userLaw
  infer_instance

abbrev Background (m n : ℕ) (Seed : Type*) := (Fin m → UserDraw n) × (Fin n → Seed)

abbrev Sample (m n : ℕ) (Seed : Type*) := Background m n Seed × Equiv.Perm (Fin n)

noncomputable def backgroundLaw (Γ : FiniteGame m n c Seed) : Measure (Background m n Seed) :=
  (Measure.pi fun _ : Fin m => userLaw Γ).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)

instance (Γ : FiniteGame m n c Seed) : IsProbabilityMeasure (backgroundLaw Γ) := by
  unfold backgroundLaw
  infer_instance

noncomputable def sampleLaw (Γ : FiniteGame m n c Seed) : Measure (Sample m n Seed) :=
  (backgroundLaw Γ).prod (permLaw n)

instance (Γ : FiniteGame m n c Seed) : IsProbabilityMeasure (sampleLaw Γ) := by
  unfold sampleLaw
  infer_instance

noncomputable def drawsRealization (d : Fin m → UserDraw n) : Realization m n where
  action l := (d l).1.2
  recipients l := firstK (d l).2 (d l).1.2.routeCount
  chosen_size l := card_firstK _ _ (d l).1.2.routeCount_le

noncomputable def deviated (i : Fin m) (a : JointAction n) (ω : Sample m n Seed) :
    Realization m n :=
  deviate (drawsRealization ω.1.1) i a.bid a.bid_nonneg (firstK ω.2 a.routeCount)

omit [MeasurableSpace Seed] in
theorem deviated_recipients_self (i : Fin m) (a : JointAction n) (ω : Sample m n Seed) :
    (deviated i a ω).recipients i = firstK ω.2 a.routeCount := by
  simp [deviated, deviate]

omit [MeasurableSpace Seed] in
theorem deviated_recipients_other (i l : Fin m) (hl : l ≠ i) (a : JointAction n)
    (ω : Sample m n Seed) :
    (deviated i a ω).recipients l = firstK (ω.1.1 l).2 (ω.1.1 l).1.2.routeCount := by
  simp [deviated, deviate, Function.update, hl, drawsRealization]

omit [MeasurableSpace Seed] in
theorem deviated_bid_self (i : Fin m) (a : JointAction n) (ω : Sample m n Seed) :
    ((deviated i a ω).action i).bid = a.bid := by
  simp [deviated, deviate]

omit [MeasurableSpace Seed] in
theorem deviated_bid_other (i l : Fin m) (hl : l ≠ i) (a : JointAction n)
    (ω : Sample m n Seed) :
    ((deviated i a ω).action l).bid = (ω.1.1 l).1.2.bid := by
  simp [deviated, deviate, Function.update, hl, drawsRealization]

noncomputable def focalCount (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    (ω : Sample m n Seed) : Fin (n + 1) :=
  boundedCount (deviated i a ω) Γ.policy ω.1.2 i

theorem focalCount_le (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    (ω : Sample m n Seed) : (focalCount Γ i a ω).val ≤ a.routeCount := by
  have h := inclusionCount_le_chosen (deviated i a ω) Γ.policy ω.1.2 i
  have hc : ((deviated i a ω).action i).routeCount = a.routeCount := by
    rw [← (deviated i a ω).chosen_size i, deviated_recipients_self]
    exact card_firstK _ _ a.routeCount_le
  simpa [focalCount, boundedCount, hc] using h

section Measurability

theorem measurableSet_mem_firstK (j : Fin n) :
    MeasurableSet {x : Equiv.Perm (Fin n) × ℕ | j ∈ firstK x.1 x.2} :=
  (Set.to_countable _).measurableSet

theorem measurable_observe_deviated (i : Fin m) (a : JointAction n) (j : Fin n) :
    Measurable (fun ω : Sample m n Seed => observe (deviated i a ω) j) := by
  classical
  rw [measurable_pi_iff]
  intro l
  by_cases hl : l = i
  · subst hl
    have hfun : (fun ω : Sample m n Seed => observe (deviated l a ω) j l) =
        fun ω => if j ∈ firstK ω.2 a.routeCount then some a.bid else none := by
      funext ω
      simp only [observe, deviated_recipients_self, deviated_bid_self]
    rw [hfun]
    refine Measurable.ite ?_ measurable_const measurable_const
    have hs : {ω : Sample m n Seed | j ∈ firstK ω.2 a.routeCount} =
        (fun ω : Sample m n Seed => (ω.2, a.routeCount)) ⁻¹'
          {x | j ∈ firstK x.1 x.2} := rfl
    rw [hs]
    exact measurable_snd.prodMk measurable_const (measurableSet_mem_firstK j)
  · have hfun : (fun ω : Sample m n Seed => observe (deviated i a ω) j l) =
        fun ω => if j ∈ firstK (ω.1.1 l).2 (ω.1.1 l).1.2.routeCount
          then some (ω.1.1 l).1.2.bid else none := by
      funext ω
      simp only [observe, deviated_recipients_other i l hl, deviated_bid_other i l hl]
    rw [hfun]
    have hdraw : Measurable (fun ω : Sample m n Seed => ω.1.1 l) :=
      (measurable_pi_apply l).comp (measurable_fst.comp measurable_fst)
    have hact : Measurable (fun ω : Sample m n Seed => (ω.1.1 l).1.2) :=
      measurable_snd.comp (measurable_fst.comp hdraw)
    refine Measurable.ite ?_ ((measurable_some).comp ((measurable_bid n).comp hact))
      measurable_const
    have hs : {ω : Sample m n Seed | j ∈ firstK (ω.1.1 l).2 (ω.1.1 l).1.2.routeCount} =
        (fun ω : Sample m n Seed => ((ω.1.1 l).2, (ω.1.1 l).1.2.routeCount)) ⁻¹'
          {x | j ∈ firstK x.1 x.2} := rfl
    rw [hs]
    exact ((measurable_snd.comp hdraw).prodMk ((measurable_routeCount n).comp hact))
      (measurableSet_mem_firstK j)

theorem measurable_allocation_deviated (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (j : Fin n) :
    Measurable (fun ω : Sample m n Seed => allocation (deviated i a ω) Γ.policy ω.1.2 j) := by
  have hseed : Measurable (fun ω : Sample m n Seed => ω.1.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)
  exact (Γ.policy_measurable j).comp ((measurable_observe_deviated i a j).prodMk hseed)

theorem measurable_focalCount (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n) :
    Measurable (focalCount Γ i a) := by
  classical
  have hcount : Measurable (fun ω : Sample m n Seed =>
      inclusionCount (deviated i a ω) Γ.policy ω.1.2 i) := by
    have he : (fun ω : Sample m n Seed => inclusionCount (deviated i a ω) Γ.policy ω.1.2 i) =
        fun ω => ∑ j, (if i ∈ allocation (deviated i a ω) Γ.policy ω.1.2 j then 1 else 0) := by
      funext ω
      exact inclusionCount_eq_sum _ _ _ _
    rw [he]
    refine Finset.measurable_sum _ (fun j _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurable_allocation_deviated Γ i a j)
      (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  apply measurable_to_countable'
  intro r
  have hs : focalCount Γ i a ⁻¹' {r} = (fun ω : Sample m n Seed =>
      inclusionCount (deviated i a ω) Γ.policy ω.1.2 i) ⁻¹' {r.val} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, focalCount, boundedCount]
    exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩
  rw [hs]
  exact hcount (measurableSet_singleton _)

end Measurability

noncomputable def problem (Γ : FiniteGame m n c Seed) (i : Fin m) : Interim.Problem n :=
  Interim.Problem.ofBoundedCounts (sampleLaw Γ) Γ.A Γ.G Γ.g Γ.g_nonneg
    (focalCount Γ i) (measurable_focalCount Γ i) (focalCount_le Γ i)

theorem problem_outcome (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n) :
    (problem Γ i).outcome a =
      CountLaw.ofMeasure (sampleLaw Γ) (focalCount Γ i a) (measurable_focalCount Γ i a) :=
  rfl

noncomputable def beliefReceipts (A : Schedule n) (belief : Fin m → FiniteLaw (Fin n))
    (ℓ : LocalList m) : Fin m → ℝ :=
  fun l => match ℓ l with
    | some b => Finite.conditionalReceipt A (belief l) b
    | none => 0

def ProposerRational (Γ : FiniteGame m n c Seed) (j : Fin n) : Prop :=
  ∃ belief : LocalList m → Fin m → FiniteLaw (Fin n), ∀ ℓ s,
    Finite.Optimal c (beliefReceipts Γ.A (belief ℓ) ℓ) (Γ.policy j ℓ s).val

def UsersOptimal (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ i, ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂(Γ.σ v), (problem Γ i).BestResponse v a

structure IsEquilibrium (Γ : FiniteGame m n c Seed) : Prop where
  users : UsersOptimal Γ
  proposers : ∀ j, ProposerRational Γ j

end Bayes
end FCAppendix
