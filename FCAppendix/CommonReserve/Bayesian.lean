import FCAppendix.CommonReserve.Accounting
import FCAppendix.Game.Bayesian

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

abbrev UserDraw (n : ℕ) (r : ℝ) := ℝ × Action n r
abbrev Sample (m n : ℕ) (r : ℝ) (Seed : Type*) :=
  (Fin m → UserDraw n r) × (Fin n → Seed)

structure FiniteGame (m n c : ℕ) (r : ℝ) (Seed : Type*) [MeasurableSpace Seed] where
  F : Measure ℝ
  hF : IsProbabilityMeasure F
  σ : Kernel ℝ (Action n r)
  hσ : IsMarkovKernel σ
  seedLaw : Measure Seed
  hseed : IsProbabilityMeasure seedLaw
  policy : Fin n → LocalPolicy m c Seed
  policy_measurable : ∀ j, Measurable (fun p : LocalList m × Seed => (policy j p.1 p.2).val)
  G : Schedule n
  g : ℝ
  g_nonneg : 0 ≤ g
  reserve_nonneg : 0 ≤ r

attribute [instance] FiniteGame.hF FiniteGame.hσ FiniteGame.hseed
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

namespace FiniteGame

def userLaw (Γ : FiniteGame m n c r Seed) : Measure (UserDraw n r) := Γ.F ⊗ₘ Γ.σ
instance (Γ : FiniteGame m n c r Seed) : IsProbabilityMeasure Γ.userLaw := by
  unfold userLaw
  infer_instance

def sampleLaw (Γ : FiniteGame m n c r Seed) : Measure (Sample m n r Seed) :=
  (Measure.pi fun _ : Fin m => Γ.userLaw).prod (Measure.pi fun _ : Fin n => Γ.seedLaw)
instance (Γ : FiniteGame m n c r Seed) : IsProbabilityMeasure Γ.sampleLaw := by
  unfold sampleLaw
  infer_instance

def deviated (i : Fin m) (a : Action n r) (ω : Sample m n r Seed) : Profile m n r := by
  classical
  exact Function.update (fun l => (ω.1 l).2) i a

theorem measurable_observe_deviated_joint (i : Fin m) (j : Fin n) :
    Measurable (fun p : Action n r × Sample m n r Seed => observe (deviated i p.1 p.2) j) := by
  classical
  rw [measurable_pi_iff]
  intro l
  have hev : Measurable (fun a : Action n r => a.val j) :=
    (measurable_pi_apply j).comp measurable_subtype_coe
  by_cases hl : l = i
  · subst l
    simpa [observe, deviated, Function.update, Function.comp_def] using hev.comp measurable_fst
  · have hd : Measurable (fun p : Action n r × Sample m n r Seed => (p.2.1 l).2) :=
      measurable_snd.comp ((measurable_pi_apply l).comp (measurable_fst.comp measurable_snd))
    simpa [observe, deviated, Function.update, Function.comp_def, hl] using hev.comp hd

def focalCount (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r)
    (ω : Sample m n r Seed) : Fin (n + 1) :=
  ⟨count (deviated i a ω) Γ.policy ω.2 i, Nat.lt_succ_of_le (count_le _ _ _ _)⟩

theorem measurable_focalCount_joint (Γ : FiniteGame m n c r Seed) (i : Fin m) :
    Measurable (fun p : Action n r × Sample m n r Seed => Γ.focalCount i p.1 p.2) := by
  classical
  have hseed (j : Fin n) : Measurable (fun p : Action n r × Sample m n r Seed => p.2.2 j) :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have halloc (j : Fin n) : Measurable (fun p : Action n r × Sample m n r Seed =>
      allocation (deviated i p.1 p.2) Γ.policy p.2.2 j) :=
    (Γ.policy_measurable j).comp ((measurable_observe_deviated_joint i j).prodMk (hseed j))
  have hcount : Measurable (fun p : Action n r × Sample m n r Seed =>
      count (deviated i p.1 p.2) Γ.policy p.2.2 i) := by
    have he : (fun p : Action n r × Sample m n r Seed =>
        count (deviated i p.1 p.2) Γ.policy p.2.2 i) =
        fun p => ∑ j, if i ∈ allocation (deviated i p.1 p.2) Γ.policy p.2.2 j then 1 else 0 := by
      funext p
      rw [count, ← Game.sum_membership]
      simp [accepted]
    rw [he]
    refine Finset.measurable_sum _ (fun j _ => Measurable.ite ?_ measurable_const measurable_const)
    exact (halloc j) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})
  apply measurable_to_countable'
  intro k
  have he : (fun p : Action n r × Sample m n r Seed => Γ.focalCount i p.1 p.2) ⁻¹' {k} =
      (fun p : Action n r × Sample m n r Seed => count (deviated i p.1 p.2) Γ.policy p.2.2 i) ⁻¹' {k.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, focalCount]
    exact ⟨fun h => by rw [← h], fun h => Fin.ext h⟩
  rw [he]
  exact hcount (measurableSet_singleton _)

def outcome (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) : CountLaw n :=
  by
    have hm : Measurable (fun ω : Sample m n r Seed => (a, ω)) :=
      measurable_const.prodMk measurable_id
    have h := (Γ.measurable_focalCount_joint i).comp hm
    exact CountLaw.ofMeasure Γ.sampleLaw (Γ.focalCount i a) h

def purePayoff (Γ : FiniteGame m n c r Seed) (i : Fin m) (v : ℝ) (a : Action n r) : ℝ :=
  ∫ ω, payoff v Γ.g Γ.G (deviated i a ω) Γ.policy ω.2 i ∂Γ.sampleLaw

def envelope (Γ : FiniteGame m n c r Seed) (i : Fin m) (v : ℝ) : ℝ :=
  sSup (Set.range (Γ.purePayoff i v))

def UsersOptimal (Γ : FiniteGame m n c r Seed) : Prop :=
  ∀ i, ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, ∀ b, Γ.purePayoff i v b ≤ Γ.purePayoff i v a

def paymentError (Γ : FiniteGame m n c r Seed) (i : Fin m) (p : ℝ) (a : Action n r) : ℝ :=
  ∫ ω, shortfall p (deviated i a ω) Γ.policy ω.2 i ∂Γ.sampleLaw

def mixedOutcome (Γ : FiniteGame m n c r Seed) (i : Fin m)
    (ν : Measure (Action n r)) [IsProbabilityMeasure ν] : CountLaw n :=
  CountLaw.ofMeasure (ν.prod Γ.sampleLaw)
    (fun p : Action n r × Sample m n r Seed => Γ.focalCount i p.1 p.2)
    (Γ.measurable_focalCount_joint i)

def typeOutcome (Γ : FiniteGame m n c r Seed) (i : Fin m) (v : ℝ) : CountLaw n :=
  CountLaw.ofMeasure ((Γ.σ v).prod Γ.sampleLaw)
    (fun p : Action n r × Sample m n r Seed => Γ.focalCount i p.1 p.2)
    (Γ.measurable_focalCount_joint i)

def totalPayment (Γ : FiniteGame m n c r Seed) (i : Fin m) (a : Action n r) : ℝ :=
  ∫ ω, payment (deviated i a ω) Γ.policy ω.2 i +
    Γ.g * Γ.G.charge (count (deviated i a ω) Γ.policy ω.2 i) ∂Γ.sampleLaw

def coverage (Γ : FiniteGame m n c r Seed) : ℝ :=
  (∫ ω, ∑ i, successIndicator (count (fun l => (ω.1 l).2) Γ.policy ω.2 i) ∂Γ.sampleLaw) / m

def load (Γ : FiniteGame m n c r Seed) : ℝ :=
  (∫ ω, ∑ i, (count (fun l => (ω.1 l).2) Γ.policy ω.2 i : ℝ) ∂Γ.sampleLaw) / m

end FiniteGame
end FCAppendix.CommonReserve
