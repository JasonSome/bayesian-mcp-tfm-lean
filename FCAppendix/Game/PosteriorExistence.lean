import FCAppendix.Game.PosteriorBeliefs
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Lemmas

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Set

theorem standardBorel_of_measurableEquiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace β]
    (e : α ≃ᵐ β) : StandardBorelSpace α := by
  letI := upgradeStandardBorel β
  letI : TopologicalSpace α := TopologicalSpace.induced e inferInstance
  refine ⟨⟨inferInstance, ?_, e.toEquiv.polishSpace_induced⟩⟩
  refine ⟨?_⟩
  change ‹MeasurableSpace α› = @borel α (TopologicalSpace.induced e inferInstance)
  rw [borel_comap, ← BorelSpace.measurable_eq]
  exact e.measurableEmbedding.comap_eq.symm

def jointActionCode (n : ℕ) :
    JointAction n ≃ᵐ (Ici (0 : ℝ) × {k : ℕ // k ≤ n}) where
  toFun a := (⟨a.bid, a.bid_nonneg⟩, ⟨a.routeCount, a.routeCount_le⟩)
  invFun x := ⟨x.1.val, x.1.property, x.2.val, x.2.property⟩
  left_inv a := by cases a; rfl
  right_inv x := by cases x; rfl
  measurable_toFun := by
    exact (measurable_bid n).subtype_mk.prodMk (measurable_routeCount n).subtype_mk
  measurable_invFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap
      (fun x : Ici (0 : ℝ) × {k : ℕ // k ≤ n} =>
        (⟨x.1.val, x.1.property, x.2.val, x.2.property⟩ : JointAction n))
      (MeasurableSpace.comap (fun a : JointAction n => (a.bid, a.routeCount))
        inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    exact ((measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)).comap_le

instance standardBorelJointAction (n : ℕ) : StandardBorelSpace (JointAction n) := by
  letI : StandardBorelSpace (Ici (0 : ℝ)) := measurableSet_Ici.standardBorel
  letI : StandardBorelSpace {k : ℕ // k ≤ n} :=
    (measurableSet_le measurable_id measurable_const).standardBorel
  exact standardBorel_of_measurableEquiv (jointActionCode n)

instance nonemptyUserDraw (n : ℕ) : Nonempty (UserDraw n) :=
  ⟨((0, Interim.abstain n), Equiv.refl _)⟩

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def regularUserPosterior (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Kernel (LocalList m) (UserProfile m n) :=
  condDistrib id (fun d => observe (drawsRealization d) j) (userProfileLaw Γ)

instance (Γ : FiniteGame m n c Seed) (j : Fin n) :
    IsMarkovKernel (regularUserPosterior Γ j) := by
  unfold regularUserPosterior
  infer_instance

theorem regularUserPosterior_disintegrates (Γ : FiniteGame m n c Seed) (j : Fin n) :
    (userProfileLaw Γ).map (fun d => (observe (drawsRealization d) j, d)) =
      (observedListLaw Γ j) ⊗ₘ regularUserPosterior Γ j := by
  exact (compProd_map_condDistrib (μ := userProfileLaw Γ)
    (X := fun d => observe (drawsRealization d) j) measurable_id.aemeasurable).symm

end FCAppendix.Bayes
