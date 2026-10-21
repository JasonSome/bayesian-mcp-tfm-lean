import FCAppendix.Game.JointMeasurability
import FCAppendix.Game.PosteriorBeliefs
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def submittedBidMeasure (Γ : FiniteGame m n c Seed) : Measure ℝ :=
  (Γ.F ⊗ₘ Γ.σ).map (fun x : ℝ × JointAction n => x.2.bid)

def contactsProposer (j : Fin n) : Set (UserDraw n) :=
  {d | j ∈ firstK d.2 d.1.2.routeCount}

def visibleBidMeasure (Γ : FiniteGame m n c Seed) (j : Fin n) : Measure ℝ :=
  ((userLaw Γ).restrict (contactsProposer j)).map
    (fun d : UserDraw n => d.1.2.bid)

theorem measurable_draw_bid : Measurable (fun d : UserDraw n => d.1.2.bid) :=
  (measurable_bid n).comp (measurable_snd.comp measurable_fst)

theorem measurableSet_contactsProposer (j : Fin n) :
    MeasurableSet (contactsProposer j) := by
  exact (measurable_snd.prodMk
    ((measurable_routeCount n).comp (measurable_snd.comp measurable_fst)))
      (measurableSet_mem_firstK j)

theorem actual_draw_bid_ne (Γ : FiniteGame m n c Seed)
    [NullSingletonClass (submittedBidMeasure Γ)] (b : ℝ) :
    ∀ᵐ d ∂userLaw Γ, d.1.2.bid ≠ b := by
  have hm : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  have hz : (Γ.F ⊗ₘ Γ.σ) {x : ℝ × JointAction n | x.2.bid = b} = 0 := by
    have h := measure_singleton (μ := submittedBidMeasure Γ) b
    simpa only [submittedBidMeasure, Measure.map_apply hm (measurableSet_singleton b),Set.preimage,Set.mem_singleton_iff] using h
  have ha : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.bid ≠ b :=
    measure_eq_zero_iff_ae_notMem.mp hz
  exact (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw n)).quasiMeasurePreserving.ae ha

theorem visibleBidMeasure_atomless (Γ : FiniteGame m n c Seed)
    [NullSingletonClass (submittedBidMeasure Γ)] (j : Fin n) :
    NullSingletonClass (visibleBidMeasure Γ j) := by
  constructor
  intro b
  rw [visibleBidMeasure, Measure.map_apply measurable_draw_bid (measurableSet_singleton b)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  exact ae_restrict_of_ae (actual_draw_bid_ne Γ b)

def VisibleAtomless (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ j : Fin n, NullSingletonClass (visibleBidMeasure Γ j)

theorem visibleAtomless_of_submitted (Γ : FiniteGame m n c Seed)
    [NullSingletonClass (submittedBidMeasure Γ)] : VisibleAtomless Γ :=
  visibleBidMeasure_atomless Γ

theorem usersOptimal_iff_common_all_actions (Γ : FiniteGame m n c Seed) :
    UsersOptimal Γ ↔
      ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ i : Fin m, ∀ a' : JointAction n,
        (problem Γ i).payoff x.1 a' ≤ (problem Γ i).payoff x.1 x.2 := by
  constructor
  · intro hu
    have h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ i : Fin m,
        (problem Γ i).BestResponse x.1 x.2 :=
      ae_all_iff.mpr (fun i => ae_bestResponse_compProd Γ hu i)
    exact h
  · intro h i
    have hi : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), (problem Γ i).BestResponse x.1 x.2 :=
      h.mono (fun _ hx => hx i)
    exact Measure.ae_ae_of_ae_compProd hi

theorem common_all_actions_after_disintegration (Γ : FiniteGame m n c Seed)
    (hu : UsersOptimal Γ) :
    ∀ᵐ v ∂Γ.F, ∀ᵐ a ∂Γ.σ v, ∀ i : Fin m, ∀ a' : JointAction n,
      (problem Γ i).payoff v a' ≤ (problem Γ i).payoff v a :=
  Measure.ae_ae_of_ae_compProd ((usersOptimal_iff_common_all_actions Γ).mp hu)

end FCAppendix.Affine.Uniform07Finishing
