import FCAppendix.Game.PosteriorFeasible

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.PosteriorCore
open MeasureTheory ProbabilityTheory Game Bayes Set Filter

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def profileSet (G : Fin n → Set (LocalList m)) : Set (UserProfile m n) :=
  {x | ∀ j, observe (drawsRealization x) j ∈ G j}

theorem measurableSet_profileSet (G : Fin n → Set (LocalList m))
    (hG : ∀ j, MeasurableSet (G j)) : MeasurableSet (profileSet G) := by
  simp only [profileSet, setOf_forall]
  exact MeasurableSet.iInter fun j => (hG j).preimage (measurable_observe_draws j)

def step (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (j : Fin n) : Set (LocalList m) :=
  G j ∩ {L | B.posterior j L (profileSet G)ᶜ = 0}

theorem measurableSet_step (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j)) (j : Fin n) :
    MeasurableSet (step Γ B G j) := by
  exact (hG j).inter (measurableSet_eq_fun
    ((B.posterior j).measurable_coe (measurableSet_profileSet G hG).compl)
    measurable_const)

theorem ae_profileSet (Γ : FiniteGame m n c Seed)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j))
    (hfull : ∀ j, ∀ᵐ L ∂observedListLaw Γ j, L ∈ G j) :
    ∀ᵐ x ∂userProfileLaw Γ, x ∈ profileSet G := by
  apply ae_all_iff.mpr
  intro j
  exact (ae_map_iff (measurable_observe_draws j).aemeasurable (hG j)).mp (hfull j)

theorem ae_step (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j))
    (hfull : ∀ j, ∀ᵐ L ∂observedListLaw Γ j, L ∈ G j) (j : Fin n) :
    ∀ᵐ L ∂observedListLaw Γ j, L ∈ step Γ B G j := by
  have hp := B.ae_posterior_of_ae Γ j (fun x => x ∈ profileSet G)
    (measurableSet_profileSet G hG) (ae_profileSet Γ G hG hfull)
  filter_upwards [hfull j, hp] with L hL hpL
  exact ⟨hL, ae_iff.mp hpL⟩

def stage (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) : ℕ → Fin n → Set (LocalList m)
  | 0 => G
  | k+1 => step Γ B (stage Γ B G k)

theorem measurableSet_stage (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j))
    (k : ℕ) (j : Fin n) : MeasurableSet (stage Γ B G k j) := by
  induction k generalizing j with
  | zero => exact hG j
  | succ k ih => exact measurableSet_step Γ B _ ih j

theorem ae_stage (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j))
    (hfull : ∀ j, ∀ᵐ L ∂observedListLaw Γ j, L ∈ G j) (k : ℕ) (j : Fin n) :
    ∀ᵐ L ∂observedListLaw Γ j, L ∈ stage Γ B G k j := by
  induction k generalizing j with
  | zero => exact hfull j
  | succ k ih => exact ae_step Γ B _ (measurableSet_stage Γ B G hG k) ih j

def core (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (j : Fin n) : Set (LocalList m) :=
  ⋂ k : ℕ, stage Γ B G k j

theorem measurableSet_core (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j)) (j : Fin n) :
    MeasurableSet (core Γ B G j) :=
  MeasurableSet.iInter (fun k => measurableSet_stage Γ B G hG k j)

theorem ae_core (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (hG : ∀ j, MeasurableSet (G j))
    (hfull : ∀ j, ∀ᵐ L ∂observedListLaw Γ j, L ∈ G j) (j : Fin n) :
    ∀ᵐ L ∂observedListLaw Γ j, L ∈ core Γ B G j := by
  have hh := ae_all_iff.mpr (fun k => ae_stage Γ B G hG hfull k j)
  exact hh.mono fun _ h => mem_iInter.mpr h

theorem core_subset (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (j : Fin n) : core Γ B G j ⊆ G j := by
  intro L hL
  exact mem_iInter.mp hL 0

theorem core_posterior (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (G : Fin n → Set (LocalList m)) (j : Fin n) (L : LocalList m)
    (hL : L ∈ core Γ B G j) :
    ∀ᵐ x ∂B.posterior j L, ∀ l, observe (drawsRealization x) l ∈ core Γ B G l := by
  have hh : ∀ k : ℕ, ∀ᵐ x ∂B.posterior j L,
      ∀ l, observe (drawsRealization x) l ∈ stage Γ B G k l := by
    intro k
    have hs := mem_iInter.mp hL (k+1)
    exact ae_iff.mpr hs.2
  filter_upwards [ae_all_iff.mpr hh] with x hx
  intro l
  exact mem_iInter.mpr fun k => hx k l

end FCAppendix.Appendix08.GeneralLow.PosteriorCore
