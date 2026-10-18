import FCAppendix.Game.PosteriorExistence

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Set Filter

noncomputable section

def entryBid : Option ℝ → ℝ
  | none => 0
  | some b => b

theorem measurable_entryBid : Measurable entryBid := by
  intro s hs
  change MeasurableSet s
  exact hs

def completedAction (n : ℕ) : Option ℝ → JointAction n
  | none => Interim.abstain n
  | some b => ⟨max b 0, le_max_right _ _, n, le_rfl⟩

theorem measurable_completedAction (n : ℕ) : Measurable (completedAction n) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  change MeasurableSpace.comap
    (fun o : Option ℝ => ((completedAction n o).bid, (completedAction n o).routeCount))
      inferInstance ≤ _
  apply Measurable.comap_le
  intro s hs
  change MeasurableSet ((fun b : ℝ => (max b 0, n)) ⁻¹' s)
  exact ((measurable_id.max measurable_const).prodMk measurable_const) hs

def completedProfile (m n : ℕ) (ℓ : LocalList m) : UserProfile m n :=
  fun i => ((0, completedAction n (ℓ i)), Equiv.refl _)

theorem measurable_completedProfile (m n : ℕ) : Measurable (completedProfile m n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_const.prodMk
    ((measurable_completedAction n).comp (measurable_pi_apply i))).prodMk measurable_const

def NonnegativeList {m : ℕ} (ℓ : LocalList m) : Prop := ∀ i, 0 ≤ entryBid (ℓ i)

theorem measurableSet_nonnegativeList (m : ℕ) :
    MeasurableSet {ℓ : LocalList m | NonnegativeList ℓ} := by
  simp only [NonnegativeList, setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le (measurable_const (a := (0 : ℝ)))
    (measurable_entryBid.comp (measurable_pi_apply i))

theorem observe_completedProfile {m n : ℕ} (j : Fin n) (ℓ : LocalList m)
    (hℓ : NonnegativeList ℓ) : observe (drawsRealization (completedProfile m n ℓ)) j = ℓ := by
  funext i
  cases he : ℓ i with
  | none => simp [observe, drawsRealization, completedProfile, completedAction, he,
      Interim.abstain, mem_firstK]
  | some b =>
    have hb : 0 ≤ b := by simpa only [he, entryBid] using hℓ i
    simp [observe, drawsRealization, completedProfile, completedAction, he,
      mem_firstK, max_eq_left hb, j.isLt]

theorem feasibleObservedList_iff_nonnegative {m n : ℕ} (j : Fin n) (ℓ : LocalList m) :
    FeasibleObservedList j ℓ ↔ NonnegativeList ℓ := by
  constructor
  · rintro ⟨d, rfl⟩ i
    unfold observe
    split
    · exact (d i).1.2.bid_nonneg
    · exact le_rfl
  · intro hℓ
    exact ⟨completedProfile m n ℓ, observe_completedProfile j ℓ hℓ⟩

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def broadcastFallback (m n : ℕ) : Kernel (LocalList m) (UserProfile m n) :=
  Kernel.deterministic (completedProfile m n) (measurable_completedProfile m n)

instance (m n : ℕ) : IsMarkovKernel (broadcastFallback m n) := by
  unfold broadcastFallback
  infer_instance

theorem broadcastFallback_feasible (j : Fin n) (ℓ : LocalList m)
    (hℓ : FeasibleObservedList j ℓ) :
    ∀ᵐ d ∂broadcastFallback m n ℓ, observe (drawsRealization d) j = ℓ := by
  rw [broadcastFallback, Kernel.deterministic_apply]
  apply (ae_dirac_iff (measurableSet_eq_lists (measurable_observe_draws j) measurable_const)).mpr
  exact observe_completedProfile j ℓ ((feasibleObservedList_iff_nonnegative j ℓ).mp hℓ)

def goodPosteriorLists (Γ : FiniteGame m n c Seed) (P : Set (UserProfile m n))
    (j : Fin n) : Set (LocalList m) :=
  {ℓ | regularUserPosterior Γ j ℓ
    {d | ¬(observe (drawsRealization d) j = ℓ ∧ d ∈ P)} = 0}

theorem measurableSet_goodPosteriorLists (Γ : FiniteGame m n c Seed)
    {P : Set (UserProfile m n)} (hP : MeasurableSet P) (j : Fin n) :
    MeasurableSet (goodPosteriorLists Γ P j) := by
  have hgraph : MeasurableSet {p : LocalList m × UserProfile m n |
      ¬(observe (drawsRealization p.2) j = p.1 ∧ p.2 ∈ P)} :=
    ((measurableSet_eq_lists ((measurable_observe_draws j).comp measurable_snd)
      measurable_fst).inter (measurable_snd hP)).compl
  exact measurableSet_eq_fun (Kernel.measurable_kernel_prodMk_left hgraph) measurable_const

theorem ae_goodPosteriorLists (Γ : FiniteGame m n c Seed)
    {P : Set (UserProfile m n)} (hP : MeasurableSet P)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ P) (j : Fin n) :
    ∀ᵐ ℓ ∂observedListLaw Γ j, ℓ ∈ goodPosteriorLists Γ P j := by
  have hgraph : MeasurableSet {p : LocalList m × UserProfile m n |
      observe (drawsRealization p.2) j = p.1 ∧ p.2 ∈ P} :=
    (measurableSet_eq_lists ((measurable_observe_draws j).comp measurable_snd)
      measurable_fst).inter (measurable_snd hP)
  have hgood : ∀ᵐ ℓ ∂observedListLaw Γ j,
      ∀ᵐ d ∂regularUserPosterior Γ j ℓ,
        observe (drawsRealization d) j = ℓ ∧ d ∈ P := by
    apply Measure.ae_ae_of_ae_compProd (μ := observedListLaw Γ j)
      (κ := regularUserPosterior Γ j)
      (p := fun p => observe (drawsRealization p.2) j = p.1 ∧ p.2 ∈ P)
    rw [← regularUserPosterior_disintegrates Γ j]
    apply (ae_map_iff ((measurable_observe_draws j).prodMk measurable_id).aemeasurable
      hgraph).mpr
    exact hfull.mono fun _ hd => ⟨rfl, hd⟩
  exact hgood.mono fun _ hd => ae_iff.mp hd

noncomputable def posteriorWithFallbackKernel (Γ : FiniteGame m n c Seed)
    {P : Set (UserProfile m n)} (hP : MeasurableSet P)
    (fallback : Fin n → Kernel (LocalList m) (UserProfile m n))
    (j : Fin n) : Kernel (LocalList m) (UserProfile m n) := by
  classical
  exact Kernel.piecewise (measurableSet_goodPosteriorLists Γ hP j)
    (regularUserPosterior Γ j) (fallback j)

instance (Γ : FiniteGame m n c Seed) {P : Set (UserProfile m n)}
    (hP : MeasurableSet P) (fallback : Fin n → Kernel (LocalList m) (UserProfile m n))
    [∀ j, IsMarkovKernel (fallback j)] (j : Fin n) :
    IsMarkovKernel (posteriorWithFallbackKernel Γ hP fallback j) := by
  unfold posteriorWithFallbackKernel
  infer_instance

noncomputable def posteriorWithFallback (Γ : FiniteGame m n c Seed)
    {P : Set (UserProfile m n)} (hP : MeasurableSet P)
    (hfull : ∀ᵐ d ∂userProfileLaw Γ, d ∈ P)
    (fallback : Fin n → Kernel (LocalList m) (UserProfile m n))
    [∀ j, IsMarkovKernel (fallback j)]
    (hfeasible : ∀ j ℓ, FeasibleObservedList j ℓ →
      ∀ᵐ d ∂fallback j ℓ, observe (drawsRealization d) j = ℓ) : PosteriorSystem Γ where
  posterior := posteriorWithFallbackKernel Γ hP fallback
  markov := fun _ => inferInstance
  on_path j := by
    have he : posteriorWithFallbackKernel Γ hP fallback j =ᵐ[observedListLaw Γ j]
        regularUserPosterior Γ j := by
      filter_upwards [ae_goodPosteriorLists Γ hP hfull j] with ℓ hℓ
      simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hℓ]
    exact (regularUserPosterior_disintegrates Γ j).trans (Measure.compProd_congr he).symm
  feasible j ℓ hℓ := by
    classical
    by_cases hg : ℓ ∈ goodPosteriorLists Γ P j
    · simp only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_pos hg]
      have hgood : ∀ᵐ d ∂regularUserPosterior Γ j ℓ,
          observe (drawsRealization d) j = ℓ ∧ d ∈ P := ae_iff.mpr hg
      exact hgood.mono fun _ hd => hd.1
    · simpa only [posteriorWithFallbackKernel, Kernel.piecewise_apply, if_neg hg]
        using hfeasible j ℓ hℓ

theorem exists_posteriorSystem (Γ : FiniteGame m n c Seed) : Nonempty (PosteriorSystem Γ) := by
  exact ⟨posteriorWithFallback Γ MeasurableSet.univ (Eventually.of_forall fun _ => mem_univ _)
    (fun _ => broadcastFallback m n) broadcastFallback_feasible⟩

end
end FCAppendix.Bayes
