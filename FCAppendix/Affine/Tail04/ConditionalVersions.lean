import FCAppendix.Game.JointMeasurability
import FCAppendix.Game.PosteriorFeasible

noncomputable section
namespace FCAppendix.Affine.Tail04.ConditionalVersions
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical

section CommonSet
variable {X A : Type*} [MeasurableSpace X]
  [TopologicalSpace A] [SecondCountableTopology A]

theorem common_all_actions (μ : Measure X) (u : X → A → ℝ) (w : X → ℝ)
    (hu : ∀ x, Continuous (u x))
    (hfixed : ∀ a, ∀ᵐ x ∂μ, u x a ≤ w x) :
    ∀ᵐ x ∂μ, ∀ a, u x a ≤ w x := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense A
  have hD : ∀ᵐ x ∂μ, ∀ a ∈ D, u x a ≤ w x :=
    (ae_ball_iff hDc).mpr (fun a _ => hfixed a)
  filter_upwards [hD] with x hx
  have hc : IsClosed {a | u x a ≤ w x} := isClosed_le (hu x) continuous_const
  have hcl := closure_minimal (fun a ha => hx a ha) hc
  intro a
  exact hcl (hDd.closure_eq ▸ mem_univ a)

theorem common_actions_on_countable_cover {I : Type*} [Countable I]
    (μ : Measure X) (S : I→ Set A) (hcover : ∀ a,∃ i,a∈S i)
    (u : X→ A→ℝ) (w : X→ℝ)
    (hu : ∀ x i,Continuous (fun a : S i => u x a.1))
    (hfixed : ∀ a,∀ᵐ x∂μ,u x a≤ w x) :
    ∀ᵐ x∂μ,∀ a,u x a≤ w x := by
  have hpieces : ∀ i,∀ᵐ x∂μ,∀ a : S i,u x a.1≤ w x := by
    intro i
    exact common_all_actions μ (fun x (a : S i) => u x a.1) w (fun x => hu x i)
      (fun (a : S i) => hfixed a.1)
  have hall : ∀ᵐ x∂μ,∀ i,∀ a : S i,u x a.1≤ w x := ae_all_iff.mpr hpieces
  filter_upwards [hall] with x hx
  intro a
  obtain ⟨i,hi⟩ := hcover a
  exact hx i ⟨a,hi⟩

theorem common_all_nonnegative_bids_and_routes (μ : Measure X)
    (u : X → ℝ → Fin 3 → ℝ) (w : X → ℝ)
    (hu : ∀ x k, Continuous (fun b : Ioi (0:ℝ) => u x b.1 k))
    (hfixed : ∀ b, 0 ≤ b → ∀ k, ∀ᵐ x ∂μ, u x b k ≤ w x) :
    ∀ᵐ x ∂μ, ∀ b, 0 ≤ b → ∀ k, u x b k ≤ w x := by
  have hp : ∀ k, ∀ᵐ x ∂μ, ∀ b : Ioi (0:ℝ), u x b.1 k ≤ w x := by
    intro k
    exact common_all_actions μ (fun x (b : Ioi (0:ℝ)) => u x b.1 k) w
      (fun x => hu x k) (fun (b : Ioi (0:ℝ)) => hfixed b.1 b.2.le k)
  have hpc : ∀ᵐ x ∂μ, ∀ k, ∀ b : Ioi (0:ℝ), u x b.1 k ≤ w x :=
    ae_all_iff.mpr hp
  have hz : ∀ᵐ x ∂μ, ∀ k, u x 0 k ≤ w x :=
    ae_all_iff.mpr (hfixed 0 le_rfl)
  filter_upwards [hpc,hz] with x hx hx0
  intro b hb k
  rcases eq_or_lt_of_le hb with he | he
  · simpa only [← he] using hx0 k
  · exact hx k ⟨b,he⟩
end CommonSet

section Repair
variable {V A : Type*} [MeasurableSpace V] [MeasurableSpace A]

def goodTypes (σ : Kernel V A) (S : Set (V × A)) : Set V :=
  {v | σ v {a | (v,a) ∉ S} = 0}

theorem measurableSet_goodTypes (σ : Kernel V A) [IsSFiniteKernel σ] {S : Set (V × A)}
    (hS : MeasurableSet S) : MeasurableSet (goodTypes σ S) :=
  measurableSet_eq_fun (Kernel.measurable_kernel_prodMk_left hS.compl) measurable_const

theorem goodTypes_spec (σ : Kernel V A) (S : Set (V × A))
    (v : V) (hv : v ∈ goodTypes σ S) : ∀ᵐ a ∂σ v, (v,a) ∈ S :=
  ae_iff.mpr hv

theorem ae_goodTypes (μ : Measure V) (σ : Kernel V A) (S : Set (V × A))
    (h : ∀ᵐ v ∂μ, ∀ᵐ a ∂σ v, (v,a) ∈ S) :
    ∀ᵐ v ∂μ, v ∈ goodTypes σ S :=
  h.mono (fun _ hv => ae_iff.mp hv)

def repair (σ : Kernel V A) [IsSFiniteKernel σ] {S : Set (V × A)} (hS : MeasurableSet S)
    (f : V → A) (hf : Measurable f) : Kernel V A :=
  Kernel.piecewise (measurableSet_goodTypes σ hS) σ (Kernel.deterministic f hf)

instance repair_isSFinite (σ : Kernel V A) [IsSFiniteKernel σ]
    {S : Set (V × A)} (hS : MeasurableSet S) (f : V → A) (hf : Measurable f) :
    IsSFiniteKernel (repair σ hS f hf) := by
  unfold repair
  infer_instance

instance repair_isMarkov (σ : Kernel V A) [IsMarkovKernel σ]
    {S : Set (V × A)} (hS : MeasurableSet S) (f : V → A) (hf : Measurable f) :
    IsMarkovKernel (repair σ hS f hf) := by
  unfold repair
  infer_instance

theorem repair_apply_good (σ : Kernel V A) [IsSFiniteKernel σ] {S : Set (V × A)}
    (hS : MeasurableSet S) (f : V → A) (hf : Measurable f)
    (v : V) (hv : v ∈ goodTypes σ S) : repair σ hS f hf v = σ v := by
  simp only [repair,Kernel.piecewise_apply,if_pos hv]

theorem repair_apply_bad (σ : Kernel V A) [IsSFiniteKernel σ] {S : Set (V × A)}
    (hS : MeasurableSet S) (f : V → A) (hf : Measurable f)
    (v : V) (hv : v ∉ goodTypes σ S) : repair σ hS f hf v = Measure.dirac (f v) := by
  simp only [repair,Kernel.piecewise_apply,if_neg hv,Kernel.deterministic_apply]

theorem repair_ae_eq (μ : Measure V) (σ : Kernel V A) [IsSFiniteKernel σ]
    {S : Set (V × A)} (hS : MeasurableSet S) (f : V → A) (hf : Measurable f)
    (h : ∀ᵐ v ∂μ, ∀ᵐ a ∂σ v, (v,a) ∈ S) : repair σ hS f hf =ᵐ[μ] σ := by
  filter_upwards [ae_goodTypes μ σ S h] with v hv
  exact repair_apply_good σ hS f hf v hv

theorem repair_compProd (μ : Measure V) [SFinite μ]
    (σ : Kernel V A) [IsSFiniteKernel σ]
    {S : Set (V × A)} (hS : MeasurableSet S) (f : V → A) (hf : Measurable f)
    (h : ∀ᵐ v ∂μ, ∀ᵐ a ∂σ v, (v,a) ∈ S) :
    μ ⊗ₘ repair σ hS f hf = μ ⊗ₘ σ :=
  Measure.compProd_congr (repair_ae_eq μ σ hS f hf h)

variable [MeasurableSingletonClass A]

theorem repair_fixed_value_support (σ : Kernel V A) [IsSFiniteKernel σ]
    {S : Set (V × A)} (hS : MeasurableSet S) (f : V → A) (hf : Measurable f)
    (v : V) : ∀ᵐ a ∂repair σ hS f hf v, (v,a) ∈ S ∨ a = f v := by
  by_cases hv : v ∈ goodTypes σ S
  · rw [repair_apply_good σ hS f hf v hv]
    exact (goodTypes_spec σ S v hv).mono (fun _ ha => Or.inl ha)
  · rw [repair_apply_bad σ hS f hf v hv]
    rw [ae_dirac_eq]
    exact Filter.mem_pure.mpr (Or.inr rfl)

theorem reference_regret_at_every_value (σ : Kernel V A) [IsSFiniteKernel σ]
    (u w : V × A → ℝ) (err : V → ℝ)
    (hS : MeasurableSet {p : V × A | ∀ a, u (p.1,a) ≤ u p})
    (f : V → A) (hf : Measurable f)
    (hmax : ∀ v a, w (v,a) ≤ w (v,f v))
    (herr0 : ∀ v, 0 ≤ err v)
    (herr : ∀ v a, |u (v,a)-w (v,a)| ≤ err v) :
    ∀ v, ∀ᵐ a ∂repair σ hS f hf v, ∀ b,
      w (v,b) ≤ w (v,a)+2*err v := by
  intro v
  have hs := repair_fixed_value_support σ hS f hf v
  filter_upwards [hs] with a ha
  intro b
  rcases ha with ha | rfl
  · have hba := ha b
    have hea := (abs_le.mp (herr v a)).2
    have heb := (abs_le.mp (herr v b)).1
    linarith
  · linarith [hmax v b,herr0 v]

end Repair

section MeasurableOptimalSet
variable {V A : Type*}
  [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [SecondCountableTopology A]

theorem measurableSet_allAction (u : V × A → ℝ) (hu : Continuous u) :
    MeasurableSet {p : V × A | ∀ a, u (p.1,a) ≤ u p} := by
  have he : {p : V × A | ∀ a, u (p.1,a) ≤ u p} =
      ⋂ a, {p | u (p.1,a) ≤ u p} := by ext p; simp
  rw [he]
  exact (isClosed_iInter (fun a => isClosed_le
    (hu.comp (continuous_fst.prodMk continuous_const)) hu)).measurableSet

omit [TopologicalSpace V] [BorelSpace V] [BorelSpace A] in
theorem measurableSet_allAction_on_countable_cover {I : Type*} [Countable I]
    (S : I→ Set A) (hcover : ∀ a,∃ i,a∈S i)
    (u : V×A→ℝ) (hu : Measurable u)
    (hcont : ∀ v i,Continuous (fun a : S i => u (v,a.1))) :
    MeasurableSet {p : V×A | ∀ a,u (p.1,a)≤ u p} := by
  choose D hDc hDd using (fun i : I => TopologicalSpace.exists_countable_dense (S i))
  have he : {p : V×A | ∀ a,u (p.1,a)≤ u p} =
      ⋂ i, ⋂ a∈D i, {p : V×A | u (p.1,a.1)≤ u p} := by
    ext p
    simp only [mem_setOf_eq,mem_iInter]
    constructor
    · intro hp i a _
      exact hp a.1
    · intro hp a
      obtain ⟨i,hi⟩ := hcover a
      have hc : IsClosed {b : S i | u (p.1,b.1)≤ u p} :=
        isClosed_le (hcont p.1 i) continuous_const
      have hsub : D i ⊆ {b : S i | u (p.1,b.1)≤ u p} := fun b hb => hp i b hb
      exact (closure_minimal hsub hc) ((hDd i).closure_eq ▸ mem_univ (⟨a,hi⟩ : S i))
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact MeasurableSet.biInter (hDc i) (fun a _ => measurableSet_le
    (hu.comp (measurable_fst.prodMk measurable_const)) hu)
end MeasurableOptimalSet

section Native
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def withStrategy (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ] : FiniteGame m n c Seed :=
  { Γ with σ := τ, hσ := inferInstance }

theorem withStrategy_joint (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) :
    (withStrategy Γ τ).F ⊗ₘ (withStrategy Γ τ).σ = Γ.F ⊗ₘ Γ.σ :=
  Measure.compProd_congr hτ

theorem withStrategy_userLaw (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) : userLaw (withStrategy Γ τ) = userLaw Γ := by
  unfold userLaw
  rw [withStrategy_joint Γ τ hτ]

theorem withStrategy_userProfileLaw (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) : userProfileLaw (withStrategy Γ τ) = userProfileLaw Γ := by
  simp only [userProfileLaw,withStrategy_userLaw Γ τ hτ]

theorem withStrategy_observedListLaw (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) (j : Fin n) :
    observedListLaw (withStrategy Γ τ) j = observedListLaw Γ j := by
  simp only [observedListLaw,withStrategy_userProfileLaw Γ τ hτ]

theorem withStrategy_sampleLaw (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) : sampleLaw (withStrategy Γ τ) = sampleLaw Γ := by
  simp only [sampleLaw,backgroundLaw,withStrategy_userLaw Γ τ hτ]
  rfl

theorem withStrategy_focalCount (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (i : Fin m) (a : JointAction n) :
    focalCount (withStrategy Γ τ) i a = focalCount Γ i a := rfl

theorem withStrategy_problem (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) (i : Fin m) :
    problem (withStrategy Γ τ) i = problem Γ i := by
  unfold problem
  simp only [withStrategy_sampleLaw Γ τ hτ]
  rfl

def withStrategy_posterior (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) (B : PosteriorSystem Γ) :
    PosteriorSystem (withStrategy Γ τ) where
  posterior := B.posterior
  markov := B.markov
  on_path j := by
    simpa only [withStrategy_userProfileLaw Γ τ hτ,
      withStrategy_observedListLaw Γ τ hτ] using B.on_path j
  feasible := B.feasible

theorem withStrategy_equilibrium (Γ : FiniteGame m n c Seed)
    (τ : Kernel ℝ (JointAction n)) [IsMarkovKernel τ]
    (hτ : τ =ᵐ[Γ.F] Γ.σ) (hΓ : IsBayesianEquilibrium Γ) :
    IsBayesianEquilibrium (withStrategy Γ τ) := by
  refine ⟨?_,?_⟩
  · intro i
    filter_upwards [hΓ.users i,hτ] with v hv he
    change ∀ᵐ a ∂τ v, (problem (withStrategy Γ τ) i).BestResponse v a
    rw [he,withStrategy_problem Γ τ hτ i]
    exact hv
  · obtain ⟨B,hB⟩ := hΓ.beliefs
    refine ⟨withStrategy_posterior Γ τ hτ B,?_⟩
    exact hB
end Native

end FCAppendix.Affine.Tail04.ConditionalVersions
