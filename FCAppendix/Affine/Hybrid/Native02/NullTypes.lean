import FCAppendix.Affine.Hybrid.Native02.OriginalPopulation
import FCAppendix.Game.PosteriorBeliefs

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem exists_measurable_common_conull (F : Measure ℝ) (P : ℝ→ Prop)
    (hP : ∀ᵐv ∂F,P v) :
    ∃S : Set ℝ,MeasurableSet S ∧ (∀ᵐv ∂F,v∈ S) ∧ ∀ v∈ S,P v := by
  let bad : Set ℝ := {v | ¬P v}
  let S : Set ℝ := (toMeasurable F bad)ᶜ
  have hbad : F bad=0 := by simpa only [bad] using ae_iff.mp hP
  have hnull : F (toMeasurable F bad)=0 := by
    rw [measure_toMeasurable,hbad]
  refine ⟨S,(measurableSet_toMeasurable F bad).compl,?_,?_⟩
  · rw [ae_iff]
    simpa only [S,mem_compl_iff,not_not,Set.setOf_mem_eq] using hnull
  · intro v hv
    by_contra h
    exact hv (subset_toMeasurable F bad h)

def nullTypeGame (G : FiniteGame m 2 c Seed) (S : Set ℝ) (hS : MeasurableSet S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) : FiniteGame m 2 c Seed where
  F:=G.F
  hF:=G.hF
  σ:=Kernel.piecewise hS G.σ (Kernel.deterministic action ha)
  hσ:=by infer_instance
  seedLaw:=G.seedLaw
  hseed:=G.hseed
  policy:=G.policy
  policy_measurable:=G.policy_measurable
  A:=G.A
  G:=G.G
  g:=G.g
  g_nonneg:=G.g_nonneg

theorem nullTypeGame_strategy_ae (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    (nullTypeGame G S hS action ha).σ=ᵐ[G.F]G.σ := by
  filter_upwards [hfull] with v hv
  rw [show (nullTypeGame G S hS action ha).σ v=G.σ v by
    simp only [nullTypeGame,Kernel.piecewise_apply,if_pos hv]]

theorem nullTypeGame_joint_law (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    (nullTypeGame G S hS action ha).F⊗ₘ(nullTypeGame G S hS action ha).σ=G.F⊗ₘG.σ := by
  exact Measure.compProd_congr (nullTypeGame_strategy_ae G S hS hfull action ha)

theorem nullTypeGame_user_law (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    userLaw (nullTypeGame G S hS action ha)=userLaw G := by
  rw [userLaw,userLaw,nullTypeGame_joint_law G S hS hfull action ha]

theorem nullTypeGame_profile_law (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    userProfileLaw (nullTypeGame G S hS action ha)=userProfileLaw G := by
  simp only [userProfileLaw,nullTypeGame_user_law G S hS hfull action ha]

theorem nullTypeGame_background_law (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    backgroundLaw (nullTypeGame G S hS action ha)=backgroundLaw G := by
  simp only [backgroundLaw,nullTypeGame_user_law G S hS hfull action ha]
  rfl

theorem nullTypeGame_sample_law (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    sampleLaw (nullTypeGame G S hS action ha)=sampleLaw G := by
  simp only [sampleLaw,nullTypeGame_background_law G S hS hfull action ha]

theorem nullTypeGame_outcome (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action)
    (i : Fin m) (dev : JointAction 2) :
    (problem (nullTypeGame G S hS action ha) i).outcome dev=(problem G i).outcome dev := by
  rw [problem_outcome,problem_outcome]
  have hs:=nullTypeGame_sample_law G S hS hfull action ha
  have hcount : focalCount (nullTypeGame G S hS action ha) i dev=focalCount G i dev := rfl
  simp only [hcount,hs]

theorem nullTypeGame_payoff (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action)
    (i : Fin m) (v : ℝ) (dev : JointAction 2) :
    (problem (nullTypeGame G S hS action ha) i).payoff v dev=(problem G i).payoff v dev := by
  unfold Interim.Problem.payoff
  rw [nullTypeGame_outcome G S hS hfull action ha]
  rfl

theorem nullTypeGame_users_optimal (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) (hIC : UsersOptimal G) :
    UsersOptimal (nullTypeGame G S hS action ha) := by
  intro i
  change ∀ᵐv ∂G.F,∀ᵐact ∂(nullTypeGame G S hS action ha).σ v,
    (problem (nullTypeGame G S hS action ha) i).BestResponse v act
  filter_upwards [hfull,hIC i] with v hv hvi
  rw [show (nullTypeGame G S hS action ha).σ v=G.σ v by
    simp only [nullTypeGame,Kernel.piecewise_apply,if_pos hv]]
  filter_upwards [hvi] with act hact
  intro dev
  simpa only [nullTypeGame_payoff G S hS hfull action ha] using hact dev

def nullTypePosterior (G : FiniteGame m 2 c Seed) (B : PosteriorSystem G)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    PosteriorSystem (nullTypeGame G S hS action ha) where
  posterior:=B.posterior
  markov:=B.markov
  on_path:=by
    intro j
    simpa only [observedListLaw,nullTypeGame_profile_law G S hS hfull action ha]
      using B.on_path j
  feasible:=B.feasible

theorem nullTypePosterior_receipts (G : FiniteGame m 2 c Seed) (B : PosteriorSystem G)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) (j : Fin 2) (L : LocalList m) :
    beliefReceipts (nullTypeGame G S hS action ha).A
      (posteriorCountBelief (nullTypeGame G S hS action ha)
        (nullTypePosterior G B S hS hfull action ha) j L) L=
      beliefReceipts G.A (posteriorCountBelief G B j L) L := rfl

theorem nullTypeGame_typeOutcome_outside (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) (i : Fin m)
    (v : ℝ) (hv : v∉S) :
    typeOutcome (nullTypeGame G S hS action ha) i v=(problem G i).outcome (action v) := by
  apply FiniteLaw.ext
  intro r
  change (∫act,((problem (nullTypeGame G S hS action ha) i).outcome act).mass r
    ∂(nullTypeGame G S hS action ha).σ v)=_
  rw [show (nullTypeGame G S hS action ha).σ v=Measure.dirac (action v) by
    simp only [nullTypeGame,Kernel.piecewise_apply,if_neg hv,Kernel.deterministic_apply]]
  rw [integral_dirac]
  rw [nullTypeGame_outcome G S hS hfull action ha]

theorem nullTypeGame_typeOutcome_inside (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) (i : Fin m)
    (v : ℝ) (hv : v∈ S) :
    typeOutcome (nullTypeGame G S hS action ha) i v=typeOutcome G i v := by
  apply FiniteLaw.ext
  intro r
  change (∫act,((problem (nullTypeGame G S hS action ha) i).outcome act).mass r
    ∂(nullTypeGame G S hS action ha).σ v)=∫act,((problem G i).outcome act).mass r ∂G.σ v
  simp only [nullTypeGame_outcome G S hS hfull action ha]
  have hs : (nullTypeGame G S hS action ha).σ v=G.σ v := by
    simp only [nullTypeGame,Kernel.piecewise_apply,if_pos hv]
  rw [hs]

theorem nullTypeGame_finiteLoad (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    finiteLoad (nullTypeGame G S hS action ha)=finiteLoad G := by
  have hp : profileLoad (nullTypeGame G S hS action ha)=profileLoad G := rfl
  rw [finiteLoad,finiteLoad,hp,nullTypeGame_profile_law G S hS hfull action ha]

theorem nullTypeGame_finiteCoverage (G : FiniteGame m 2 c Seed)
    (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂G.F,v∈ S)
    (action : ℝ→ JointAction 2) (ha : Measurable action) :
    finiteCoverage (nullTypeGame G S hS action ha)=finiteCoverage G := by
  have hp : profileCoverage (nullTypeGame G S hS action ha)=profileCoverage G := rfl
  rw [finiteCoverage,finiteCoverage,hp,nullTypeGame_profile_law G S hS hfull action ha]

theorem fixed_value_limits_after_null_patch {M C : ℕ→ℕ}
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (F : Measure ℝ)
    (hF : ∀ k,(G k).F=F) (S : Set ℝ) (hS : MeasurableSet S) (hfull : ∀ᵐv ∂F,v∈ S)
    (action : ℕ→ℝ→ JointAction 2) (ha : ∀ k,Measurable (action k))
    (K : Set ℝ) (limit : ℝ→ Fin 3→ℝ)
    (hinside : ∀ v∈ K,v∈ S→∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r) atTop (𝓝 (limit v r)))
    (houtside : ∀ v∈ K,v∉S→∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>((problem (G k) (i k)).outcome (action k v)).mass r)
        atTop (𝓝 (limit v r))) :
    ∀ v∈ K,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (nullTypeGame (G k) S hS (action k) (ha k)) (i k) v).mass r)
        atTop (𝓝 (limit v r)) := by
  intro v hv i r
  have hfullk (k : ℕ) : ∀ᵐv ∂(G k).F,v∈ S := by simpa only [hF k] using hfull
  by_cases hs : v∈ S
  · simpa only [nullTypeGame_typeOutcome_inside (G _) S hS (hfullk _) (action _) (ha _) _ v hs]
      using hinside v hv hs i r
  · simpa only [nullTypeGame_typeOutcome_outside (G _) S hS (hfullk _) (action _) (ha _) _ v hs]
      using houtside v hv hs i r

end FCAppendix.Affine.Hybrid.Native02
