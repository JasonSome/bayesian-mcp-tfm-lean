import FCAppendix.Game.PosteriorFeasible
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Affine.Tail04.FeasibleListNormalization
open MeasureTheory ProbabilityTheory Set Filter Game Bayes Classical
open scoped BigOperators

def cleanEntry : Option ℝ → Option ℝ
  | none => none
  | some b => if 0≤ b then some b else none

theorem measurable_cleanEntry : Measurable cleanEntry := by
  intro S hS
  change MeasurableSet ((fun b : ℝ => if 0≤ b then some b else none) ⁻¹' S)
  exact (Measurable.ite measurableSet_Ici measurable_some measurable_const) hS

def cleanList {m : ℕ} (L : LocalList m) : LocalList m := fun i => cleanEntry (L i)

theorem measurable_cleanList {m : ℕ} : Measurable (cleanList (m:=m)) :=
  measurable_pi_lambda _ (fun i => measurable_cleanEntry.comp (measurable_pi_apply i))

theorem cleanList_nonnegative {m : ℕ} (L : LocalList m) : NonnegativeList (cleanList L) := by
  intro i
  cases he : L i with
  | none => simp [cleanList,cleanEntry,he,entryBid]
  | some b =>
    by_cases hb : 0≤ b <;> simp [cleanList,cleanEntry,he,hb,entryBid]

theorem cleanList_eq {m : ℕ} (L : LocalList m) (hL : NonnegativeList L) : cleanList L=L := by
  funext i
  cases he : L i with
  | none => simp [cleanList,cleanEntry,he]
  | some b =>
    have hb : 0≤ b := by simpa only [he,entryBid] using hL i
    simp [cleanList,cleanEntry,he,hb]

theorem cleanList_present {m : ℕ} (L : LocalList m) (i : Fin m)
    (hi : cleanList L i≠none) : L i≠none ∧ cleanList L i=L i := by
  cases he : L i with
  | none => simp [cleanList,cleanEntry,he] at hi
  | some b =>
    by_cases hb : 0≤ b
    · simp [cleanList,cleanEntry,he,hb]
    · simp [cleanList,cleanEntry,he,hb] at hi

theorem nonnegative_observe {m n : ℕ} (x : Realization m n) (j : Fin n) :
    NonnegativeList (observe x j) := by
  intro i
  unfold observe
  split_ifs
  · exact (x.action i).bid_nonneg
  · exact le_rfl

section Native
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (Γ : FiniteGame m n c Seed)

def policy (j : Fin n) : LocalPolicy m c Seed := fun L s =>
  ⟨(Γ.policy j (cleanList L) s).val,(Γ.policy j (cleanList L) s).property.1,
    fun i hi => (cleanList_present L i ((Γ.policy j (cleanList L) s).property.2 i hi)).1⟩

theorem measurable_policy (j : Fin n) :
    Measurable (fun p : LocalList m×Seed => (policy Γ j p.1 p.2).val) :=
  (Γ.policy_measurable j).comp
    ((measurable_cleanList.comp measurable_fst).prodMk measurable_snd)

def game : FiniteGame m n c Seed :=
  {Γ with policy:=policy Γ,policy_measurable:=measurable_policy Γ}

theorem allocation_eq (x : Realization m n) (s : Fin n → Seed) (j : Fin n) :
    allocation x (game Γ).policy s j=allocation x Γ.policy s j := by
  change (Γ.policy j (cleanList (observe x j)) (s j)).val=_
  rw [cleanList_eq _ (nonnegative_observe x j)]
  rfl

theorem focalCount_eq (i : Fin m) (act : JointAction n) (ω : Sample m n Seed) :
    focalCount (game Γ) i act ω=focalCount Γ i act ω := by
  apply Fin.ext
  simp only [focalCount,boundedCount,inclusionCount_eq_sum,allocation_eq Γ]

theorem problem_eq (i : Fin m) : problem (game Γ) i=problem Γ i := by
  have hc : focalCount (game Γ) i=focalCount Γ i := by
    funext act ω
    exact focalCount_eq Γ i act ω
  unfold problem
  simp only [hc]
  rfl

theorem conditionalCount_eq (hm : 0< m) (v : ℝ) :
    conditionalTypeCountLaw (game Γ) hm v=conditionalTypeCountLaw Γ hm v := by
  apply FiniteLaw.ext
  intro r
  have he : (conditionalTypeCountLaw (game Γ) hm v).expect (fun z => if z=r then 1 else 0)=
      (conditionalTypeCountLaw Γ hm v).expect (fun z => if z=r then 1 else 0) := by
    rw [conditionalTypeCountLaw_expect,conditionalTypeCountLaw_expect]
    simp_rw [problem_eq Γ]
    rfl
  simpa only [FiniteLaw.expect_singleton] using he

def posteriorKernel (B : PosteriorSystem Γ) (j : Fin n) : Kernel (LocalList m) (UserProfile m n) where
  toFun L := B.posterior j (cleanList L)
  measurable' := (B.posterior j).measurable.comp measurable_cleanList

instance posteriorKernel_markov (B : PosteriorSystem Γ) (j : Fin n) :
    IsMarkovKernel (posteriorKernel Γ B j) where
  isProbabilityMeasure L := by change IsProbabilityMeasure (B.posterior j (cleanList L));infer_instance

theorem posteriorKernel_ae (B : PosteriorSystem Γ) (j : Fin n) :
    posteriorKernel Γ B j=ᵐ[observedListLaw Γ j] B.posterior j := by
  have hclean : ∀ᵐ L ∂observedListLaw Γ j,cleanList L=L := by
    apply (ae_map_iff (measurable_observe_draws j).aemeasurable
      (measurableSet_eq_lists measurable_cleanList measurable_id)).mpr
    exact Eventually.of_forall (fun d => cleanList_eq _ (nonnegative_observe _ j))
  exact hclean.mono (fun L hL => by change B.posterior j (cleanList L)=B.posterior j L;rw [hL])

def posterior (B : PosteriorSystem Γ) : PosteriorSystem (game Γ) where
  posterior := posteriorKernel Γ B
  markov := fun _ => inferInstance
  on_path j := by
    change (userProfileLaw Γ).map (fun d => (observe (drawsRealization d) j,d))=
      (observedListLaw Γ j)⊗ₘposteriorKernel Γ B j
    exact (B.on_path j).trans (Measure.compProd_congr (posteriorKernel_ae Γ B j)).symm
  feasible j L hL := by
    change ∀ᵐ d ∂B.posterior j (cleanList L),observe (drawsRealization d) j=L
    rw [cleanList_eq L ((feasibleObservedList_iff_nonnegative j L).mp hL)]
    exact B.feasible j L hL

theorem otherInclusionCount_eq (j : Fin n) (i : Fin m) (ω : Background m n Seed) :
    otherInclusionCount (game Γ) j i ω=otherInclusionCount Γ j i ω := by
  apply Fin.ext
  simp only [otherInclusionCount_eq_sum,allocation_eq Γ]

theorem posteriorCount_eq (B : PosteriorSystem Γ) (j : Fin n) (L : LocalList m) (i : Fin m) :
    posteriorCountBelief (game Γ) (posterior Γ B) j L i=
      posteriorCountBelief Γ B j (cleanList L) i := by
  have hc : otherInclusionCount (game Γ) j i=otherInclusionCount Γ j i := by
    funext ω
    exact otherInclusionCount_eq Γ j i ω
  unfold posteriorCountBelief
  simp only [hc]
  rfl

theorem receipt_nonpositive (A : Schedule n) (ν : FiniteLaw (Fin n)) (b : ℝ) (hb : b≤0) :
    Finite.conditionalReceipt A ν b≤0 := by
  apply ν.expect_le_const
  intro k
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hb (A.nonneg _ (by omega))) (by positivity)

theorem normalized_receipt_le (B : PosteriorSystem Γ) (j : Fin n) (L : LocalList m) (i : Fin m) :
    beliefReceipts (game Γ).A (posteriorCountBelief (game Γ) (posterior Γ B) j L) L i≤
      beliefReceipts Γ.A (posteriorCountBelief Γ B j (cleanList L)) (cleanList L) i := by
  cases he : L i with
  | none => simp [beliefReceipts,he,cleanList,cleanEntry]
  | some b =>
    by_cases hb : 0≤ b
    · simp only [beliefReceipts,he,cleanList,cleanEntry,if_pos hb,posteriorCount_eq Γ B]
      exact le_rfl
    · simp only [beliefReceipts,he,cleanList,cleanEntry,if_neg hb]
      exact receipt_nonpositive Γ.A _ b (le_of_not_ge hb)

theorem normalized_receipt_selected (B : PosteriorSystem Γ) (j : Fin n) (L : LocalList m)
    (s : Seed) (i : Fin m) (hi : i∈((game Γ).policy j L s).val) :
    beliefReceipts (game Γ).A (posteriorCountBelief (game Γ) (posterior Γ B) j L) L i=
      beliefReceipts Γ.A (posteriorCountBelief Γ B j (cleanList L)) (cleanList L) i := by
  have hp := (Γ.policy j (cleanList L) s).property.2 i hi
  have he := (cleanList_present L i hp).2
  unfold beliefReceipts
  rw [he]
  cases hentry : L i with
  | none => rfl
  | some b => rw [posteriorCount_eq Γ B];rfl

theorem proposers (B : PosteriorSystem Γ)
    (hB : ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        (Γ.policy j L s).val) :
    PosteriorProposerOptimal (game Γ) (posterior Γ B) := by
  intro j L s
  have hclean := hB j (cleanList L)
    ((feasibleObservedList_iff_nonnegative j (cleanList L)).mpr (cleanList_nonnegative L)) s
  refine ⟨hclean.1,?_⟩
  intro T hT
  calc
    _ ≤ ∑ i∈T,beliefReceipts Γ.A (posteriorCountBelief Γ B j (cleanList L)) (cleanList L) i :=
      Finset.sum_le_sum (fun i _ => normalized_receipt_le Γ B j L i)
    _ ≤ ∑ i∈(Γ.policy j (cleanList L) s).val,
        beliefReceipts Γ.A (posteriorCountBelief Γ B j (cleanList L)) (cleanList L) i := hclean.2 T hT
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (normalized_receipt_selected Γ B j L s i hi).symm

theorem equilibrium (husers : UsersOptimal Γ) (B : PosteriorSystem Γ)
    (hB : ∀ j L,FeasibleObservedList j L → ∀ s,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        (Γ.policy j L s).val) : IsBayesianEquilibrium (game Γ) := by
  refine ⟨?_,⟨posterior Γ B,proposers Γ B hB⟩⟩
  intro i
  change ∀ᵐ v ∂Γ.F,∀ᵐ act ∂Γ.σ v,(problem (game Γ) i).BestResponse v act
  rw [problem_eq Γ i]
  exact husers i

end Native
end FCAppendix.Affine.Tail04.FeasibleListNormalization
