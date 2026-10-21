import FCAppendix.Affine.Uniform07Finishing.Native.OriginalLawTransport
import FCAppendix.Game.PosteriorFeasible

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.AllLists
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def clean (L : LocalList m) : LocalList m :=
  fun i=>if 0≤ entryBid (L i) then L i else none

lemma measurable_clean : Measurable (clean (m:=m)) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_le measurable_const (measurable_entryBid.comp (measurable_pi_apply i)))
    (measurable_pi_apply i) measurable_const

lemma clean_nonnegative (L : LocalList m) : NonnegativeList (clean L) := by
  intro i
  unfold clean
  split_ifs with h
  · exact h
  · exact le_rfl

lemma clean_eq (L : LocalList m) (h:NonnegativeList L) : clean L=L := by
  funext i
  simp only [clean,if_pos (h i)]

lemma clean_present (L : LocalList m) (i : Fin m) (hi:clean L i≠none) :
    clean L i=L i ∧ 0≤ entryBid (L i) ∧ L i≠none := by
  by_cases hb:0≤ entryBid (L i)
  · exact ⟨if_pos hb,hb,by simpa only [clean,if_pos hb] using hi⟩
  · exact (hi (if_neg hb)).elim

lemma clean_observe (x : Realization m n) (j : Fin n) : clean (observe x j)=observe x j := by
  apply clean_eq
  intro i
  unfold observe
  split_ifs
  · exact (x.action i).bid_nonneg
  · exact le_rfl

def policy (Γ : FiniteGame m n c Seed) (j : Fin n) : LocalPolicy m c Seed :=
  fun L s=>⟨(Γ.policy j (clean L) s).val,
    (Γ.policy j (clean L) s).property.1,
    fun i hi=>(clean_present L i ((Γ.policy j (clean L) s).property.2 i hi)).2.2⟩

lemma measurable_policy (Γ : FiniteGame m n c Seed) (j : Fin n) :
    Measurable (fun q : LocalList m×Seed=>(policy Γ j q.1 q.2).val) :=
  (Γ.policy_measurable j).comp ((measurable_clean.comp measurable_fst).prodMk measurable_snd)

def game (Γ : FiniteGame m n c Seed) : FiniteGame m n c Seed :=
  {Γ with policy:=policy Γ,policy_measurable:=measurable_policy Γ}

@[simp] lemma policy_observe (Γ : FiniteGame m n c Seed) (x : Realization m n)
    (j : Fin n) (s : Seed) :
    ((game Γ).policy j (observe x j) s).val=(Γ.policy j (observe x j) s).val := by
  change (Γ.policy j (clean (observe x j)) s).val=_
  rw [clean_observe]

@[simp] lemma allocation_eq (Γ : FiniteGame m n c Seed) (x : Realization m n)
    (s : Fin n→ Seed) (j : Fin n) : allocation x (game Γ).policy s j=allocation x Γ.policy s j :=
  policy_observe Γ x j (s j)

@[simp] lemma focalCount_eq (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (ω : Sample m n Seed) : focalCount (game Γ) i a ω=focalCount Γ i a ω := by
  apply Fin.ext
  simp only [focalCount,boundedCount,inclusionCount,accepted,allocation_eq]

@[simp] lemma outcome_eq (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n) :
    (problem (game Γ) i).outcome a=(problem Γ i).outcome a := by
  rw [problem_outcome,problem_outcome]
  exact CountLaw.ofMeasure_congr_ae (sampleLaw Γ) _ _ _ _
    (Filter.Eventually.of_forall (focalCount_eq Γ i a))

@[simp] lemma payoff_eq (Γ : FiniteGame m n c Seed) (i : Fin m) (v : ℝ) (a : JointAction n) :
    (problem (game Γ) i).payoff v a=(problem Γ i).payoff v a := by
  unfold Interim.Problem.payoff
  rw [outcome_eq]
  rfl

lemma users_optimal (Γ : FiniteGame m n c Seed) (hu:UsersOptimal Γ) : UsersOptimal (game Γ) := by
  apply (usersOptimal_iff_common_all_actions (game Γ)).mpr
  filter_upwards [(usersOptimal_iff_common_all_actions Γ).mp hu] with x hx
  intro i a
  simpa only [payoff_eq] using hx i a

lemma conditional_count_eq (Γ : FiniteGame m n c Seed) (hm:0< m) (v : ℝ) :
    conditionalTypeCountLaw (game Γ) hm v=conditionalTypeCountLaw Γ hm v := by
  unfold conditionalTypeCountLaw
  congr 1
  funext i
  apply FiniteLaw.ext
  intro r
  change (∫a,((problem (game Γ) i).outcome a).mass r ∂Γ.σ v)=
    ∫a,((problem Γ i).outcome a).mass r ∂Γ.σ v
  simp only [outcome_eq]

def posteriorKernel (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n) :
    Kernel (LocalList m) (UserProfile m n) := (B.posterior j).comap clean measurable_clean

instance posteriorKernel_markov (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) (j : Fin n) :
    IsMarkovKernel (posteriorKernel Γ B j) := by
  unfold posteriorKernel
  infer_instance

lemma posteriorKernel_apply (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (L : LocalList m) : posteriorKernel Γ B j L=B.posterior j (clean L) := rfl

lemma clean_ae_observed (Γ : FiniteGame m n c Seed) (j : Fin n) :
    ∀ᵐL∂observedListLaw Γ j,clean L=L := by
  apply (ae_map_iff (measurable_observe_draws j).aemeasurable
    (measurableSet_eq_lists measurable_clean measurable_id)).mpr
  exact Filter.Eventually.of_forall (fun d=>clean_observe (drawsRealization d) j)

def posterior (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : PosteriorSystem (game Γ) where
  posterior:=posteriorKernel Γ B
  markov:=posteriorKernel_markov Γ B
  on_path j:=by
    change (userProfileLaw Γ).map (fun d=>(observe (drawsRealization d) j,d))=
      (observedListLaw Γ j)⊗ₘposteriorKernel Γ B j
    rw [B.on_path j]
    apply Measure.compProd_congr
    filter_upwards [clean_ae_observed Γ j] with L hL
    rw [posteriorKernel_apply,hL]
  feasible j L hL:=by
    rw [posteriorKernel_apply,clean_eq L ((feasibleObservedList_iff_nonnegative j L).mp hL)]
    exact B.feasible j L hL

@[simp] lemma otherCount_eq (Γ : FiniteGame m n c Seed) (j : Fin n) (i : Fin m)
    (ω : Background m n Seed) : otherInclusionCount (game Γ) j i ω=otherInclusionCount Γ j i ω := by
  apply Fin.ext
  simp only [otherInclusionCount,allocation_eq]

lemma posterior_count_eq (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (j : Fin n) (L : LocalList m) (i : Fin m) :
    posteriorCountBelief (game Γ) (posterior Γ B) j L i=
      posteriorCountBelief Γ B j (clean L) i := by
  unfold posteriorCountBelief
  change FiniteLaw.ofMeasure (posteriorBackground Γ B j (clean L))
    (otherInclusionCount (game Γ) j i) _=FiniteLaw.ofMeasure _ (otherInclusionCount Γ j i) _
  exact FiniteLaw.ofMeasure_congr_ae _ _ _ _ _
    (Filter.Eventually.of_forall (otherCount_eq Γ j i))

lemma receipt_nonpos (A : Schedule n) (ν : FiniteLaw (Fin n)) {b : ℝ} (hb:b≤ 0) :
    Finite.conditionalReceipt A ν b≤ 0 := by
  apply ν.expect_le_const
  intro r
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hb (A.nonneg (r.val+1) (by omega))) (by positivity)

lemma receipt_clean_dominate (A : Schedule n) (ν : Fin m→ FiniteLaw (Fin n))
    (L : LocalList m) (i : Fin m) : beliefReceipts A ν L i≤ beliefReceipts A ν (clean L) i := by
  by_cases hi:0≤ entryBid (L i)
  · have hc : clean L i = L i := if_pos hi
    simp [beliefReceipts,hc]
  · cases he:L i with
    | none=>simp [he,entryBid] at hi
    | some b=>
      have hb:b≤ 0:=by simpa only [he,entryBid] using (le_of_not_ge hi)
      have hneg : ¬ 0 ≤ b := by simpa only [he,entryBid] using hi
      have hc : clean L i = none := by simp only [clean,he,entryBid,if_neg hneg]
      simpa only [beliefReceipts,he,hc] using receipt_nonpos A (ν i) hb

theorem proposer_optimal_all_lists (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (hopt:∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        (Γ.policy j L s).val) : PosteriorProposerOptimal (game Γ) (posterior Γ B) := by
  intro j L s
  let S:=(Γ.policy j (clean L) s).val
  let ν:=posteriorCountBelief Γ B j (clean L)
  have hh:=hopt j (clean L) ((feasibleObservedList_iff_nonnegative j _).mpr (clean_nonnegative L)) s
  have hbelief:posteriorCountBelief (game Γ) (posterior Γ B) j L=ν := by
    funext i
    exact posterior_count_eq Γ B j L i
  change Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief (game Γ) (posterior Γ B) j L) L) S
  rw [hbelief]
  refine ⟨hh.1,?_⟩
  intro T hT
  calc
    (∑i∈T,beliefReceipts Γ.A ν L i)≤∑i∈T,beliefReceipts Γ.A ν (clean L) i :=
      Finset.sum_le_sum (fun i _=>receipt_clean_dominate Γ.A ν L i)
    _≤∑i∈S,beliefReceipts Γ.A ν (clean L) i:=hh.2 T hT
    _=∑i∈S,beliefReceipts Γ.A ν L i:=by
      apply Finset.sum_congr rfl
      intro i hi
      have he:clean L i=L i:=(clean_present L i ((Γ.policy j (clean L) s).property.2 i hi)).1
      simp only [beliefReceipts,he]

theorem equilibrium_of_feasible (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ)
    (hu:UsersOptimal Γ)
    (hopt:∀j L,FeasibleObservedList j L→∀s,
      Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L)
        (Γ.policy j L s).val) : IsBayesianEquilibrium (game Γ) :=
  ⟨users_optimal Γ hu,⟨posterior Γ B,proposer_optimal_all_lists Γ B hopt⟩⟩

end FCAppendix.Affine.Uniform07Finishing.AllLists
