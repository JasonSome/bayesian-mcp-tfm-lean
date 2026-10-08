import FCAppendix.Ample.BoundaryInfiniteRate
import FCAppendix.Ample.ActualEventRate

noncomputable section
namespace FCAppendix.Ample.Shortage
open Finset

theorem iidLaw_eq_commonList {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (N : ℕ) : iidLaw μ N = CommonList.iid μ N := by
  apply FiniteLaw.ext
  intro x
  rfl

theorem hits_eq_includers {n N : ℕ} (x : Fin N → Finset (Fin n)) (j : Fin n) :
    hits x j = CommonList.includers j x := by
  rfl

theorem congestionProb_eq_simultaneous {n : ℕ}
    (μ : FiniteLaw (Finset (Fin n))) (N c : ℕ) (S : Finset (Fin n)) :
    congestionProb μ N c S = SimultaneousCongestion.congestionProb μ S N c := by
  rw [congestionProb, iidLaw_eq_commonList]
  congr 1

theorem congestionProb_contactLaw {n : ℕ} (lam : ℕ → ℝ) (hlam : ValidLaw n lam)
    (N c k : ℕ) :
    congestionProb (contactLaw n lam hlam) N c (selected n k) =
      congestProb n N c k lam := by
  rw [congestionProb_eq_simultaneous, contactLaw_congestionProb]
  rfl

theorem allMass_contactLaw_univ {n : ℕ} (hn : 0<n)
    (lam : ℕ → ℝ) (hlam : ValidLaw n lam) :
    allMass (contactLaw n lam hlam) Finset.univ = lam n := by
  classical
  have hpred (T : Finset (Fin n)) : (Finset.univ ⊆ T) ↔ T=Finset.univ :=
    ⟨fun h => Finset.Subset.antisymm (Finset.subset_univ T) h, fun h => by simp [h]⟩
  have hne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
    intro he
    have hx : (⟨0,hn⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    simp only [he, Finset.notMem_empty] at hx
  unfold allMass
  simp_rw [FiniteLaw.prob_eq_expect, hpred]
  rw [FiniteLaw.expect_singleton,contactLaw_mass,contactWeight_of_ne lam hne]
  simp

theorem allMass_contactLaw_one {n : ℕ} (hn : 0<n)
    (lam : ℕ → ℝ) (hlam : ValidLaw n lam) :
    allMass (contactLaw n lam hlam) (selected n 1)=contactMarginal n lam := by
  classical
  let j : Fin n := ⟨0,hn⟩
  have he : selected n 1={j} := by
    ext l
    simp only [selected,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
      Fin.ext_iff]
    change l.val<1 ↔ l.val=0
    omega
  rw [he,allMass]
  have hp : (fun T : Finset (Fin n) => {j}⊆T) = (fun T => j∈T) := by
    funext T
    exact propext Finset.singleton_subset_iff
  rw [hp]
  exact contactLaw_marginal n lam hlam j

theorem allHits_cons {n N : ℕ} (S T : Finset (Fin n))
    (x : Fin N → Finset (Fin n)) :
    allHits (Fin.cons T x) S = (if S ⊆ T then 1 else 0) + allHits x S := by
  classical
  unfold allHits
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

theorem allHits_expect_binomial {n : ℕ}
    (μ : FiniteLaw (Finset (Fin n))) (N : ℕ) (S : Finset (Fin n)) (φ : ℕ → ℝ) :
    (iidLaw μ N).expect (fun x => φ (allHits x S)) =
      (IndependentCounts.binomial N (allMass μ S)
        (μ.prob_nonneg (fun T => S ⊆ T)) (μ.prob_le_one (fun T => S ⊆ T))).expect
          (fun r => φ r.val) := by
  classical
  simp only [iidLaw_eq_commonList]
  induction N generalizing φ with
  | zero =>
    rw [CommonList.expect_iid_zero]
    simp [IndependentCounts.binomial, IndependentCounts.independentCount, allHits]
  | succ N ih =>
    rw [CommonList.expect_iid_succ, IndependentCounts.expect_binomial_succ]
    simp only [allHits_cons, IndependentCounts.val_add_false, IndependentCounts.val_add_true]
    set β := IndependentCounts.binomial N (allMass μ S)
      (μ.prob_nonneg (fun T => S ⊆ T)) (μ.prob_le_one (fun T => S ⊆ T))
    have hh : ∀ T : Finset (Fin n),
        (CommonList.iid μ N).expect (fun x => φ ((if S ⊆ T then 1 else 0) + allHits x S)) =
          (if S ⊆ T then 1 else 0) * β.expect (fun r => φ (1 + r.val)) +
            (1 - (if S ⊆ T then 1 else 0)) * β.expect (fun r => φ r.val) := by
      intro T
      rw [ih (fun r => φ ((if S ⊆ T then 1 else 0) + r))]
      by_cases hT : S ⊆ T <;> simp [hT]
    rw [FiniteLaw.expect_congr μ hh, FiniteLaw.expect_add, FiniteLaw.expect_mul_const,
      FiniteLaw.expect_mul_const, FiniteLaw.expect_sub, FiniteLaw.expect_const]
    have he : μ.expect (fun T => if S ⊆ T then (1 : ℝ) else 0) = allMass μ S := by
      exact (FiniteLaw.prob_eq_expect μ (fun T => S ⊆ T)).symm
    rw [he]
    ring

theorem allHits_tail_eq_binomial {n : ℕ}
    (μ : FiniteLaw (Finset (Fin n))) (N r : ℕ) (S : Finset (Fin n)) :
    (iidLaw μ N).prob (fun x => r ≤ allHits x S) =
      (IndependentCounts.binomial N (allMass μ S)
        (μ.prob_nonneg (fun T => S ⊆ T)) (μ.prob_le_one (fun T => S ⊆ T))).prob
          (fun x => r ≤ x.val) := by
  classical
  simp only [FiniteLaw.prob_eq_expect]
  exact allHits_expect_binomial μ N S (fun x => if r ≤ x then 1 else 0)

end FCAppendix.Ample.Shortage

namespace FCAppendix.Bayes.CompletionDraft
open MeasureTheory ProbabilityTheory Game Filter Set Topology
variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def allContactMass (Γ : FiniteGame (N + 1) n c Seed)
    (b : ℝ) (S : Finset (Fin n)) : ℝ :=
  Ample.Shortage.allMass (visibleLaw Γ b) S

theorem actual_joint_rejection_AM9
    (Γ : FiniteGame (N + 1) n c Seed) (hc : c ≤ N)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) {b : ℝ} (hb : 0 < b) (S : Finset (Fin n)) :
    allContactMass Γ b S ^ N ≤
      (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} ∧
    (∀ θ : ℝ, 0 ≤ θ →
      (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} ≤
        Real.exp (θ * (S.card : ℝ) * (N - c : ℕ)) *
          (allContactMass Γ b S + (1 - allContactMass Γ b S) * Real.exp (-θ)) ^ N) := by
  have he : (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} =
      Ample.Shortage.congestionProb (visibleLaw Γ b) N c S := by
    rw [ppi_joint_rejection_eq_congestProbAt Γ hA hatom hpolicy i b hb S,
      Ample.Shortage.congestionProb_eq_simultaneous,
      visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb]
  rw [he]
  exact ⟨(Ample.Shortage.finite_sandwich (visibleLaw Γ b) N c hc S).1,
    fun θ hθ => Ample.Shortage.chernoff_shortage (visibleLaw Γ b) N c S hθ⟩

theorem actual_joint_rejection_AM9_exact
    (Γ : FiniteGame (N + 1) n c Seed) (hc : c ≤ N)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) {b : ℝ} (hb : 0 < b) (S : Finset (Fin n)) :
    let A := allContactMass Γ b S
    A ^ N ≤ (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} ∧
    (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} ≤
      (IndependentCounts.binomial N A
        ((visibleLaw Γ b).prob_nonneg (fun T => S ⊆ T))
        ((visibleLaw Γ b).prob_le_one (fun T => S ⊆ T))).prob
          (fun r => N - S.card * (N-c) ≤ r.val) := by
  intro A
  have he : (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i b j ω} =
      Ample.Shortage.congestionProb (visibleLaw Γ b) N c S := by
    rw [ppi_joint_rejection_eq_congestProbAt Γ hA hatom hpolicy i b hb S,
      Ample.Shortage.congestionProb_eq_simultaneous,
      visibleLaw_eq_contactLaw, Ample.contactLaw_congestionProb]
  rw [he]
  simpa only [A, allContactMass, Ample.Shortage.allHits_tail_eq_binomial] using
    Ample.Shortage.finite_sandwich (visibleLaw Γ b) N c hc S

theorem actual_action_failure_AM9
    (Γ : FiniteGame (N + 1) n c Seed) (hc : c ≤ N)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) :
    let S := firstK (Equiv.refl (Fin n)) a.routeCount
    let A := allContactMass Γ a.bid S
    A ^ N ≤ 1 - ((problem Γ i).outcome a).success ∧
    (∀ θ : ℝ, 0 ≤ θ →
      1 - ((problem Γ i).outcome a).success ≤
        Real.exp (θ * (a.routeCount : ℝ) * (N - c : ℕ)) *
          (A + (1 - A) * Real.exp (-θ)) ^ N) := by
  intro S A
  have hfinite := actual_joint_rejection_AM9 Γ hc hA hatom hpolicy i hb S
  have hfailure := ppi_failure_eq_congestProb Γ hA hatom hpolicy i a hb
  have hset := ppi_joint_rejection_eq_congestProbAt Γ hA hatom hpolicy i a.bid hb S
  have hprob : (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i a.bid j ω} =
      1 - ((problem Γ i).outcome a).success := by
    rw [hset, hfailure]
    rw [Ample.congestProbAt_eq_congestProb]
    simp only [S, card_firstK _ _ a.routeCount_le]
  rw [hprob] at hfinite
  simpa [A, S, card_firstK _ _ a.routeCount_le] using hfinite

theorem actual_action_failure_AM9_exact
    (Γ : FiniteGame (N + 1) n c Seed) (hc : c ≤ N)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (hpolicy : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (a : JointAction n) (hb : 0 < a.bid) :
    let S := firstK (Equiv.refl (Fin n)) a.routeCount
    let A := allContactMass Γ a.bid S
    A ^ N ≤ 1 - ((problem Γ i).outcome a).success ∧
    1 - ((problem Γ i).outcome a).success ≤
      (IndependentCounts.binomial N A
        ((visibleLaw Γ a.bid).prob_nonneg (fun T => S ⊆ T))
        ((visibleLaw Γ a.bid).prob_le_one (fun T => S ⊆ T))).prob
          (fun r => N - a.routeCount * (N-c) ≤ r.val) := by
  intro S A
  have hfinite := actual_joint_rejection_AM9_exact Γ hc hA hatom hpolicy i hb S
  have hfailure := ppi_failure_eq_congestProb Γ hA hatom hpolicy i a hb
  have hset := ppi_joint_rejection_eq_congestProbAt Γ hA hatom hpolicy i a.bid hb S
  have hprob : (backgroundLaw Γ).real {ω | ∀ j ∈ S, ¬ Accepts Γ i a.bid j ω} =
      1 - ((problem Γ i).outcome a).success := by
    rw [hset, hfailure, Ample.congestProbAt_eq_congestProb]
    simp only [S, card_firstK _ _ a.routeCount_le]
  rw [hprob] at hfinite
  simpa only [S, card_firstK _ _ a.routeCount_le] using hfinite

end FCAppendix.Bayes.CompletionDraft
