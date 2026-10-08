import FCAppendix.Ample.BoundaryRankAlgebra
import FCAppendix.Ample.RankFiniteIdentities
import FCAppendix.Ample.BoundaryActualContact

noncomputable section
namespace FCAppendix.Ample.CompletionDraft
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators

theorem containing_card_indicator {n j : ℕ} (S : Finset (Fin n)) :
    (∑ T : Finset (Fin n), if S ⊆ T ∧ T.card = j then (1 : ℝ) else 0) =
      if S.card ≤ j then ((n-S.card).choose (j-S.card) : ℝ) else 0 := by
  classical
  have hfilter : (Finset.univ.filter (fun T : Finset (Fin n) =>
      S ⊆ T ∧ T.card = j)) =
      ((Finset.univ : Finset (Fin n)).powersetCard j).filter (S ⊆ ·) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact and_comm
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hfilter]
  by_cases hSj : S.card ≤ j
  · rw [if_pos hSj, containing_subsets_card S hSj]
  · rw [if_neg hSj]
    have he : (((Finset.univ : Finset (Fin n)).powersetCard j).filter (S ⊆ ·)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro T hT
      have hcard := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
      have hle := Finset.card_le_card (Finset.mem_filter.mp hT).2
      exact hSj (hcard ▸ hle)
    simp only [he, Finset.card_empty, Nat.cast_zero]

theorem contactLaw_contains_card {n j : ℕ} (p : ℕ → ℝ) (hp : ValidLaw n p)
    (S : Finset (Fin n)) (hj : 1 ≤ j) :
    (contactLaw n p hp).prob (fun T => S ⊆ T ∧ T.card = j) =
      containsCoefficient n S.card j * p j := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  have he : (∑ T : Finset (Fin n),
      (contactLaw n p hp).mass T * (if S ⊆ T ∧ T.card = j then 1 else 0)) =
      (p j / (n.choose j : ℝ)) *
        (∑ T : Finset (Fin n), if S ⊆ T ∧ T.card = j then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases hT : S ⊆ T ∧ T.card = j
    · have hne : T ≠ ∅ := by
        intro hzero
        have : j = 0 := by simpa only [hzero, Finset.card_empty] using hT.2.symm
        omega
      simp only [hT, contactLaw_mass, contactWeight, if_neg hne]
    · simp only [hT, if_false, mul_zero]
  rw [he, containing_card_indicator]
  unfold containsCoefficient
  split_ifs <;> ring

theorem allMass_contactLaw {n : ℕ} (p : ℕ → ℝ) (hp : ValidLaw n p)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    Shortage.allMass (contactLaw n p hp) S =
      ∑ j ∈ Finset.Icc 1 n, containsCoefficient n S.card j * p j := by
  classical
  have hpartition (T : Finset (Fin n)) :
      (if S ⊆ T then (1 : ℝ) else 0) =
        ∑ j ∈ Finset.Icc 1 n, if S ⊆ T ∧ T.card = j then (1 : ℝ) else 0 := by
    by_cases hST : S ⊆ T
    · have hT : T.Nonempty := hS.mono hST
      have hcard : T.card ∈ Finset.Icc 1 n := by
        refine Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hT, ?_⟩
        simpa using Finset.card_le_card (Finset.subset_univ T)
      rw [if_pos hST, Finset.sum_eq_single_of_mem T.card hcard]
      · simp only [hST, true_and, if_true]
      · intro j _ hj
        simp only [hST, true_and, if_neg (Ne.symm hj)]
    · simp only [hST, if_false, false_and, Finset.sum_const_zero]
  unfold Shortage.allMass
  rw [FiniteLaw.prob_eq_expect]
  rw [(contactLaw n p hp).expect_congr hpartition,
    FiniteLaw.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← FiniteLaw.prob_eq_expect]
  exact contactLaw_contains_card p hp S (Finset.mem_Icc.mp hj).1

theorem containsCoefficient_le_one {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    containsCoefficient n k j ≤ 1 := by
  classical
  let S := firstK (Equiv.refl (Fin n)) k
  have hScard : S.card = k := card_firstK _ _ hk
  by_cases hkj : k ≤ j
  · have hcount := Finset.card_le_card
      (Finset.filter_subset (fun T : Finset (Fin n) => S ⊆ T)
        ((Finset.univ : Finset (Fin n)).powersetCard j))
    have hSj : S.card ≤ j := by simpa only [hScard] using hkj
    rw [containing_subsets_card S hSj,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, hScard] at hcount
    have hc : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos hj
    rw [containsCoefficient, if_pos hkj, div_le_one hc]
    exact_mod_cast hcount
  · simp only [containsCoefficient, if_neg hkj, zero_le_one]

def boundaryClassContact (n k : ℕ) (p : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, containsCoefficient n k j * p j

theorem boundaryClassContact_nonneg {n k : ℕ} {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) :
    0 ≤ boundaryClassContact n k p :=
  Finset.sum_nonneg (fun j hj => mul_nonneg (containsCoefficient_nonneg _ _ _) (hp j hj))

theorem boundaryClassContact_mono {n k : ℕ} {p q : ℕ → ℝ}
    (hpq : ∀ j ∈ Finset.Icc 1 n, p j ≤ q j) :
    boundaryClassContact n k p ≤ boundaryClassContact n k q :=
  Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hpq j hj)
    (containsCoefficient_nonneg _ _ _))

theorem boundaryClassContact_le_total {n k : ℕ} (hk : k ≤ n) {p : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, 0 ≤ p j) :
    boundaryClassContact n k p ≤ ∑ j ∈ Finset.Icc 1 n, p j := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_of_le_one_left (hp j hj)
    (containsCoefficient_le_one hk (Finset.mem_Icc.mp hj).2)

theorem boundaryClassContact_le_one {n k : ℕ} (hk : k ≤ n) {p : ℕ → ℝ}
    (hp : ValidLaw n p) : boundaryClassContact n k p ≤ 1 :=
  (boundaryClassContact_le_total hk hp.nonneg).trans hp.total_le

theorem boundaryClassContact_tendsto {n k : ℕ} {p : ℕ → ℕ → ℝ} {q : ℕ → ℝ}
    (hp : ∀ j ∈ Finset.Icc 1 n, Tendsto (fun t => p t j) atTop (𝓝 (q j))) :
    Tendsto (fun t => boundaryClassContact n k (p t)) atTop
      (𝓝 (boundaryClassContact n k q)) := by
  apply tendsto_finsetSum
  intro j hj
  exact tendsto_const_nhds.mul (hp j hj)

@[simp] theorem boundaryClassContact_rankTail (n k : ℕ) (nu : ℕ → Measure ℝ) (h u : ℝ) :
    boundaryClassContact n k (Bayes.rankTail nu h u) = allContactTail n k nu h u := rfl

end FCAppendix.Ample.CompletionDraft

namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Filter Topology Real
open scoped BigOperators
open Ample Ample.CompletionDraft
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem actual_allContactMass_eq {N : ℕ} (Γ : FiniteGame (N+1) n c Seed)
    (b : ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    CompletionDraft.allContactMass Γ b S =
      boundaryClassContact n S.card (visibleClassMass Γ b) := by
  unfold CompletionDraft.allContactMass
  rw [visibleLaw_eq_contactLaw]
  exact allMass_contactLaw _ _ S hS

theorem actual_failure_coefficient_AM9 (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hc : c ≤ m-1) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (a : JointAction n) (hb : 0 < a.bid) (hk : 0 < a.routeCount) :
    let A := boundaryClassContact n a.routeCount (visibleClassMass Γ a.bid)
    A ^ (m-1) ≤ actualFailure Γ a ∧
      ∀ θ ≥ 0, actualFailure Γ a ≤
        exp (θ * (a.routeCount : ℝ) * (m-1-c : ℕ)) *
          (A + (1-A)*exp (-θ)) ^ (m-1) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  intro A
  let S := firstK (Equiv.refl (Fin n)) a.routeCount
  have hScard : S.card = a.routeCount := card_firstK _ _ a.routeCount_le
  have hS : S.Nonempty := Finset.card_pos.mp (by simpa only [hScard] using hk)
  have hfinite := CompletionDraft.actual_action_failure_AM9 Γ (by simpa using hc)
    hA hatom hj ⟨0, by omega⟩ a hb
  have he : CompletionDraft.allContactMass Γ a.bid S = A := by
    rw [actual_allContactMass_eq Γ a.bid S hS, hScard]
  change CompletionDraft.allContactMass Γ a.bid S ^ N ≤
      1 - ((problem Γ ⟨0, by omega⟩).outcome a).success ∧
    (∀ θ ≥ 0, 1 - ((problem Γ ⟨0, by omega⟩).outcome a).success ≤
      exp (θ * (a.routeCount : ℝ) * (N-c : ℕ)) *
        (CompletionDraft.allContactMass Γ a.bid S +
          (1-CompletionDraft.allContactMass Γ a.bid S)*exp (-θ)) ^ N) at hfinite
  rw [he] at hfinite
  simpa only [actualFailure, dif_pos (show 0 < N+1 by omega),
    Nat.succ_sub_one] using hfinite

theorem actual_failure_rank_AM9 (Γ : FiniteGame m n c Seed) (hm : 0 < m)
    (hc : c ≤ m-1) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (a : JointAction n) (hb : 0 < a.bid) (hk : 0 < a.routeCount)
    {u θ : ℝ} (hu : u ≤ ascendingBidRank Γ a.bid) (hθ : 0 ≤ θ) :
    let A := boundaryClassContact n a.routeCount
      (fun j => (rankClassLaw Γ j).real (Ioi u))
    actualFailure Γ a ≤ exp (θ * (a.routeCount : ℝ) * (m-1-c : ℕ)) *
      (A + (1-A)*exp (-θ)) ^ (m-1) := by
  intro A
  let B := boundaryClassContact n a.routeCount (visibleClassMass Γ a.bid)
  have hBA : B ≤ A := boundaryClassContact_mono (fun j hj =>
    visibleClassMass_le_rank_cut Γ hatom hb.le hu (Finset.mem_Icc.mp hj).1)
  have hB0 : 0 ≤ B := boundaryClassContact_nonneg (visibleClassMass_valid Γ a.bid).nonneg
  have hB1 : B ≤ 1 := boundaryClassContact_le_one a.routeCount_le
    (visibleClassMass_valid Γ a.bid)
  have he : exp (-θ) ≤ 1 := by simpa using exp_le_exp.mpr (neg_nonpos.mpr hθ)
  have hbase : B + (1-B)*exp (-θ) ≤ A + (1-A)*exp (-θ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hBA) (sub_nonneg.mpr he)]
  have hbase0 : 0 ≤ B + (1-B)*exp (-θ) :=
    add_nonneg hB0 (mul_nonneg (sub_nonneg.mpr hB1) (exp_pos _).le)
  exact ((actual_failure_coefficient_AM9 Γ hm hc hA hatom hj a hb hk).2 θ hθ).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase _) (exp_pos _).le)

theorem rank_failure_AM9_all_identities (Γ : FiniteGame m n c Seed)
    (hc : c ≤ m-1) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ)
    (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid) (hk : 0 < a.routeCount)
    {u θ : ℝ} (hu : u ≤ ascendingBidRank Γ a.bid) (hθ : 0 ≤ θ) :
    let A := boundaryClassContact n a.routeCount
      (fun j => (rankClassLaw Γ j).real (Ioi u))
    1 - ((problem Γ i).outcome a).success ≤
      exp (θ * (a.routeCount : ℝ) * (m-1-c : ℕ)) *
        (A + (1-A)*exp (-θ)) ^ (m-1) := by
  have hm : 0 < m := Nat.zero_lt_of_lt i.isLt
  dsimp only
  rw [← rank_actualFailure_eq_identity Γ hm hA hatom hj i a hb]
  exact actual_failure_rank_AM9 Γ hm hc hA hatom hj a hb hk hu hθ

end FCAppendix.Bayes
