import FCAppendix.Affine.UniformFinite.NativeRowKernel

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.NativeRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

theorem supported_best_reply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ξ : ℝ) (b : ι → ℝ) (c : ℕ) (P Q : FiniteLaw (Finset ι))
    (hP : ∀ S, P.mass S ≠ 0 → S.card ≤ c)
    (hBR : ∀ R : FiniteLaw (Finset ι), (∀ S, R.mass S ≠ 0 → S.card ≤ c) →
      revenueAgainst ξ b R Q ≤ revenueAgainst ξ b P Q) :
    ∀ S, P.mass S ≠ 0 → Finite.Optimal c
      (fun a => b a*(1-ξ*Proposer.marginal Q a)) S := by
  apply CommonList.support_optimal c _ P hP
  intro R hR
  simpa only [revenueAgainst_eq] using hBR R hR

theorem pure_numerical_optimal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : LowBody.PureTemplate ι) (ξ : ℝ) (b : ι → ℝ)
    (hb : ∀ a, a ∉ T.support → b a = 0) :
    Finite.Optimal T.residual₀
        (fun a => b a*(1-ξ*(if a∈(T.selection (1-ξ) b).2 then (1:ℝ) else 0)))
        (T.selection (1-ξ) b).1 ∧
      Finite.Optimal T.residual₁
        (fun a => b a*(1-ξ*(if a∈(T.selection (1-ξ) b).1 then (1:ℝ) else 0)))
        (T.selection (1-ξ) b).2 := by
  have hf := T.selection_feasible (1-ξ) b
  have hn := T.selection_nash (1-ξ) b
  have hr (S R : Finset ι) : LowBody.CompleteInformation.revenue (1-ξ) b S R =
      ∑ a∈S, b a*(1-ξ*(if a∈R then (1:ℝ) else 0)) := by
    unfold LowBody.CompleteInformation.revenue
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a∈R <;> simp only [ha, if_true, if_false, mul_one, mul_zero, sub_zero]; ring
  have hfilter (S R : Finset ι) :
      (∑ a∈S∩T.support,b a*(1-ξ*(if a∈R then (1:ℝ) else 0))) =
        ∑ a∈S,b a*(1-ξ*(if a∈R then (1:ℝ) else 0)) := by
    exact Finset.sum_subset Finset.inter_subset_left (fun a ha hnot => by
      have han : a ∉ T.support := fun ht => hnot (Finset.mem_inter.mpr ⟨ha,ht⟩)
      rw [hb a han, zero_mul])
  constructor
  · refine ⟨hf.1,?_⟩
    intro S hS
    have h := hn.1 (S∩T.support) ((Finset.card_le_card Finset.inter_subset_left).trans hS)
      Finset.inter_subset_right
    rwa [hr,hr,hfilter] at h
  · refine ⟨hf.2.2.1,?_⟩
    intro S hS
    have h := hn.2 (S∩T.support) ((Finset.card_le_card Finset.inter_subset_left).trans hS)
      Finset.inter_subset_right
    rwa [hr,hr,hfilter] at h

theorem privateLaw_optimal (i : Row) (row : Source.CountRow M) (x : State i M)
    (q : Signal row) (hq : 0 < (commonLaw i row x).mass q) (j : Fin 2)
    (S : Finset (Fin M)) (hS : (privateLaw i row j x q).mass S ≠ 0) :
    Finite.Optimal (Source.residual row j)
      (fun a => Source.lowerBids row (bids i x) a *
        (1-xi i*Proposer.marginal (privateLaw i row (Hybrid.otherProposer j) x q) a)) S := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · have hs : Source.small row = Source.residual row j := by
      fin_cases j <;> simp [Source.small, he]
    have hopt := EqualCapacity.canonicalLottery_support_optimal (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row (bids i x)) S
      (by simpa only [privateLaw, if_pos he, equalLottery, EqualCapacity.canonicalLottery] using hS)
    have hm := (EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row (bids i x))).2
    have hmass (a : Fin M) : Proposer.marginal
        (privateLaw i row (Hybrid.otherProposer j) x q) a =
        EqualCapacity.positiveMarginal (xi i) (Source.small row)
          (Source.lowerBids row (bids i x)) a := by
      simpa only [privateLaw,if_pos he,equalLottery,EqualCapacity.canonicalLottery,Proposer.marginal]
        using hm a
    simp only [hmass]
    simpa only [hs] using hopt
  · cases q with
    | none =>
      have hsel : S = pureSet i row j x := by
        by_contra hn
        simp [privateLaw, he, FiniteLaw.dirac, hn] at hS
      subst S
      have hp := pure_numerical_optimal (Source.lowerTemplate row) (xi i)
        (Source.lowerBids row (bids i x)) (fun a ha => Source.lowerBids_of_not_mem row _ ha)
      have hm (k : Fin 2) (a : Fin M) :
          Proposer.marginal (privateLaw i row k x none) a =
            if a∈pureSet i row k x then (1:ℝ) else 0 := by
        simp [privateLaw, he, Proposer.marginal, FiniteLaw.prob_eq_expect, FiniteLaw.expect_dirac]
      simp only [hm]
      fin_cases j
      · simpa [pureSet,Hybrid.otherProposer,Source.lowerTemplate,kappa] using hp.1
      · simpa [pureSet,Hybrid.otherProposer,Source.lowerTemplate,kappa] using hp.2
    | some p =>
      obtain ⟨hne,ha,hpath⟩ := common_some_support i row x p hq
      have hg := Source.guardAlpha_pos i x.1 row (bids i x) (Nat.pos_of_ne_zero (NeZero.ne M))
        (fun a _ => (bids_bounds i x a).2) ha
      have hr := Source.rootBounds i x.1
      have hpathspec := Source.guarded_weighted_path_root i x.1 row (bids i x)
        (fun a _ => (bids_bounds i x a).2) ha p hpath
      have hz := hr.1.trans_le hpathspec.2.1.1
      have hn := Literal.weighted_conditional_nash (Source.lowerBids row (bids i x))
        (Source.sourceWeights i x.1 row (bids i x)) (Source.small row) (Source.imbalance row)
        (xi_range i).1 (xi_range i).2 (cap_pos i) hr.1 hr.2.1 hr.2.2 hg.2.1 hg.2.2 hg.1 p hpath
      have hsImp := Literal.completion_implements (xi_range i).1 hz _ _
        (Source.small row) hpathspec.2.2.1
      have hlImp := Literal.largeCompletion_implements (xi_range i).1 hz _ _
        (Source.small row) hpathspec.2.2.1
      have hsLaw : smallLaw i row p x = Literal.completion (xi i) (actualRoot i row p x)
          (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p) := by
        rw [smallLaw, usableRoot_eq i row p x (alpha_pos_raw i row x ha)]
      have hlLaw : largeLaw i row p x = Literal.largeCompletion (xi i) (actualRoot i row p x)
          (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p) := by
        rw [largeLaw, hsLaw]
        rfl
      have hsBR : ∀ A, (smallLaw i row p x).mass A ≠ 0 →
          Finite.Optimal (Source.small row)
            (fun a => Source.lowerBids row (bids i x) a *
              (1-xi i*Proposer.marginal (largeLaw i row p x) a)) A := by
        rw [hsLaw,hlLaw]
        exact supported_best_reply (xi i) _ (Source.small row) _ _
          (fun A hA => (hsImp.1 A hA).le) hn.1
      have hlBR : ∀ A, (largeLaw i row p x).mass A ≠ 0 →
          Finite.Optimal (Source.large row)
            (fun a => Source.lowerBids row (bids i x) a *
              (1-xi i*Proposer.marginal (smallLaw i row p x) a)) A := by
        rw [hlLaw,hsLaw, ← Source.small_add_imbalance]
        exact supported_best_reply (xi i) _ (Source.small row+Source.imbalance row) _ _
          (fun A hA => by simpa only [hpathspec.1] using (hlImp.1 A hA).le) hn.2
      by_cases h01 : Source.residual row 0 < Source.residual row 1
      · have hs0 : Source.small row = Source.residual row 0 := min_eq_left h01.le
        have hl1 : Source.large row = Source.residual row 1 := max_eq_right h01.le
        fin_cases j
        · have hA : (smallLaw i row p x).mass S ≠ 0 := by simpa [privateLaw,he,largeSide,h01] using hS
          simpa [privateLaw,he,largeSide,h01,Hybrid.otherProposer,hs0] using hsBR S hA
        · have hA : (largeLaw i row p x).mass S ≠ 0 := by simpa [privateLaw,he,largeSide,h01] using hS
          simpa [privateLaw,he,largeSide,h01,Hybrid.otherProposer,hl1] using hlBR S hA
      · have h10 : Source.residual row 1 ≤ Source.residual row 0 := le_of_not_gt h01
        have hs1 : Source.small row = Source.residual row 1 := min_eq_right h10
        have hl0 : Source.large row = Source.residual row 0 := max_eq_left h10
        fin_cases j
        · have hA : (largeLaw i row p x).mass S ≠ 0 := by simpa [privateLaw,he,largeSide,h01] using hS
          simpa [privateLaw,he,largeSide,h01,Hybrid.otherProposer,hl0] using hlBR S hA
        · have hA : (smallLaw i row p x).mass S ≠ 0 := by simpa [privateLaw,he,largeSide,h01] using hS
          simpa [privateLaw,he,largeSide,h01,Hybrid.otherProposer,hs1] using hsBR S hA

theorem privateSample_acceptance (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M × Signal row) (a : Fin M) :
    (∫ s : unitInterval, if a∈privateSample i row j x s then (1:ℝ) else 0) =
      Proposer.marginal (privateLaw i row j x.1 x.2) a := by
  have hm := (privateSample_measurable i row j).comp
    ((measurable_const (a := x)).prodMk measurable_id)
  have h := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume _ hm
    (privateLaw i row j x.1 x.2) (privateSample_law i row j x)
  rw [Proposer.marginal, FiniteLaw.prob_eq_expect, ← h, FiniteLaw.expect_ofMeasure]
  rfl

def acceptance (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (common : unitInterval) (a : Fin M) : ℝ :=
  ∫ s : unitInterval, if a∈select i row j x common s then (1:ℝ) else 0

theorem acceptance_eq (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (common : unitInterval) (a : Fin M) :
    acceptance i row j x common a =
      Proposer.marginal (privateLaw i row j x (commonSample i row x common)) a :=
  privateSample_acceptance i row j _ a

theorem select_optimal (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (common privateSeed : unitInterval) :
    Finite.Optimal (Source.residual row j)
      (fun a => Source.lowerBids row (bids i x) a *
        (1-xi i*acceptance i row (Hybrid.otherProposer j) x common a))
      (select i row j x common privateSeed) := by
  simp only [acceptance_eq]
  let q := commonSample i row x common
  let S := privateSample i row j (x,q) privateSeed
  have hq := commonSample_support i row x common
  have hS := (privateSample_support i row j (x,q) privateSeed).ne'
  have hopt := privateLaw_optimal i row x q hq j S hS
  convert! hopt using 1

end FCAppendix.Affine.UniformFinite.NativeRow
