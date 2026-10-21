import FCAppendix.Existence.R01PayOnceCanonicalPolicy
import FCAppendix.Exclusive.CanonicalBayesianConstruction
import FCAppendix.PayOnce.BayesianCommonList
import FCAppendix.Proposer.LotterySupport

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open MeasureTheory ProbabilityTheory Game Set Filter Classical
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveMarginal_threshold (n c : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) :
    ∃ lam : ℝ, 0 ≤ lam ∧
      Proposer.Threshold (positiveMarginal n c b)
        (fun i => b i * PayOnce.H n (positiveMarginal n c b i)) lam ∧
      lam * ((c : ℝ) - (min c (positiveSupport b).card : ℕ)) = 0 := by
  let S := positiveSupport b
  let q : S → ℝ := CommonList.kernelMarginal n c (fun j : S => b j.1)
  let p := positiveMarginal n c b
  have hb : ∀ j : S, 0 < b j.1 := fun j => (mem_positiveSupport b j.1).mp j.2
  obtain ⟨hq0, hq1, hsum, lam, hlam, ht⟩ :=
    CommonList.kernelMarginal_spec n hn c (fun j : S => b j.1) hb
  change Proposer.Threshold q (fun i => b i.1 * PayOnce.H n (q i)) lam at ht
  have hinside (i : S) : p i.1 = q i := onSupport_inside n c S b i
  have houtside (i : ι) (hi : i ∉ S) : p i = 0 := onSupport_outside n c S b i hi
  by_cases hover : c ≤ S.card
  · refine ⟨lam, hlam, ?_, ?_⟩
    · change Proposer.Threshold p (fun i => b i * PayOnce.H n (p i)) lam
      constructor
      · intro i hi0
        by_cases hi : i ∈ S
        · change b i * PayOnce.H n (p i) ≤ lam
          rw [hinside ⟨i, hi⟩]
          exact ht.1 ⟨i, hi⟩ ((hinside ⟨i, hi⟩).symm.trans hi0)
        · have hbi : b i ≤ 0 := le_of_not_gt (fun h => hi ((mem_positiveSupport b i).mpr h))
          simpa only [houtside i hi, PayOnce.H_zero n (by omega), mul_one] using hbi.trans hlam
      · constructor
        · intro i hi1
          by_cases hi : i ∈ S
          · change lam ≤ b i * PayOnce.H n (p i)
            rw [hinside ⟨i, hi⟩]
            exact ht.2.1 ⟨i, hi⟩ ((hinside ⟨i, hi⟩).symm.trans hi1)
          · rw [houtside i hi] at hi1
            norm_num at hi1
        · intro i hi0 hi1
          by_cases hi : i ∈ S
          · change b i * PayOnce.H n (p i) = lam
            rw [hinside ⟨i, hi⟩]
            exact ht.2.2 ⟨i, hi⟩ (by simpa only [← hinside ⟨i, hi⟩] using hi0)
              (by simpa only [← hinside ⟨i, hi⟩] using hi1)
          · rw [houtside i hi] at hi0
            exact (lt_irrefl _ hi0).elim
    · rw [Nat.min_eq_left hover, sub_self, mul_zero]
  · have hsmall : S.card ≤ c := le_of_not_ge hover
    have hsumq : (∑ j : S, q j) = (S.card : ℝ) := by
      simpa only [Nat.min_eq_right hsmall, Fintype.card_coe] using hsum
    have hsumzero : (∑ j : S, (1 - q j)) = 0 := by
      rw [Finset.sum_sub_distrib, hsumq]
      simp
    have hqone (i : S) : q i = 1 := by
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : S => 1 - q j) (fun j _ => sub_nonneg.mpr (hq1 j)) (Finset.mem_univ i)
      rw [hsumzero] at h
      exact le_antisymm (hq1 i) (by linarith)
    refine ⟨0, le_rfl, ?_, by simp⟩
    change Proposer.Threshold p (fun i => b i * PayOnce.H n (p i)) 0
    constructor
    · intro i hi0
      by_cases hi : i ∈ S
      · have h1 : p i = 1 := (hinside ⟨i, hi⟩).trans (hqone _)
        rw [h1] at hi0
        norm_num at hi0
      · have hbi : b i ≤ 0 := le_of_not_gt (fun h => hi ((mem_positiveSupport b i).mpr h))
        simpa only [houtside i hi, PayOnce.H_zero n (by omega), mul_one] using hbi
    · constructor
      · intro i hi1
        by_cases hi : i ∈ S
        · exact mul_nonneg (hb ⟨i, hi⟩).le
            (PayOnce.H_pos n (by omega) (p i)
              ((positiveMarginal_spec n c hn b).1 i)
              ((positiveMarginal_spec n c hn b).2.1 i)).le
        · rw [houtside i hi] at hi1
          norm_num at hi1
      · intro i hi0 hi1
        by_cases hi : i ∈ S
        · have h1 : p i = 1 := (hinside ⟨i, hi⟩).trans (hqone _)
          rw [h1] at hi1
          exact (lt_irrefl _ hi1).elim
        · rw [houtside i hi] at hi0
          exact (lt_irrefl _ hi0).elim

theorem lottery_support_optimal (n c : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) :
    ∀ S, (ExactCapacity.symmetricLottery (positiveMarginal n c b)).mass S ≠ 0 →
      Finite.Optimal c (fun i => b i * PayOnce.H n (positiveMarginal n c b i)) S := by
  let p := positiveMarginal n c b
  let r := fun i => b i * PayOnce.H n (p i)
  let mu := ExactCapacity.symmetricLottery p
  obtain ⟨hp0, hp1, hsum⟩ := positiveMarginal_spec n c hn b
  change (∑ i, p i) = (min c (positiveSupport b).card : ℕ) at hsum
  have himpl := ExactCapacity.symmetricLottery_implements p
    (min c (positiveSupport b).card) hp0 hp1 hsum
  have hfeas : CommonList.Feasible c mu := fun S hS =>
    (himpl.1 S hS).le.trans (min_le_left _ _)
  apply CommonList.support_optimal c r mu hfeas
  intro nu hnu
  rw [Proposer.revenue_marginals, Proposer.revenue_marginals]
  simp_rw [show ∀ i, Proposer.marginal mu i = p i from himpl.2]
  obtain ⟨lam, hlam, ht, hslack⟩ := positiveMarginal_threshold n c hn b
  have hs : (∑ i, (Proposer.marginal nu i - p i) * (r i - lam)) ≤ 0 :=
    Finset.sum_nonpos fun i _ => Proposer.coordinate_threshold p r lam hp0 hp1 ht i
      (Proposer.marginal nu i) (nu.prob_nonneg _) (nu.prob_le_one _)
  have he : (∑ i, (Proposer.marginal nu i - p i) * (r i - lam)) =
      (∑ i, Proposer.marginal nu i * r i) - (∑ i, p i * r i) -
        lam * ((∑ i, Proposer.marginal nu i) - (min c (positiveSupport b).card : ℕ)) := by
    simp_rw [sub_mul, mul_sub]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
    ring
  have hcap := Proposer.marginal_capacity nu c hnu
  have hmul := mul_le_mul_of_nonneg_left hcap hlam
  rw [he] at hs
  nlinarith

theorem bayesian_policy_optimal {m k c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : Bayes.FiniteGame m (k+1) c Seed) (hn : 2 ≤ k+1)
    (hA : Gamma.A = Schedule.once (k+1)) (B : Bayes.PosteriorSystem Gamma)
    (hcommon : ∀ j L, Bayes.FeasibleObservedList j L →
      ∀ᵐ d ∂B.posterior j L, ∀ l, Game.observe (Bayes.drawsRealization d) l = L)
    (hlaw : ∀ j L, Bayes.seedLottery Gamma j L =
      ExactCapacity.symmetricLottery (listMarginal (k+1) c L)) :
    Bayes.PosteriorProposerOptimalAE Gamma B := by
  intro j L hL
  let p := listMarginal (k+1) c L
  let mu := ExactCapacity.symmetricLottery p
  have hp := positiveMarginal_spec (k+1) c hn (listBids L)
  have himpl := ExactCapacity.symmetricLottery_implements p
    (min c (positiveSupport (listBids L)).card) hp.1 hp.2.1 hp.2.2
  have hr : Bayes.beliefReceipts Gamma.A (Bayes.posteriorCountBelief Gamma B j L) L =
      fun i => listBids L i * PayOnce.H (k+1) (p i) := by
    funext i
    cases he : L i with
    | none => simp [Bayes.beliefReceipts, listBids, he]
    | some b =>
      have hh := Bayes.posterior_payOnce_receipt Gamma hA B j L (hcommon j L hL) mu
        (fun l => hlaw l L) i b
      have hm : Proposer.marginal mu i = p i := himpl.2 i
      rw [hm] at hh
      simpa only [Bayes.beliefReceipts, he, listBids, Option.getD_some] using hh
  apply FiniteLaw.ae_property_of_ofMeasure Gamma.seedLaw
    (fun s => (Gamma.policy j L s).val) (Bayes.measurable_policy_at_list Gamma j L) mu
    (hlaw j L) (fun S => Finite.Optimal c
      (Bayes.beliefReceipts Gamma.A (Bayes.posteriorCountBelief Gamma B j L) L) S)
  intro S hS
  rw [hr]
  exact lottery_support_optimal (k+1) c hn (listBids L) S hS

end FCAppendix.Existence.PayOnceBounded
