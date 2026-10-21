import FCAppendix.Affine.WeightedSampling
import FCAppendix.Affine.ClippedResidualContinuity
import FCAppendix.Affine.EqualCapacityLottery
import FCAppendix.Affine.Hybrid.SupportSampler

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory Filter Topology
open scoped BigOperators

namespace Literal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open ClippedResidual
open WeightedSampling (Weights Path pathLaw finalSet totalWeight remainingWeight indicator)

theorem expect_congr_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    {f g : Ω → ℝ} (h : ∀ x, 0 < P.mass x → f x = g x) :
    P.expect f = P.expect g := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < P.mass x
  · rw [h x hx]
  · have hz : P.mass x = 0 := le_antisymm (le_of_not_gt hx) (P.nonneg x)
    simp [hz]

theorem map_support {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (P : FiniteLaw Ω) (f : Ω → Ξ) (x : Ξ) (hx : (P.map f).mass x ≠ 0) :
    ∃ y, P.mass y ≠ 0 ∧ f y = x := by
  classical
  by_contra hn
  have hz : ∀ y, f y = x → P.mass y = 0 := by
    intro y hy
    by_contra hp
    exact hn ⟨y, hp, hy⟩
  apply hx
  change (∑ y, if f y = x then P.mass y else 0) = 0
  apply Finset.sum_eq_zero
  intro y _
  by_cases hy : f y = x
  · simp [hy, hz y hy]
  · simp [hy]

theorem zero_marginal_omitted (P : FiniteLaw (Finset ι)) (i : ι)
    (hi : Proposer.marginal P i = 0) (S : Finset ι)
    (hS : P.mass S ≠ 0) : i ∉ S := by
  intro hiS
  have hp := FiniteLaw.marginal_pos_of_support_mem P S hS i hiS
  change 0 < Proposer.marginal P i at hp
  rw [hi] at hp
  exact (lt_irrefl 0) hp

def root (ξ lo hi : ℝ) (b : ι → ℝ) (E : Finset ι) (d : ℕ) : ℝ := by
  classical
  exact if h : ∃ z, z ∈ Icc lo hi ∧ remainingDemand ξ b E z = (d : ℝ)
  then h.choose else 0

theorem root_spec {ξ U lo hi slack : ℝ} (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hguard : (1 - ξ) * U ≤ lo)
    (hb : ∀ i, b i ≤ U) (hd : 0 < d) (hs : 0 < slack)
    (hlow : (d : ℝ) + E.card + slack < ∑ i, exposure ξ lo (b i))
    (hhigh : (∑ i, exposure ξ hi (b i)) < (d : ℝ) - slack) :
    root ξ lo hi b E d ∈ Icc lo hi ∧
      remainingDemand ξ b E (root ξ lo hi b E d) = (d : ℝ) := by
  have hex := (exists_unique_balanced_root b E hξ hξ1 hU hlo hlh hguard hb
    (by exact_mod_cast hd) hs hlow hhigh).exists
  rw [root, dif_pos hex]
  exact hex.choose_spec

def completion (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (smallMarginal ξ z b E)

def largeCompletion (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) :
    FiniteLaw (Finset ι) :=
  (completion ξ z b E).map (fun S => E ∪ S)

def conditionalCompletion (ξ z : ℝ) (b : ι → ℝ) (E : Finset ι) :
    FiniteLaw (Finset ι × Finset ι) :=
  (largeCompletion ξ z b E).prod (completion ξ z b E)

theorem completion_implements {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hr : remainingDemand ξ b E z = (d : ℝ)) :
    ExactCapacity.Implements (smallMarginal ξ z b E) d (completion ξ z b E) := by
  have hp := marginal_bounds hξ hz b E
  exact ExactCapacity.symmetricLottery_implements _ d
    (fun i => (hp i).1.1) (fun i => (hp i).1.2) hr

theorem completion_disjoint {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hr : remainingDemand ξ b E z = (d : ℝ)) (S : Finset ι)
    (hS : (completion ξ z b E).mass S ≠ 0) : Disjoint E S := by
  have hm := completion_implements hξ hz b E d hr
  apply Finset.disjoint_left.mpr
  intro i hiE hiS
  have hi : Proposer.marginal (completion ξ z b E) i = 0 := by
    change (completion ξ z b E).prob (fun S => i ∈ S) = 0
    rw [hm.2 i, smallMarginal, if_pos hiE]
  exact zero_marginal_omitted _ i hi S hS hiS

theorem largeCompletion_implements {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hr : remainingDemand ξ b E z = (d : ℝ)) :
    ExactCapacity.Implements (largeMarginal ξ z b E) (d + E.card)
      (largeCompletion ξ z b E) := by
  have hm := completion_implements hξ hz b E d hr
  constructor
  · intro T hT
    obtain ⟨S, hS, hST⟩ := map_support (completion ξ z b E) (fun S => E ∪ S) T hT
    rw [← hST, Finset.card_union_of_disjoint (completion_disjoint hξ hz b E d hr S hS),
      hm.1 S hS, Nat.add_comm]
  · intro i
    rw [FiniteLaw.prob_eq_expect, largeCompletion, FiniteLaw.expect_map]
    by_cases hi : i ∈ E
    · simp [hi, largeMarginal]
    · simpa [hi, largeMarginal, smallMarginal, FiniteLaw.prob_eq_expect] using hm.2 i

theorem conditional_completion_nash {ξ U z : ℝ} (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hz : 0 < z)
    (hguard : (1 - ξ) * U ≤ z) (hbU : ∀ i, b i ≤ U)
    (hE : ∀ i ∈ E, z ≤ b i) (hr : remainingDemand ξ b E z = (d : ℝ)) :
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d) →
      revenueAgainst ξ b ν (largeCompletion ξ z b E) ≤
        revenueAgainst ξ b (completion ξ z b E) (largeCompletion ξ z b E)) ∧
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d + E.card) →
      revenueAgainst ξ b ν (completion ξ z b E) ≤
        revenueAgainst ξ b (largeCompletion ξ z b E) (completion ξ z b E)) := by
  have hs := completion_implements hξ hz b E d hr
  have hl := largeCompletion_implements hξ hz b E d hr
  have hp := marginal_bounds hξ hz b E
  have ht := pair_threshold hξ hξ1 hz hguard b hbU E hE
  have hsumS : (∑ i, smallMarginal ξ z b E i) = (d : ℝ) := hr
  have hsumL : (∑ i, largeMarginal ξ z b E i) = ((d + E.card : ℕ) : ℝ) := by
    rw [largeMarginal_sum, hsumS, Nat.cast_add]
  constructor
  · intro ν hν
    rw [revenueAgainst_eq, revenueAgainst_eq, Proposer.revenue_marginals,
      Proposer.revenue_marginals]
    simp only [Proposer.marginal, hs.2, hl.2]
    exact Proposer.threshold_linear_optimal _ _ z d
      (fun i => (hp i).1.1) (fun i => (hp i).1.2) hsumS hz.le ht.1
      (Proposer.marginal ν) (fun i => ν.prob_nonneg _) (fun i => ν.prob_le_one _)
      (Proposer.marginal_capacity ν d hν)
  · intro ν hν
    rw [revenueAgainst_eq, revenueAgainst_eq, Proposer.revenue_marginals,
      Proposer.revenue_marginals]
    simp only [Proposer.marginal, hs.2, hl.2]
    exact Proposer.threshold_linear_optimal _ _ z ((d + E.card : ℕ) : ℝ)
      (fun i => (hp i).2.1) (fun i => (hp i).2.2) hsumL hz.le ht.2
      (Proposer.marginal ν) (fun i => ν.prob_nonneg _) (fun i => ν.prob_le_one _)
      (Proposer.marginal_capacity ν (d + E.card) hν)

def firstCopy (i : ι) (P : Finset ι × Finset ι) : ℝ :=
  indicator i P.1 + indicator i P.2 - indicator i P.1 * indicator i P.2

def duplicateCopy (i : ι) (P : Finset ι × Finset ι) : ℝ :=
  indicator i P.1 * indicator i P.2

theorem conditional_first_copy {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hr : remainingDemand ξ b E z = (d : ℝ)) (i : ι) :
    (conditionalCompletion ξ z b E).expect (firstCopy i) =
      if i ∈ E then 1 else 2 * exposure ξ z (b i) - exposure ξ z (b i) ^ 2 := by
  have hs := (completion_implements hξ hz b E d hr).2 i
  have hl := (largeCompletion_implements hξ hz b E d hr).2 i
  have hs' : (completion ξ z b E).expect (indicator i) = smallMarginal ξ z b E i :=
    (FiniteLaw.prob_eq_expect _ _).symm.trans hs
  have hl' : (largeCompletion ξ z b E).expect (indicator i) = largeMarginal ξ z b E i :=
    (FiniteLaw.prob_eq_expect _ _).symm.trans hl
  change ((largeCompletion ξ z b E).prod (completion ξ z b E)).expect
    (fun P => indicator i P.1 + indicator i P.2 - indicator i P.1 * indicator i P.2) = _
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_add, FiniteLaw.expect_prod_mul]
  have hfirst : ((largeCompletion ξ z b E).prod (completion ξ z b E)).expect
      (fun P => indicator i P.1) = largeMarginal ξ z b E i := by
    rw [FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const, hl']
  have hsecond : ((largeCompletion ξ z b E).prod (completion ξ z b E)).expect
      (fun P => indicator i P.2) = smallMarginal ξ z b E i := by
    rw [FiniteLaw.expect_prod]
    simp only [hs', FiniteLaw.expect_const]
  rw [hfirst, hsecond, hl', hs']
  by_cases hi : i ∈ E
  · simp [hi, smallMarginal, largeMarginal]
  · simp only [smallMarginal, largeMarginal, if_neg hi]
    ring

theorem conditional_duplicate_copy {ξ z : ℝ} (hξ : 0 < ξ) (hz : 0 < z)
    (b : ι → ℝ) (E : Finset ι) (d : ℕ)
    (hr : remainingDemand ξ b E z = (d : ℝ)) (i : ι) :
    (conditionalCompletion ξ z b E).expect (duplicateCopy i) =
      if i ∈ E then 0 else exposure ξ z (b i) ^ 2 := by
  have hs := (completion_implements hξ hz b E d hr).2 i
  have hl := (largeCompletion_implements hξ hz b E d hr).2 i
  unfold conditionalCompletion duplicateCopy
  rw [FiniteLaw.expect_prod_mul]
  change (largeCompletion ξ z b E).expect (fun S => if i ∈ S then 1 else 0) *
      (completion ξ z b E).expect (fun S => if i ∈ S then 1 else 0) = _
  rw [← FiniteLaw.prob_eq_expect, ← FiniteLaw.prob_eq_expect, hl, hs]
  by_cases hi : i ∈ E
  · simp [hi, smallMarginal, largeMarginal]
  · simp only [smallMarginal, largeMarginal, if_neg hi]
    ring

def WeightedGuard (ξ U lo hi slack : ℝ) (b : ι → ℝ) (w : Weights ι)
    (d Δ : ℕ) : Prop :=
  (∀ i, b i ≤ U) ∧
  (d : ℝ) + Δ + slack < ∑ i, exposure ξ lo (b i) ∧
  (∑ i, exposure ξ hi (b i)) < (d : ℝ) - slack ∧
  (Δ : ℝ) + slack < totalWeight w ∧
  (∀ i, 0 < w.1 i → hi ≤ b i)

variable [Nonempty ι]

def weightedExperiment (ξ lo hi : ℝ) (b : ι → ℝ) (w : Weights ι) (d Δ : ℕ) :
    FiniteLaw (Path ι Δ × (Finset ι × Finset ι)) :=
  WeightedSampling.pairLaw (pathLaw w Δ ∅) (fun p =>
    let E := finalSet Δ ∅ p
    conditionalCompletion ξ (root ξ lo hi b E d) b E)

@[simp] theorem weightedExperiment_mass (ξ lo hi : ℝ) (b : ι → ℝ)
    (w : Weights ι) (d Δ : ℕ) (p : Path ι Δ) (S T : Finset ι) :
    (weightedExperiment ξ lo hi b w d Δ).mass (p, (S,T)) =
      (pathLaw w Δ ∅).mass p *
        ((largeCompletion ξ (root ξ lo hi b (finalSet Δ ∅ p) d) b (finalSet Δ ∅ p)).mass S *
          (completion ξ (root ξ lo hi b (finalSet Δ ∅ p) d) b (finalSet Δ ∅ p)).mass T) := rfl

theorem weighted_path_root {ξ U lo hi slack : ℝ} (b : ι → ℝ) (w : Weights ι) (d Δ : ℕ)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (h : WeightedGuard ξ U lo hi slack b w d Δ) (p : Path ι Δ)
    (hp : 0 < (pathLaw w Δ ∅).mass p) :
    (finalSet Δ ∅ p).card = Δ ∧
      root ξ lo hi b (finalSet Δ ∅ p) d ∈ Icc lo hi ∧
      remainingDemand ξ b (finalSet Δ ∅ p) (root ξ lo hi b (finalSet Δ ∅ p) d) = (d : ℝ) ∧
      ∀ i ∈ finalSet Δ ∅ p, hi ≤ b i := by
  have hw : ((∅ : Finset ι).card : ℝ) + Δ < totalWeight w := by
    simp only [Finset.card_empty, Nat.cast_zero, zero_add]
    linarith [h.2.2.2.1]
  have hc := WeightedSampling.finalSet_card w Δ ∅ hw p hp
  simp only [Finset.card_empty, zero_add] at hc
  have he : ∀ i ∈ finalSet Δ ∅ p, hi ≤ b i := by
    intro i hiE
    exact h.2.2.2.2 i (WeightedSampling.finalSet_weight_pos w Δ ∅ hw
      (by simp) p hp i hiE)
  have hr := root_spec b (finalSet Δ ∅ p) d hξ hξ1 hU hlo hlh hg h.1 hd hs
    (by simpa only [hc] using h.2.1) h.2.2.1
  exact ⟨hc, hr.1, hr.2, he⟩

theorem weighted_conditional_nash {ξ U lo hi slack : ℝ} (b : ι → ℝ) (w : Weights ι)
    (d Δ : ℕ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (h : WeightedGuard ξ U lo hi slack b w d Δ) (p : Path ι Δ)
    (hp : 0 < (pathLaw w Δ ∅).mass p) :
    let E := finalSet Δ ∅ p
    let z := root ξ lo hi b E d
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d) →
      revenueAgainst ξ b ν (largeCompletion ξ z b E) ≤
        revenueAgainst ξ b (completion ξ z b E) (largeCompletion ξ z b E)) ∧
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d + Δ) →
      revenueAgainst ξ b ν (completion ξ z b E) ≤
        revenueAgainst ξ b (largeCompletion ξ z b E) (completion ξ z b E)) := by
  obtain ⟨hc, hz, hr, he⟩ := weighted_path_root b w d Δ hξ hξ1 hU hlo hlh hg hd hs h p hp
  simpa only [hc] using conditional_completion_nash b (finalSet Δ ∅ p) d hξ hξ1
    (hlo.trans_le hz.1) (hg.trans hz.1) h.1 (fun i hiE => hz.2.trans (he i hiE)) hr

theorem weighted_first_copy {ξ U lo hi slack : ℝ} (b : ι → ℝ) (w : Weights ι)
    (d Δ : ℕ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (h : WeightedGuard ξ U lo hi slack b w d Δ) (i : ι) :
    (weightedExperiment ξ lo hi b w d Δ).expect (fun out => firstCopy i out.2) =
      (pathLaw w Δ ∅).expect (fun p =>
        let E := finalSet Δ ∅ p
        let z := root ξ lo hi b E d
        if i ∈ E then 1 else 2 * exposure ξ z (b i) - exposure ξ z (b i) ^ 2) := by
  rw [weightedExperiment, WeightedSampling.expect_pairLaw]
  apply expect_congr_support
  intro p hp
  obtain ⟨_, hz, hr, _⟩ := weighted_path_root b w d Δ hξ hξ1 hU hlo hlh hg hd hs h p hp
  exact conditional_first_copy hξ (hlo.trans_le hz.1) b _ d hr i

theorem weighted_duplicate_copy {ξ U lo hi slack : ℝ} (b : ι → ℝ) (w : Weights ι)
    (d Δ : ℕ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (h : WeightedGuard ξ U lo hi slack b w d Δ) (i : ι) :
    (weightedExperiment ξ lo hi b w d Δ).expect (fun out => duplicateCopy i out.2) =
      (pathLaw w Δ ∅).expect (fun p =>
        let E := finalSet Δ ∅ p
        let z := root ξ lo hi b E d
        if i ∈ E then 0 else exposure ξ z (b i) ^ 2) := by
  rw [weightedExperiment, WeightedSampling.expect_pairLaw]
  apply expect_congr_support
  intro p hp
  obtain ⟨_, hz, hr, _⟩ := weighted_path_root b w d Δ hξ hξ1 hU hlo hlh hg hd hs h p hp
  exact conditional_duplicate_copy hξ (hlo.trans_le hz.1) b _ d hr i

omit [DecidableEq ι] [Nonempty ι] in
theorem continuous_totalWeight : Continuous (totalWeight : Weights ι → ℝ) := by
  unfold totalWeight
  fun_prop

omit [Nonempty ι] in
theorem continuous_remainingWeight (S : Finset ι) :
    Continuous (fun w : Weights ι => remainingWeight w S) := by
  classical
  unfold remainingWeight
  apply continuous_finsetSum
  intro i _
  by_cases hi : i ∈ S
  · simp only [if_pos hi]
    exact continuous_const
  · simp only [if_neg hi]
    exact (continuous_apply i).comp continuous_subtype_val

theorem continuousAt_oneDraw_mass (S : Finset ι) (i : ι) (w : Weights ι)
    (hw : 0 < remainingWeight w S) :
    ContinuousAt (fun w : Weights ι => (WeightedSampling.oneDraw w S).mass i) w := by
  have hc : Continuous (fun w : Weights ι => if i ∈ S then (0 : ℝ) else w.1 i) := by
    by_cases hi : i ∈ S
    · simpa [hi] using (continuous_const : Continuous (fun _ : Weights ι => (0 : ℝ)))
    · simp only [if_neg hi]
      exact (continuous_apply i).comp continuous_subtype_val
  have hd := hc.continuousAt.div (continuous_remainingWeight S).continuousAt hw.ne'
  apply hd.congr_of_eventuallyEq
  have he : ∀ᶠ w' in 𝓝 w, 0 < remainingWeight w' S :=
    (continuous_remainingWeight S).continuousAt.eventually (eventually_gt_nhds hw)
  filter_upwards [he] with w' hw'
  exact WeightedSampling.oneDraw_mass w' S hw' i

theorem continuousAt_path_mass (n : ℕ) (S : Finset ι) (p : Path ι n)
    (w : Weights ι) (hw : (S.card : ℝ) + n < totalWeight w) :
    ContinuousAt (fun w : Weights ι => (pathLaw w n S).mass p) w := by
  induction n generalizing S with
  | zero => exact continuousAt_const
  | succ n ih =>
    have hd : 0 < remainingWeight w S := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hw
      linarith [WeightedSampling.denominator_lower w S]
    have hcard : ((insert p.1 S).card : ℝ) ≤ (S.card : ℝ) + 1 := by
      exact_mod_cast Finset.card_insert_le p.1 S
    have hw' : ((insert p.1 S).card : ℝ) + n < totalWeight w := by
      push_cast at hw
      linarith
    exact (continuousAt_oneDraw_mass S p.1 w hd).mul (ih (insert p.1 S) p.2 hw')

theorem measurable_oneDraw_mass (S : Finset ι) (i : ι) :
    Measurable (fun w : Weights ι => (WeightedSampling.oneDraw w S).mass i) := by
  have hn : Measurable (fun w : Weights ι => if i ∈ S then (0 : ℝ) else w.1 i) := by
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      exact measurable_const
    · simp only [if_neg hi]
      exact (measurable_pi_apply i).comp measurable_subtype_coe
  have he : (fun w : Weights ι => (WeightedSampling.oneDraw w S).mass i) =
      (fun w => if 0 < remainingWeight w S then
        (if i ∈ S then 0 else w.1 i) / remainingWeight w S
        else (FiniteLaw.dirac (Classical.choice ‹Nonempty ι›)).mass i) := by
    funext w
    by_cases hw : 0 < remainingWeight w S
    · simpa only [if_pos hw] using WeightedSampling.oneDraw_mass w S hw i
    · simp [WeightedSampling.oneDraw, hw]
  rw [he]
  exact Measurable.ite (measurableSet_lt measurable_const (continuous_remainingWeight S).measurable)
    (hn.div (continuous_remainingWeight S).measurable) measurable_const

theorem measurable_path_mass (n : ℕ) (S : Finset ι) (p : Path ι n) :
    Measurable (fun w : Weights ι => (pathLaw w n S).mass p) := by
  induction n generalizing S with
  | zero => exact measurable_const
  | succ n ih => exact (measurable_oneDraw_mass S p.1).mul (ih (insert p.1 S) p.2)

end Literal
end FCAppendix.Affine.UniformFinite
