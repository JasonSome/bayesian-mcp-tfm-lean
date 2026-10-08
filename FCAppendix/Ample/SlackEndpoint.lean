import FCAppendix.Ample.SlackAsymptotics
import FCAppendix.Finite.RankConcentration
import FCAppendix.Ample.CongestionRate

noncomputable section
namespace FCAppendix.Bayes
open MeasureTheory ProbabilityTheory Game Set Finset Filter Topology Real
open scoped BigOperators
variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def singletonAboveAt (j : Fin n) (b : ℝ) : Set (UserDraw n) :=
  {x : ℝ × JointAction n | b < x.2.bid ∧ x.2.routeCount = 1} ×ˢ
    {τ : Equiv.Perm (Fin n) | j ∈ firstK τ 1}

lemma measurable_singletonAboveAt (j : Fin n) (b : ℝ) :
    MeasurableSet (singletonAboveAt j b) := by
  exact ((measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)).inter
    (((measurable_routeCount n).comp measurable_snd) (measurableSet_singleton 1))).prod
      (Set.to_countable _).measurableSet

lemma singletonAboveAt_subset (j : Fin n) (b : ℝ) : singletonAboveAt j b ⊆ aboveAt j b := by
  rintro d ⟨hd, hj⟩
  exact ⟨by simpa only [singletonAboveAt, Set.mem_setOf_eq, hd.2] using hj, hd.1⟩

lemma singletonAboveAt_probability (Γ : FiniteGame m n c Seed) (hn : 0 < n)
    (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    (userLaw Γ).real (singletonAboveAt j b) =
      positiveRouteTail Γ (fun k => k = 1) b / n := by
  rw [singletonAboveAt, userLaw, measureReal_prod_prod,
    permLaw_mem_firstK n 1 hn hn j, Nat.cast_one, mul_one_div]
  congr 1
  rw [positiveRouteTail_class_eq Γ b hb (by omega : 1 ≤ 1),
    visibleClassMass_eq_compProd Γ b (by omega : 1 ≤ 1)]

lemma binomBelow_higher_le_singletonTail (Γ : FiniteGame m n c Seed)
    (hn : 0 < n) (i : Fin m) (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    binomBelow (m - 1) (alphaGt Γ j b) c ≤
      binomBelow (m - 1) (positiveRouteTail Γ (fun k => k = 1) b / n) c := by
  have hsub : {ω : Background m n Seed | rivals i (aboveAt j b) ω < c} ⊆
      {ω | rivals i (singletonAboveAt j b) ω < c} := by
    intro ω hω
    have hc : rivals i (singletonAboveAt j b) ω ≤ rivals i (aboveAt j b) ω := by
      classical
      simp only [rivals_eq_card]
      apply Finset.card_le_card
      intro l hl
      exact mem_filter.mpr ⟨(mem_filter.mp hl).1,
        singletonAboveAt_subset j b (mem_filter.mp hl).2⟩
    exact hc.trans_lt hω
  have hh := measureReal_mono (μ := backgroundLaw Γ) hsub (measure_ne_top _ _)
  rw [prob_rivals_lt Γ i _ (measurableSet_aboveAt j b),
    prob_rivals_lt Γ i _ (measurable_singletonAboveAt j b),
    singletonAboveAt_probability Γ hn j b hb] at hh
  exact hh

lemma ppi_singleton_failure_ge_tail (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hA : Γ.A = Schedule.ppi n)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (i : Fin m) (a : JointAction n) (hb : 0 < a.bid) (hk : a.routeCount = 1) :
    1 - binomBelow (m - 1) (positiveRouteTail Γ (fun k => k = 1) a.bid / n) c ≤
      1 - ((problem Γ i).outcome a).success := by
  let j : Fin n := ⟨0, hn⟩
  have hbnd := binomBelow_higher_le_singletonTail Γ hn i j a.bid hb.le
  rw [singleton_success Γ hn i a hk]
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [ppi_meanAcceptProb_eq_rank Γ hA hatom hj i j a.bid hb]
  simpa only [Nat.succ_sub_one] using sub_le_sub_left hbnd 1

lemma exists_supported_tail_gt (Γ : FiniteGame m n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (hu : UsersOptimal Γ)
    (hact : NonpositiveAbstention Γ) (i : Fin m) (P : ℕ → Prop)
    {q : ℝ} (hq : 0 ≤ q) (hqm : q < positiveRouteMass Γ P) :
    ∃ w : ℝ, ∃ a : JointAction n, 0 < w ∧
      (problem Γ i).BestResponse (w + Γ.g) a ∧ 0 < a.bid ∧
      0 < a.routeCount ∧ P a.routeCount ∧ q < positiveRouteTail Γ P a.bid := by
  let lo := (q + positiveRouteMass Γ P) / 2
  let hi := (lo + positiveRouteMass Γ P) / 2
  have hlo : 0 < lo := by dsimp [lo]; linarith
  have hlh : lo < hi := by dsimp [hi, lo]; linarith
  have hhi : hi < positiveRouteMass Γ P := by dsimp [hi, lo]; linarith
  have hgood : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ),
      (problem Γ i).BestResponse x.1 x.2 ∧ (x.1 ≤ Γ.g → x.2.routeCount = 0) :=
    (ae_bestResponse_compProd Γ hu i).and hact
  obtain ⟨x, hx, hl, _, _, hxb⟩ :=
    (positiveBidStratum Γ hatom P).exists_good_in_band
      ((measurable_bid n).comp measurable_snd) hlo hlh hhi ∅
      (by simpa using sub_pos.mpr hlh) _ hgood
  have hv : Γ.g < x.1 := by
    by_contra hv
    have hh := hxb.2 (le_of_not_gt hv)
    have hr : 0 < x.2.routeCount := hx.2.1
    omega
  refine ⟨x.1 - Γ.g, x.2, by linarith, ?_, hx.1, hx.2.1, hx.2.2, ?_⟩
  · simpa only [sub_add_cancel] using hxb.1
  · have hql : q < lo := by dsimp [lo]; linarith
    exact hql.trans_le (by simpa only [positiveBidStratum_tail] using hl)

theorem ppi_AM3_positive (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (i : Fin m) :
    1 - binomBelow (m - 1) (positiveRouteMass Γ (fun k => k = 1) / n) c ≤
      allPositiveCongestion Γ i := by
  let piMass := positiveRouteMass Γ (fun k => k = 1)
  by_cases hpiMass : piMass = 0
  · change 1 - binomBelow (m - 1) (piMass / n) c ≤ _
    rw [hpiMass, zero_div, binomBelow_zero_probability _ _ hc, sub_self]
    exact measureReal_nonneg
  have hpiMass0 : 0 < piMass := lt_of_le_of_ne (positiveRouteMass_nonneg Γ _) (Ne.symm hpiMass)
  let q : ℕ → ℝ := fun r => piMass - piMass / ((r : ℝ) + 2)
  have hq (r : ℕ) : 0 ≤ q r ∧ q r < piMass := by
    have hr : (0 : ℝ) < r + 2 := by positivity
    have hdiv : 0 < piMass / ((r : ℝ) + 2) := div_pos hpiMass0 hr
    have hdiv' : piMass / ((r : ℝ) + 2) ≤ piMass := by
      apply (div_le_iff₀ hr).mpr
      have hnR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    dsimp [q]
    constructor <;> linarith
  have he (r : ℕ) := exists_supported_tail_gt Γ hatom hu hact i (fun k => k = 1)
    (hq r).1 (hq r).2
  choose w a hw ha hb hr hk ht using he
  have hqconv : Tendsto q atTop (𝓝 piMass) := by
    have hden : Tendsto (fun r : ℕ => (r : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hd : Tendsto (fun r : ℕ => piMass / ((r : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    simpa only [q, sub_zero] using tendsto_const_nhds.sub hd
  have htail : Tendsto (fun r => positiveRouteTail Γ (fun k => k = 1) (a r).bid)
      atTop (𝓝 piMass) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hqconv tendsto_const_nhds
    · exact fun r => (ht r).le
    · exact fun r => positiveRouteTail_le_mass Γ _ _
  have hlim : Tendsto (fun r => 1 - binomBelow (m - 1)
      (positiveRouteTail Γ (fun k => k = 1) (a r).bid / n) c) atTop
      (𝓝 (1 - binomBelow (m - 1) (piMass / n) c)) :=
    tendsto_const_nhds.sub ((continuous_binomBelow (m - 1) c).continuousAt.tendsto.comp
      (htail.div_const n))
  apply le_of_tendsto hlim
  filter_upwards [] with r
  exact (ppi_singleton_failure_ge_tail Γ hm hn hA hatom hj i (a r) (hb r) (hk r)).trans
    (ppi_AM1_failure Γ hm hn hA hfree hatom hj i (hw r) (a r) (ha r))

theorem allPositiveCongestion_le_totalRoutes (Γ : FiniteGame m n c Seed) (i : Fin m) :
    allPositiveCongestion Γ i ≤ (backgroundLaw Γ).real
      {ω | n * c ≤ ∑ l ∈ (Finset.univ.erase i), (ω.1 l).1.2.routeCount} := by
  classical
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hsum : n * c ≤ ∑ j : Fin n, rivals i (aboveAt j 0) ω := by
    simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using
      (Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun j _ => hω j))
  apply hsum.trans
  simp only [rivals, PiBinomial.count_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro l _
  simp only [aboveAt, Set.mem_setOf_eq]
  by_cases hb : 0 < (ω.1 l).1.2.bid
  · simp only [hb, and_true]
    have hfilter : (Finset.univ.filter fun j : Fin n =>
        j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount) =
        firstK (ω.1 l).2 (ω.1 l).1.2.routeCount := by ext j; simp
    rw [← Finset.card_filter, hfilter,
      card_firstK _ _ (ω.1 l).1.2.routeCount_le]
  · simp only [hb, and_false, if_false, sum_const_zero]
    exact Nat.zero_le _

theorem ppi_AM3 (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hn : 0 < n) (hc : 0 < c)
    (hA : Γ.A = Schedule.ppi n) (hfree : FreeDuplicateBase Γ)
    (hatom : PositiveVisibleAtomless Γ) (hj : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hu : UsersOptimal Γ) (hact : NonpositiveAbstention Γ) (hz : RejectsZeroBids Γ)
    (i : Fin m) :
    1 - binomBelow (m - 1) ((Γ.F ⊗ₘ Γ.σ).real {x | x.2.routeCount = 1} / n) c ≤
      allPositiveCongestion Γ i ∧
    allPositiveCongestion Γ i ≤ (backgroundLaw Γ).real
      {ω | n * c ≤ ∑ l ∈ (Finset.univ.erase i), (ω.1 l).1.2.routeCount} := by
  refine ⟨?_, allPositiveCongestion_le_totalRoutes Γ i⟩
  rw [← ppi_positiveRouteMass_eq_raw Γ hm hn hc hA hatom hj hu hact hz
    (fun k => k = 1) (by intro k hk; omega)]
  exact ppi_AM3_positive Γ hm hn hc hA hfree hatom hj hu hact i

end FCAppendix.Bayes

namespace FCAppendix.Ample
open Finset Filter Topology Real CommonList Proposer
open scoped BigOperators

def singletonOnly (p : ℝ) (j : ℕ) : ℝ := if j = 1 then p else 0

lemma singletonOnly_valid {n : ℕ} (hn : 0 < n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ValidLaw n (singletonOnly p) where
  nonneg := by intro j hj; dsimp [singletonOnly]; split <;> positivity
  total_le := by simpa [singletonOnly, show 1 ≤ n from hn] using hp1

lemma singletonOnly_marginal {n : ℕ} (hn : 0 < n) (p : ℝ) :
    contactMarginal n (singletonOnly p) = p / n := by
  simp [contactMarginal, singletonOnly, show 1 ≤ n from hn]

lemma congest_one_eq_binomial {n N c : ℕ} (hn : 0 < n) (hc : c ≤ N + 1)
    {lawWeights : ℕ → ℝ} (hlam : ValidLaw n lawWeights) :
    congestProb n N c 1 lawWeights = 1 - Bayes.binomBelow N (contactMarginal n lawWeights) c := by
  classical
  let j : Fin n := ⟨0, hn⟩
  let μ := contactLaw n lawWeights hlam
  have hsel : selected n 1 = {j} := by
    ext k
    simp only [selected, mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
    change k.val < 1 ↔ k.val = 0
    omega
  have hp : (iid μ N).prob (fun T => includers j T < c) =
      Bayes.binomBelow N (marginal μ j) c := by
    rw [FiniteLaw.prob_eq_expect]
    change (iid μ N).expect ((fun r : ℕ => if r < c then 1 else 0) ∘ includers j) = _
    rw [show ((fun r : ℕ => if r < c then (1 : ℝ) else 0) ∘ includers j) =
      (fun T => (fun r : ℕ => if r < c then (1 : ℝ) else 0) (includers j T)) from rfl,
      expect_includers μ j N (fun r => if r < c then 1 else 0),
      Bayes.binomBelow_eq_prob N c hc _ (marginal_nonneg μ j) (marginal_le_one μ j),
      FiniteLaw.prob_eq_expect]
  rw [congestProb, hsel, ← contactLaw_congestionProb n lawWeights hlam]
  change (iid μ N).prob (fun T => ∀ s ∈ ({j} : Finset (Fin n)), c ≤ includers s T) = _
  have he : (fun T : Fin N → Finset (Fin n) => ∀ s ∈ ({j} : Finset (Fin n)),
      c ≤ includers s T) = fun T => ¬ includers j T < c := by
    funext T
    simp only [mem_singleton, forall_eq, not_lt]
  rw [he, FiniteLaw.prob_compl, hp]
  simp only [μ, contactLaw_marginal]

theorem singleton_entropy_separation {n : ℕ} (hn : 2 ≤ n) {p ρ : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hample : p < (n : ℝ) * ρ) (hρ1 : ρ < 1) :
    ∃ θ d : ℝ, 0 ≤ θ ∧
      rivalRate n ρ 1 (singletonOnly p) < d ∧
      d < rivalObjective n ρ 2 (singletonOnly p) θ := by
  have hn0 : 0 < n := by omega
  have hlam := singletonOnly_valid hn0 hp.le hp1
  have hslack : contactMarginal n (singletonOnly p) < ρ := by
    rw [singletonOnly_marginal hn0]
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hn0)).mpr
    nlinarith
  have htop : ∃ j ∈ Icc 1 n, 0 < singletonOnly p j ∧
      ((1 : ℕ) : ℝ) * ρ < (min 1 j : ℕ) := by
    refine ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_, ?_⟩
    · simpa [singletonOnly] using hp
    · simpa using hρ1
  obtain ⟨θ, hθ, hgap⟩ := strict_added_constraint_of_law (by omega : 1 ≤ 1)
    hn hlam hslack (by simpa [singletonOnly] using hp) htop
  obtain ⟨d, hd, hd'⟩ := exists_between hgap
  exact ⟨θ, d, hθ, hd, hd'⟩

end FCAppendix.Ample
