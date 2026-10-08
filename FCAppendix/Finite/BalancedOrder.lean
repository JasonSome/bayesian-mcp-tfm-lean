import FCAppendix.Game.Bayesian
import FCAppendix.Probability.PiBinomial
import FCAppendix.Finite.ReceiptOrder

namespace FCAppendix
namespace Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def presentList (ω : Background m n Seed) (i : Fin m) (b : ℝ) (j : Fin n) :
    LocalList m := by
  classical
  exact fun l => if l = i then some b else observe (drawsRealization ω.1) j l

omit [MeasurableSpace Seed] in
theorem presentList_self (ω : Background m n Seed) (i : Fin m) (b : ℝ) (j : Fin n) :
    presentList ω i b j i = some b := by
  simp [presentList]

omit [MeasurableSpace Seed] in
theorem presentList_other (ω : Background m n Seed) (i l : Fin m) (hl : l ≠ i) (b : ℝ)
    (j : Fin n) :
    presentList ω i b j l =
      if j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount then some (ω.1 l).1.2.bid else none := by
  simp [presentList, hl, observe, drawsRealization]

abbrev Accepts (Γ : FiniteGame m n c Seed) (i : Fin m) (b : ℝ) (j : Fin n)
    (ω : Background m n Seed) : Prop :=
  i ∈ (Γ.policy j (presentList ω i b j) (ω.2 j)).val

noncomputable def acceptProb (Γ : FiniteGame m n c Seed) (i : Fin m) (b : ℝ) (j : Fin n) : ℝ :=
  (backgroundLaw Γ).real {ω | Accepts Γ i b j ω}

noncomputable def meanAcceptProb (Γ : FiniteGame m n c Seed) (i : Fin m) (b : ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ j, acceptProb Γ i b j

theorem measurable_presentList (i : Fin m) (b : ℝ) (j : Fin n) :
    Measurable (fun ω : Background m n Seed => presentList ω i b j) := by
  classical
  rw [measurable_pi_iff]
  intro l
  by_cases hl : l = i
  · subst hl
    have hf : (fun ω : Background m n Seed => presentList ω l b j l) = fun _ => some b := by
      funext ω
      exact presentList_self ω l b j
    rw [hf]
    exact measurable_const
  · have hf : (fun ω : Background m n Seed => presentList ω i b j l) =
        fun ω => if j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount
          then some (ω.1 l).1.2.bid else none := by
      funext ω
      exact presentList_other ω i l hl b j
    rw [hf]
    have hdraw : Measurable (fun ω : Background m n Seed => ω.1 l) :=
      (measurable_pi_apply l).comp measurable_fst
    have hact : Measurable (fun ω : Background m n Seed => (ω.1 l).1.2) :=
      measurable_snd.comp (measurable_fst.comp hdraw)
    refine Measurable.ite ?_ ((measurable_some).comp ((measurable_bid n).comp hact))
      measurable_const
    have hs : {ω : Background m n Seed | j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount} =
        (fun ω : Background m n Seed => ((ω.1 l).2, (ω.1 l).1.2.routeCount)) ⁻¹'
          {x | j ∈ firstK x.1 x.2} := rfl
    rw [hs]
    exact ((measurable_snd.comp hdraw).prodMk ((measurable_routeCount n).comp hact))
      (measurableSet_mem_firstK j)

theorem measurableSet_accepts (Γ : FiniteGame m n c Seed) (i : Fin m) (b : ℝ) (j : Fin n) :
    MeasurableSet {ω : Background m n Seed | Accepts Γ i b j ω} := by
  have hseed : Measurable (fun ω : Background m n Seed => ω.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have hmeas := (Γ.policy_measurable j).comp ((measurable_presentList i b j).prodMk hseed)
  exact hmeas (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i ∈ S})

omit [MeasurableSpace Seed] in
theorem observe_deviated_of_mem (i : Fin m) (a : JointAction n) (ω : Sample m n Seed)
    (j : Fin n) (hj : j ∈ firstK ω.2 a.routeCount) :
    observe (deviated i a ω) j = presentList ω.1 i a.bid j := by
  classical
  funext l
  by_cases hl : l = i
  · subst hl
    rw [presentList_self]
    simp [observe, deviated_recipients_self, deviated_bid_self, hj]
  · rw [presentList_other ω.1 i l hl]
    simp [observe, deviated_recipients_other i l hl, deviated_bid_other i l hl]

theorem mem_allocation_deviated_iff (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) (ω : Sample m n Seed) (j : Fin n) :
    i ∈ allocation (deviated i a ω) Γ.policy ω.1.2 j ↔
      j ∈ firstK ω.2 a.routeCount ∧ Accepts Γ i a.bid j ω.1 := by
  classical
  by_cases hj : j ∈ firstK ω.2 a.routeCount
  · have ho := observe_deviated_of_mem i a ω j hj
    unfold allocation Accepts
    rw [ho]
    exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩
  · constructor
    · intro h
      exfalso
      have hlist := (Γ.policy j (observe (deviated i a ω) j) (ω.1.2 j)).property.2 i h
      apply hlist
      simp [observe, deviated_recipients_self, hj]
    · intro h
      exact absurd h.1 hj

theorem focalCount_val_eq (Γ : FiniteGame m n c Seed) (i : Fin m) (a : JointAction n)
    (ω : Sample m n Seed) :
    ((focalCount Γ i a ω).val : ℝ) =
      ∑ j, (if j ∈ firstK ω.2 a.routeCount then (1 : ℝ) else 0) *
        (if Accepts Γ i a.bid j ω.1 then 1 else 0) := by
  classical
  have h := inclusionCount_eq_sum (deviated i a ω) Γ.policy ω.1.2 i
  simp only [focalCount, boundedCount]
  rw [h]
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hA : i ∈ allocation (deviated i a ω) Γ.policy ω.1.2 j
  · have := (mem_allocation_deviated_iff Γ i a ω j).mp hA
    simp [hA, this.1, this.2]
  · rw [if_neg hA]
    by_cases hj : j ∈ firstK ω.2 a.routeCount
    · have hnot : ¬ Accepts Γ i a.bid j ω.1 := fun hacc =>
        hA ((mem_allocation_deviated_iff Γ i a ω j).mpr ⟨hj, hacc⟩)
      simp [hj, hnot]
    · simp [hj]

theorem load_eq (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m) (a : JointAction n) :
    ((problem Γ i).outcome a).load =
      ((a.routeCount : ℝ) / n) * ∑ j, acceptProb Γ i a.bid j := by
  classical
  rw [problem_outcome, CountLaw.load, CountLaw.expect_ofMeasure]
  simp_rw [focalCount_val_eq]
  have hind : ∀ j : Fin n, Integrable (fun ω : Sample m n Seed =>
      (if j ∈ firstK ω.2 a.routeCount then (1 : ℝ) else 0) *
        (if Accepts Γ i a.bid j ω.1 then 1 else 0)) (sampleLaw Γ) := by
    intro j
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
      · exact Measurable.ite ((measurable_snd.prodMk measurable_const)
          (measurableSet_mem_firstK j)) measurable_const measurable_const
      · exact Measurable.ite (measurable_fst (measurableSet_accepts Γ i a.bid j))
          measurable_const measurable_const
    · split_ifs <;> simp
  rw [integral_finsetSum _ (fun j _ => hind j), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold sampleLaw
  rw [show (fun ω : Sample m n Seed =>
      (if j ∈ firstK ω.2 a.routeCount then (1 : ℝ) else 0) *
        (if Accepts Γ i a.bid j ω.1 then 1 else 0)) =
      fun ω => (if Accepts Γ i a.bid j ω.1 then (1 : ℝ) else 0) *
        (if j ∈ firstK ω.2 a.routeCount then (1 : ℝ) else 0) from by
    funext ω; ring]
  rw [integral_prod_mul (μ := backgroundLaw Γ) (ν := permLaw n)
    (fun x : Background m n Seed => if Accepts Γ i a.bid j x then (1 : ℝ) else 0)
    (fun τ : Equiv.Perm (Fin n) => if j ∈ firstK τ a.routeCount then (1 : ℝ) else 0)]
  have h1 : ∫ ω, (if Accepts Γ i a.bid j ω then (1 : ℝ) else 0) ∂(backgroundLaw Γ) =
      acceptProb Γ i a.bid j := by
    rw [acceptProb, ← integral_indicator_one (measurableSet_accepts Γ i a.bid j)]
    congr 1
    funext ω
    simp [Set.indicator]
  have h2 : ∫ τ, (if j ∈ firstK τ a.routeCount then (1 : ℝ) else 0) ∂(permLaw n) =
      (a.routeCount : ℝ) / n := by
    rw [← permLaw_mem_firstK n a.routeCount hn a.routeCount_le j,
      ← integral_indicator_one (MeasurableSet.of_discrete)]
    congr 1
    funext τ
    simp [Set.indicator]
  rw [h1, h2]
  ring

theorem load_le_routeCount_mul_success (Γ : FiniteGame m n c Seed) (i : Fin m)
    (a : JointAction n) :
    ((problem Γ i).outcome a).load ≤
      (a.routeCount : ℝ) * ((problem Γ i).outcome a).success := by
  rw [problem_outcome, CountLaw.load, CountLaw.success, CountLaw.expect_ofMeasure,
    CountLaw.expect_ofMeasure, ← integral_const_mul]
  apply integral_mono
    (CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a) (fun r => (r.val : ℝ)))
    ((CountLaw.integrable_comp _ _ (measurable_focalCount Γ i a)
      (fun r => successIndicator r.val)).const_mul _)
  intro ω
  have hK := focalCount_le Γ i a ω
  by_cases h0 : (focalCount Γ i a ω).val = 0
  · simp [h0, successIndicator]
  · simp only [successIndicator, if_neg h0, mul_one]
    exact_mod_cast hK

theorem meanAcceptProb_le_success (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (a : JointAction n) (hk : 1 ≤ a.routeCount) :
    meanAcceptProb Γ i a.bid ≤ ((problem Γ i).outcome a).success := by
  have hload := load_eq Γ hn i a
  have hle := load_le_routeCount_mul_success Γ i a
  have hkR : (0 : ℝ) < a.routeCount := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ((problem Γ i).outcome a).load = (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid := by
    rw [hload, meanAcceptProb]
    field_simp
  rw [heq] at hle
  exact le_of_mul_le_mul_left hle hkR

theorem load_eq_mean (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (a : JointAction n) :
    ((problem Γ i).outcome a).load = (a.routeCount : ℝ) * meanAcceptProb Γ i a.bid := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [load_eq Γ hn i a, meanAcceptProb]
  field_simp

theorem success_le_n_meanAcceptProb (Γ : FiniteGame m n c Seed) (hn : 0 < n) (i : Fin m)
    (a : JointAction n) :
    ((problem Γ i).outcome a).success ≤ (n : ℝ) * meanAcceptProb Γ i a.bid := by
  have h1 := ((problem Γ i).outcome a).success_le_load
  rw [load_eq_mean Γ hn i a] at h1
  have hq : 0 ≤ meanAcceptProb Γ i a.bid := by
    unfold meanAcceptProb acceptProb
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  have hk : (a.routeCount : ℝ) ≤ n := by exact_mod_cast a.routeCount_le
  nlinarith

def atLeastAt (j : Fin n) (x : ℝ) : Set (UserDraw n) :=
  {d | j ∈ firstK d.2 d.1.2.routeCount ∧ x ≤ d.1.2.bid}

def aboveAt (j : Fin n) (x : ℝ) : Set (UserDraw n) :=
  {d | j ∈ firstK d.2 d.1.2.routeCount ∧ x < d.1.2.bid}

theorem measurableSet_reach (j : Fin n) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet {d : UserDraw n | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ B} := by
  have hk : Measurable (fun d : UserDraw n => (d.2, d.1.2.routeCount)) :=
    measurable_snd.prodMk ((measurable_routeCount n).comp (measurable_snd.comp measurable_fst))
  have hb : Measurable (fun d : UserDraw n => d.1.2.bid) :=
    (measurable_bid n).comp (measurable_snd.comp measurable_fst)
  exact (hk (measurableSet_mem_firstK j)).inter (hb hB)

theorem measurableSet_atLeastAt (j : Fin n) (x : ℝ) : MeasurableSet (atLeastAt j x) :=
  measurableSet_reach j (measurableSet_Ici (a := x))

theorem measurableSet_aboveAt (j : Fin n) (x : ℝ) : MeasurableSet (aboveAt j x) :=
  measurableSet_reach j (measurableSet_Ioi (a := x))

noncomputable def alphaGe (Γ : FiniteGame m n c Seed) (j : Fin n) (x : ℝ) : ℝ :=
  (userLaw Γ).real (atLeastAt j x)

noncomputable def alphaGt (Γ : FiniteGame m n c Seed) (j : Fin n) (x : ℝ) : ℝ :=
  (userLaw Γ).real (aboveAt j x)

noncomputable def rivals (i : Fin m) (E : Set (UserDraw n)) (ω : Background m n Seed) : ℕ :=
  PiBinomial.count E (Finset.univ.erase i) ω.1

open Classical in
omit [MeasurableSpace Seed] in
theorem rivals_eq_card (i : Fin m) (E : Set (UserDraw n)) (ω : Background m n Seed) :
    rivals i E ω = ((Finset.univ.erase i).filter (fun l => ω.1 l ∈ E)).card := rfl

noncomputable def binomBelow (N : ℕ) (p : ℝ) (c : ℕ) : ℝ :=
  ∑ r ∈ Finset.range c, PiBinomial.pmf N p r

theorem prob_rivals_lt (Γ : FiniteGame m n c Seed) (i : Fin m) (E : Set (UserDraw n))
    (hE : MeasurableSet E) (q : ℕ) :
    (backgroundLaw Γ).real {ω | rivals i E ω < q} =
      binomBelow (m - 1) ((userLaw Γ).real E) q := by
  classical
  have hpre : {ω : Background m n Seed | rivals i E ω < q} =
      {d : Fin m → UserDraw n | PiBinomial.count E (Finset.univ.erase i) d < q} ×ˢ Set.univ := by
    ext ω
    simp [rivals]
  have hmeasSet : MeasurableSet
      {d : Fin m → UserDraw n | PiBinomial.count E (Finset.univ.erase i) d < q} :=
    (PiBinomial.measurable_count E hE _) (measurableSet_Iio (a := q))
  rw [hpre, backgroundLaw, measureReal_prod_prod, probReal_univ, mul_one]
  have hunion : {d : Fin m → UserDraw n | PiBinomial.count E (Finset.univ.erase i) d < q} =
      ⋃ r ∈ Finset.range q, {d | PiBinomial.count E (Finset.univ.erase i) d = r} := by
    ext d
    simp
  rw [hunion, measureReal_biUnion_finset]
  · unfold binomBelow
    refine Finset.sum_congr ?_ (fun r _ => ?_)
    · rfl
    · rw [PiBinomial.measureReal_count_eq _ E hE]
      congr 1
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  · intro r _ r' _ hrr'
    exact Set.disjoint_left.mpr fun d h1 h2 => hrr' (h1.symm.trans h2)
  · intro r _
    exact (PiBinomial.measurable_count E hE _) (measurableSet_singleton r)

omit [MeasurableSpace Seed] in

theorem beliefReceipts_bounds (A : Schedule n) (belief : Fin m → FiniteLaw (Fin n))
    (ℓ : LocalList m) (a : ℝ) (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ A.charge r)
    (l : Fin m) (x : ℝ) (hx : 0 ≤ x) (hl : ℓ l = some x) :
    a * x ≤ beliefReceipts A belief ℓ l ∧ beliefReceipts A belief ℓ l ≤ x := by
  have h := Finite.conditionalReceipt_bounds A (belief l) a x hx hA
  simp only [beliefReceipts, hl]
  exact h

omit [MeasurableSpace Seed] in
theorem beliefReceipts_none (A : Schedule n) (belief : Fin m → FiniteLaw (Fin n))
    (ℓ : LocalList m) (l : Fin m) (hl : ℓ l = none) : beliefReceipts A belief ℓ l = 0 := by
  simp [beliefReceipts, hl]

omit [MeasurableSpace Seed] in
theorem presentList_bid_nonneg (ω : Background m n Seed) (i : Fin m) (b : ℝ) (hb : 0 ≤ b)
    (j : Fin n) (l : Fin m) (x : ℝ) (hl : presentList ω i b j l = some x) : 0 ≤ x := by
  by_cases hli : l = i
  · subst hli
    rw [presentList_self] at hl
    cases hl
    exact hb
  · rw [presentList_other ω i l hli] at hl
    split_ifs at hl with h
    · cases hl
      exact (ω.1 l).1.2.bid_nonneg

omit [MeasurableSpace Seed] in

theorem presentList_other_some (ω : Background m n Seed) (i l : Fin m) (hl : l ≠ i) (b : ℝ)
    (j : Fin n) (x : ℝ) (h : presentList ω i b j l = some x) :
    j ∈ firstK (ω.1 l).2 (ω.1 l).1.2.routeCount ∧ (ω.1 l).1.2.bid = x := by
  rw [presentList_other ω i l hl] at h
  split_ifs at h with hj
  · cases h
    exact ⟨hj, rfl⟩

theorem accepts_of_few_rivals (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRational Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b)
    (ω : Background m n Seed) (hfew : rivals i (atLeastAt j (a * b)) ω < c) :
    Accepts Γ i b j ω := by
  classical
  obtain ⟨belief, hopt⟩ := hj
  set ℓ := presentList ω i b j with hℓ
  set r := beliefReceipts Γ.A (belief ℓ) ℓ with hr
  have hri := beliefReceipts_bounds Γ.A (belief ℓ) ℓ a hA i b hb.le (presentList_self ω i b j)
  have hpos : 0 < r i := lt_of_lt_of_le (mul_pos ha hb) hri.1
  refine Finite.included_of_few_competitors c r _ (hopt ℓ (ω.2 j)) i hpos ?_
  rw [rivals_eq_card] at hfew
  refine lt_of_le_of_lt (Finset.card_le_card ?_) hfew
  intro l hlT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlT
  obtain ⟨hli, hle⟩ := hlT
  have hlpos : 0 < r l := lt_of_lt_of_le hpos hle
  rcases hsome : ℓ l with _ | x
  · rw [hr, beliefReceipts_none Γ.A (belief ℓ) ℓ l hsome] at hlpos
    exact absurd hlpos (lt_irrefl 0)
  · have hx0 := presentList_bid_nonneg ω i b hb.le j l x hsome
    have hrl := beliefReceipts_bounds Γ.A (belief ℓ) ℓ a hA l x hx0 hsome
    obtain ⟨hreach, hbid⟩ := presentList_other_some ω i l hli b j x hsome
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, atLeastAt, Set.mem_setOf_eq]
    refine ⟨hli, hreach, ?_⟩
    rw [hbid]
    linarith [hri.1, hrl.2]

theorem few_rivals_of_accepts (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRational Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b)
    (ω : Background m n Seed) (hacc : Accepts Γ i b j ω) :
    rivals i (aboveAt j (b / a)) ω < c := by
  classical
  obtain ⟨belief, hopt⟩ := hj
  set ℓ := presentList ω i b j with hℓ
  set r := beliefReceipts Γ.A (belief ℓ) ℓ with hr
  have hri := beliefReceipts_bounds Γ.A (belief ℓ) ℓ a hA i b hb.le (presentList_self ω i b j)
  by_contra hmany
  push Not at hmany
  refine Finite.excluded_of_many_better c r _ (hopt ℓ (ω.2 j)) i ?_ hacc
  rw [rivals_eq_card] at hmany
  refine le_trans hmany (Finset.card_le_card ?_)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    and_true, aboveAt, Set.mem_setOf_eq] at hl
  obtain ⟨hli, hreach, hbid⟩ := hl
  have hsome : ℓ l = some (ω.1 l).1.2.bid := by
    rw [hℓ, presentList_other ω i l hli, if_pos hreach]
  have hrl := beliefReceipts_bounds Γ.A (belief ℓ) ℓ a hA l _ (ω.1 l).1.2.bid_nonneg hsome
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hab : b < a * (ω.1 l).1.2.bid := by
    have := mul_lt_mul_of_pos_left hbid ha
    rwa [mul_div_cancel₀ b (ne_of_gt ha)] at this
  linarith [hri.2, hrl.1]

theorem acceptProb_bounds (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRational Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b) :
    binomBelow (m - 1) (alphaGe Γ j (a * b)) c ≤ acceptProb Γ i b j ∧
      acceptProb Γ i b j ≤ binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
  constructor
  · rw [alphaGe, ← prob_rivals_lt Γ i _ (measurableSet_atLeastAt j (a * b)) c, acceptProb]
    exact measureReal_mono (fun ω hω => accepts_of_few_rivals Γ j hj i a ha hA b hb ω hω)
  · rw [alphaGt, ← prob_rivals_lt Γ i _ (measurableSet_aboveAt j (b / a)) c, acceptProb]
    exact measureReal_mono (fun ω hω => few_rivals_of_accepts Γ j hj i a ha hA b hb ω hω)

end Bayes
end FCAppendix
