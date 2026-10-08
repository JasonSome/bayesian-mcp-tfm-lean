import FCAppendix.Finite.NoOverbidAE
import FCAppendix.Finite.ReceiptBounds

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped BigOperators ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ProposerRationalAtFeasibleLists (Γ : FiniteGame m n c Seed) (j : Fin n) : Prop :=
  ∃ belief : LocalList m → Fin m → FiniteLaw (Fin n),
    ∀ ℓ, FeasibleObservedList j ℓ → ∀ᵐ s ∂Γ.seedLaw,
      Finite.Optimal c (beliefReceipts Γ.A (belief ℓ) ℓ) (Γ.policy j ℓ s).val

def PosteriorProposerOptimalAE (Γ : FiniteGame m n c Seed) (B : PosteriorSystem Γ) : Prop :=
  ∀ j ℓ, FeasibleObservedList j ℓ → ∀ᵐ s ∂Γ.seedLaw,
    Finite.Optimal c (beliefReceipts Γ.A (posteriorCountBelief Γ B j ℓ) ℓ)
      (Γ.policy j ℓ s).val

theorem posterior_rationalAtFeasibleLists (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B) (j : Fin n) :
    ProposerRationalAtFeasibleLists Γ j := ⟨posteriorCountBelief Γ B j, hB j⟩

theorem posterior_rationalOnPath (Γ : FiniteGame m n c Seed)
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B) (j : Fin n) :
    ProposerRationalOnPath Γ j := by
  refine ⟨posteriorCountBelief Γ B j, ?_⟩
  filter_upwards [B.ae_observation Γ j] with ℓ hℓ
  obtain ⟨d, hd⟩ := hℓ.exists
  exact hB j ℓ ⟨d, hd⟩

theorem posterior_isAEEquilibrium (Γ : FiniteGame m n c Seed) (hu : UsersOptimal Γ)
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B) : IsAEEquilibrium Γ :=
  ⟨hu, posterior_rationalOnPath Γ B hB⟩

noncomputable def presentDrawList (d : UserProfile m n) (i : Fin m) (b : ℝ) (j : Fin n) :
    LocalList m := fun l => if l = i then some b else observe (drawsRealization d) j l

omit [MeasurableSpace Seed] in
theorem presentDrawList_feasible (d : UserProfile m n) (i : Fin m) (b : ℝ) (hb : 0 ≤ b)
    (j : Fin n) : FeasibleObservedList j (presentDrawList d i b j) := by
  classical
  let a : JointAction n := ⟨b, hb, n, le_rfl⟩
  let d' : UserProfile m n := Function.update d i ((0, a), Equiv.refl (Fin n))
  refine ⟨d', ?_⟩
  funext l
  by_cases hl : l = i
  · subst l
    simp [presentDrawList, observe, drawsRealization, d', a, mem_firstK]
  · simp [presentDrawList, observe, drawsRealization, d', hl]

theorem accepts_of_few_rivals_local (Γ : FiniteGame m n c Seed) (j : Fin n)
    (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b)
    (ω : Background m n Seed) (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c (beliefReceipts Γ.A belief (presentList ω i b j))
      (Γ.policy j (presentList ω i b j) (ω.2 j)).val) (hfew : rivals i (atLeastAt j (a * b)) ω < c) :
    Accepts Γ i b j ω := by
  classical
  set ℓ := presentList ω i b j with hℓ
  set r := beliefReceipts Γ.A belief ℓ with hr
  have hri := beliefReceipts_bounds Γ.A belief ℓ a hA i b hb.le (presentList_self ω i b j)
  have hpos : 0 < r i := lt_of_lt_of_le (mul_pos ha hb) hri.1
  refine Finite.included_of_few_competitors c r _ hopt i hpos ?_
  rw [rivals_eq_card] at hfew
  refine lt_of_le_of_lt (Finset.card_le_card ?_) hfew
  intro l hlT
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlT
  obtain ⟨hli, hle⟩ := hlT
  have hlpos : 0 < r l := lt_of_lt_of_le hpos hle
  rcases hsome : ℓ l with _ | x
  · rw [hr, beliefReceipts_none Γ.A belief ℓ l hsome] at hlpos
    exact absurd hlpos (lt_irrefl 0)
  · have hx0 := presentList_bid_nonneg ω i b hb.le j l x hsome
    have hrl := beliefReceipts_bounds Γ.A belief ℓ a hA l x hx0 hsome
    obtain ⟨hreach, hbid⟩ := presentList_other_some ω i l hli b j x hsome
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, atLeastAt, Set.mem_setOf_eq]
    refine ⟨hli, hreach, ?_⟩
    rw [hbid]
    linarith [hri.1, hrl.2]

theorem few_rivals_of_accepts_local (Γ : FiniteGame m n c Seed) (j : Fin n)
    (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b)
    (ω : Background m n Seed) (belief : Fin m → FiniteLaw (Fin n))
    (hopt : Finite.Optimal c (beliefReceipts Γ.A belief (presentList ω i b j))
      (Γ.policy j (presentList ω i b j) (ω.2 j)).val) (hacc : Accepts Γ i b j ω) :
    rivals i (aboveAt j (b / a)) ω < c := by
  classical
  set ℓ := presentList ω i b j with hℓ
  set r := beliefReceipts Γ.A belief ℓ with hr
  have hri := beliefReceipts_bounds Γ.A belief ℓ a hA i b hb.le (presentList_self ω i b j)
  by_contra hmany
  push Not at hmany
  refine Finite.excluded_of_many_better c r _ hopt i ?_ hacc
  rw [rivals_eq_card] at hmany
  refine le_trans hmany (Finset.card_le_card ?_)
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    and_true, aboveAt, Set.mem_setOf_eq] at hl
  obtain ⟨hli, hreach, hbid⟩ := hl
  have hsome : ℓ l = some (ω.1 l).1.2.bid := by
    rw [hℓ, presentList_other ω i l hli, if_pos hreach]
  have hrl := beliefReceipts_bounds Γ.A belief ℓ a hA l _ (ω.1 l).1.2.bid_nonneg hsome
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hab : b < a * (ω.1 l).1.2.bid := by
    have := mul_lt_mul_of_pos_left hbid ha
    rwa [mul_div_cancel₀ b (ne_of_gt ha)] at this
  linarith [hri.2, hrl.1]

theorem measurableSet_rivals_lt (i : Fin m) (E : Set (UserDraw n))
    (hE : MeasurableSet E) (q : ℕ) :
    MeasurableSet {ω : Background m n Seed | rivals i E ω < q} :=
  ((PiBinomial.measurable_count E hE (Finset.univ.erase i)).comp measurable_fst)
    (measurableSet_Iio (a := q))

theorem ae_receipt_rank_bounds (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalAtFeasibleLists Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b : ℝ) (hb : 0 < b) : ∀ᵐ ω ∂backgroundLaw Γ,
    (rivals i (atLeastAt j (a * b)) ω < c → Accepts Γ i b j ω) ∧
      (Accepts Γ i b j ω → rivals i (aboveAt j (b / a)) ω < c) := by
  have hl := measurableSet_rivals_lt (Seed := Seed) i (atLeastAt j (a * b))
    (measurableSet_atLeastAt j (a * b)) c
  have hu := measurableSet_rivals_lt (Seed := Seed) i (aboveAt j (b / a))
    (measurableSet_aboveAt j (b / a)) c
  have hac := measurableSet_accepts Γ i b j
  have hp : MeasurableSet {ω : Background m n Seed |
      (rivals i (atLeastAt j (a * b)) ω < c → Accepts Γ i b j ω) ∧
        (Accepts Γ i b j ω → rivals i (aboveAt j (b / a)) ω < c)} := by
    simpa only [imp_iff_not_or, Set.compl_setOf, Set.setOf_or, Set.setOf_and] using
      (hl.compl.union hac).inter (hac.compl.union hu)
  apply (Measure.ae_prod_iff_ae_ae hp).mpr
  obtain ⟨belief, hopt⟩ := hj
  apply Filter.Eventually.of_forall
  intro d
  let ℓ := presentDrawList d i b j
  have hs := hopt ℓ (presentDrawList_feasible d i b hb.le j)
  have hseeds := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae hs
  filter_upwards [hseeds] with s hS
  exact ⟨accepts_of_few_rivals_local Γ j i a ha hA b hb (d, s) (belief ℓ) hS,
    few_rivals_of_accepts_local Γ j i a ha hA b hb (d, s) (belief ℓ) hS⟩

theorem acceptProb_bounds_ae (Γ : FiniteGame m n c Seed) (j : Fin n)
    (hj : ProposerRationalAtFeasibleLists Γ j) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r) (b : ℝ) (hb : 0 < b) :
    binomBelow (m - 1) (alphaGe Γ j (a * b)) c ≤ acceptProb Γ i b j ∧
      acceptProb Γ i b j ≤ binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
  have hbounds := ae_receipt_rank_bounds Γ j hj i a ha hA b hb
  constructor
  · rw [alphaGe, ← prob_rivals_lt Γ i _ (measurableSet_atLeastAt j (a * b)) c, acceptProb]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hbounds.mono fun _ h => h.1))
  · rw [alphaGt, ← prob_rivals_lt Γ i _ (measurableSet_aboveAt j (b / a)) c, acceptProb]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hbounds.mono fun _ h => h.2))

def PositiveVisibleAtomless (Γ : FiniteGame m n c Seed) : Prop :=
  ∀ (j : Fin n) (b : ℝ), 0 < b → userLaw Γ {d |
    j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid = b} = 0

theorem VisibleAtomless.positive (Γ : FiniteGame m n c Seed) (h : VisibleAtomless Γ) :
    PositiveVisibleAtomless Γ := fun j b _ => h j b

theorem alphaGe_eq_alphaGt_pos (Γ : FiniteGame m n c Seed) (hΓ : PositiveVisibleAtomless Γ)
    (j : Fin n) (b : ℝ) (hb : 0 < b) : alphaGe Γ j b = alphaGt Γ j b := by
  apply measureReal_congr
  have hnull := measure_eq_zero_iff_ae_notMem.mp (hΓ j b hb)
  filter_upwards [hnull] with d hd
  apply propext
  change (j ∈ firstK d.2 d.1.2.routeCount ∧ b ≤ d.1.2.bid) ↔
    (j ∈ firstK d.2 d.1.2.routeCount ∧ b < d.1.2.bid)
  constructor
  · rintro ⟨hj, hb⟩
    exact ⟨hj, lt_of_le_of_ne hb (fun he => hd ⟨hj, he.symm⟩)⟩
  · exact fun h => ⟨h.1, h.2.le⟩

theorem meanAcceptProb_bounds_ae (Γ : FiniteGame m n c Seed) (hΓ : ∀ j, ProposerRationalAtFeasibleLists Γ j)
    (hatom : PositiveVisibleAtomless Γ) (j : Fin n) (i : Fin m)
    (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (b : ℝ) (hb : 0 < b) :
    binomBelow (m - 1) (alphaGt Γ j (a * b)) c ≤ meanAcceptProb Γ i b ∧
      meanAcceptProb Γ i b ≤ binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
  have hbounds (l : Fin n) := acceptProb_bounds_ae Γ l (hΓ l) i a ha hA b hb
  have hlo (l : Fin n) : binomBelow (m - 1) (alphaGt Γ j (a * b)) c ≤
      acceptProb Γ i b l := by
    have h := (hbounds l).1
    rwa [alphaGe_eq_alphaGt_pos Γ hatom l (a * b) (mul_pos ha hb), alphaGt_eq Γ l j] at h
  have hhi (l : Fin n) : acceptProb Γ i b l ≤
      binomBelow (m - 1) (alphaGt Γ j (b / a)) c := by
    have h := (hbounds l).2
    rwa [alphaGt_eq Γ l j] at h
  have hsumlo := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hlo l)
  have hsumhi := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hhi l)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumlo hsumhi
  unfold meanAcceptProb
  constructor
  · have h := mul_le_mul_of_nonneg_left hsumlo (one_div_pos.mpr hn).le
    simpa only [← mul_assoc, one_div_mul_cancel hn.ne', one_mul] using h
  · have h := mul_le_mul_of_nonneg_left hsumhi (one_div_pos.mpr hn).le
    simpa only [← mul_assoc, one_div_mul_cancel hn.ne', one_mul] using h

theorem alphaGt_le_value_tail_onPath (Γ : FiniteGame m n c Seed) (hm : 0 < m) (hc : 0 < c)
    (hΓ : IsAEEquilibrium Γ) (j : Fin n) (b : ℝ) (hb : 0 ≤ b) :
    alphaGt Γ j b ≤ Γ.F.real (Set.Ioi (Γ.g + b)) := by
  have hsub : aboveAt j b ≤ᵐ[userLaw Γ] {d : UserDraw n | Γ.g + b < d.1.1} := by
    filter_upwards [ae_no_overbid_userLaw_onPath Γ hm hc hΓ] with d hd hreach
    have hk : 0 < d.1.2.routeCount := by
      have hcard := Finset.card_pos.mpr ⟨j, hreach.1⟩
      rwa [card_firstK _ _ d.1.2.routeCount_le] at hcard
    have hbid := hd hk
    have hmax : b < max (d.1.1 - Γ.g) 0 := lt_of_lt_of_le hreach.2 hbid
    rcases (lt_max_iff).mp hmax with hval | hzero
    · change Γ.g + b < d.1.1
      linarith
    · exact (not_lt_of_ge hb hzero).elim
  have hmeasure := measure_mono_ae hsub
  have heq : userLaw Γ {d : UserDraw n | Γ.g + b < d.1.1} = Γ.F (Set.Ioi (Γ.g + b)) := by
    rw [← userLaw_value_map Γ, Measure.map_apply
      (show Measurable (fun d : UserDraw n => d.1.1) from
        measurable_fst.comp measurable_fst) measurableSet_Ioi]
    rfl
  change (userLaw Γ (aboveAt j b)).toReal ≤ (Γ.F (Set.Ioi (Γ.g + b))).toReal
  rw [← heq]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure

theorem balanced_receipt_bounds_ae (Γ : FiniteGame m n c Seed)
    (hm : 0 < m) (hc : 0 < c) (hu : UsersOptimal Γ)
    (B : PosteriorSystem Γ) (hB : PosteriorProposerOptimalAE Γ B)
    (hatom : PositiveVisibleAtomless Γ)
    (j : Fin n) (i : Fin m) (a : ℝ) (ha : 0 < a)
    (hA : ∀ r : ℕ, 0 < r → r ≤ n → a * (r : ℝ) ≤ Γ.A.charge r)
    (act : JointAction n) (hb : 0 < act.bid) (hk : 1 ≤ act.routeCount) :
    (binomBelow (m - 1) (alphaGt Γ j (a * act.bid)) c ≤ meanAcceptProb Γ i act.bid ∧
      meanAcceptProb Γ i act.bid ≤ binomBelow (m - 1) (alphaGt Γ j (act.bid / a)) c) ∧
    ((problem Γ i).outcome act).load = act.routeCount * meanAcceptProb Γ i act.bid ∧
    (meanAcceptProb Γ i act.bid ≤ ((problem Γ i).outcome act).success ∧
      ((problem Γ i).outcome act).success ≤ n * meanAcceptProb Γ i act.bid) ∧
    (∀ᵐ v ∂Γ.F, ∀ᵐ b ∂(Γ.σ v), 0 < b.routeCount → b.bid ≤ max (v - Γ.g) 0) ∧
    (∀ b : ℝ, 0 ≤ b → alphaGt Γ j b ≤ Γ.F.real (Set.Ioi (Γ.g + b))) := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have heq := posterior_isAEEquilibrium Γ hu B hB
  exact ⟨meanAcceptProb_bounds_ae Γ (posterior_rationalAtFeasibleLists Γ B hB)
      hatom j i a ha hA act.bid hb,
    load_eq_mean Γ hn i act,
    ⟨meanAcceptProb_le_success Γ hn i act hk, success_le_n_meanAcceptProb Γ hn i act⟩,
    ae_no_overbid_onPath Γ hm hc heq, alphaGt_le_value_tail_onPath Γ hm hc heq j⟩

end FCAppendix.Bayes
