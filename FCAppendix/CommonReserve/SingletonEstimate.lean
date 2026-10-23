import FCAppendix.CommonReserve.FiniteEstimates
import FCAppendix.CommonReserve.ActualInterim
import FCAppendix.Finite.RankConcentration

noncomputable section
namespace FCAppendix.CommonReserve
open Game MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
variable {m n c : ℕ} {r : ℝ} {Seed : Type*} [MeasurableSpace Seed]

def rivalCount (i : Fin m) (j : Fin n) (x : ℝ) (d : Fin m → UserDraw n r) : ℕ :=
  PiBinomial.count (aboveAt j x) (Finset.univ.erase i) d

theorem measurable_rivalCount (i : Fin m) (j : Fin n) (x : ℝ) :
    Measurable (rivalCount (r := r) i j x) :=
  PiBinomial.measurable_count (aboveAt j x) (measurableSet_aboveAt j x) _

theorem singleton_included_of_rank (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b x : ℝ) (hb : r ≤ b) (hb0 : 0 < b)
    (hxb : x < b) (ω : Sample m n r Seed)
    (hopt : Finite.Optimal c
      (fun l => Bayes.entryBid (observe (FiniteGame.deviated i (singleton j b hb) ω) j l))
      (allocation (FiniteGame.deviated i (singleton j b hb) ω) Γ.policy ω.2 j))
    (hrank : rivalCount i j x ω.1 < c) :
    successIndicator (Γ.focalCount i (singleton j b hb) ω).val = 1 := by
  classical
  let L := observe (FiniteGame.deviated i (singleton j b hb) ω) j
  have hLi : L i = some b := by simp [L, observe, FiniteGame.deviated, singleton]
  have hsub : Finset.univ.filter (fun l => l ≠ i ∧
      Bayes.entryBid (L i) ≤ Bayes.entryBid (L l)) ⊆
      (Finset.univ.erase i).filter (fun l => ω.1 l ∈ aboveAt j x) := by
    intro l hl
    have hh := (Finset.mem_filter.mp hl).2
    have he : L l = (ω.1 l).2.val j := by
      simp [L, observe, FiniteGame.deviated, Function.update_of_ne hh.1]
    have hle : b ≤ Bayes.entryBid ((ω.1 l).2.val j) := by
      simpa only [hLi, he, Bayes.entryBid] using hh.2
    have hsome : (ω.1 l).2.val j ≠ none := by
      intro hz
      have hzero : b ≤ 0 := by simpa [hz, Bayes.entryBid] using hle
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hh.1, Finset.mem_univ l⟩,
      ⟨hsome, hxb.trans_le hle⟩⟩
  have hcomp : (Finset.univ.filter (fun l => l ≠ i ∧
      Bayes.entryBid (L i) ≤ Bayes.entryBid (L l))).card < c :=
    (Finset.card_le_card hsub).trans_lt hrank
  have hi := Finite.included_of_few_competitors c _ _ hopt i
    (show 0 < Bayes.entryBid (L i) by simpa only [hLi, Bayes.entryBid] using hb0) hcomp
  have hK : 0 < count (FiniteGame.deviated i (singleton j b hb) ω) Γ.policy ω.2 i := by
    apply Finset.card_pos.mpr
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hi⟩⟩
  simp only [FiniteGame.focalCount, successIndicator, ne_of_gt hK, if_false]

theorem singleton_success_ge_rank (Γ : FiniteGame m n c r Seed)
    (i : Fin m) (j : Fin n) (b x : ℝ) (hb : r ≤ b) (hb0 : 0 < b)
    (hxb : x < b) (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    (∫ d : Fin m → UserDraw n r, if rivalCount i j x d < c then (1 : ℝ) else 0
      ∂(Measure.pi fun _ : Fin m => Γ.userLaw)) ≤
        (Γ.outcome i (singleton j b hb)).success := by
  classical
  let a := singleton j b hb
  have hm : Measurable (fun ω : Sample m n r Seed =>
      if rivalCount i j x ω.1 < c then (1 : ℝ) else 0) :=
    Measurable.ite (((measurable_rivalCount i j x).comp measurable_fst)
      (MeasurableSet.of_discrete : MeasurableSet {k : ℕ | k < c}))
      measurable_const measurable_const
  have hS : Measurable (fun ω => successIndicator (Γ.focalCount i a ω).val) :=
    (measurable_of_countable (fun k : Fin (n + 1) => successIndicator k.val)).comp
      (Γ.measurable_focalCount i a)
  have hset := measurableSet_le hm hS
  have hle : ∀ᵐ ω ∂Γ.sampleLaw,
      (if rivalCount i j x ω.1 < c then (1 : ℝ) else 0) ≤
        successIndicator (Γ.focalCount i a ω).val := by
    apply (Measure.ae_prod_iff_ae_ae hset).mpr
    apply Eventually.of_forall
    intro d
    let L : LocalList m := fun l => (Function.update (fun k => (d k).2) i a l).val j
    have hL (l : Fin m) (t : ℝ) (ht : L l = some t) : r ≤ t :=
      (Function.update (fun k => (d k).2) i a l).property j t ht
    have hs := (measurePreserving_eval (fun _ : Fin n => Γ.seedLaw) j).quasiMeasurePreserving.ae
      (hT.ae_optimal Γ.reserve_nonneg L hL)
    filter_upwards [hs] with s hs
    by_cases hrank : rivalCount i j x d < c
    · rw [if_pos hrank, singleton_included_of_rank Γ i j b x hb hb0 hxb (d, s) hs hrank]
    · rw [if_neg hrank]
      exact successIndicator_nonneg _
  have hi : Integrable (fun ω : Sample m n r Seed =>
      if rivalCount i j x ω.1 < c then (1 : ℝ) else 0) Γ.sampleLaw :=
    Integrable.of_bound hm.aestronglyMeasurable 1
      (Eventually.of_forall fun _ => by split_ifs <;> norm_num)
  have hh := integral_mono_ae hi (Γ.integrable_count_test i a
    (fun k => successIndicator k.val)) hle
  have hsuccess : (Γ.outcome i a).success =
      ∫ ω, successIndicator (Γ.focalCount i a ω).val ∂Γ.sampleLaw :=
    Γ.outcome_expect i a (fun z => successIndicator z.val)
  rw [← hsuccess] at hh
  have hfst : (∫ ω : Sample m n r Seed,
      if rivalCount i j x ω.1 < c then (1 : ℝ) else 0 ∂Γ.sampleLaw) =
      ∫ d : Fin m → UserDraw n r, if rivalCount i j x d < c then (1 : ℝ) else 0
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw) := by
    change (∫ ω : Sample m n r Seed,
      if rivalCount i j x ω.1 < c then (1 : ℝ) else 0
        ∂(Measure.pi fun _ : Fin m => Γ.userLaw).prod
          (Measure.pi fun _ : Fin n => Γ.seedLaw)) = _
    rw [integral_prod _ hi]
    apply integral_congr_ae
    exact Eventually.of_forall fun d => by
      by_cases hd : rivalCount i j x d < c <;> simp [hd]
  exact hfst.symm.trans_le hh

theorem singleton_success_ge_binomial (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hc : c ≤ m) (i : Fin m) (j : Fin n) (b x : ℝ)
    (hb : r ≤ b) (hb0 : 0 < b) (hxb : x < b)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    Bayes.binomBelow (m - 1) (bidTail Γ j x) c ≤
      (Γ.outcome i (singleton j b hb)).success := by
  have hh := singleton_success_ge_rank Γ i j b x hb hb0 hxb hT
  have hprob := (PiBinomial.integral_count_eq Γ.userLaw (aboveAt j x)
    (measurableSet_aboveAt j x) (Finset.univ.erase i)
    (fun k => if k < c then (1 : ℝ) else 0)).symm.trans_le hh
  have he : (Finset.univ.erase i).card = m - 1 := by simp
  rw [he] at hprob
  rw [Bayes.binomBelow_eq_prob (m - 1) c (by omega)
    (bidTail Γ j x) (bidTail_nonneg Γ j x) (bidTail_le_one Γ j x)]
  refine le_trans ?_ hprob
  apply le_of_eq
  unfold FiniteLaw.prob
  apply FiniteLaw.expect_congr
  intro z
  split_ifs <;> rfl

theorem singleton_at_quantile (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hc : c ≤ m) (i : Fin m) (j : Fin n)
    (δ d : ℝ) (hδ : 0 < δ) (hδκ : δ < (c : ℝ) / m) (hd : 0 < d)
    (hT : UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    ∃ hb : r ≤ quantile Γ j δ + d,
      1 - ((m - 1 : ℕ) : ℝ) / (4 * ((m : ℝ) * δ) ^ 2) ≤
        (Γ.outcome i (singleton j (quantile Γ j δ + d) hb)).success := by
  have ht := reserve_le_quantile Γ j δ hδκ
  have hb : r ≤ quantile Γ j δ + d := by linarith
  refine ⟨hb, ?_⟩
  let x := quantile Γ j δ + d / 2
  have hx := quantile_tail_above Γ j δ (d / 2) hδκ (by linarith)
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmul : (m : ℝ) * bidTail Γ j x ≤ c - (m : ℝ) * δ := by
    have hh := mul_le_mul_of_nonneg_left hx hmR.le
    rw [mul_sub, mul_div_cancel₀ _ hmR.ne'] at hh
    exact hh
  have hmr : ((m - 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.mpr (Nat.sub_le _ _)
  have hgap : (m : ℝ) * δ ≤ c - ((m - 1 : ℕ) : ℝ) * bidTail Γ j x := by
    have hh := mul_le_mul_of_nonneg_right hmr (bidTail_nonneg Γ j x)
    linarith
  exact (Bayes.binomBelow_lower_of_gap (m - 1) c (by omega) (bidTail Γ j x)
    ((m : ℝ) * δ) (bidTail_nonneg Γ j x) (bidTail_le_one Γ j x)
    (mul_pos hmR hδ) hgap).trans
      (singleton_success_ge_binomial Γ hm hc i j (quantile Γ j δ + d) x hb
        (by have := Γ.reserve_nonneg; linarith) (by dsimp [x]; linarith) hT)

theorem singleton_at_min_quantile (Γ : FiniteGame m n c r Seed)
    (hm : 0 < m) (hc : c ≤ m) (hn : 0 < n) (i : Fin m)
    (δ d : ℝ) (hδ : 0 < δ) (hδκ : δ < (c : ℝ) / m) (hd : 0 < d)
    (hT : ∀ j, UniformReserveRule Γ.seedLaw (Γ.policy j) r) :
    ∃ (j : Fin n) (hb : r ≤ price Γ δ + d),
      1 - ((m - 1 : ℕ) : ℝ) / (4 * ((m : ℝ) * δ) ^ 2) ≤
        (Γ.outcome i (singleton j (price Γ δ + d) hb)).success := by
  obtain ⟨j, hj⟩ := exists_price_minimizer Γ δ hn
  rw [hj]
  obtain ⟨hb, hS⟩ := singleton_at_quantile Γ hm hc i j δ d hδ hδκ hd (hT j)
  exact ⟨j, hb, hS⟩

end FCAppendix.CommonReserve
