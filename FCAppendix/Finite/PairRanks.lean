import FCAppendix.Probability.BernoulliPairs
import FCAppendix.Finite.ReceiptBoundsAE
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game Filter Topology
open scoped BigOperators

variable {N n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def pairRankIndicators (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ)
    (l : Fin N) (k : Fin 2) (d : UserProfile (N + 1) n) : ℝ :=
  by classical exact if d (i.succAbove l) ∈ aboveAt (j k) b then 1 else 0

lemma pairRankIndicators_measurable (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ)
    (l : Fin N) (k : Fin 2) : Measurable (pairRankIndicators i j b l k) := by
  classical
  unfold pairRankIndicators
  have he : Measurable (fun d : UserProfile (N + 1) n => d (i.succAbove l)) :=
    measurable_pi_apply _
  exact Measurable.ite (he (measurableSet_aboveAt (j k) b)) measurable_const measurable_const

lemma pairRankIndicators_bernoulli (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ)
    (l : Fin N) (k : Fin 2) (d : UserProfile (N + 1) n) :
    pairRankIndicators i j b l k d = 0 ∨ pairRankIndicators i j b l k d = 1 := by
  unfold pairRankIndicators
  split_ifs <;> simp

lemma pairRankIndicators_indep (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ) :
    iIndepFun (BernoulliPairs.pair (pairRankIndicators i j b))
      (Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)) := by
  classical
  let f : UserDraw n → EuclideanSpace ℝ (Fin 2) := fun d =>
    WithLp.toLp 2 (fun k => if d ∈ aboveAt (j k) b then 1 else 0)
  have hf : Measurable f := by
    apply (PiLp.continuous_toLp _ _).measurable.comp
    exact measurable_pi_lambda _ (fun k => Measurable.ite (measurableSet_aboveAt _ _)
      measurable_const measurable_const)
  have hi := iIndepFun_pi (μ := fun _ : Fin (N + 1) => userLaw Γ)
    (X := fun _ => f) (fun _ => hf.aemeasurable)
  have hi' : iIndepFun (fun (l : Fin N) (d : UserProfile (N + 1) n) =>
      f (d (i.succAbove l))) (Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)) :=
    hi.precomp (g := i.succAbove) (Fin.succAboveOrderEmb i).injective
  have he : BernoulliPairs.pair (pairRankIndicators i j b) =
      (fun (l : Fin N) (d : UserProfile (N + 1) n) => f (d (i.succAbove l))) := rfl
  rw [he]
  exact hi'

lemma pairRankIndicators_integral (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ) (l : Fin N) (k : Fin 2) :
    (∫ d, pairRankIndicators i j b l k d ∂Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)) =
      alphaGt Γ (j 0) b := by
  classical
  let f : UserDraw n → ℝ := fun d => if d ∈ aboveAt (j k) b then 1 else 0
  have hf : Measurable f := Measurable.ite (measurableSet_aboveAt (j k) b)
    measurable_const measurable_const
  change (∫ d, f (d (i.succAbove l)) ∂Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)) = _
  rw [integral_comp_eval (μ := fun _ : Fin (N + 1) => userLaw Γ)
    (i := i.succAbove l) (f := f) hf.aestronglyMeasurable]
  dsimp only [f]

  have hh := integral_indicator_one (μ := userLaw Γ) (measurableSet_aboveAt (j k) b)
  change (∫ d, if d ∈ aboveAt (j k) b then (1 : ℝ) else 0 ∂userLaw Γ) = _ at hh
  rw [hh]
  exact alphaGt_eq Γ (j k) (j 0) b

lemma sum_pairRankIndicators (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b : ℝ)
    (k : Fin 2) (d : UserProfile (N + 1) n) :
    (∑ l, pairRankIndicators i j b l k d) =
      (PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d : ℝ) := by
  classical
  rw [PiBinomial.count_eq_sum, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hsum := Fin.sum_univ_succAbove
    (fun l => if d l ∈ aboveAt (j k) b then (1 : ℝ) else 0) i
  have herase := Finset.sum_erase_add Finset.univ
    (fun l => if d l ∈ aboveAt (j k) b then (1 : ℝ) else 0) (Finset.mem_univ i)
  dsimp only [pairRankIndicators]
  linarith

def pairRankThreshold (N c : ℕ) (p σ : ℝ) : ℝ := ((c : ℝ) - 1 - N * p) / σ

lemma pairRank_load_eq (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b p σ : ℝ)
    (k : Fin 2) (d : UserProfile (N + 1) n) :
    BernoulliPairs.load (pairRankIndicators i j b) p σ k d =
      ((PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d : ℝ) - N * p) / σ := by
  rw [BernoulliPairs.load_eq, Finset.sum_sub_distrib, sum_pairRankIndicators]
  simp

lemma pairRank_load_le_iff (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b p σ : ℝ)
    (hσ : 0 < σ) (k : Fin 2) (d : UserProfile (N + 1) n) :
    BernoulliPairs.load (pairRankIndicators i j b) p σ k d ≤ pairRankThreshold N c p σ ↔
      PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d < c := by
  rw [pairRank_load_eq, pairRankThreshold, div_le_div_iff_of_pos_right hσ]
  have hh : (PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d : ℝ) + 1 ≤ c ↔
      PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d < c := by
    norm_cast
  constructor
  · intro h
    apply hh.mp
    linarith
  · intro h
    have h' := hh.mpr h
    linarith

theorem ae_rivals_atLeast_eq_above (Γ : FiniteGame (N + 1) n c Seed)
    (hatom : PositiveVisibleAtomless Γ) (i : Fin (N + 1)) (j : Fin n) (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂backgroundLaw Γ, rivals i (atLeastAt j b) ω = rivals i (aboveAt j b) ω := by
  classical
  have hn := measure_eq_zero_iff_ae_notMem.mp (hatom j b hb)
  have he : ∀ᵐ d ∂userLaw Γ, (d ∈ atLeastAt j b ↔ d ∈ aboveAt j b) := by
    filter_upwards [hn] with d hd
    change (_ ∧ b ≤ _) ↔ (_ ∧ b < _)
    constructor
    · rintro ⟨hreach, hbid⟩
      exact ⟨hreach, lt_of_le_of_ne hbid (fun hh => hd ⟨hreach, hh.symm⟩)⟩
    · exact fun hh => ⟨hh.1, hh.2.le⟩
  have hall : ∀ᵐ d ∂Measure.pi (fun _ : Fin (N + 1) => userLaw Γ),
      ∀ l, d l ∈ atLeastAt j b ↔ d l ∈ aboveAt j b :=
    ae_all_iff.mpr (fun l => (measurePreserving_eval (fun _ : Fin (N + 1) => userLaw Γ) l).quasiMeasurePreserving.ae he)
  have hback : ∀ᵐ ω ∂backgroundLaw Γ,
      ∀ l, ω.1 l ∈ atLeastAt j b ↔ ω.1 l ∈ aboveAt j b :=
    measurePreserving_fst.quasiMeasurePreserving.ae hall
  filter_upwards [hback] with ω hω
  unfold rivals PiBinomial.count
  congr 1
  ext l
  simp only [Finset.mem_filter, hω l]

theorem ae_ppi_accepts_iff_rank (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (j : Fin n) (hj : ProposerRationalAtFeasibleLists Γ j)
    (i : Fin (N + 1)) (b : ℝ) (hb : 0 < b) :
    ∀ᵐ ω ∂backgroundLaw Γ, Accepts Γ i b j ω ↔ rivals i (aboveAt j b) ω < c := by
  have hcharge (r : ℕ) (_hr : 0 < r) (_hrn : r ≤ n) : 1 * (r : ℝ) ≤ Γ.A.charge r := by
    simp [hA, Schedule.ppi]
  have hr := ae_receipt_rank_bounds Γ j hj i 1 (by norm_num) hcharge b hb
  simp only [one_mul, div_one] at hr
  filter_upwards [hr, ae_rivals_atLeast_eq_above Γ hatom i j b hb] with ω hω he
  exact ⟨hω.2, fun hh => hω.1 (by rwa [he])⟩

theorem ppi_pair_acceptance_eq_rank (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (j : Fin 2 → Fin n) (hj : ∀ k, ProposerRationalAtFeasibleLists Γ (j k))
    (i : Fin (N + 1)) (b : ℝ) (hb : 0 < b) :
    (backgroundLaw Γ).real {ω | Accepts Γ i b (j 0) ω ∧ Accepts Γ i b (j 1) ω} =
      (Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)).real {d |
        PiBinomial.count (aboveAt (j 0) b) (Finset.univ.erase i) d < c ∧
        PiBinomial.count (aboveAt (j 1) b) (Finset.univ.erase i) d < c} := by
  have he : (backgroundLaw Γ).real {ω | Accepts Γ i b (j 0) ω ∧ Accepts Γ i b (j 1) ω} =
      (backgroundLaw Γ).real {ω | rivals i (aboveAt (j 0) b) ω < c ∧
        rivals i (aboveAt (j 1) b) ω < c} := by
    apply measureReal_congr
    filter_upwards [ae_ppi_accepts_iff_rank Γ hA hatom (j 0) (hj 0) i b hb,
      ae_ppi_accepts_iff_rank Γ hA hatom (j 1) (hj 1) i b hb] with ω h0 h1
    exact propext (and_congr h0 h1)
  rw [he]
  have hset : {ω : Background (N + 1) n Seed | rivals i (aboveAt (j 0) b) ω < c ∧
      rivals i (aboveAt (j 1) b) ω < c} = {d : UserProfile (N + 1) n |
        PiBinomial.count (aboveAt (j 0) b) (Finset.univ.erase i) d < c ∧
        PiBinomial.count (aboveAt (j 1) b) (Finset.univ.erase i) d < c} ×ˢ Set.univ := by
    ext ω
    simp [rivals]
  rw [hset, backgroundLaw, measureReal_prod_prod, probReal_univ, mul_one]

theorem ppi_pair_acceptance_eq_normalized (Γ : FiniteGame (N + 1) n c Seed)
    (hA : Γ.A = Schedule.ppi n) (hatom : PositiveVisibleAtomless Γ)
    (j : Fin 2 → Fin n) (hj : ∀ k, ProposerRationalAtFeasibleLists Γ (j k))
    (i : Fin (N + 1)) (b : ℝ) (hb : 0 < b) (σ : ℝ) (hσ : 0 < σ) :
    (backgroundLaw Γ).real {ω | Accepts Γ i b (j 0) ω ∧ Accepts Γ i b (j 1) ω} =
      (Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)).real {d |
        BernoulliPairs.load (pairRankIndicators i j b) (alphaGt Γ (j 0) b) σ 0 d ≤
          pairRankThreshold N c (alphaGt Γ (j 0) b) σ ∧
        BernoulliPairs.load (pairRankIndicators i j b) (alphaGt Γ (j 0) b) σ 1 d ≤
          pairRankThreshold N c (alphaGt Γ (j 0) b) σ} := by
  rw [ppi_pair_acceptance_eq_rank Γ hA hatom j hj i b hb]
  congr 1
  ext d
  simp only [Set.mem_setOf_eq, pairRank_load_le_iff _ _ _ _ _ hσ]

lemma nonrare_standardized_threshold_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (hm : ∫ ω, X ω ∂μ = 0) (hv : variance X μ = 1)
    (ε t : ℝ) (hε : 0 < ε) (hq : ε ≤ μ.real {ω | X ω ≤ t}) :
    -Real.sqrt (2 / ε) ≤ t := by
  have hs : 0 < Real.sqrt (2 / ε) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 / ε by positivity)
  have hi : ∫ ω, X ω ^ 2 ∂μ = 1 := by
    rw [variance_eq_integral hX.aemeasurable, hm] at hv
    simpa only [sub_zero] using hv
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg (X ω)) hX.integrable_sq
    (Real.sqrt (2 / ε) ^ 2)
  rw [hi] at hmark
  by_contra hnot
  have ht : t < -Real.sqrt (2 / ε) := lt_of_not_ge hnot
  have hsub : {ω | X ω ≤ t} ⊆ {ω | Real.sqrt (2 / ε) ^ 2 ≤ X ω ^ 2} := by
    intro ω hω
    change X ω ≤ t at hω
    change Real.sqrt (2 / ε) ^ 2 ≤ X ω ^ 2
    have hh : Real.sqrt (2 / ε) < -X ω := by linarith
    nlinarith [sq_nonneg (X ω + Real.sqrt (2 / ε))]
  have hq' := hq.trans (measureReal_mono hsub)
  have hprod := mul_le_mul_of_nonneg_left hq' (sq_nonneg (Real.sqrt (2 / ε)))
  have he : Real.sqrt (2 / ε) ^ 2 * ε = 2 := by rw [hs2]; field_simp
  linarith

lemma pairRank_cdf_eq_binomBelow (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b p σ : ℝ) (hσ : 0 < σ) (k : Fin 2) :
    (Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)).real {d |
      BernoulliPairs.load (pairRankIndicators i j b) p σ k d ≤ pairRankThreshold N c p σ} =
      binomBelow N (alphaGt Γ (j k) b) c := by
  have he : {d : UserProfile (N + 1) n |
      BernoulliPairs.load (pairRankIndicators i j b) p σ k d ≤ pairRankThreshold N c p σ} =
      {d | PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d < c} := by
    ext d
    exact pairRank_load_le_iff i j b p σ hσ k d
  rw [he]
  have hp := prob_rivals_lt Γ i (aboveAt (j k) b) (measurableSet_aboveAt _ _) c
  have hset : {ω : Background (N + 1) n Seed | rivals i (aboveAt (j k) b) ω < c} =
      {d : UserProfile (N + 1) n | PiBinomial.count (aboveAt (j k) b) (Finset.univ.erase i) d < c} ×ˢ Set.univ := by
    ext ω
    simp [rivals]
  rw [hset, backgroundLaw, measureReal_prod_prod, probReal_univ, mul_one] at hp
  simpa only [Nat.add_sub_cancel, alphaGt] using hp

lemma nonrare_pairRankThreshold_ge (Γ : FiniteGame (N + 1) n c Seed)
    (i : Fin (N + 1)) (j : Fin 2 → Fin n) (b σ : ℝ) (hσ : 0 < σ)
    (hvar : (N : ℝ) * alphaGt Γ (j 0) b * (1 - alphaGt Γ (j 0) b) = σ ^ 2)
    (ε : ℝ) (hε : 0 < ε) (hq : ε ≤ binomBelow N (alphaGt Γ (j 0) b) c) :
    -Real.sqrt (2 / ε) ≤ pairRankThreshold N c (alphaGt Γ (j 0) b) σ := by
  let μ := Measure.pi (fun _ : Fin (N + 1) => userLaw Γ)
  have hm := pairRankIndicators_measurable i j b
  have h01 : ∀ l k, ∀ᵐ d ∂μ, pairRankIndicators i j b l k d = 0 ∨ pairRankIndicators i j b l k d = 1 :=
    fun l k => Filter.Eventually.of_forall (pairRankIndicators_bernoulli i j b l k)
  apply nonrare_standardized_threshold_ge μ
    (BernoulliPairs.load (pairRankIndicators i j b) (alphaGt Γ (j 0) b) σ 0)
    (BernoulliPairs.memLp_load _ _ _ hm h01 2 0)
    (BernoulliPairs.integral_load _ _ _ hm h01 (pairRankIndicators_integral Γ i j b) 0)
    (BernoulliPairs.variance_load _ _ _ hm h01 (pairRankIndicators_integral Γ i j b)
      (pairRankIndicators_indep Γ i j b) hσ hvar 0) ε _ hε
  rwa [pairRank_cdf_eq_binomBelow Γ i j b _ σ hσ 0]

theorem eventually_ppi_pair_acceptance_pos
    (M C : ℕ → ℕ) (Γ : (m : ℕ) → FiniteGame (M m + 1) n (C m) Seed)
    (i : (m : ℕ) → Fin (M m + 1)) (j : Fin 2 → Fin n) (b σ : ℕ → ℝ)
    (hA : ∀ m, (Γ m).A = Schedule.ppi n)
    (hatom : ∀ m, PositiveVisibleAtomless (Γ m))
    (hj : ∀ m k, ProposerRationalAtFeasibleLists (Γ m) (j k))
    (hb : ∀ m, 0 < b m) (hσ : ∀ m, 0 < σ m)
    (hvar : ∀ m, (M m : ℝ) * alphaGt (Γ m) (j 0) (b m) *
      (1 - alphaGt (Γ m) (j 0) (b m)) = σ m ^ 2)
    (hσlim : Tendsto σ atTop atTop) {ρ : ℝ}
    (hp : Tendsto (fun m => alphaGt (Γ m) (j 0) (b m)) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (a : ℝ)
    (ht : ∀ᶠ m in atTop, a ≤ pairRankThreshold (M m) (C m) (alphaGt (Γ m) (j 0) (b m)) (σ m)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ m in atTop, d ≤ (backgroundLaw (Γ m)).real
      {ω | Accepts (Γ m) (i m) (b m) (j 0) ω ∧ Accepts (Γ m) (i m) (b m) (j 1) ω} := by
  let μ := fun m => Measure.pi (fun _ : Fin (M m + 1) => userLaw (Γ m))
  have hpair := BernoulliPairs.eventually_joint_pos μ M
    (fun m => pairRankIndicators (i m) j (b m))
    (fun m => alphaGt (Γ m) (j 0) (b m)) σ
    (fun m => pairRankIndicators_measurable (i m) j (b m))
    (fun m l k => Filter.Eventually.of_forall (pairRankIndicators_bernoulli (i m) j (b m) l k))
    (fun m => pairRankIndicators_integral (Γ m) (i m) j (b m))
    (fun m => pairRankIndicators_indep (Γ m) (i m) j (b m))
    hσ hvar hσlim hp hρ0 hρ1 a
    (fun m => pairRankThreshold (M m) (C m) (alphaGt (Γ m) (j 0) (b m)) (σ m)) ht
  obtain ⟨d, hd, hde⟩ := hpair
  refine ⟨d, hd, ?_⟩
  filter_upwards [hde] with m hm
  rw [ppi_pair_acceptance_eq_normalized (Γ m) (hA m) (hatom m) j (hj m) (i m) (b m) (hb m) (σ m) (hσ m)]
  exact hm

theorem eventually_nonrare_ppi_pair_acceptance_pos
    (M C : ℕ → ℕ) (Γ : (m : ℕ) → FiniteGame (M m + 1) n (C m) Seed)
    (i : (m : ℕ) → Fin (M m + 1)) (j : Fin 2 → Fin n) (b σ : ℕ → ℝ)
    (hA : ∀ m, (Γ m).A = Schedule.ppi n)
    (hatom : ∀ m, PositiveVisibleAtomless (Γ m))
    (hj : ∀ m k, ProposerRationalAtFeasibleLists (Γ m) (j k))
    (hb : ∀ m, 0 < b m) (hσ : ∀ m, 0 < σ m)
    (hvar : ∀ m, (M m : ℝ) * alphaGt (Γ m) (j 0) (b m) *
      (1 - alphaGt (Γ m) (j 0) (b m)) = σ m ^ 2)
    (hσlim : Tendsto σ atTop atTop) {ρ : ℝ}
    (hp : Tendsto (fun m => alphaGt (Γ m) (j 0) (b m)) atTop (𝓝 ρ))
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2) (ε : ℝ) (hε : 0 < ε)
    (hq : ∀ᶠ m in atTop, ε ≤ binomBelow (M m) (alphaGt (Γ m) (j 0) (b m)) (C m)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ m in atTop, d ≤ (backgroundLaw (Γ m)).real
      {ω | Accepts (Γ m) (i m) (b m) (j 0) ω ∧ Accepts (Γ m) (i m) (b m) (j 1) ω} := by
  apply eventually_ppi_pair_acceptance_pos M C Γ i j b σ hA hatom hj hb hσ hvar hσlim hp
    hρ0 hρ1 (-Real.sqrt (2 / ε))
  filter_upwards [hq] with m hm
  exact nonrare_pairRankThreshold_ge (Γ m) (i m) j (b m) (σ m) (hσ m) (hvar m) ε hε hm

end FCAppendix.Bayes
