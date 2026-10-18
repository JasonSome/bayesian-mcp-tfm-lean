import FCAppendix.Proposer.ExactCapacity
import Mathlib.Probability.Kernel.Representation

noncomputable section
namespace FCAppendix.ExactCapacity
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
attribute [local instance] Classical.propDecidable

def endpointSet (p : ι → ℝ) : Finset ι := Finset.univ.filter (fun i => p i = 1)
def Roundable (p : ι → ℝ) (a : ι × ι) : Prop :=
  a.1 ≠ a.2 ∧ (0 < p a.1 ∧ p a.1 < 1) ∧ (0 < p a.2 ∧ p a.2 < 1)
def upStep (p : ι → ℝ) (a : ι × ι) : ℝ := min (1-p a.1) (p a.2)
def downStep (p : ι → ℝ) (a : ι × ι) : ℝ := min (p a.1) (1-p a.2)
def upWeight (p : ι → ℝ) (a : ι × ι) : ℝ :=
  downStep p a / (upStep p a + downStep p a)

omit [Fintype ι] [DecidableEq ι] in
lemma upStep_pos {p : ι → ℝ} {a : ι × ι} (h : Roundable p a) : 0 < upStep p a :=
  lt_min (sub_pos.mpr h.2.1.2) h.2.2.1
omit [Fintype ι] [DecidableEq ι] in
lemma downStep_pos {p : ι → ℝ} {a : ι × ι} (h : Roundable p a) : 0 < downStep p a :=
  lt_min h.2.1.1 (sub_pos.mpr h.2.2.2)
omit [Fintype ι] [DecidableEq ι] in
lemma upWeight_nonneg {p : ι → ℝ} {a : ι × ι} (h : Roundable p a) : 0 ≤ upWeight p a :=
  (div_pos (downStep_pos h) (add_pos (upStep_pos h) (downStep_pos h))).le
omit [Fintype ι] [DecidableEq ι] in
lemma upWeight_le_one {p : ι → ℝ} {a : ι × ι} (h : Roundable p a) : upWeight p a ≤ 1 := by
  apply (div_le_one (add_pos (upStep_pos h) (downStep_pos h))).mpr
  linarith [upStep_pos h]

def scanRound (next : (ι → ℝ) → FiniteLaw (Finset ι)) (p : ι → ℝ) :
    List (ι × ι) → FiniteLaw (Finset ι)
  | [] => FiniteLaw.dirac (endpointSet p)
  | a :: rest => if h : Roundable p a then
      FiniteLaw.mixture
        (next (shift p a.1 a.2 (upStep p a)))
        (next (shift p a.1 a.2 (-downStep p a)))
        (upWeight p a) (upWeight_nonneg h) (upWeight_le_one h)
      else scanRound next p rest

def roundingLottery : ℕ → (ι → ℝ) → FiniteLaw (Finset ι)
  | 0, p => FiniteLaw.dirac (endpointSet p)
  | d+1, p => scanRound (roundingLottery d) p (Finset.univ.toList)

def measurableLottery (p : ι → ℝ) : FiniteLaw (Finset ι) :=
  roundingLottery (Fintype.card ι) p

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_roundable (a : ι × ι) : MeasurableSet {p : ι → ℝ | Roundable p a} := by
  unfold Roundable
  exact (MeasurableSet.const _).inter
    (((measurableSet_lt measurable_const (measurable_pi_apply a.1)).inter
      (measurableSet_lt (measurable_pi_apply a.1) measurable_const)).inter
      ((measurableSet_lt measurable_const (measurable_pi_apply a.2)).inter
      (measurableSet_lt (measurable_pi_apply a.2) measurable_const)))

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_upStep (a : ι × ι) : Measurable (fun p => upStep p a) :=
  (measurable_const.sub (measurable_pi_apply a.1)).min (measurable_pi_apply a.2)
omit [Fintype ι] [DecidableEq ι] in
lemma measurable_downStep (a : ι × ι) : Measurable (fun p => downStep p a) :=
  (measurable_pi_apply a.1).min (measurable_const.sub (measurable_pi_apply a.2))
omit [Fintype ι] [DecidableEq ι] in
lemma measurable_upWeight (a : ι × ι) : Measurable (fun p => upWeight p a) :=
  (measurable_downStep a).div ((measurable_upStep a).add (measurable_downStep a))

omit [Fintype ι] in
lemma measurable_shift (a : ι × ι) (t : (ι → ℝ) → ℝ) (ht : Measurable t) :
    Measurable (fun p => shift p a.1 a.2 (t p)) := by
  apply measurable_pi_lambda
  intro i
  unfold shift
  split_ifs <;> fun_prop

lemma measurable_endpoint_mass (S : Finset ι) :
    Measurable (fun p : ι → ℝ => (FiniteLaw.dirac (endpointSet p)).mass S) := by
  have hm : MeasurableSet {p : ι → ℝ | S = endpointSet p} := by
    have he : {p : ι → ℝ | S = endpointSet p} =
        ⋂ i, {p : ι → ℝ | (i ∈ S ↔ p i = 1)} := by
      ext p
      simp only [mem_setOf_eq, mem_iInter]
      constructor
      · intro h i
        rw [h]
        simp [endpointSet]
      · intro h
        ext i
        simpa [endpointSet] using h i
    rw [he]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ S
    · simpa [hi] using measurableSet_eq_fun (measurable_pi_apply i) measurable_const
    · convert (measurableSet_eq_fun (measurable_pi_apply i : Measurable (fun p : ι → ℝ => p i))
        (measurable_const : Measurable (fun _ : ι → ℝ => (1 : ℝ)))).compl using 1
      ext p
      simp only [mem_setOf_eq, mem_compl_iff, hi, false_iff]
  simpa only [FiniteLaw.dirac] using Measurable.ite hm measurable_const measurable_const

lemma measurable_scanRound_mass
    (next : (ι → ℝ) → FiniteLaw (Finset ι))
    (hnext : ∀ S, Measurable (fun p => (next p).mass S))
    (pairs : List (ι × ι)) (S : Finset ι) :
    Measurable (fun p => (scanRound next p pairs).mass S) := by
  classical
  induction pairs with
  | nil => exact measurable_endpoint_mass S
  | cons a rest ih =>
    have hplus := (hnext S).comp (measurable_shift a _ (measurable_upStep a))
    have hminus := (hnext S).comp (measurable_shift a _ (measurable_downStep a).neg)
    have hmass : Measurable (fun p : ι → ℝ =>
        upWeight p a * (next (shift p a.1 a.2 (upStep p a))).mass S +
        (1-upWeight p a) * (next (shift p a.1 a.2 (-downStep p a))).mass S) :=
      ((measurable_upWeight a).mul hplus).add
        ((measurable_const.sub (measurable_upWeight a)).mul hminus)
    convert Measurable.ite (measurableSet_roundable a) hmass ih using 1
    funext p
    simp only [scanRound]
    split <;> simp_all only [FiniteLaw.mixture]
    exact fun _ => Classical.propDecidable _

theorem measurable_roundingLottery_mass (d : ℕ) :
    ∀ S : Finset ι, Measurable (fun p => (roundingLottery d p).mass S) := by
  induction d with
  | zero => exact measurable_endpoint_mass
  | succ d ih => exact fun S => measurable_scanRound_mass _ ih _ S

theorem measurable_measurableLottery_mass (S : Finset ι) :
    Measurable (fun p => (measurableLottery p).mass S) :=
  measurable_roundingLottery_mass _ S

def Implements (p : ι → ℝ) (c : ℕ) (μ : FiniteLaw (Finset ι)) : Prop :=
  (∀ S, μ.mass S ≠ 0 → S.card = c) ∧
    (∀ i, μ.prob (fun S => i ∈ S) = p i)

lemma endpoint_implements (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : ∑ i, p i = c) (hf : fractional p = ∅) :
    Implements p c (FiniteLaw.dirac (endpointSet p)) := by
  have endpoints : ∀ i, p i = 0 ∨ p i = 1 := by
    intro i
    have hnot : ¬ (0 < p i ∧ p i < 1) := by
      intro hi
      have hm : i ∈ fractional p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [hf] at hm
      exact Finset.notMem_empty i hm
    by_cases hz : p i = 0
    · exact Or.inl hz
    · right
      exact le_antisymm (hp1 i) (le_of_not_gt fun hlt =>
        hnot ⟨lt_of_le_of_ne (hp0 i) (Ne.symm hz), hlt⟩)
  have hmarg : ∀ i, (if i ∈ endpointSet p then (1 : ℝ) else 0) = p i := by
    intro i
    rcases endpoints i with hz | ho
    · simp [endpointSet, hz]
    · simp [endpointSet, ho]
  have hcard : (endpointSet p).card = c := by
    have he : ((endpointSet p).card : ℝ) = (c : ℝ) := by
      rw [← Game.sum_membership_real]
      simp_rw [hmarg]
      exact hsum
    exact_mod_cast he
  constructor
  · intro S hS
    have he : S = endpointSet p := by
      by_contra hne
      exact hS (by simp [FiniteLaw.dirac, hne])
    simpa only [he] using hcard
  · intro i
    rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_dirac]
    exact hmarg i

lemma mixture_implements (p : ι → ℝ) (c : ℕ) (a : ι × ι)
    (h : Roundable p a) (μ ν : FiniteLaw (Finset ι))
    (hμ : Implements (shift p a.1 a.2 (upStep p a)) c μ)
    (hν : Implements (shift p a.1 a.2 (-downStep p a)) c ν) :
    Implements p c (FiniteLaw.mixture μ ν (upWeight p a)
      (upWeight_nonneg h) (upWeight_le_one h)) := by
  constructor
  · intro S hS
    by_cases hm : μ.mass S = 0
    · exact hν.1 S (fun hn => hS (by simp [FiniteLaw.mixture, hm, hn]))
    · exact hμ.1 S hm
  · intro i
    rw [FiniteLaw.prob_eq_expect, FiniteLaw.expect_mixture,
      ← FiniteLaw.prob_eq_expect, ← FiniteLaw.prob_eq_expect, hμ.2, hν.2]
    exact shift_mixture p a.1 a.2 (upStep p a) (downStep p a)
      (upStep_pos h) (downStep_pos h) i

lemma scanRound_implements (d : ℕ)
    (next : (ι → ℝ) → FiniteLaw (Finset ι))
    (hnext : ∀ (p : ι → ℝ) (c : ℕ), (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) →
      (∑ i, p i = c) → (fractional p).card ≤ d → Implements p c (next p))
    (pairs : List (ι × ι)) (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : ∑ i, p i = c) (hfrac : (fractional p).card ≤ d+1)
    (hcover : ∀ a, Roundable p a → a ∈ pairs) :
    Implements p c (scanRound next p pairs) := by
  induction pairs with
  | nil =>
    have hf : fractional p = ∅ := by
      by_contra hne
      obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hi' := (Finset.mem_filter.mp hi).2
      obtain ⟨j,hji,hj0,hj1⟩ := another_fractional p c hp0 hp1 hsum i hi'
      exact List.not_mem_nil (hcover (i,j) ⟨hji.symm,hi',hj0,hj1⟩)
    exact endpoint_implements p c hp0 hp1 hsum hf
  | cons a rest ih =>
    by_cases ha : Roundable p a
    · rw [scanRound, dif_pos ha]
      have hplus := shift_box p hp0 hp1 a.1 a.2 ha.1 (upStep p a)
        (by have := upStep_pos ha; linarith [hp0 a.1]) (min_le_left _ _)
        (by have := upStep_pos ha; linarith [hp1 a.2]) (min_le_right _ _)
      have hminus := shift_box p hp0 hp1 a.1 a.2 ha.1 (-downStep p a)
        (by have := min_le_left (p a.1) (1-p a.2); change -p a.1 ≤ -min (p a.1) (1-p a.2); linarith)
        (by have := downStep_pos ha; linarith [hp1 a.1])
        (by have := min_le_right (p a.1) (1-p a.2); change p a.2-1 ≤ -min (p a.1) (1-p a.2); linarith)
        (by have := downStep_pos ha; linarith [hp0 a.2])
      have hdrop := fractional_card_drop p a.1 a.2 ha.1 ha.2.1 ha.2.2
      apply mixture_implements p c a ha
      · exact hnext _ c hplus.1 hplus.2 (by rw [sum_shift]; exact hsum)
          (by simpa only [upStep] using (show (fractional (shift p a.1 a.2 (min (1-p a.1) (p a.2)))).card ≤ d by omega))
      · exact hnext _ c hminus.1 hminus.2 (by rw [sum_shift]; exact hsum)
          (by simpa only [downStep] using (show (fractional (shift p a.1 a.2 (-min (p a.1) (1-p a.2)))).card ≤ d by omega))
    · rw [scanRound, dif_neg ha]
      apply ih
      intro b hb
      exact (List.mem_cons.mp (hcover b hb)).resolve_left (fun he => ha (he ▸ hb))

theorem roundingLottery_implements (d : ℕ) (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hsum : ∑ i, p i = c) (hfrac : (fractional p).card ≤ d) :
    Implements p c (roundingLottery d p) := by
  induction d generalizing p c with
  | zero =>
    apply endpoint_implements p c hp0 hp1 hsum
    exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hfrac)
  | succ d ih =>
    exact scanRound_implements d _ (fun q c hq0 hq1 hqsum hqfrac =>
      ih q c hq0 hq1 hqsum hqfrac) _ p c hp0 hp1 hsum hfrac
      (fun a _ => Finset.mem_toList.mpr (Finset.mem_univ a))

theorem measurableLottery_implements (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = c) :
    Implements p c (measurableLottery p) :=
  roundingLottery_implements _ p c hp0 hp1 hsum (Finset.card_le_univ _)

end FCAppendix.ExactCapacity

namespace FCAppendix.FiniteLaw
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {Ω X : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace X]

def probabilityMeasure (μ : FiniteLaw Ω) : Measure Ω :=
  ∑ ω, ENNReal.ofReal (μ.mass ω) • Measure.dirac ω

instance probabilityMeasure_isProbability (μ : FiniteLaw Ω) :
    IsProbabilityMeasure (probabilityMeasure μ) := by
  constructor
  simp only [probabilityMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => μ.nonneg ω), μ.total]
  exact ENNReal.ofReal_one

lemma probabilityMeasure_singleton (μ : FiniteLaw Ω) (ω : Ω) :
    probabilityMeasure μ {ω} = ENNReal.ofReal (μ.mass ω) := by
  classical
  simp [probabilityMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Pi.single_apply, eq_comm]

def probabilityKernel (μ : X → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) : Kernel X Ω where
  toFun x := probabilityMeasure (μ x)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun E _hE => ?_
    simp only [probabilityMeasure, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun ω _ => (hμ ω).ennreal_ofReal.mul_const _)

instance probabilityKernel_isMarkov (μ : X → FiniteLaw Ω)
    (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) :
    IsMarkovKernel (probabilityKernel μ hμ) where
  isProbabilityMeasure x := probabilityMeasure_isProbability (μ x)

omit [MeasurableSingletonClass Ω] in

theorem exists_measurable_sampler [Nonempty Ω] [StandardBorelSpace Ω]
    (μ : X → FiniteLaw Ω) (hμ : ∀ ω, Measurable (fun x => (μ x).mass ω)) :
    ∃ f : X → unitInterval → Ω, Measurable (Function.uncurry f) ∧
      ∀ x, volume.map (f x) = probabilityMeasure (μ x) :=
  (probabilityKernel μ hμ).exists_measurable_map_eq_unitInterval

end FCAppendix.FiniteLaw

namespace FCAppendix.FiniteLaw
open scoped BigOperators
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

def finiteMix (weights : FiniteLaw Ω) (laws : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  mass ξ := weights.expect (fun ω => (laws ω).mass ξ)
  nonneg ξ := weights.expect_nonneg (fun ω => (laws ω).nonneg ξ)
  total := by
    simp only [expect]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (laws _).total, mul_one]
    exact weights.total

lemma expect_finiteMix (weights : FiniteLaw Ω) (laws : Ω → FiniteLaw Ξ) (f : Ξ → ℝ) :
    (finiteMix weights laws).expect f = weights.expect (fun ω => (laws ω).expect f) := by
  change (∑ ξ, (∑ ω, weights.mass ω * (laws ω).mass ξ) * f ξ) =
    ∑ ω, weights.mass ω * (∑ ξ, (laws ω).mass ξ * f ξ)
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end FCAppendix.FiniteLaw

namespace FCAppendix.ExactCapacity
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def symmetricLottery (p : ι → ℝ) : FiniteLaw (Finset ι) :=
  FiniteLaw.finiteMix (FiniteLaw.uniform (Equiv.Perm ι))
    (fun e => (measurableLottery (p ∘ e)).map (fun S => S.map e.toEmbedding))

lemma expect_symmetricLottery (p : ι → ℝ) (f : Finset ι → ℝ) :
    (symmetricLottery p).expect f =
      (FiniteLaw.uniform (Equiv.Perm ι)).expect (fun e =>
        (measurableLottery (p ∘ e)).expect (fun S => f (S.map e.toEmbedding))) := by
  rw [symmetricLottery, FiniteLaw.expect_finiteMix]
  simp only [FiniteLaw.expect_map]

theorem measurable_symmetricLottery_mass (S : Finset ι) :
    Measurable (fun p : ι → ℝ => (symmetricLottery p).mass S) := by
  simp only [symmetricLottery, FiniteLaw.finiteMix, FiniteLaw.expect, FiniteLaw.map]
  apply Finset.measurable_sum
  intro e _
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro T _
  by_cases hT : T.map e.toEmbedding = S
  · simp only [hT, ite_true]
    exact (measurable_measurableLottery_mass T).comp
      (by apply measurable_pi_lambda; intro i; exact measurable_pi_apply (e i))
  · simp only [hT, ite_false]
    exact measurable_const

theorem symmetricLottery_equivariant (p : ι → ℝ) (r : Equiv.Perm ι) :
    symmetricLottery (p ∘ r.symm) = (symmetricLottery p).map (fun S => S.map r.toEmbedding) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [expect_symmetricLottery, FiniteLaw.expect_map, expect_symmetricLottery]
  let g : Equiv.Perm ι → ℝ := fun e =>
    (measurableLottery ((p ∘ r.symm) ∘ e)).expect (fun S => f (S.map e.toEmbedding))
  have h := FiniteLaw.uniform_expect_equiv (Equiv.mulLeft r) g
  apply h.symm.trans
  apply (FiniteLaw.uniform (Equiv.Perm ι)).expect_congr
  intro e
  have hp : (p ∘ r.symm) ∘ (r*e) = p ∘ e := by
    funext i
    simp
  change (measurableLottery ((p ∘ r.symm) ∘ (r*e))).expect _ = _
  rw [hp]
  apply FiniteLaw.expect_congr
  intro S
  congr 1
  ext i
  simp only [Finset.mem_map_equiv]
  have hs : (r*e).symm i = e.symm (r.symm i) := by
    apply (r*e).injective
    simp
  change (r*e).symm i ∈ S ↔ e.symm (r.symm i) ∈ S
  rw [hs]

theorem symmetricLottery_implements (p : ι → ℝ) (c : ℕ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hsum : ∑ i, p i = c) :
    Implements p c (symmetricLottery p) := by
  have himpl (e : Equiv.Perm ι) : Implements (p ∘ e) c (measurableLottery (p ∘ e)) :=
    measurableLottery_implements _ c (fun i => hp0 (e i)) (fun i => hp1 (e i))
      (by exact (Equiv.sum_comp e p).trans hsum)
  constructor
  · intro S hS
    by_contra hc
    apply hS
    simp only [symmetricLottery, FiniteLaw.finiteMix, FiniteLaw.expect, FiniteLaw.map]
    apply Finset.sum_eq_zero
    intro e _
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro T _
    split_ifs with he
    · apply by_contra
      intro hm
      exact hc (by rw [← he, Finset.card_map]; exact (himpl e).1 T hm)
    · rfl
  · intro i
    rw [FiniteLaw.prob_eq_expect, expect_symmetricLottery]
    have he : ∀ e : Equiv.Perm ι,
        (measurableLottery (p ∘ e)).expect
          (fun S => if i ∈ S.map e.toEmbedding then (1 : ℝ) else 0) = p i := by
      intro e
      simp only [Finset.mem_map_equiv]
      rw [← FiniteLaw.prob_eq_expect, (himpl e).2]
      simp
    simp_rw [he]
    exact FiniteLaw.expect_const _ _

theorem exists_symmetricLottery_sampler
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    [StandardBorelSpace (Finset ι)] :
    ∃ f : (ι → ℝ) → unitInterval → Finset ι,
      Measurable (Function.uncurry f) ∧
      ∀ p, volume.map (f p) = FiniteLaw.probabilityMeasure (symmetricLottery p) :=
  FiniteLaw.exists_measurable_sampler symmetricLottery measurable_symmetricLottery_mass

end FCAppendix.ExactCapacity
