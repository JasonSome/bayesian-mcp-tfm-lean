import FCAppendix.Proposer.MeasurableLotteryPolicy
import FCAppendix.Affine.Hybrid.SupportSampler

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mixedReciprocalSum (I : Finset ι) (b : ι → ℝ) : ℝ :=
  ∑ i ∈ I, 1 / b i

def realizedResidual (c : ℕ) (fixed : Finset ι) : ℕ := c - fixed.card

def realizedMixedMultiplier (xi : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) : ℝ :=
  ((I.card : ℝ) - xi * realizedResidual c fixed) / mixedReciprocalSum I b

def realizedMixedMarginal (xi : ℝ) (c : ℕ) (fixed I : Finset ι)
    (b : ι → ℝ) (i : ι) : ℝ :=
  (1 - realizedMixedMultiplier xi c fixed I b / b i) / xi

def typicalMarginal (xi : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) (i : ι) : ℝ :=
  if i ∈ fixed then 1 else if i ∈ I then realizedMixedMarginal xi c fixed I b i else 0

def typicalLottery (xi : ℝ) (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) :
    FiniteLaw (Finset ι) := ExactCapacity.symmetricLottery (typicalMarginal xi c fixed I b)

omit [Fintype ι] [DecidableEq ι] in
theorem mixedReciprocalSum_pos (I : Finset ι) (b : ι → ℝ)
    (hI : I.Nonempty) (hb : ∀ i ∈ I, 0 < b i) :
    0 < mixedReciprocalSum I b :=
  Finset.sum_pos (fun i hi => one_div_pos.mpr (hb i hi)) hI

omit [Fintype ι] [DecidableEq ι] in
theorem realizedMixedMarginal_sum {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (hW : 0 < mixedReciprocalSum I b) :
    (∑ i ∈ I, realizedMixedMarginal xi c fixed I b i) = realizedResidual c fixed := by
  have hdiv : (∑ i ∈ I, realizedMixedMultiplier xi c fixed I b / b i) =
      realizedMixedMultiplier xi c fixed I b * mixedReciprocalSum I b := by
    simp only [mixedReciprocalSum, div_eq_mul_inv, one_mul, Finset.mul_sum]
  unfold realizedMixedMarginal
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hdiv]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  unfold realizedMixedMultiplier
  field_simp [ne_of_gt hxi, ne_of_gt hW]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem realizedMixedMarginal_bounds {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ) (i : ι) (hbi : 0 < b i)
    (hlo : (1 - xi) * b i ≤ realizedMixedMultiplier xi c fixed I b)
    (hhi : realizedMixedMultiplier xi c fixed I b ≤ b i) :
    0 ≤ realizedMixedMarginal xi c fixed I b i ∧
      realizedMixedMarginal xi c fixed I b i ≤ 1 := by
  have hl : 1 - xi ≤ realizedMixedMultiplier xi c fixed I b / b i :=
    (le_div_iff₀ hbi).mpr hlo
  have hu : realizedMixedMultiplier xi c fixed I b / b i ≤ 1 :=
    (div_le_one hbi).mpr hhi
  constructor
  · exact div_nonneg (sub_nonneg.mpr hu) hxi.le
  · apply (div_le_one hxi).mpr
    linarith

omit [Fintype ι] in
theorem realizedResidual_private_owners (c : ℕ) (privateSet owners : Finset ι)
    (hdis : Disjoint privateSet owners) :
    realizedResidual c (privateSet ∪ owners) = c - privateSet.card - owners.card := by
  rw [realizedResidual, Finset.card_union_of_disjoint hdis]
  omega

theorem typicalMarginal_sum {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (hdis : Disjoint fixed I) (hfixed : fixed.card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) :
    (∑ i, typicalMarginal xi c fixed I b i) = c := by
  have hp (i : ι) : typicalMarginal xi c fixed I b i =
      (if i ∈ fixed then (1 : ℝ) else 0) +
        (if i ∈ I then realizedMixedMarginal xi c fixed I b i else 0) := by
    by_cases hf : i ∈ fixed
    · have hi : i ∉ I := fun hi => (Finset.disjoint_left.mp hdis) hf hi
      simp [typicalMarginal, hf, hi]
    · simp [typicalMarginal, hf]
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [realizedMixedMarginal_sum hxi c fixed I b hW]
  have hn : fixed.card + realizedResidual c fixed = c := by
    unfold realizedResidual
    omega
  exact_mod_cast hn

theorem typicalLottery_implements {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (hdis : Disjoint fixed I) (hfixed : fixed.card ≤ c)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ i ∈ I, (1 - xi) * b i ≤ realizedMixedMultiplier xi c fixed I b)
    (hhi : ∀ i ∈ I, realizedMixedMultiplier xi c fixed I b ≤ b i) :
    ExactCapacity.Implements (typicalMarginal xi c fixed I b) c
      (typicalLottery xi c fixed I b) := by
  apply ExactCapacity.symmetricLottery_implements
  · intro i
    unfold typicalMarginal
    split_ifs with hf hi
    · norm_num
    · exact (realizedMixedMarginal_bounds hxi c fixed I b i (hb i hi) (hlo i hi) (hhi i hi)).1
    · norm_num
  · intro i
    unfold typicalMarginal
    split_ifs with hf hi
    · norm_num
    · exact (realizedMixedMarginal_bounds hxi c fixed I b i (hb i hi) (hlo i hi) (hhi i hi)).2
    · norm_num
  · exact typicalMarginal_sum hxi c fixed I b hdis hfixed hW

theorem typicalLottery_support_subset {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (hdis : Disjoint fixed I) (hfixed : fixed.card ≤ c)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ i ∈ I, (1 - xi) * b i ≤ realizedMixedMultiplier xi c fixed I b)
    (hhi : ∀ i ∈ I, realizedMixedMultiplier xi c fixed I b ≤ b i)
    (S : Finset ι) (hS : (typicalLottery xi c fixed I b).mass S ≠ 0) :
    S ⊆ fixed ∪ I := by
  have himpl := typicalLottery_implements hxi c fixed I b hdis hfixed hW hb hlo hhi
  intro i hi
  by_contra hnot
  have hf : i ∉ fixed := fun hf => hnot (Finset.mem_union.mpr (Or.inl hf))
  have hI : i ∉ I := fun hI => hnot (Finset.mem_union.mpr (Or.inr hI))
  have hpos := FiniteLaw.marginal_pos_of_support_mem _ S hS i hi
  rw [himpl.2 i] at hpos
  have hh : (0 : ℝ) < 0 := by
    simpa only [typicalMarginal, if_neg hf, if_neg hI] using hpos
  exact (lt_irrefl 0) hh

theorem prob_pos_of_support_event {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (E : Ω → Prop) (x : Ω) (hm : μ.mass x ≠ 0) (hx : E x) :
    0 < μ.prob E := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  have hp : 0 < μ.mass x := lt_of_le_of_ne (μ.nonneg x) hm.symm
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun y => μ.mass y * (if E y then (1 : ℝ) else 0))
    (fun y _ => mul_nonneg (μ.nonneg y) (by split_ifs <;> norm_num))
    (Finset.mem_univ x)
  rw [if_pos hx, mul_one] at hh
  exact hp.trans_le hh

theorem typicalLottery_support_contains_fixed {xi : ℝ} (hxi : 0 < xi)
    (c : ℕ) (fixed I : Finset ι) (b : ι → ℝ)
    (hdis : Disjoint fixed I) (hfixed : fixed.card ≤ c)
    (hW : 0 < mixedReciprocalSum I b)
    (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ i ∈ I, (1 - xi) * b i ≤ realizedMixedMultiplier xi c fixed I b)
    (hhi : ∀ i ∈ I, realizedMixedMultiplier xi c fixed I b ≤ b i)
    (S : Finset ι) (hS : (typicalLottery xi c fixed I b).mass S ≠ 0) :
    fixed ⊆ S := by
  have himpl := typicalLottery_implements hxi c fixed I b hdis hfixed hW hb hlo hhi
  intro i hi
  by_contra hn
  have hpos := prob_pos_of_support_event (typicalLottery xi c fixed I b)
    (fun S => i ∉ S) S hS hn
  rw [FiniteLaw.prob_compl, himpl.2 i] at hpos
  have hh : (0 : ℝ) < 0 := by
    simpa only [typicalMarginal, if_pos hi, sub_self] using hpos
  exact (lt_irrefl 0) hh

theorem measurable_typicalLottery_mass (xi : ℝ) (c : ℕ) (fixed I : Finset ι)
    (S : Finset ι) :
    Measurable (fun b : ι → ℝ => (typicalLottery xi c fixed I b).mass S) := by
  apply (ExactCapacity.measurable_symmetricLottery_mass S).comp
  apply measurable_pi_lambda
  intro i
  unfold typicalMarginal
  split_ifs with hf hi
  · exact measurable_const
  · unfold realizedMixedMarginal realizedMixedMultiplier mixedReciprocalSum
    fun_prop
  · exact measurable_const

theorem exists_typicalLottery_sampler (xi : ℝ) (c : ℕ) (fixed I : Finset ι) :
    ∃ f : (ι → ℝ) → unitInterval → Finset ι,
      Measurable (Function.uncurry f) ∧
      (∀ b z, 0 < (typicalLottery xi c fixed I b).mass (f b z)) ∧
      ∀ b, volume.map (f b) = FiniteLaw.probabilityMeasure (typicalLottery xi c fixed I b) :=
  Hybrid.exists_support_sampler (fun b => typicalLottery xi c fixed I b)
    (measurable_typicalLottery_mass xi c fixed I)

end FCAppendix.Affine.Tail04
