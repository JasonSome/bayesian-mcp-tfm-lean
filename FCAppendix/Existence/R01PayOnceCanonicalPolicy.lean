import FCAppendix.Existence.R01PayOnceKernel
import FCAppendix.Proposer.MeasurableLotteryPolicy

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set MeasureTheory ProbabilityTheory Game
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSupport (b : ι → ℝ) : Finset ι := Finset.univ.filter (fun i => 0 < b i)

omit [DecidableEq ι] in
theorem mem_positiveSupport (b : ι → ℝ) (i : ι) : i ∈ positiveSupport b ↔ 0 < b i := by
  simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and]

def positiveStratum (S : Finset ι) : Set (ι → ℝ) := {b | ∀ i : S, 0 < b i.1}

omit [DecidableEq ι] in
theorem isOpen_positiveStratum (S : Finset ι) : IsOpen (positiveStratum S) := by
  have he : positiveStratum S = ⋂ i : S, {b : ι → ℝ | 0 < b i.1} := by
    ext b
    simp only [positiveStratum,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite (fun i : S => isOpen_lt (continuous_const (y := (0:ℝ)))
    (continuous_apply i.1 : Continuous (fun b : ι → ℝ => b i.1)))

def stratumKernel (n c : ℕ) (S : Finset ι) : (ι → ℝ) → ι → ℝ :=
  (positiveStratum S).piecewise (onSupport n c S) (fun _ _ => 0)

theorem measurable_stratumKernel (n c : ℕ) (hn : 2 ≤ n) (S : Finset ι) :
    Measurable (stratumKernel n c S) := by
  apply ContinuousOn.measurable_piecewise _ continuousOn_const
    (isOpen_positiveStratum S).measurableSet
  intro b hb
  exact (continuousAt_onSupport n c hn S b (fun i hi => hb ⟨i,hi⟩)).continuousWithinAt

theorem measurable_positiveSupport : Measurable (positiveSupport (ι := ι)) := by
  apply measurable_to_countable'
  intro S
  have he : positiveSupport ⁻¹' {S} =
      ⋂ i : ι, {b : ι → ℝ | (i ∈ S ↔ 0 < b i)} := by
    ext b
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_setOf_eq]
    exact ⟨fun h i => h ▸ mem_positiveSupport b i,
      fun h => Finset.ext (fun i => (mem_positiveSupport b i).trans (h i).symm)⟩
  rw [he]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ S
  · simpa only [hi,true_iff] using measurableSet_lt measurable_const (measurable_pi_apply i)
  · simpa only [hi,false_iff,not_lt] using measurableSet_le (measurable_pi_apply i) measurable_const

def positiveMarginal (n c : ℕ) (b : ι → ℝ) : ι → ℝ :=
  onSupport n c (positiveSupport b) b

theorem measurable_positiveMarginal (n c : ℕ) (hn : 2 ≤ n) :
    Measurable (positiveMarginal (ι := ι) n c) := by
  have he : positiveMarginal (ι := ι) n c =
      fun b => ∑ S : Finset ι, if positiveSupport b=S then stratumKernel n c S b else 0 := by
    funext b i
    simp only [Finset.sum_apply,ite_apply,Pi.zero_apply]
    rw [Finset.sum_eq_single (positiveSupport b)]
    · have hpos : b ∈ positiveStratum (positiveSupport b) :=
        fun j => (mem_positiveSupport b j.1).mp j.2
      simp [positiveMarginal,stratumKernel,Set.piecewise,hpos]
    · intro S _ hS
      simp only [if_neg (Ne.symm hS)]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rw [he]
  apply Finset.measurable_sum
  intro S _
  exact Measurable.ite (measurableSet_eq_fun measurable_positiveSupport measurable_const)
    (measurable_stratumKernel n c hn S) measurable_const

theorem positiveMarginal_spec (n c : ℕ) (hn : 2 ≤ n) (b : ι → ℝ) :
    (∀ i, 0 ≤ positiveMarginal n c b i) ∧
    (∀ i, positiveMarginal n c b i ≤ 1) ∧
    (∑ i, positiveMarginal n c b i = (min c (positiveSupport b).card : ℕ)) :=
  onSupport_spec n c hn _ b (fun i hi => (mem_positiveSupport b i).mp hi)

def listBids {m : ℕ} (L : LocalList m) : Fin m → ℝ := fun i => (L i).getD 0

theorem measurable_listBids {m : ℕ} : Measurable (listBids (m := m)) := by
  apply measurable_pi_lambda
  intro i
  have hread : Measurable (fun x : Option ℝ => x.getD 0) := by
    intro E hE
    change MeasurableSet ((fun b : ℝ => b) ⁻¹' E)
    exact hE
  exact hread.comp (measurable_pi_apply i)

def listMarginal {m : ℕ} (n c : ℕ) (L : LocalList m) : Fin m → ℝ :=
  positiveMarginal n c (listBids L)

theorem measurable_listMarginal (m n c : ℕ) (hn : 2 ≤ n) :
    Measurable (listMarginal (m := m) n c) :=
  (measurable_positiveMarginal n c hn).comp measurable_listBids

theorem exists_payOnce_localPolicy (m n c : ℕ) (hn : 2 ≤ n) :
    ∃ (policy : LocalPolicy m c unitInterval)
      (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)),
      ∀ L, FiniteLaw.ofMeasure volume (fun s => (policy L s).val)
        (hpolicy.comp (measurable_const.prodMk measurable_id)) =
        ExactCapacity.symmetricLottery (listMarginal n c L) := by
  apply exists_measurable_localPolicy_finiteLaw (listMarginal n c)
    (measurable_listMarginal m n c hn) (fun L => min c (positiveSupport (listBids L)).card)
    (fun _ => min_le_left _ _)
  · intro L i
    exact (positiveMarginal_spec n c hn (listBids L)).1 i
  · intro L i
    exact (positiveMarginal_spec n c hn (listBids L)).2.1 i
  · intro L
    exact (positiveMarginal_spec n c hn (listBids L)).2.2
  · intro L i hi
    apply onSupport_outside
    rw [mem_positiveSupport]
    simp only [listBids,hi,Option.getD_none,lt_self_iff_false,not_false_eq_true]

end FCAppendix.Existence.PayOnceBounded
