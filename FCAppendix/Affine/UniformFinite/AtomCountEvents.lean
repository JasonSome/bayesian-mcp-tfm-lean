import FCAppendix.Affine.UniformFinite.AtomEventRates
import FCAppendix.Game.CommonListSeeds
import FCAppendix.Proposer.LotterySupport

noncomputable section

namespace FCAppendix.Affine.UniformFinite.AtomEvents

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

variable {X : Type*} [MeasurableSpace X]

lemma measurableSet_count_upper (N K : ℕ) (B : Set X) (hB : MeasurableSet B) :
    MeasurableSet {ω : Fin N→ X | K≤ PiBinomial.count B Finset.univ ω} :=
  measurableSet_le measurable_const (PiBinomial.measurable_count B hB Finset.univ)

theorem actual_count_upper_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (B : Set X) (hB : MeasurableSet B) (N K : ℕ) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {ω | K≤ PiBinomial.count B Finset.univ ω} =
      (IndependentCounts.binomial N (μ.real B) (measureReal_nonneg)
        (measureReal_le_one)).prob (fun r => K≤ r.val) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let C : (Fin N→ X)→ℕ := PiBinomial.count B Finset.univ
  have hC : Measurable C := PiBinomial.measurable_count B hB Finset.univ
  have hfiber (r : Fin (N+1)) : MeasurableSet {ω : Fin N→ X | C ω=r.val} :=
    measurableSet_eq_fun hC measurable_const
  have hfi (r : Fin (N+1)) :
      Integrable (fun ω : Fin N→ X => if C ω=r.val then (1:ℝ) else 0) ν := by
    convert!
      (integrable_const (1:ℝ) : Integrable (fun _ : Fin N→ X => (1:ℝ)) ν).indicator (hfiber r)
      using 1
    funext ω
    simp only [Set.indicator_apply, mem_setOf_eq]
  have hpoint (ω : Fin N→ X) :
      (if K≤ C ω then (1:ℝ) else 0) =
      ∑r : Fin (N+1), (if C ω=r.val then (1:ℝ) else 0)*(if K≤ r.val then 1 else 0) := by
    have hcount : C ω≤ N := by
      simpa only [Finset.card_univ,Fintype.card_fin,C] using
        PiBinomial.count_le B (Finset.univ : Finset (Fin N)) ω
    let k : Fin (N+1) := ⟨C ω,by omega⟩
    symm
    rw [Finset.sum_eq_single k]
    · simp [k]
    · intro r _ hr
      have hneq : C ω≠r.val := by
        intro he
        apply hr
        apply Fin.ext
        exact he.symm
      simp only [if_neg hneq,zero_mul]
    · simp
  have htail := integral_indicator_one (μ:=ν) (measurableSet_count_upper N K B hB)
  have htail' : (∫ω : Fin N→ X,if K≤ C ω then (1:ℝ) else 0 ∂ν)=
      ν.real {ω | K≤ C ω} := by
    simpa only [Set.indicator,mem_setOf_eq,Pi.one_apply,C] using htail
  rw [← htail']
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun r _ =>
    (hfi r).mul_const (if K≤ r.val then (1:ℝ) else 0))]
  rw [FiniteLaw.prob_eq_expect]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_mul_const,PiBinomial.binomial_mass]
  have hmass := PiBinomial.measureReal_count_eq μ B hB
    (Finset.univ : Finset (Fin N)) r.val
  have hf := integral_indicator_one (μ:=ν) (hfiber r)
  have hf' : (∫ω : Fin N→ X,if C ω=r.val then (1:ℝ) else 0 ∂ν) =
      PiBinomial.pmf N (μ.real B) r.val := by
    calc
      _ = ν.real {ω | C ω=r.val} := by
        simpa only [Set.indicator,mem_setOf_eq,Pi.one_apply] using hf
      _ = _ := by simpa only [ν,C,Finset.card_univ,Fintype.card_fin] using hmass
  rw [hf']

theorem deleted_cluster_count_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (N K : ℕ) (i : Fin (N+1)) :
    (Measure.pi (fun _ : Fin (N+1) => μ)).real
      {ω | ω i∈A ∧ K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))} =
      μ.real A * (IndependentCounts.binomial N (μ.real B)
        (measureReal_nonneg) (measureReal_le_one)).prob (fun r => K≤ r.val) := by
  let E : Set (Fin N→ X) := {ω | K≤ PiBinomial.count B Finset.univ ω}
  have hE : MeasurableSet E := measurableSet_count_upper N K B hB
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i
  have he := congrArg (fun ν : Measure (X×(Fin N→ X)) => ν (A×ˢE)) hp.map_eq
  rw [Measure.map_apply hp.measurable (hA.prod hE),Measure.prod_prod] at he
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_mul] at hr
  change (Measure.pi (fun _ : Fin (N+1) => μ)).real
      {ω | ω i∈A ∧ K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))} =
    μ.real A * (Measure.pi (fun _ : Fin N => μ)).real E at hr
  rw [show (Measure.pi (fun _ : Fin N => μ)).real E = _ from
    actual_count_upper_probability μ B hB N K] at hr
  exact hr

theorem harmful_deleted_count_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (N K : ℕ) :
    (Measure.pi (fun _ : Fin (N+1) => μ)).real
      {ω | ∃i : Fin (N+1),ω i∈A ∧
        K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))} ≤
      ((N+1:ℕ):ℝ)*μ.real A *
        (IndependentCounts.binomial N (μ.real B) (measureReal_nonneg)
          (measureReal_le_one)).prob (fun r => K≤ r.val) := by
  classical
  have hu := measureReal_iUnion_fintype_le
    (μ:=Measure.pi (fun _ : Fin (N+1) => μ))
    (fun i : Fin (N+1) => {ω | ω i∈A ∧
      K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))})
  have heq : {ω : Fin (N+1)→ X | ∃i : Fin (N+1),ω i∈A ∧
      K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))} =
    ⋃i : Fin (N+1),{ω | ω i∈A ∧
      K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))} := by
    ext ω
    simp
  rw [heq]
  apply hu.trans
  simp_rw [deleted_cluster_count_probability μ A B hA hB N K]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

theorem physical_harmful_event_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (N K : ℕ) (D : Set (Fin (N+1)→ X))
    (hsub : D⊆{ω | ∃i : Fin (N+1),ω i∈A ∧
      K≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j))}) :
    (Measure.pi (fun _ : Fin (N+1) => μ)).real D ≤
      ((N+1:ℕ):ℝ)*μ.real A *
        (IndependentCounts.binomial N (μ.real B) (measureReal_nonneg)
          (measureReal_le_one)).prob (fun r => K≤ r.val) :=
  (measureReal_mono hsub).trans (harmful_deleted_count_probability μ A B hA hB N K)

end FCAppendix.Affine.UniformFinite.AtomEvents
