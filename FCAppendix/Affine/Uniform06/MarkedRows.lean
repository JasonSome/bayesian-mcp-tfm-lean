import FCAppendix.Affine.Uniform06.MixedLaw
import FCAppendix.Probability.TiltedProduct

set_option autoImplicit false
noncomputable section

namespace FCAppendix.Affine.Uniform06.MarkedRows

open MeasureTheory ProbabilityTheory Set
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.ExponentialTilt

abbrev Pair := MixedLaw.Pair

def sumX {N : ℕ} (row : Fin N → Pair) : ℝ := ∑ j, (row j).1
def sumY {N : ℕ} (row : Fin N → Pair) : ℝ := ∑ j, (row j).2
def deficit {N : ℕ} (c : ℝ) (row : Fin N → Pair) : ℝ := c-sumX row

def append {r N : ℕ} (fixed : Fin r → Pair) (row : Fin N → Pair) :
    Fin (r+N) → Pair := Fin.append fixed row

theorem sumX_append {r N : ℕ} (fixed : Fin r → Pair) (row : Fin N → Pair) :
    sumX (append fixed row) = sumX fixed+sumX row := by
  unfold sumX append
  rw [Fin.sum_univ_add]
  simp

theorem sumY_append {r N : ℕ} (fixed : Fin r → Pair) (row : Fin N → Pair) :
    sumY (append fixed row) = sumY fixed+sumY row := by
  unfold sumY append
  rw [Fin.sum_univ_add]
  simp

theorem measurable_append {r N : ℕ} (fixed : Fin r → Pair) :
    Measurable (append (N := N) fixed) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [append]
  · intro k
    simpa [append] using measurable_pi_apply k

def fixedPrefixLaw {r N : ℕ} (μ : Measure Pair) (fixed : Fin r → Pair) :
    Measure (Fin (r+N) → Pair) :=
  (Measure.pi (fun _ : Fin N => μ)).map (append fixed)

instance fixedPrefixLaw_probability {r N : ℕ} (μ : Measure Pair)
    [IsProbabilityMeasure μ] (fixed : Fin r → Pair) :
    IsProbabilityMeasure (fixedPrefixLaw (N := N) μ fixed) :=
  Measure.isProbabilityMeasure_map (measurable_append fixed).aemeasurable

theorem marked_cell_event {r N : ℕ} (fixed : Fin r → Pair)
    (c a h y : ℝ) :
    {row : Fin N → Pair |
      deficit c (append fixed row) ∈ Icc a (a+h) ∧ sumY (append fixed row)=y} =
    {row : Fin N → Pair |
      deficit c row ∈ Icc (a+sumX fixed) (a+sumX fixed+h) ∧
        sumY row=y-sumY fixed} := by
  ext row
  simp only [mem_setOf_eq, mem_Icc, deficit, sumX_append, sumY_append]
  constructor <;> rintro ⟨⟨h₁,h₂⟩,h₃⟩ <;>
    refine ⟨⟨by linarith, by linarith⟩, by linarith⟩

theorem marked_cell_probability {r N : ℕ} (μ : Measure Pair)
    (fixed : Fin r → Pair) (c a h y : ℝ) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {row | deficit c (append fixed row) ∈ Icc a (a+h) ∧
        sumY (append fixed row)=y} =
    (Measure.pi (fun _ : Fin N => μ)).real
      {row | deficit c row ∈ Icc (a+sumX fixed) (a+sumX fixed+h) ∧
        sumY row=y-sumY fixed} := by
  rw [marked_cell_event]

def physicalLowerMarks {r : ℕ} (i : Row) (b : ℝ) (fixed : Fin r → ℝ × ℝ) :
    Fin r → Pair := fun j => (exposure (xi i) b (fixed j).2,0)

theorem physicalLowerMarks_sumY {r : ℕ} (i : Row) (b : ℝ)
    (fixed : Fin r → ℝ × ℝ) : sumY (physicalLowerMarks i b fixed) = 0 := by
  simp [sumY, physicalLowerMarks]

theorem physicalLowerMarks_sumX_bounds {r : ℕ} (i : Row) {b : ℝ}
    (hb : 0 < b) (fixed : Fin r → ℝ × ℝ) :
    sumX (physicalLowerMarks i b fixed) ∈ Icc (0:ℝ) r := by
  constructor
  · apply Finset.sum_nonneg
    intro j _
    exact exposure_nonneg (xi_pos i) hb
  · calc
      _ ≤ ∑ _j : Fin r, (1:ℝ) :=
        Finset.sum_le_sum (fun _ _ => exposure_le_one _ _ _)
      _ = _ := by simp

theorem lower_marked_cell_probability {r N : ℕ} (i : Row) {b : ℝ}
    (hb : 0 < b) (G : Measure (ℝ × ℝ))
    (fixed : Fin r → ℝ × ℝ) (c a h y : ℝ) :
    ∃ s ∈ Icc (0:ℝ) r,
      (Measure.pi (fun _ : Fin N => MixedLaw.law i (MixedLaw.physicalLowerLaw i b G))).real
        {row | deficit c (append (physicalLowerMarks i b fixed) row) ∈ Icc a (a+h) ∧
          sumY (append (physicalLowerMarks i b fixed) row)=y} =
      (Measure.pi (fun _ : Fin N => MixedLaw.law i (MixedLaw.physicalLowerLaw i b G))).real
        {row | deficit c row ∈ Icc (a+s) (a+s+h) ∧ sumY row=y} := by
  refine ⟨sumX (physicalLowerMarks i b fixed),
    physicalLowerMarks_sumX_bounds i hb fixed, ?_⟩
  rw [marked_cell_probability, physicalLowerMarks_sumY, sub_zero]

theorem identDistrib_eval {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ} (j : Fin N) :
    IdentDistrib (fun row : Fin N → Ω => row j) id
      (Measure.pi (fun _ : Fin N => μ)) μ := by
  refine ⟨(measurable_pi_apply j).aemeasurable, measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  exact (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq

theorem independent_evals {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    iIndepFun (fun (j : Fin N) (row : Fin N → Ω) => row j)
      (Measure.pi (fun _ : Fin N => μ)) := by
  exact iIndepFun_pi (fun _ : Fin N => measurable_id.aemeasurable)

theorem tilted_original_product (i : Row) {b : ℝ} (hb : 0 < b)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (u : ℝ) (N : ℕ) :
    Measure.pi (fun _ : Fin N =>
        MixedLaw.tiltedLaw i (MixedLaw.physicalLowerLaw i b G) u) =
      (Measure.pi (fun _ : Fin N =>
        MixedLaw.law i (MixedLaw.physicalLowerLaw i b G))).tilted
          (fun row => u*sumX row) := by
  letI := MixedLaw.physicalLowerLaw_probability i hb G
  exact pi_tilted_eq_tilted_iidSum
    (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) Prod.fst u N

theorem original_product_low_chernoff (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m : ℕ} (hm : 2 ≤ m) :
    (Measure.pi (fun _ : Fin (m-1) => LowChernoff.originalStatisticLaw i G)).real
      {row | (∑ j, row j) ≤ (capacity m : ℝ)} ≤
      Real.exp ((LowChernoff.thetaQ i : ℝ)*(capacity m : ℝ)-
        (m-1:ℕ)*((LowChernoff.thetaQ i : ℝ)*rho+
          LowChernoff.rankI0 i+LowChernoff.sourceGap i)) := by
  exact LowChernoff.original_iid_row_bound i G hvalue hfloor _ hm
    (fun j (row : Fin (m-1) → ℝ) => row j) (fun j => measurable_pi_apply j)
    (independent_evals _ _) (fun j => identDistrib_eval _ j)

theorem marked_product_low_chernoff (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst = LowChernoff.conditionalValueLaw i)
    (hfloor : ∀ᵐ p ∂G, LowChernoff.physicalFloor i p.1 ≤ p.2)
    {m r : ℕ} (hm : r+2 ≤ m) (fixed : Fin r → ℝ × ℝ) :
    (Measure.pi (fun _ : Fin (m-1-r) => LowChernoff.originalStatisticLaw i G)).real
      {row | (∑ j, LowChernoff.physicalStatistic i (fixed j).2)+
        (∑ j, row j) ≤ (capacity m : ℝ)} ≤
      Real.exp ((LowChernoff.thetaQ i : ℝ)*
          ((capacity m : ℝ)-∑ j, LowChernoff.physicalStatistic i (fixed j).2)-
        (m-1-r:ℕ)*((LowChernoff.thetaQ i : ℝ)*rho+
          LowChernoff.rankI0 i+LowChernoff.sourceGap i)) := by
  have he : {row : Fin (m-1-r) → ℝ |
      (∑ j, LowChernoff.physicalStatistic i (fixed j).2)+(∑ j, row j) ≤ (capacity m : ℝ)} =
      {row | (∑ j, row j) ≤ (capacity m : ℝ)-
        ∑ j, LowChernoff.physicalStatistic i (fixed j).2} := by
    ext row
    simp only [mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [he]
  exact LowChernoff.original_iid_bound i G hvalue hfloor
    (Measure.pi (fun _ : Fin (m-1-r) => LowChernoff.originalStatisticLaw i G))
    (by omega : 0 < m-1-r)
    (fun j (row : Fin (m-1-r) → ℝ) => row j) (fun j => measurable_pi_apply j)
    (independent_evals _ _) (fun j => identDistrib_eval _ j) _

end FCAppendix.Affine.Uniform06.MarkedRows
