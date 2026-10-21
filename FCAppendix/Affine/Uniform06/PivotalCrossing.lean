import FCAppendix.Affine.Uniform06.PivotalCounts
import FCAppendix.Affine.Uniform06.PureDuplicateRare
import FCAppendix.Affine.Uniform06.PureRankProbability

noncomputable section
namespace FCAppendix.Affine.Uniform06.PivotalCrossing

open MeasureTheory Set Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

omit [MeasurableSpace Ω] in
theorem count_delete_split (E : Set Ω) (ω : Fin (N+1) → Ω) (i : Fin (N+1)) :
    PiBinomial.count E Finset.univ ω=
      (if ω i ∈ E then 1 else 0)+
        PiBinomial.count E Finset.univ (fun j => ω (i.succAbove j)) := by
  classical
  rw [PiBinomial.count_eq_sum,PiBinomial.count_eq_sum,Fin.sum_univ_succAbove _ i]

theorem deleted_rectangle_probability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (D : Set (Fin N → Ω)) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (i : Fin (N+1)) :
    (Measure.pi fun _ : Fin (N+1) => μ).real
      {ω | ω i ∈ C ∧ (fun j => ω (i.succAbove j)) ∈ D}=
        μ.real C*(Measure.pi fun _ : Fin N => μ).real D := by
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i
  have hh := congrArg (fun ν : Measure (Ω × (Fin N → Ω)) => ν (C ×ˢ D)) hp.map_eq
  rw [Measure.map_apply hp.measurable (hC.prod hD),Measure.prod_prod] at hh
  have hr := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_mul] at hr
  exact hr

theorem any_coordinate_probability_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (N : ℕ) :
    (Measure.pi fun _ : Fin N => μ).real {ω | ∃ j, ω j ∈ C} ≤ (N:ℝ)*μ.real C := by
  have he : {ω : Fin N → Ω | ∃ j, ω j ∈ C}=⋃ j : Fin N, {ω | ω j ∈ C} := by
    ext ω
    simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  have hp (j : Fin N) : (Measure.pi fun _ : Fin N => μ).real {ω | ω j ∈ C}=μ.real C := by
    have hm := measurePreserving_eval (fun _ : Fin N => μ) j
    have hh := congrArg (fun ν : Measure Ω => ν C) hm.map_eq
    rw [Measure.map_apply hm.measurable hC] at hh
    exact congrArg ENNReal.toReal hh
  simp only [hp,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact le_rfl

def boundarySet (E B : Set Ω) (r c : ℕ) : Set (Fin N → Ω) :=
  {ω | PiBinomial.count E Finset.univ ω=r ∧ c ≤ PiBinomial.count B Finset.univ ω}

theorem measurableSet_boundarySet (E B : Set Ω) (hE : MeasurableSet E)
    (hB : MeasurableSet B) (r c : ℕ) :
    MeasurableSet (boundarySet (N := N) E B r c) :=
  ((PiBinomial.measurable_count E hE Finset.univ) (measurableSet_singleton r)).inter
    ((PiBinomial.measurable_count B hB Finset.univ) measurableSet_Ici)

theorem count_crossing_lower
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Elo Ehi C B : Set Ω)
    (hlo : MeasurableSet Elo) (_hhi : MeasurableSet Ehi)
    (hC : MeasurableSet C) (hB : MeasurableSet B)
    (hmono : Elo ⊆ Ehi) (hCsub : C ⊆ Ehi) (hCE : Disjoint C Elo)
    (c : ℕ) (hc : 0 < c) :
    ((N:ℝ)+1)*μ.real C*
      ((Measure.pi fun _ : Fin N => μ).real (boundarySet Elo B (c-1) c)-
        (N:ℝ)*μ.real C) ≤
      (Measure.pi fun _ : Fin (N+1) => μ).real
        {ω | PiBinomial.count Elo Finset.univ ω< c ∧
          c ≤ PiBinomial.count Ehi Finset.univ ω ∧
          c ≤ PiBinomial.count B Finset.univ ω} := by
  classical
  let P := Measure.pi fun _ : Fin N => μ
  let P' := Measure.pi fun _ : Fin (N+1) => μ
  let Bad : Set (Fin N → Ω) := {ω | ∃ j, ω j ∈ C}
  let D : Set (Fin N → Ω) := boundarySet Elo B (c-1) c \ Bad
  have hBad : MeasurableSet Bad := by
    have he : Bad=⋃ j : Fin N, {ω | ω j ∈ C} := by ext ω; simp [Bad]
    rw [he]
    exact MeasurableSet.iUnion fun j => (measurable_pi_apply j) hC
  have hD : MeasurableSet D := (measurableSet_boundarySet Elo B hlo hB (c-1) c).diff hBad
  have hDlower : P.real (boundarySet Elo B (c-1) c)-(N:ℝ)*μ.real C ≤ P.real D := by
    have hp := measureReal_inter_add_sdiff (μ := P)
      (s := boundarySet Elo B (c-1) c) hBad
    have hb := (measureReal_mono (μ := P)
      (s₁ := boundarySet Elo B (c-1) c ∩ Bad) (s₂ := Bad) inter_subset_right).trans
      (any_coordinate_probability_le μ C hC N)
    dsimp only [D]
    linarith
  let A := fun i : Fin (N+1) => {ω : Fin (N+1) → Ω |
    ω i ∈ C ∧ (fun j => ω (i.succAbove j)) ∈ D}
  have hAm (i : Fin (N+1)) : MeasurableSet (A i) :=
    ((measurable_pi_apply i) hC).inter
      ((measurable_pi_lambda _ fun j => measurable_pi_apply (i.succAbove j)) hD)
  have hdis : ∀ i j : Fin (N+1), i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro ω hi hj
    have hn : ¬∃ k : Fin N, ω (i.succAbove k) ∈ C := hi.2.2
    obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    exact hn ⟨k,by simpa only [hk] using hj.1⟩
  have hAi (i : Fin (N+1)) : P'.real (A i)=μ.real C*P.real D :=
    deleted_rectangle_probability μ C D hC hD i
  have hUnion : P'.real (⋃ i, A i)=((N:ℝ)+1)*μ.real C*P.real D := by
    have he : (⋃ i, A i)=⋃ i ∈ (Finset.univ : Finset (Fin (N+1))), A i := by simp
    rw [he,measureReal_biUnion_finset]
    · simp only [hAi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      ring
    · intro i _ j _ hij
      exact hdis i j hij
    · intro i _
      exact hAm i
  have hsub : (⋃ i, A i) ⊆
      {ω | PiBinomial.count Elo Finset.univ ω< c ∧
        c ≤ PiBinomial.count Ehi Finset.univ ω ∧
        c ≤ PiBinomial.count B Finset.univ ω} := by
    intro ω hω
    obtain ⟨i,hi⟩ := mem_iUnion.mp hω
    have hmarkE : ω i ∉ Elo := Set.disjoint_left.mp hCE hi.1
    have hmarkH : ω i ∈ Ehi := hCsub hi.1
    have hrest := hi.2.1
    change PiBinomial.count Elo Finset.univ (fun j => ω (i.succAbove j))=c-1 ∧
      c ≤ PiBinomial.count B Finset.univ (fun j => ω (i.succAbove j)) at hrest
    have hloCount := count_delete_split Elo ω i
    rw [if_neg hmarkE,hrest.1,zero_add] at hloCount
    have hhiCount := count_delete_split Ehi ω i
    rw [if_pos hmarkH] at hhiCount
    have hrestMono := PureRankProbability.count_mono_of_subset hmono
      (fun j => ω (i.succAbove j))
    have hBCount := count_delete_split B ω i
    constructor
    · omega
    constructor
    · omega
    · split_ifs at hBCount <;> omega
  have hmul := mul_le_mul_of_nonneg_left hDlower
    (show 0 ≤ ((N:ℝ)+1)*μ.real C by positivity)
  exact hmul.trans (by rw [← hUnion]; exact measureReal_mono hsub)

end FCAppendix.Affine.Uniform06.PivotalCrossing
