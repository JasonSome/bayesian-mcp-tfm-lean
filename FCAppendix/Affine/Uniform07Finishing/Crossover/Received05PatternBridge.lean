import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05RowBridge
import FCAppendix.Affine.UniformFinite.OriginalPopulationRows

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment LowBody
open scoped BigOperators
variable {N : ℕ}

def threeKind (k : Fin 4) : Fin 3 := if k=0 then 0 else if k=2 then 1 else 2

theorem threeKind_zero (k : Fin 4) : threeKind k=0 ↔ k=0 := by
  fin_cases k <;> simp [threeKind]

theorem threeKind_one (k : Fin 4) : threeKind k=1 ↔ k=2 := by
  fin_cases k <;> simp [threeKind]

theorem threeKind_two (k : Fin 4) (hk : k≠1) : threeKind k=2 ↔ k=3 := by
  fin_cases k <;> simp_all [threeKind]

def patternCountRow (kind : Fin N→ Fin 4) : UniformFinite.Source.CountRow (N+1) :=
  UniformFinite.Source.countRowOfKind (Fin.cons 0 (fun j=>threeKind (kind j)))

theorem patternCountRow_lower (kind : Fin N→ Fin 4) (c : ℕ) :
    (patternCountRow kind).lower=(patternTemplate c kind).support := by
  ext j
  refine Fin.cases ?_ (fun k=>?_) j
  · simp [patternCountRow,UniformFinite.Source.countRowOfKind,patternTemplate,
      rowLowList,patternRow]
  · simp only [patternCountRow,UniformFinite.Source.countRowOfKind,
      Finset.mem_filter,Finset.mem_univ,true_and,Fin.cons_succ,threeKind_zero,
      patternTemplate,rowLowList,patternRow]
    by_cases hk : kind k=0 <;> simp [hk]

theorem patternCountRow_lower_card (kind : Fin N→ Fin 4) :
    (patternCountRow kind).lower.card=1+classCount 0 (patternRow kind) := by
  rw [patternCountRow_lower kind 0]
  exact patternTemplate_card 0 kind

theorem patternCountRow_upper0 (kind : Fin N→ Fin 4) :
    (patternCountRow kind).upper0=classCount 2 (patternRow kind) := by
  unfold patternCountRow UniformFinite.Source.countRowOfKind
  change (Finset.univ.filter (fun a : Fin (N+1)=>
    (Fin.cons (0:Fin 3) (fun j=>threeKind (kind j)) : Fin (N+1)→Fin 3) a=1)).card=_
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,Fin.zero_ne_one,if_false,zero_add,
    threeKind_one,classCount,patternRow]
  rfl

theorem patternCountRow_upper1 (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1) :
    (patternCountRow kind).upper1=classCount 3 (patternRow kind) := by
  unfold patternCountRow UniformFinite.Source.countRowOfKind
  change (Finset.univ.filter (fun a : Fin (N+1)=>
    (Fin.cons (0:Fin 3) (fun j=>threeKind (kind j)) : Fin (N+1)→Fin 3) a=2)).card=_
  rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,show (0:Fin 3)≠2 by decide,
    if_false,zero_add,classCount,patternRow]
  apply Finset.sum_congr rfl
  intro j _
  simp only [threeKind_two (kind j) (hno j)]
  rfl

theorem classCount_one_eq_zero (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1) :
    classCount 1 (patternRow kind)=0 := by
  simp [classCount,patternRow,hno]

theorem patternCountRow_residual (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1)
    (j : Fin 2) :
    UniformFinite.Source.residual (patternCountRow kind) j=
      rowResidual (Uniform07.capacity (N+1)) j (patternRow kind) := by
  simp only [UniformFinite.Source.residual,patternCountRow_lower_card,
    UniformFinite.Source.upperCount,patternCountRow_upper0,
    patternCountRow_upper1 kind hno,rowResidual,classCount_one_eq_zero kind hno,Nat.sub_zero]
  fin_cases j <;> simp

theorem patternCountRow_template (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1) :
    UniformFinite.Source.lowerTemplate (patternCountRow kind)=
      patternTemplate (Uniform07.capacity (N+1)) kind := by
  unfold UniformFinite.Source.lowerTemplate patternTemplate
  congr 1
  · exact patternCountRow_lower kind (Uniform07.capacity (N+1))
  · exact patternCountRow_residual kind hno 0
  · exact patternCountRow_residual kind hno 1

theorem rowBids_outside_countRow (b : ℝ) (ω : Fin N→ RowRival) :
    ∀j,j∉(patternCountRow (fun k=>(ω k).1)).lower→ rowBids b ω j=0 := by
  rw [patternCountRow_lower (fun k=>(ω k).1) (Uniform07.capacity (N+1))]
  exact rowBids_outside _ b ω

theorem patternCountRow_coordinates (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1) :
    rowCountCoordinates (patternCountRow kind)=countCoordinate (N+1) kind := by
  have hcount (k : Fin 4) : EntryFullRestoration.count k kind=
      classCount k (patternRow kind) :=
    EntryFullRestoration.count_eq_classCount k (patternRow kind)
  simp only [rowCountCoordinates,countCoordinate,patternCountRow_lower_card,
    patternCountRow_upper0,patternCountRow_upper1 kind hno,hcount,Nat.cast_add,Nat.cast_one]
  rw [add_comm (1:ℝ)]

theorem patternCountRow_guard (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 4) (hno : ∀j,kind j≠1) :
    rowGuardData i G (patternCountRow kind)=
      {received06GuardData i (N+1) G.multiplier G.rejectionRoot with
        countMargin:=received06CountMargin i (N+1) kind} := by
  simp only [rowGuardData,received06CountMargin,patternCountRow_coordinates kind hno]
  rfl

theorem original_pattern_success_duplicate_eq05 (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) {b : ℝ} (hb : b∈Icc (0:ℝ) (Early.bidCap i))
    (ω : Fin N→ RowRival) (hno : ∀j,(ω j).1≠1)
    (hcap : ∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) :
    (rowLaw (Uniform07.xi i) (Uniform07.kappa i) (Uniform07.capacity (N+1))
      (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
      (received06CountMargin i (N+1)) b ω).expect (first 0)=
      UniformFinite.successProbability i G (patternCountRow (fun j=>(ω j).1))
        (rowBids b ω) 0 ∧
    (rowLaw (Uniform07.xi i) (Uniform07.kappa i) (Uniform07.capacity (N+1))
      (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
      (received06CountMargin i (N+1)) b ω).expect (duplicate 0)=
      UniformFinite.duplicateProbability i G (patternCountRow (fun j=>(ω j).1))
        (rowBids b ω) 0 := by
  have hu : ∀j,rowBids b ω j≤ Early.bidCap i := by
    intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · exact hb.2
    · by_cases hk : (ω k).1=0
      · simpa only [rowBids,Fin.cons_succ,if_pos hk] using (hcap k hk).2
      · simp only [rowBids,Fin.cons_succ,if_neg hk]
        exact (Concrete05.native_cap_positive i).le
  have h:=received_continuation_tests_eq05 i G (Nat.succ_pos N)
    (patternCountRow (fun j=>(ω j).1)) (rowBids b ω)
    (rowBids_outside_countRow b ω) hu 0
  simpa only [patternCountRow_template _ hno,patternCountRow_guard i G _ hno,rowLaw] using! h

theorem original_row_regular (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N=>LowBody.rivalLaw (Uniform07.cutoff i) 0
      (1-Uniform07.cutoff i) ((G.bidLaw:Measure (Uniform05.Bid i)).map Subtype.val))),
      (∀j,(ω j).1≠1) ∧
        (∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) := by
  let μ:Measure RowRival:=LowBody.rivalLaw (Uniform07.cutoff i) 0
    (1-Uniform07.cutoff i) ((G.bidLaw:Measure (Uniform05.Bid i)).map Subtype.val)
  letI : IsProbabilityMeasure ((G.bidLaw:Measure (Uniform05.Bid i)).map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  letI : IsProbabilityMeasure μ := rivalLaw_isProbability _ _ _
    (Uniform07.cutoff_pos i).le le_rfl
    (sub_nonneg.mpr (Uniform07.cutoff_lt_one i).le) (by ring) _
  have hμ : ∀ᵐ r∂μ,r.1≠1 ∧ (r.1=0→ r.2∈Icc (0:ℝ) (Early.bidCap i)) := by
    unfold μ LowBody.rivalLaw
    simp only [ENNReal.ofReal_zero,zero_smul,add_zero,ae_add_measure_iff]
    refine ⟨⟨?_,?_⟩,?_⟩
    · apply Measure.ae_smul_measure
      apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable
        (by measurability)).mpr
      apply (ae_map_iff measurable_subtype_coe.aemeasurable (by measurability)).mpr
      exact ae_of_all _ fun r=>⟨by change (0:Fin 4)≠1; decide,fun _=>by
        change (r:ℝ)∈Icc (0:ℝ) (Early.bidCap i)
        rw [←Concrete05.cap_eq]
        exact r.property⟩
    · apply Measure.ae_smul_measure
      simp
    · apply Measure.ae_smul_measure
      simp
  have hall : ∀ᵐ ω ∂Measure.pi (fun _ : Fin N=>μ),∀j,
      (ω j).1≠1 ∧ ((ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval (fun _ : Fin N=>μ) j).quasiMeasurePreserving.ae hμ
  filter_upwards [hall] with ω hω
  exact ⟨fun j=>(hω j).1,fun j=>(hω j).2⟩

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
