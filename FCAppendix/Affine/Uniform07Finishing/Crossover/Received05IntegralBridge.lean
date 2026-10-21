import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05PatternBridge
import FCAppendix.Affine.Uniform06.LiteralKernelMeasurable

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Uniform06.LiteralKernelMeasurable LowBody
open scoped BigOperators
variable {m N : ℕ}

theorem received_bidLaw_eq_realBid {i : Uniform07.Row}
    (E : UniformFinite.ExactRestrictedLaw i m) :
    ((E.law.bidLaw : Measure (Uniform05.Bid i)).map Subtype.val)=
      (E.realBid : Measure ℝ) := by
  rw [UniformFinite.ExactRestrictedLaw.law,UniformFinite.restrictedLaw_bidLaw]
  rfl

theorem numericalOfFour_kind (i : Uniform07.Row) (r : RowRival) :
    UniformFinite.numericKind i (UniformFinite.OriginalPopulation.numericalOfFour i r)=
      threeKind r.1 := by
  rcases r with ⟨k,b⟩
  fin_cases k <;>
    simp [UniformFinite.OriginalPopulation.numericalOfFour,UniformFinite.numericKind,threeKind]

theorem numericalOfFour_bid (i : Uniform07.Row) (r : RowRival)
    (hcap : r.1=0→ r.2∈Icc (0:ℝ) (Early.bidCap i)) :
    UniformFinite.numericBid i (UniformFinite.OriginalPopulation.numericalOfFour i r)=
      if r.1=0 then r.2 else 0 := by
  by_cases hr : r.1=0
  · have hb:=hcap hr
    have hU : r.2≤Uniform05.cap i := by
      rw [Concrete05.cap_eq]
      exact hb.2
    simp only [UniformFinite.OriginalPopulation.numericalOfFour,if_pos hr,
      UniformFinite.numericBid,Sum.elim_inl,UniformFinite.OriginalPopulation.clipBid,
      max_eq_right hb.1,min_eq_right hU]
  · simp only [UniformFinite.OriginalPopulation.numericalOfFour,if_neg hr,
      UniformFinite.numericBid]
    split_ifs <;> rfl

theorem received_numericFocalPayoff (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    (own : Uniform05.Bid i) (v : ℝ) (ω : Fin N→ RowRival)
    (hno : ∀j,(ω j).1≠1)
    (hcap : ∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) :
    UniformFinite.numericFocalPayoff i N G v own
      (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j))=
      (v-(own:ℝ))*(rowLaw (Uniform07.xi i) (Uniform07.kappa i)
        (Uniform07.capacity (N+1))
        (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
        (received06CountMargin i (N+1)) own ω).expect (first 0)-
      Uniform07.eta i*(own:ℝ)*(rowLaw (Uniform07.xi i) (Uniform07.kappa i)
        (Uniform07.capacity (N+1))
        (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
        (received06CountMargin i (N+1)) own ω).expect (duplicate 0) := by
  have hb : (own:ℝ)∈Icc (0:ℝ) (Early.bidCap i) := by
    simpa only [←Concrete05.cap_eq] using own.property
  have ht:=original_pattern_success_duplicate_eq05 i G hb ω hno hcap
  unfold UniformFinite.numericFocalPayoff
  have hbids : (fun j=>UniformFinite.numericBid i
      (UniformFinite.OriginalPopulation.numericalOfFour i (ω j)))=
      fun j=>if (ω j).1=0 then (ω j).2 else 0 := by
    funext j
    exact numericalOfFour_bid i (ω j) (hcap j)
  simp only [numericalOfFour_kind,hbids]
  change UniformFinite.rowPayoff i G (patternCountRow (fun j=>(ω j).1))
    v (rowBids own ω) 0=_
  rw [UniformFinite.rowPayoff_success_duplicate,←ht.1,←ht.2]
  simp only [rowBids,Fin.cons_zero,Uniform05.eta_eq_canonical]

theorem received_rawUtility_eq_source {i : Uniform07.Row}
    (E : UniformFinite.ExactRestrictedLaw i m) (N : ℕ)
    (own : Uniform05.Bid i) (v : ℝ) :
    UniformFinite.rawUtility i N E.law v own=
      Rank.payoff (Uniform07.eta i) v own
        (sourceSuccess i (N+1) (Concrete05.realJoint E)
          (received06GuardData i (N+1) E.law.multiplier E.law.rejectionRoot)
          (received06CountMargin i (N+1)) own)
        (sourceDuplicate i (N+1) (Concrete05.realJoint E)
          (received06GuardData i (N+1) E.law.multiplier E.law.rejectionRoot)
          (received06CountMargin i (N+1)) own) := by
  let μ : Measure RowRival:=rivalLaw (Uniform07.cutoff i) 0
    (1-Uniform07.cutoff i) (E.realBid : Measure ℝ)
  letI : IsProbabilityMeasure μ:=rivalLaw_isProbability _ _ _ (Uniform07.cutoff_pos i).le
    le_rfl (sub_nonneg.mpr (Uniform07.cutoff_lt_one i).le) (by ring) _
  letI : IsProbabilityMeasure (μ.map (UniformFinite.OriginalPopulation.numericalOfFour i)) :=
    Measure.isProbabilityMeasure_map
      (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).aemeasurable
  let P:=Measure.pi (fun _ : Fin N=>μ)
  let f:=UniformFinite.numericFocalPayoff i N E.law v own
  let g:=received06GuardData i (N+1) E.law.multiplier E.law.rejectionRoot
  let cm : (Fin N→Fin 4)→ℝ:=fun r=>received06CountMargin i (N+1) r
  have hf : Measurable f:=UniformFinite.measurable_numericFocalPayoff i N E.law v own
  have hmap : μ.map (UniformFinite.OriginalPopulation.numericalOfFour i)=
      UniformFinite.numericObservationLaw i E.law := by
    simpa only [μ,Uniform05.t_eq_canonical] using
      UniformFinite.OriginalPopulation.four_to_numeric_law E
  have hrowmap : P.map (fun ω=>fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j))=
      Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw i E.law) := by
    dsimp only [P]
    rw [Measure.pi_map_pi (fun _=>
      (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).aemeasurable)]
    simp only [hmap]
  have hfour : Measurable (fun ω : Fin N→ RowRival=>
      fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j)) :=
    measurable_pi_lambda _ fun j=>
      (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).comp (measurable_pi_apply j)
  have hdrop : Measurable (fun x : Fin N→ UniformFinite.Source.Observation i=>
      fun j=>UniformFinite.dropValue i (x j)) :=
    measurable_pi_lambda _ fun j=>(UniformFinite.measurable_dropValue i).comp (measurable_pi_apply j)
  have hraw : UniformFinite.rawUtility i N E.law v own=
      ∫ω,f (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j)) ∂P := by
    rw [UniformFinite.rawUtility_eq_original_observation_integral,
      ←integral_map hdrop.aemeasurable hf.aestronglyMeasurable,
      UniformFinite.dropValueRow_law,←hrowmap,
      integral_map hfour.aemeasurable hf.aestronglyMeasurable]
  have hreg : ∀ᵐ ω∂P,(∀j,(ω j).1≠1) ∧
      (∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) := by
    simpa only [received_bidLaw_eq_realBid E,μ,P] using
      (original_row_regular (N:=N) i E.law)
  have hfun : (fun ω=>f (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j)))
      =ᵐ[P] (fun ω=>(v-(own:ℝ))*(rowLaw (Uniform07.xi i) (Uniform07.kappa i)
        (Uniform07.capacity (N+1)) g cm own ω).expect (first 0)-
      Uniform07.eta i*(own:ℝ)*(rowLaw (Uniform07.xi i) (Uniform07.kappa i)
        (Uniform07.capacity (N+1)) g cm own ω).expect (duplicate 0)) := by
    filter_upwards [hreg] with ω hω
    exact received_numericFocalPayoff i E.law own v ω hω.1 hω.2
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hS:=integrable_row_first (Uniform07.xi_pos i) (source_xi_lt_one i)
    (Uniform07.kappa i) (Uniform07.capacity (N+1)) g cm (own:ℝ) P
  have hD:=integrable_row_duplicate (Uniform07.xi_pos i) (source_xi_lt_one i)
    (Uniform07.kappa i) (Uniform07.capacity (N+1)) g cm (own:ℝ) P
  rw [hraw,integral_congr_ae hfun,integral_sub (hS.const_mul _) (hD.const_mul _),
    integral_const_mul,integral_const_mul]
  simp only [Rank.payoff,sourceSuccess,sourceDuplicate,actualSuccess,actualDuplicate,
    Concrete05.realJoint_bid,g,cm,P,μ]
  rfl

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
