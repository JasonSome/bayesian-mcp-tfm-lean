import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05IntegralBridge
import FCAppendix.Affine.Uniform06.LiteralKernelDecomposition

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Uniform06 Uniform06.LiteralExperiment Uniform06.LiteralKernelDecomposition LowBody
open scoped BigOperators
variable {m N : ℕ}

def fairTest (k : Fin 3) : ℝ := (k:ℝ)/2

theorem fairTest_pairCount (j : Fin m) (P : UniformFinite.Allocation m) :
    fairTest (UniformFinite.pairCount j P)=fairMarginal j P := by
  by_cases h0 : j∈P.1 <;> by_cases h1 : j∈P.2 <;>
    simp [fairTest,UniformFinite.pairCount,fairMarginal,LiteralExperiment.indicator,h0,h1]

def rowCanonicalMoment05 (i : Uniform07.Row) (G : Uniform05.RestrictedLaw i)
    [NeZero m] (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ) (j : Fin m)
    (q : Fin 3→ℝ) : ℝ :=
  if UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1 then
    (UniformFinite.equalLaw i D b).expect (fun P=>q (UniformFinite.pairCount j P))
  else UniformFinite.Source.guardAlpha i G D b*
    (UniformFinite.canonicalLaw i G D b).expect (fun P=>q (UniformFinite.pairCount j P))

def numericalCanonicalMoment05 (i : Uniform07.Row) (N : ℕ)
    (G : Uniform05.RestrictedLaw i) (own : Uniform05.Bid i) (q : Fin 3→ℝ)
    (z : Fin N→ UniformFinite.NumericObservation i) : ℝ :=
  rowCanonicalMoment05 i G
    (UniformFinite.Source.countRowOfKind (Fin.cons 0 (fun j=>UniformFinite.numericKind i (z j))))
    (Fin.cons (own:ℝ) (fun j=>UniformFinite.numericBid i (z j))) 0 q

theorem received_guarded_canonical_tests (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) [NeZero m] (hm : 0< m)
    (D : UniformFinite.Source.CountRow m) (b : Fin m→ℝ)
    (hb : ∀j,j∉D.lower→ b j=0) (hU : ∀j,b j≤ Early.bidCap i) (j : Fin m) :
    rowCanonicalMoment05 i G D b j fairTest=
      (if UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1 then
        complementMarginal (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅ j
      else guardAlpha (Uniform07.xi i) (rowGuardData i G D)
        (UniformFinite.Source.lowerTemplate D) b*
          (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
            (UniformFinite.Source.lowerTemplate D) b).expect (fairMarginal j)) ∧
    rowCanonicalMoment05 i G D b j duplicateTest=
      (if UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1 then
        (complementMarginal (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅ j)^2
      else guardAlpha (Uniform07.xi i) (rowGuardData i G D)
        (UniformFinite.Source.lowerTemplate D) b*
          (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
            (UniformFinite.Source.lowerTemplate D) b).expect (duplicate j)) := by
  have hB:=lowerBids_eq_of_outside D b hb
  have ha:=received_guardAlpha_eq i G hm D b
  rw [hB] at ha
  have hmask : maskedBids (UniformFinite.Source.lowerTemplate D) b ∅=b := by
    funext k
    by_cases hk : k∈D.lower <;> simp [maskedBids,UniformFinite.Source.lowerTemplate,hk,hb k]
  by_cases he : UniformFinite.Source.residual D 0=UniformFinite.Source.residual D 1
  · have hEq : UniformFinite.equalLaw i D b=
        (complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅).prod
          (complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅) := by
      simp only [UniformFinite.equalLaw,UniformFinite.equalLottery,complementLaw,
        EqualCapacity.canonicalLottery,Uniform05.xi_eq_canonical,
        rowGuardData_small,hB,hmask]
    have hS:=completion_pair_first (Uniform07.xi_pos i) (source_xi_lt_one i)
      (UniformFinite.Source.lowerTemplate D) b ∅ j
    have hD:=completion_pair_duplicate (Uniform07.xi_pos i) (source_xi_lt_one i)
      (UniformFinite.Source.lowerTemplate D) b ∅ j
    simp only [attachExclusive,Finset.empty_union,ite_self,Prod.mk.eta,
      Finset.notMem_empty,if_false] at hS hD
    simp only [rowCanonicalMoment05,if_pos he,hEq,fairTest_pairCount,duplicateTest_pairCount]
    refine ⟨?_,hD⟩
    have hadd : ((complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅).prod
        (complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅)).expect
          (first j)+
      ((complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅).prod
        (complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅)).expect
          (duplicate j)=
      2*((complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅).prod
        (complementLaw (Uniform07.xi i) (UniformFinite.Source.lowerTemplate D) b ∅)).expect
          (fairMarginal j) := by
      rw [←FiniteLaw.expect_add,←FiniteLaw.expect_const_mul]
      exact FiniteLaw.expect_congr _ (first_add_duplicate j)
    linarith
  · simp only [rowCanonicalMoment05,if_neg he,fairTest_pairCount,duplicateTest_pairCount,ha]
    by_cases hz : UniformFinite.Source.guardAlpha i G D b=0
    · simp [hz]
    · have hap : 0< UniformFinite.Source.guardAlpha i G D b :=
        lt_of_le_of_ne (UniformFinite.Source.guardAlpha_bounds i G D b).1 (Ne.symm hz)
      have haraw : 0< UniformFinite.Source.rawAlpha i G D b := by
        unfold UniformFinite.Source.guardAlpha at hap
        split_ifs at hap
        · exact False.elim ((lt_irrefl 0) hap)
        · exact hap
      have hc:=received_canonical_tests_eq05 i G hm D b hb hU haraw j
      have hfair : (UniformFinite.canonicalLaw i G D b).expect (fairMarginal j)=
          (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
            (UniformFinite.Source.lowerTemplate D) b).expect (fairMarginal j) := by
        have hsum (P : FiniteLaw (UniformFinite.Allocation m)) :
            P.expect (first j)+P.expect (duplicate j)=2*P.expect (fairMarginal j) := by
          rw [←FiniteLaw.expect_add,←FiniteLaw.expect_const_mul]
          exact FiniteLaw.expect_congr _ (first_add_duplicate j)
        have hleft:=hsum (UniformFinite.canonicalLaw i G D b)
        have hright:=hsum (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
          (UniformFinite.Source.lowerTemplate D) b)
        have hfirst : (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
            (UniformFinite.Source.lowerTemplate D) b).expect (first j)=
            (UniformFinite.canonicalLaw i G D b).expect (first j) := hc.1
        have hduplicate : (canonicalLaw (Uniform07.xi i) (rowGuardData i G D)
            (UniformFinite.Source.lowerTemplate D) b).expect (duplicate j)=
            (UniformFinite.canonicalLaw i G D b).expect (duplicate j) := hc.2
        linarith only [hleft,hright,hfirst,hduplicate]
      exact ⟨congrArg (fun z=>UniformFinite.Source.guardAlpha i G D b*z) hfair,
        congrArg (fun z=>UniformFinite.Source.guardAlpha i G D b*z) hc.2.symm⟩

theorem received_numerical_canonical_tests (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (own : Uniform05.Bid i)
    (ω : Fin N→ RowRival) (hno : ∀j,(ω j).1≠1)
    (hcap : ∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) :
    numericalCanonicalMoment05 i N G own fairTest
      (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j))=
      rowCanonicalFair (Uniform07.xi i) (Uniform07.capacity (N+1))
        (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
        (received06CountMargin i (N+1)) own ω ∧
    numericalCanonicalMoment05 i N G own duplicateTest
      (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j))=
      rowCanonicalDuplicate (Uniform07.xi i) (Uniform07.capacity (N+1))
        (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
        (received06CountMargin i (N+1)) own ω := by
  have hu : ∀j,rowBids own ω j≤ Early.bidCap i := by
    intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · simpa only [rowBids,Fin.cons_zero,←Concrete05.cap_eq] using own.property.2
    · by_cases hk : (ω k).1=0
      · simpa only [rowBids,Fin.cons_succ,if_pos hk] using (hcap k hk).2
      · simp only [rowBids,Fin.cons_succ,if_neg hk]
        exact (Concrete05.native_cap_positive i).le
  have h:=received_guarded_canonical_tests i G (Nat.succ_pos N)
    (patternCountRow (fun j=>(ω j).1)) (rowBids own ω)
    (rowBids_outside_countRow own ω) hu 0
  have hb : (fun j=>UniformFinite.numericBid i
      (UniformFinite.OriginalPopulation.numericalOfFour i (ω j)))=
        fun j=>if (ω j).1=0 then (ω j).2 else 0 := by
    funext j
    exact numericalOfFour_bid i (ω j) (hcap j)
  simpa only [numericalCanonicalMoment05,numericalOfFour_kind,hb,
    rowBids,patternCountRow_residual _ hno,patternCountRow_template _ hno,
    patternCountRow_guard i G _ hno,rowCanonicalFair,rowCanonicalDuplicate,
    canonicalLaw_update_countMargin] using! h

def fourOfNumerical (i : Uniform07.Row) : UniformFinite.NumericObservation i→ RowRival :=
  Sum.elim (fun b=>(0,(b:ℝ))) (fun j=>if j=0 then (2,0) else (3,0))

theorem measurable_fourOfNumerical (i : Uniform07.Row) : Measurable (fourOfNumerical i) :=
  (measurable_const.prodMk measurable_subtype_coe).sumElim (measurable_of_countable _)

theorem fourOfNumerical_regular (i : Uniform07.Row) (z : UniformFinite.NumericObservation i) :
    (fourOfNumerical i z).1≠1 ∧
      ((fourOfNumerical i z).1=0→(fourOfNumerical i z).2∈Icc (0:ℝ) (Early.bidCap i)) ∧
      UniformFinite.OriginalPopulation.numericalOfFour i (fourOfNumerical i z)=z := by
  rcases z with b|j
  · simp only [fourOfNumerical,Sum.elim_inl,UniformFinite.OriginalPopulation.numericalOfFour,
      if_true]
    refine ⟨by decide,(fun _=>by simpa only [←Concrete05.cap_eq] using b.property),?_⟩
    congr 1
    apply Subtype.ext
    simp only [UniformFinite.OriginalPopulation.clipBid,
      max_eq_right b.property.1,min_eq_right b.property.2]
  · fin_cases j <;> simp [fourOfNumerical,UniformFinite.OriginalPopulation.numericalOfFour]

theorem measurable_numericalCanonical_tests (i : Uniform07.Row)
    (G : Uniform05.RestrictedLaw i) (own : Uniform05.Bid i) :
    Measurable (numericalCanonicalMoment05 i N G own fairTest) ∧
      Measurable (numericalCanonicalMoment05 i N G own duplicateTest) := by
  let f : (Fin N→ UniformFinite.NumericObservation i)→ Fin N→ RowRival :=
    fun z j=>fourOfNumerical i (z j)
  have hf : Measurable f:=measurable_pi_lambda _ fun j=>
    (measurable_fourOfNumerical i).comp (measurable_pi_apply j)
  have heq (z : Fin N→ UniformFinite.NumericObservation i) :=
    received_numerical_canonical_tests i G own (f z)
      (fun j=>(fourOfNumerical_regular i (z j)).1)
      (fun j=>(fourOfNumerical_regular i (z j)).2.1)
  have hinv (z : Fin N→ UniformFinite.NumericObservation i) :
      (fun j=>UniformFinite.OriginalPopulation.numericalOfFour i (f z j))=z := by
    funext j
    exact (fourOfNumerical_regular i (z j)).2.2
  simp only [hinv] at heq
  have hmeas:=measurable_rowCanonical (Uniform07.xi i) (Uniform07.capacity (N+1))
    (received06GuardData i (N+1) G.multiplier G.rejectionRoot)
    (received06CountMargin i (N+1)) (own:ℝ) (Uniform07.xi_pos i) (source_xi_lt_one i)
  constructor
  · convert hmeas.2.1.comp hf using 1
    funext z
    exact (heq z).1
  · convert hmeas.2.2.comp hf using 1
    funext z
    exact (heq z).2

theorem received_canonical_integrals {i : Uniform07.Row}
    (E : UniformFinite.ExactRestrictedLaw i m) (N : ℕ) (own : Uniform05.Bid i) :
    (∫z,numericalCanonicalMoment05 i N E.law own fairTest z
      ∂Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw i E.law))=
      sourceCanonicalMarginal i (N+1) (Concrete05.realJoint E)
        (received06GuardData i (N+1) E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin i (N+1)) own ∧
    (∫z,numericalCanonicalMoment05 i N E.law own duplicateTest z
      ∂Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw i E.law))=
      sourceCanonicalDuplicate i (N+1) (Concrete05.realJoint E)
        (received06GuardData i (N+1) E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin i (N+1)) own := by
  let μ : Measure RowRival:=rivalLaw (Uniform07.cutoff i) 0
    (1-Uniform07.cutoff i) (E.realBid:Measure ℝ)
  letI : IsProbabilityMeasure μ:=rivalLaw_isProbability _ _ _ (Uniform07.cutoff_pos i).le
    le_rfl (sub_nonneg.mpr (Uniform07.cutoff_lt_one i).le) (by ring) _
  letI : IsProbabilityMeasure (μ.map (UniformFinite.OriginalPopulation.numericalOfFour i)) :=
    Measure.isProbabilityMeasure_map
      (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).aemeasurable
  let P:=Measure.pi (fun _ : Fin N=>μ)
  let f : (Fin N→ RowRival)→ Fin N→ UniformFinite.NumericObservation i :=
    fun ω j=>UniformFinite.OriginalPopulation.numericalOfFour i (ω j)
  have hf : Measurable f:=measurable_pi_lambda _ fun j=>
    (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).comp (measurable_pi_apply j)
  have hmap : P.map f=Measure.pi (fun _ : Fin N=>UniformFinite.numericObservationLaw i E.law) := by
    have hsingle : μ.map (UniformFinite.OriginalPopulation.numericalOfFour i)=
        UniformFinite.numericObservationLaw i E.law := by
      simpa only [μ,Uniform05.t_eq_canonical] using
        UniformFinite.OriginalPopulation.four_to_numeric_law E
    dsimp only [P]
    rw [Measure.pi_map_pi (fun _=>
      (UniformFinite.OriginalPopulation.measurable_numericalOfFour i).aemeasurable)]
    simp only [hsingle]
  have hreg : ∀ᵐω∂P,(∀j,(ω j).1≠1) ∧
      (∀j,(ω j).1=0→(ω j).2∈Icc (0:ℝ) (Early.bidCap i)) := by
    simpa only [received_bidLaw_eq_realBid E,μ,P] using original_row_regular (N:=N) i E.law
  have hmeas:=measurable_numericalCanonical_tests (N:=N) i E.law own
  constructor
  · rw [←hmap,integral_map hf.aemeasurable hmeas.1.aestronglyMeasurable]
    change (∫ω,numericalCanonicalMoment05 i N E.law own fairTest (f ω) ∂P)=_
    have heq := integral_congr_ae (hreg.mono fun ω hω=>
      (received_numerical_canonical_tests i E.law own ω hω.1 hω.2).1)
    simpa only [sourceCanonicalMarginal,actualCanonicalMarginal,
      Concrete05.realJoint_bid,P,μ,f] using! heq
  · rw [←hmap,integral_map hf.aemeasurable hmeas.2.aestronglyMeasurable]
    change (∫ω,numericalCanonicalMoment05 i N E.law own duplicateTest (f ω) ∂P)=_
    have heq := integral_congr_ae (hreg.mono fun ω hω=>
      (received_numerical_canonical_tests i E.law own ω hω.1 hω.2).2)
    simpa only [sourceCanonicalDuplicate,actualCanonicalDuplicate,
      Concrete05.realJoint_bid,P,μ,f] using! heq

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
