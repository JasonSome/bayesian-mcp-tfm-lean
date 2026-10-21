import FCAppendix.Affine.LowBody.PatternContinuity
import FCAppendix.Affine.LowBody.BoundedNullWeakIntegral

noncomputable section
namespace FCAppendix.Affine.LowBody
open Set Filter Topology MeasureTheory ProbabilityTheory

variable {N : ℕ}

def patternBadSet (d κ : ℝ) (kind : Fin N→Fin 4) : Set (ℝ×ℝ×(Fin N→LowValue d)) :=
  {t | t.2.1≤0 ∨ ∃P Q : Finset (Fin (N+1))×Finset (Fin (N+1)),
    focalCopy P 0≠focalCopy Q 0 ∧
    CompleteInformation.potential κ (actualPatternBids kind d t.2.1 t.2.2) P.1 P.2=
      CompleteInformation.potential κ (actualPatternBids kind d t.2.1 t.2.2) Q.1 Q.2}

theorem isClosed_patternBadSet (d κ : ℝ) (kind : Fin N→Fin 4) :
    IsClosed (patternBadSet d κ kind) := by
  classical
  let bids : (ℝ×ℝ×(Fin N→LowValue d))→(Fin (N+1)→ℝ) :=
    fun t=>actualPatternBids kind d t.2.1 t.2.2
  have hc : Continuous bids := (continuous_actualPatternBids kind d).comp
    (continuous_snd.fst.prodMk continuous_snd.snd)
  have he : patternBadSet d κ kind={t : ℝ×ℝ×(Fin N→LowValue d) | t.2.1≤0} ∪
      ⋃P : Finset (Fin (N+1))×Finset (Fin (N+1)),
      ⋃Q : Finset (Fin (N+1))×Finset (Fin (N+1)),
      {t | focalCopy P 0≠focalCopy Q 0 ∧
        CompleteInformation.potential κ (bids t) P.1 P.2=
          CompleteInformation.potential κ (bids t) Q.1 Q.2} := by
    ext t
    simp only [patternBadSet,mem_setOf_eq,mem_union,mem_iUnion,bids]
  rw [he]
  apply (isClosed_le (by fun_prop) continuous_const).union
  apply isClosed_iUnion_of_finite
  intro P
  apply isClosed_iUnion_of_finite
  intro Q
  by_cases h : focalCopy P 0=focalCopy Q 0
  · simpa only [h,ne_eq,not_true_eq_false,false_and,Set.setOf_false] using isClosed_empty
  · simpa only [h,ne_eq,not_false_eq_true,true_and,Function.comp_def] using
      isClosed_eq ((continuous_potential κ P).comp hc) ((continuous_potential κ Q).comp hc)

theorem continuousAt_patternActualPayoff_of_not_mem_bad {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) (t : ℝ×ℝ×(Fin N→LowValue d))
    (ht : t∉patternBadSet d (1-ξ) kind) :
    ContinuousAt (patternActualPayoff d ξ c kind) t := by
  have hb : 0<t.2.1 := lt_of_not_ge (fun h=>ht (Or.inl h))
  have hgeneric : ∀P Q : Finset (Fin (N+1))×Finset (Fin (N+1)),
      CompleteInformation.potential (1-ξ) (actualPatternBids kind d t.2.1 t.2.2) P.1 P.2=
        CompleteInformation.potential (1-ξ) (actualPatternBids kind d t.2.1 t.2.2) Q.1 Q.2 →
      focalCopy P 0=focalCopy Q 0 := by
    intro P Q he
    by_contra hn
    exact ht (Or.inr ⟨P,Q,hn,he⟩)
  by_cases heq : (patternTemplate c kind).residual₀=(patternTemplate c kind).residual₁
  · have he : patternActualPayoff d ξ c kind=(fun u : ℝ×ℝ×(Fin N→LowValue d)=>
        equalPayoff ξ (patternTemplate c kind).residual₀ 0 u.1 (actualPatternBids kind d u.2.1 u.2.2)) := by
      funext u
      exact if_pos heq
    rw [he]
    exact continuousAt_patternEqualPayoff hξ hξ1 hb _ kind t.2.2 t.1
  · have he : patternActualPayoff d ξ c kind=patternPurePayoff d (1-ξ) c kind := by
      funext u
      exact if_neg heq
    rw [he]
    let T:=patternTemplate c kind
    let bids : (ℝ×ℝ×(Fin N→LowValue d))→(Fin (N+1)→ℝ) :=
      fun u=>actualPatternBids kind d u.2.1 u.2.2
    have hc : Continuous bids := (continuous_actualPatternBids kind d).comp
      (continuous_snd.fst.prodMk continuous_snd.snd)
    exact continuousAt_selected_payoff
      (fun u (P : T.Candidate)=>CompleteInformation.potential (1-ξ) (bids u) P.val.1 P.val.2)
      (fun P=>(continuous_potential (1-ξ) P.val).comp hc)
      (fun P : T.Candidate=>focalCopy P.val 0)
      (fun u (P : T.Candidate)=>purePayoff (1-ξ) u.1 (bids u) P.val 0)
      (fun P=>by unfold purePayoff; split_ifs <;> fun_prop)
      (fun u P Q h=>purePayoff_eq_of_focalCopy_eq (1-ξ) u.1 (bids u) P.val Q.val 0 h)
      t (fun P Q he=>hgeneric P.val Q.val he)

theorem measurable_patternActualPayoff {d ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (c : ℕ) (kind : Fin N→Fin 4) : Measurable (patternActualPayoff d ξ c kind) := by
  classical
  let T:=patternTemplate c kind
  let bids : (ℝ×ℝ×(Fin N→LowValue d))→(Fin (N+1)→ℝ) :=
    fun t=>actualPatternBids kind d t.2.1 t.2.2
  have hc : Continuous bids := (continuous_actualPatternBids kind d).comp
    (continuous_snd.fst.prodMk continuous_snd.snd)
  have hp : Measurable (fun t=>EqualCapacity.positiveMarginal ξ T.residual₀ (bids t) 0) :=
    (measurable_pi_apply 0).comp
      ((EqualCapacity.measurable_positiveMarginal ξ T.residual₀ hξ hξ1).comp hc.measurable)
  have he : Measurable (fun t=>equalPayoff ξ T.residual₀ 0 t.1 (bids t)) := by
    unfold equalPayoff
    fun_prop
  letI : MeasurableSpace T.Candidate:=⊤
  have hs : Measurable (fun t=>FiniteSelector.select
      (fun P : T.Candidate=>CompleteInformation.potential (1-ξ) (bids t) P.val.1 P.val.2)) :=
    FiniteSelector.measurable_select _
      (fun P : T.Candidate=>((continuous_potential (1-ξ) P.val).comp hc).measurable)
  have hl : Measurable (fun t=>focalCopy (T.selection (1-ξ) (bids t)) 0) :=
    (measurable_of_countable (fun P : T.Candidate=>focalCopy P.val 0)).comp hs
  have hu : Measurable (patternPurePayoff d (1-ξ) c kind) := by
    exact Measurable.ite (measurableSet_eq_fun hl measurable_const)
      (by fun_prop) (Measurable.ite (measurableSet_eq_fun hl measurable_const) (by fun_prop) measurable_const)
  unfold patternActualPayoff
  dsimp only
  split_ifs
  · exact he
  · exact hu

def physicalPatternInput (d : ℝ) (t : (LowValue d×LowValue d)×(Fin N→LowValue d)) :
    ℝ×ℝ×(Fin N→LowValue d) := (t.1.1.1,t.1.2.1,t.2)

@[fun_prop] theorem continuous_physicalPatternInput (d : ℝ) :
    Continuous (physicalPatternInput (N:=N) d) := by unfold physicalPatternInput; fun_prop

theorem ae_physicalPattern_not_bad {d κ : ℝ} (hκ : 0<κ)
    (pi : Measure (LowValue d×LowValue d)) [IsProbabilityMeasure pi]
    (G : Measure (LowValue d)) [IsProbabilityMeasure G] [NullSingletonClass G]
    (hpos : ∀ᵐx ∂pi,0<x.2.1) (kind : Fin N→Fin 4) :
    ∀ᵐt ∂pi.prod (Measure.pi (fun _ : Fin N=>G)),
      physicalPatternInput d t∉patternBadSet d κ kind := by
  have hm : MeasurableSet {t : (LowValue d×LowValue d)×(Fin N→LowValue d) |
      physicalPatternInput d t∉patternBadSet d κ kind} :=
    ((isClosed_patternBadSet d κ kind).preimage (continuous_physicalPatternInput d)).measurableSet.compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hpos] with x hx
  filter_upwards [ae_pattern_ties_same_focalCopy hκ hx.ne' G kind] with r hr
  rintro (hn|⟨P,Q,hne,he⟩)
  · exact not_le_of_gt hx hn
  · exact hne (hr P Q he)

end FCAppendix.Affine.LowBody
