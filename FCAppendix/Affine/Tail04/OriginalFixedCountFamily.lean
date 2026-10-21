import FCAppendix.Affine.Tail04.CoefficientOneEarly
import FCAppendix.Affine.Tail04.CountLaws
import FCAppendix.Affine.Tail04.OriginalActiveComponents

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes
open OriginalValues

namespace BoundedSource
variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

def fullLimit (v : ℝ) : CountLaw 2 :=
  if P.vA-P.w≤ v then FiniteLaw.dirac 1 else s.lowerLimit hs v

theorem fullLimit_low (v : ℝ) (hv : v∈Icc (0:ℝ) P.d0) :
    s.fullLimit hs v=FiniteLaw.dirac 0 := by
  have hh : v< P.vA-P.w := by linarith [hv.2,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  simp only [fullLimit,if_neg (not_le.mpr hh),s.lowerLimit_low hs v hv]

theorem fullLimit_partial (v : ℝ) (hv : v∈P.partialValues) :
    s.fullLimit hs v=s.partialLimit hs v hv := by
  have hh : v< P.vA-P.w := by linarith [hv.2,P.partial_active_gap]
  simp only [fullLimit,if_neg (not_le.mpr hh),s.lowerLimit_partial hs v hv]

theorem fullLimit_upper (v : ℝ) (hv : P.vA-P.w≤ v) :
    s.fullLimit hs v=FiniteLaw.dirac 1 := by simp only [fullLimit,if_pos hv]

lemma binomial_two_expect (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (f : Fin 3→ℝ) :
    (IndependentCounts.binomial 2 q hq0 hq1).expect f=
      (1-q)^2*f 0+2*q*(1-q)*f 1+q^2*f 2 := by
  rw [IndependentCounts.expect_binomial_succ,
    IndependentCounts.expect_binomial_succ,IndependentCounts.expect_binomial_succ]
  simp only [IndependentCounts.binomial,IndependentCounts.independentCount,
    FiniteLaw.expect_dirac]
  change (1-q)*((1-q)*f 0+q*f 1)+q*((1-q)*f 1+q*f 2)=_
  ring

theorem fullLimit_expect_formula (v : ℝ) (f : Fin 3→ℝ) :
    (s.fullLimit hs v).expect f=
      if P.vA-P.w≤v then f 1 else if v∈P.partialValues then
        s.scalar.ownerMass*f 1+s.scalar.mixedMass*
          ((1-s.q v)^2*f 0+2*s.q v*(1-s.q v)*f 1+(s.q v)^2*f 2)
      else f 0 := by
  by_cases hH : P.vA-P.w≤v
  · simp only [fullLimit,if_pos hH,FiniteLaw.expect_dirac]
  · by_cases hP : v∈P.partialValues
    · simp only [fullLimit,if_neg hH,lowerLimit,dif_pos hP,if_pos hP,
        s.partialLimit_expect hs v hP,binomial_two_expect]
    · simp only [fullLimit,if_neg hH,lowerLimit,dif_neg hP,if_neg hP,
        FiniteLaw.expect_dirac]

theorem measurable_fullLimit_expect (f : Fin 3→ℝ) :
    Measurable (fun v=>(s.fullLimit hs v).expect f) := by
  simp_rw [s.fullLimit_expect_formula hs]
  apply Measurable.ite measurableSet_Ici measurable_const
  apply Measurable.ite measurableSet_Icc
  · have hq:=s.q_measurable
    fun_prop
  · exact measurable_const

theorem measurable_fullLimit_mass (r : Fin 3) :
    Measurable (fun v=>(s.fullLimit hs v).mass r) := by
  simpa only [FiniteLaw.expect_singleton] using
    s.measurable_fullLimit_expect hs (fun k=>if k=r then (1:ℝ) else 0)

theorem partialLimit_success_lower (v : ℝ) (hv : v∈P.partialValues) :
    s.scalar.ownerMass≤(s.partialLimit hs v hv).success := by
  have h:=s.partialLimit_expect hs v hv (fun r : Fin 3=>successIndicator r.val)
  change (s.partialLimit hs v hv).success=s.scalar.ownerMass*1+
    s.scalar.mixedMass*(IndependentCounts.binomial 2 (s.q v)
      (hs.q_interior v hv).1.le (hs.q_interior v hv).2.le).success at h
  have hq:=(IndependentCounts.binomial 2 (s.q v)
      (hs.q_interior v hv).1.le (hs.q_interior v hv).2.le).success_nonneg
  nlinarith [s.scalar.mixedMass_pos]

end BoundedSource

section Family
variable (P : ValueParameters) (s : BoundedSource P) (hs : BoundedSourceGuards s)
  (N : ℕ→ℕ) (hN : ∀j,0< N j)
  (Γ : ∀j,FiniteGame (N j) 2 (marketCapacity (N j)) unitInterval)
  (hF : ∀j,(Γ j).F=valueLaw P)
  (hL : ∀v∈Icc (0:ℝ) P.d0,∀f : Fin 3→ℝ,
    Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).expect f) atTop (𝓝 (f 0)))
  (hP : ∀v (hv : v∈P.partialValues),∀f : Fin 3→ℝ,
    Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).expect f) atTop
      (𝓝 ((s.partialLimit hs v hv).expect f)))
  (hH : ∀v,P.vA-P.w≤ v→∀f : Fin 3→ℝ,
    Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).expect f) atTop (𝓝 (f 1)))

include hL hP hH in
theorem original_fixed_count (v : ℝ)
    (hv : v∈Icc (0:ℝ) P.d0∪P.partialValues∪Ici (P.vA-P.w)) (r : Fin 3) :
    Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).mass r) atTop
      (𝓝 ((s.fullLimit hs v).mass r)) := by
  let f : Fin 3→ℝ:=fun k=> if k=r then 1 else 0
  rcases hv with (hv|hv)|hv
  · have hh:=hL v hv f
    have hd : (FiniteLaw.dirac (0 : Fin 3)).mass r=f 0 :=
      (FiniteLaw.expect_singleton (FiniteLaw.dirac (0 : Fin 3)) r).symm.trans
        (FiniteLaw.expect_dirac (0 : Fin 3) f)
    rw [s.fullLimit_low hs v hv,hd]
    simpa only [f,FiniteLaw.expect_singleton] using hh
  · have hh:=hP v hv f
    simpa only [s.fullLimit_partial hs v hv,FiniteLaw.expect_singleton,f] using hh
  · have hh:=hH v hv f
    have hd : (FiniteLaw.dirac (1 : Fin 3)).mass r=f 1 :=
      (FiniteLaw.expect_singleton (FiniteLaw.dirac (1 : Fin 3)) r).symm.trans
        (FiniteLaw.expect_dirac (1 : Fin 3) f)
    rw [s.fullLimit_upper hs v hv,hd]
    simpa only [f,FiniteLaw.expect_singleton] using hh

include hF hL hP hH in
theorem original_aggregate_count (f : Fin 3→ℝ) :
    Tendsto (fun j=>∫v,(conditionalTypeCountLaw (Γ j) (hN j) v).expect f ∂valueLaw P)
      atTop (𝓝 (∫v,(s.fullLimit hs v).expect f ∂valueLaw P)) := by
  have ha : ∀r,∀ᵐv ∂valueLaw P,
      Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).mass r) atTop
        (𝓝 ((s.fullLimit hs v).mass r)) := by
    intro r
    filter_upwards [P.fine_support] with v hv
    apply original_fixed_count P s hs N hN Γ hL hP hH v _ r
    rcases hv with ((hv|hv)|hv)|hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv.1
    · exact Or.inr (by
        change P.vA-P.w≤v
        change P.M≤v at hv
        linarith [P.active_tail_gap,P.w_pos])
  have hh:=Counts.native_expect_integral_tendsto N (fun j=> marketCapacity (N j))
    (fun _=> unitInterval) Γ hN (valueLaw P) hF (s.fullLimit hs) ha f
  simpa only [hF] using hh

include hF hL hP hH hN in
theorem original_aggregates :
    Tendsto (fun j=> finiteCoverage (Γ j)) atTop
      (𝓝 (∫v,(s.fullLimit hs v).success ∂valueLaw P)) ∧
    Tendsto (fun j=> finiteLoad (Γ j)) atTop
      (𝓝 (∫v,(s.fullLimit hs v).load ∂valueLaw P)) ∧
    Tendsto (fun j=> finiteLoad (Γ j)-finiteCoverage (Γ j)) atTop
      (𝓝 (∫v,(s.fullLimit hs v).duplicates ∂valueLaw P)) := by
  have ha : ∀r,∀ᵐv ∂valueLaw P,
      Tendsto (fun j=>(conditionalTypeCountLaw (Γ j) (hN j) v).mass r) atTop
        (𝓝 ((s.fullLimit hs v).mass r)) := by
    intro r
    filter_upwards [P.fine_support] with v hv
    apply original_fixed_count P s hs N hN Γ hL hP hH v _ r
    rcases hv with ((hv|hv)|hv)|hv
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv.1
    · exact Or.inr (by
        change P.vA-P.w≤v
        change P.M≤v at hv
        linarith [P.active_tail_gap,P.w_pos])
  exact ⟨Counts.native_coverage_tendsto N (fun j=> marketCapacity (N j))
      (fun _=> unitInterval) Γ hN (valueLaw P) hF (s.fullLimit hs) ha,
    Counts.native_load_tendsto N (fun j=> marketCapacity (N j))
      (fun _=> unitInterval) Γ hN (valueLaw P) hF (s.fullLimit hs) ha,
    Counts.native_duplicates_tendsto N (fun j=> marketCapacity (N j))
      (fun _=> unitInterval) Γ hN (valueLaw P) hF (s.fullLimit hs) ha⟩

end Family

end FCAppendix.Affine.Tail04.CoefficientOne
