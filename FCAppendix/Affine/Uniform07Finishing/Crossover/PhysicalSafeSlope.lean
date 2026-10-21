import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalBarrier

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem comparison_safe_slope_from_finite_budgets
    {delta q q' a D' N err m a0 rent0 eps E tau : ℝ}
    (hm : 0< m) (ha0 : 0< a0) (hrent0 : 0< rent0) (hq : 0≤ q)
    (ha : a0*m≤ a) (hdelta : rent0/m≤ delta)
    (hden : 0< barrierDenominator a q D') (hD' : 0≤ D')
    (hIC : delta*(2*q'-D')=N+err)
    (hsafe : N/barrierDenominator a q D'-delta≤ eps/m)
    (heps : 0≤ eps) (_hE : 0≤ E) (htau : 0≤ tau)
    (herr : |err|≤ E*q) (hfirst : 2*eps≤ rent0*tau) (hsecond : E≤ rent0*a0*tau) :
    q'≤(1+tau)*a*q := by
  have haPos : 0< a := (mul_pos ha0 hm).trans_le ha
  have hdeltaPos : 0< delta := (div_pos hrent0 hm).trans_le hdelta
  apply safe_side_log_slope hdeltaPos hden.ne' hIC
  have hKupper : barrierDenominator a q D'≤ 2*a*q := by
    unfold barrierDenominator
    linarith
  have hterm := mul_le_mul_of_nonneg_right hsafe hden.le
  have hterm' := mul_le_mul_of_nonneg_left hKupper (div_nonneg heps hm.le)
  have hfirst' := mul_le_mul_of_nonneg_right hfirst (div_nonneg (mul_nonneg haPos.le hq) hm.le)
  have hδfirst := mul_le_mul_of_nonneg_right hdelta (mul_nonneg (mul_nonneg htau haPos.le) hq)
  have hδa : rent0*a0≤ delta*a := by
    have hprod := mul_le_mul hdelta ha (mul_nonneg ha0.le hm.le) hdeltaPos.le
    have hid : (rent0/m)*(a0*m)=rent0*a0 := by field_simp [hm.ne']
    rw [hid] at hprod
    exact hprod
  have hsecond' := mul_le_mul_of_nonneg_right hsecond hq
  have hδsecond := mul_le_mul_of_nonneg_right hδa (mul_nonneg htau hq)
  have herr' := (abs_le.mp herr).2
  have hfirstBound : eps/m*(2*a*q)≤delta*tau*a*q := by
    calc
      _ = 2*eps*(a*q/m) := by ring
      _ ≤ rent0*tau*(a*q/m) := hfirst'
      _ = rent0/m*(tau*a*q) := by ring
      _ ≤ delta*(tau*a*q) := hδfirst
      _ = _ := by ring
  have hsecondBound : err≤delta*tau*a*q := by
    calc
      _ ≤ E*q := herr'
      _ ≤ rent0*a0*tau*q := hsecond'
      _ = rent0*a0*(tau*q) := by ring
      _ ≤ delta*a*(tau*q) := hδsecond
      _ = _ := by ring
  linarith only [hterm,hterm',hfirstBound,hsecondBound]

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem rank_hasDerivAt_zero_off_support (Γ : FiniteGame m 2 c Seed) (t : ℝ)
    [NullSingletonClass (lowerBidMeasure Γ t)] {b : ℝ}
    (hb : b∉(lowerBidMeasure Γ t).support) : HasDerivAt (rank Γ t) 0 b := by
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp
    (Measure.isClosed_support.isOpen_compl.mem_nhds hb)
  apply rank_hasDerivAt_zero_on_gap Γ t (x := b-d) (y := b+d)
    ⟨by linarith,by linarith⟩
  intro z hz
  apply hball
  rw [Metric.mem_ball,Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith [hz.1],by linarith [hz.2]⟩

theorem actual_marginal_derivative_residual_identity
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (B : CanonicalEvent Γ) {t b : ℝ}
    (hb : 0< b)
    (hcomp : HasDerivAt (comparisonMarginal Γ i B t) (deriv (comparisonMarginal Γ i B t) b) b)
    (hR : HasDerivAt (canonicalDuplicate Γ i B) (deriv (canonicalDuplicate Γ i B) b) b)
    (hS : HasDerivAt (success Γ i) (deriv (success Γ i) b) b)
    (hD : HasDerivAt (duplicate Γ i) (deriv (duplicate Γ i) b) b) :
    deriv (q Γ i) b=deriv (comparisonMarginal Γ i B t) b+
      (deriv (successError Γ i B t) b+deriv (duplicateError Γ i B) b)/2 := by
  have hqa := actual_marginal_hasDerivAt Γ i hb hS hD
  have hs := hS.sub ((hcomp.const_mul 2).sub hR)
  have hd := hD.sub hR
  change HasDerivAt (successError Γ i B t) _ b at hs
  change HasDerivAt (duplicateError Γ i B) _ b at hd
  rw [hqa.deriv,hs.deriv,hd.deriv]
  ring

variable {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
  {B : CanonicalEvent Γ} {L R U : ℝ}
  {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U}
  {A : ℝ→ℝ} {Amin Amax Rmax Dmax e19 e ell : ℝ}
variable (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell)
include E

theorem RemoteKernels06.safe_rent
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax) (hsize : Dmax/(m:ℝ)≤ Amin/2)
    {b eps rent0 : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b)
    (hbudget : rent0+eps+
      U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax e19 m≤ 1/Amax)
    (hbarrier : finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b-eps/(m:ℝ)≤
      rank Γ (Uniform07.cutoff row) b-b) :
    rent0/(m:ℝ)≤ rank Γ (Uniform07.cutoff row) b-b := by
  have hU23 := (E.U23 hm hAmin he19 he19Small hRmax hDmax hsize hb G).2
  have hlead := (U23_leading_bounds (source_eta_mem row).1 (source_xi_pos row)
    (E.share_bounds hb) hAmin (E.rateBounds b hb)).1
  have hscaled := mul_le_mul_of_nonneg_left hbarrier hm.le
  have hid : (m:ℝ)*(eps/(m:ℝ))=eps := by field_simp [hm.ne']
  apply (div_le_iff₀ hm).2
  nlinarith [(abs_le.mp hU23).1,hscaled,hid]

theorem actual_global_log_slope_from_used_barrier
    (hm : 1≤(m:ℝ)) (hAmin : 0< Amin) (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax) (hsize : Dmax/(m:ℝ)≤ Amin/2)
    (he : 0≤ e) (he1 : e≤ 1)
    {L' eps rent0 tau nu tolerance : ℝ} (hLL' : L≤ L') (_hL'R : L'≤ R)
    (heps : 0≤ eps) (hrent0 : 0< rent0) (htau : 0≤ tau) (hnu : 0≤ nu)
    (habsorb : 4*e≤ rent0)
    (hrentBudget : rent0+eps+
      U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax e19 m≤ 1/Amax)
    (hfirst : 2*eps≤ rent0*tau)
    (hsecond : 4*(1+(6+Dmax)/rent0)*e≤ rent0*(Amin/2)*tau)
    (hvalueBudget : e≤ nu)
    (hderivativeBudget : e*(1+(6+Dmax)/rent0)≤ nu*(Amin/2)*(m:ℝ))
    (htol : 0≤ 1+tolerance) (htransport : 1+tau+nu≤(1+tolerance)*(1-nu))
    (hbarrier : ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L' R →
      b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b-eps/(m:ℝ)≤
        rank Γ (Uniform07.cutoff row) b-b) :
    ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L' R →
      deriv (q Γ i) b≤(1+tolerance)*canonicalSlope Γ i B b*q Γ i b := by
  letI : NullSingletonClass (lowerBidMeasure Γ (Uniform07.cutoff row)) := P.atomless
  have hm0 : 0<(m:ℝ) := by linarith
  have hflowCoeff : 0≤(6+Dmax)/rent0 := by positivity
  filter_upwards [E.density,E.U22,E.canonicalAE,hbarrier] with b hb hU22 hG hbar hbJ
  have hbI : b∈Icc L R := ⟨hLL'.trans hbJ.1,hbJ.2⟩
  let G := hG hbI
  rcases hb hbI with ⟨hM,hS,hD,_,hse,hde⟩
  have hq := E.comparison_positive hbI
  have ha := E.slope_lower hm0 hAmin he19Small hbI G
  have haPos : 0< canonicalSlope Γ i B b := (mul_pos (by positivity : 0< Amin/2) hm0).trans_le ha
  have hden := E.denominators hm0 hAmin he19Small hsize hbI G
  have hdenPos := hden.1.trans_le hden.2.1
  have hflow0 : 0≤ physicalFlow Γ (Uniform07.cutoff row) b :=
    mul_nonneg (E.pureDerivativePositive b hbI).le (rank_monotone Γ (Uniform07.cutoff row)).deriv_nonneg
  have hcompD := ((E.pureDerivative b hbI).comp b hM).add G.canonicalDerivative
  change HasDerivAt (comparisonMarginal Γ i B (Uniform07.cutoff row))
    (physicalFlow Γ (Uniform07.cutoff row) b+deriv (canonicalMarginal Γ i B) b) b at hcompD
  have hcompID : deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b=
      physicalFlow Γ (Uniform07.cutoff row) b+deriv (canonicalMarginal Γ i B) b := hcompD.deriv
  have hflowAndSlope : physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)≤
      ((6+Dmax)/rent0)*comparisonMarginal Γ i B (Uniform07.cutoff row) b ∧
      deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b≤
        (1+tau)*canonicalSlope Γ i B b*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
    by_cases hbS : b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support
    · have hδ := E.safe_rent hm0 hAmin he19 he19Small hRmax hDmax hsize hbI G hrentBudget (hbar hbJ hbS)
      have hδ0 : 0< rank Γ (Uniform07.cutoff row) b-b := (div_pos hrent0 hm0).trans_le hδ
      have hδrange : rank Γ (Uniform07.cutoff row) b-b∈Icc (0:ℝ) 1 :=
        ⟨hδ0.le,by linarith [(E.rankRange b hbI).2,Uniform07.cutoff_lt_one row,E.bid0.le.trans hbI.1]⟩
      have herr := signed_residual_bound_with_flow (source_eta_mem row)
        ⟨E.bid0.le.trans hbI.1,hbI.2.trans E.bid1⟩ hδrange hq.le hflow0 hm he
        (E.successValueError b hbI) (E.duplicateValueError b hbI) hse hde
      change |signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b|≤
        4*e*(comparisonMarginal Γ i B (Uniform07.cutoff row) b+physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)) at herr
      have hIC := hU22 hbI hbS
      have hIC' : (rank Γ (Uniform07.cutoff row) b-b)*
          (2*physicalFlow Γ (Uniform07.cutoff row) b+
            (2*deriv (canonicalMarginal Γ i B) b-deriv (canonicalDuplicate Γ i B) b))=
          barrierNumerator (Uniform07.eta row) b (comparisonMarginal Γ i B (Uniform07.cutoff row) b)
            (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b)+
            signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b := by nlinarith
      have hf := physical_flow_bound_from_IC hm0 hrent0 hq.le hflow0 hden.1.le hδ he he1 habsorb
        (E.numerator_bounds hDmax hbI G).2 hIC' herr
      have hf' : physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)≤
          ((6+Dmax)/rent0)*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
        simpa only [show (2+Dmax)+4=6+Dmax by ring] using hf
      refine ⟨hf',?_⟩
      apply comparison_safe_slope_from_finite_budgets hm0 (by positivity : 0< Amin/2) hrent0 hq.le ha hδ hdenPos
        G.canonicalDerivativeRatio.1
        (by rw [hcompID]; exact hIC)
        (by
          have hs := hbar hbJ hbS
          change finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b-
            (rank Γ (Uniform07.cutoff row) b-b)≤eps/(m:ℝ)
          linarith only [hs])
        heps (by positivity : 0≤ 4*(1+(6+Dmax)/rent0)*e) htau
        (uniform_residual_after_flow_absorption he hf' herr) hfirst hsecond
    · have hzero := rank_hasDerivAt_zero_off_support Γ (Uniform07.cutoff row) hbS
      have hfzero : physicalFlow Γ (Uniform07.cutoff row) b=0 := by
        unfold physicalFlow
        rw [hzero.deriv,mul_zero]
      refine ⟨by rw [hfzero,zero_div]; positivity,?_⟩
      rw [hcompID,hfzero,zero_add,← E.slope_mul hbI]
      have h₁ := mul_le_mul_of_nonneg_left (E.canonical_le_comparison hbI) haPos.le
      have h₂ := mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)≤ 1+tau)
        (mul_nonneg haPos.le hq.le)
      nlinarith
  have hqvalue := actual_marginal_relative_error
    (qActual := q Γ i b)
    (q := comparisonMarginal Γ i B (Uniform07.cutoff row) b)
    (s := successError Γ i B (Uniform07.cutoff row) b)
    (d := duplicateError Γ i B b) (e := e) (m := (m:ℝ)) hm0
    (actual_marginal_error_identity Γ i B (Uniform07.cutoff row) (E.bid0.le.trans hbI.1))
    (E.successValueError b hbI) (E.duplicateValueError b hbI)
  have hvaluediv : e*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)≤
      nu*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
    apply (div_le_iff₀ hm0).2
    have h₁ := mul_le_mul_of_nonneg_right hvalueBudget hq.le
    have h₂ := mul_le_mul_of_nonneg_left hm (mul_nonneg hnu hq.le)
    nlinarith only [h₁,h₂]
  have hresid : e*(physicalFlow Γ (Uniform07.cutoff row) b/(m:ℝ)+
      comparisonMarginal Γ i B (Uniform07.cutoff row) b)≤
      nu*canonicalSlope Γ i B b*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
    have h₁ := mul_le_mul_of_nonneg_left (add_le_add_right hflowAndSlope.1
      (comparisonMarginal Γ i B (Uniform07.cutoff row) b)) he
    have h₂ := mul_le_mul_of_nonneg_right hderivativeBudget hq.le
    have h₃ := mul_le_mul_of_nonneg_left ha (mul_nonneg hnu hq.le)
    nlinarith only [h₁,h₂,h₃]
  have hderID := actual_marginal_derivative_residual_identity Γ i B (E.bid0.trans_le hbI.1)
    hcompD.differentiableAt.hasDerivAt G.duplicateDerivative hS hD
  have hqder : |deriv (q Γ i) b-deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b|≤
      nu*canonicalSlope Γ i B b*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
    rw [hderID]
    have habs : |deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b+
          (deriv (successError Γ i B (Uniform07.cutoff row)) b+deriv (duplicateError Γ i B) b)/2-
            deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b|=
        |deriv (successError Γ i B (Uniform07.cutoff row)) b+deriv (duplicateError Γ i B) b|/2 := by
      rw [show deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b+
          (deriv (successError Γ i B (Uniform07.cutoff row)) b+deriv (duplicateError Γ i B) b)/2-
            deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) b=
          (deriv (successError Γ i B (Uniform07.cutoff row)) b+deriv (duplicateError Γ i B) b)/2 by ring,
        abs_div]
      norm_num
    rw [habs]
    linarith only [abs_add_le (deriv (successError Γ i B (Uniform07.cutoff row)) b)
      (deriv (duplicateError Γ i B) b),hse.trans hresid,hde.trans hresid]
  exact actual_log_slope_from_comparison haPos.le hq.le htol
    (hqvalue.trans hvaluediv) hqder hflowAndSlope.2 htransport

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
