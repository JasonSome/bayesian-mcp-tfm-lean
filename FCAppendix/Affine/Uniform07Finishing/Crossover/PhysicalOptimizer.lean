import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalSafeSlope

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem finite_uniform_slope_freeze
    {a A : ℝ→ℝ} {m a0 e osc sigma x b : ℝ}
    (hm : 0< m) (_he : 0≤ e) (hsigma : 0≤ sigma)
    (hax : |a x/m-A x|≤ e) (hab : |a b/m-A b|≤ e)
    (hA : |A x-A b|≤ osc) (ha0 : a0*m≤ a b)
    (hsmall : osc+2*e≤ sigma*a0) :
    a x≤(1+sigma)*a b := by
  have h₁ := (abs_le.mp hax).2
  have h₂ := (abs_le.mp hab).1
  have h₃ := (abs_le.mp hA).2
  have hscale : a0≤ a b/m := (le_div_iff₀ hm).2 ha0
  have h₄ := mul_le_mul_of_nonneg_left hscale hsigma
  have hdiv : a x/m≤(1+sigma)*(a b/m) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hdiv hm.le
  simpa only [div_mul_cancel₀ _ hm.ne',mul_assoc] using hmul

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
  {B : CanonicalEvent Γ} {L R U : ℝ}
  {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U}
  {A : ℝ→ℝ} {Amin Amax Rmax Dmax e19 e ell : ℝ}
variable (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell)
include E

theorem RemoteKernels06.actual_marginal_lower
    (hm : 1≤(m:ℝ)) (he : 0≤ e) {b : ℝ} (hb : b∈Icc L R) :
    (1-e)*comparisonMarginal Γ i B (Uniform07.cutoff row) b≤ q Γ i b := by
  have hm0 : 0<(m:ℝ) := by linarith
  have h := actual_marginal_relative_error hm0
    (actual_marginal_error_identity Γ i B (Uniform07.cutoff row) (E.bid0.le.trans hb.1))
    (E.successValueError b hb) (E.duplicateValueError b hb)
  have hsmall : e*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)≤
      e*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
    apply (div_le_iff₀ hm0).2
    nlinarith [mul_nonneg he (E.comparison_positive hb).le]
  linarith [(abs_le.mp h).1]

theorem RemoteKernels06.actual_marginal_positive
    (hm : 1≤(m:ℝ)) (he : 0≤ e) (he1 : e<1) {b : ℝ} (hb : b∈Icc L R) :
    0< q Γ i b :=
  (mul_pos (sub_pos.mpr he1) (E.comparison_positive hb)).trans_le (E.actual_marginal_lower hm he hb)

theorem RemoteKernels06.actual_duplicate_ratio
    (hm : 1≤(m:ℝ)) (he : 0≤ e) (he1 : e<1) (hRmax : 0≤ Rmax)
    {b : ℝ} (hb : b∈Icc L R) :
    duplicate Γ i b/q Γ i b≤(Rmax+e)/((m:ℝ)*(1-e)) := by
  have hm0 : 0<(m:ℝ) := by linarith
  have hq := E.actual_marginal_positive hm he he1 hb
  have hcomp := E.comparison_positive hb
  have hcanon := E.canonicalRatio b hb
  have hcanon' := mul_le_mul_of_nonneg_left (E.canonical_le_comparison hb) hRmax
  have hcanon'' := div_le_div_of_nonneg_right hcanon' hm0.le
  have hres := (abs_le.mp (E.duplicateValueError b hb)).2
  have hD : duplicate Γ i b≤(Rmax+e)*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ) := by
    unfold duplicateError at hres
    have hid : (Rmax+e)*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)=
        Rmax*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)+
          e*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ) := by ring
    rw [hid]
    linarith only [hcanon,hcanon'',hres]
  have hlow := E.actual_marginal_lower hm he hb
  have hratio : 0≤(Rmax+e)/((m:ℝ)*(1-e)) := by positivity
  apply (div_le_iff₀ hq).2
  have hscaled := mul_le_mul_of_nonneg_left hlow hratio
  have hid : ((Rmax+e)/((m:ℝ)*(1-e)))*
      ((1-e)*comparisonMarginal Γ i B (Uniform07.cutoff row) b)=
      (Rmax+e)*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ) := by
    field_simp [hm0.ne',(sub_pos.mpr he1).ne']
  rw [hid] at hscaled
  exact hD.trans hscaled

omit E in
def actualPaymentBudget (eta xi Amax e19 e : ℝ) : ℝ :=
  (2*eta/xi*(1+e19)+eta*e*(Amax+e19))/(1-e)

omit E in

def ReferencePaymentError (Amin e19 : ℝ) : ℝ :=
  (1+e19)*(1+2*e19/Amin)-1

omit E in
theorem referencePaymentError_nonneg {Amin e19 : ℝ}
    (hAmin : 0< Amin) (he19 : 0≤ e19) : 0≤ ReferencePaymentError Amin e19 := by
  have hh : 0≤ 2*e19/Amin := by positivity
  dsimp [ReferencePaymentError]
  nlinarith [mul_nonneg he19 hh]

theorem RemoteKernels06.canonical_reference_payment_at
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    {b : ℝ} (hb : b∈Icc L R) (G : CanonicalAt06 row Γ i B A Dmax e19 b) :
    canonicalDuplicate Γ i B b≤
      2*canonicalMarginal Γ i B b*(1+ReferencePaymentError Amin e19)/
        (Uniform07.xi row*b*referenceSlope m A b) := by
  have hb0 := E.bid0.trans_le hb.1
  have haLow := E.slope_lower hm hAmin he19Small hb G
  have ha : 0< canonicalSlope Γ i B b := (mul_pos (by positivity : 0< Amin/2) hm).trans_le haLow
  have href := E.reference_slope_positive hm hAmin hb
  have hxi := source_xi_pos row
  have hD0 := (E.canonicalDuplicateProbability b hb).1
  let alpha : ℝ := 1+2*e19/Amin
  have halpha0 : 0≤ alpha := by dsimp [alpha]; positivity
  have hterm := mul_le_mul_of_nonneg_left haLow (by positivity : 0≤ 2*e19/Amin)
  have hid : (2*e19/Amin)*((Amin/2)*(m:ℝ))=e19*(m:ℝ) := by
    field_simp [hAmin.ne']
  rw [hid] at hterm
  have hsl : A b-e19≤ canonicalSlope Γ i B b/(m:ℝ) := by
    linarith [(abs_le.mp G.finiteSlope).1]
  have hsl' := (le_div_iff₀ hm).mp hsl
  have hscale : referenceSlope m A b≤ alpha*canonicalSlope Γ i B b := by
    dsimp [referenceSlope,alpha]
    nlinarith
  have hbound := (le_div_iff₀ (by positivity : 0< Uniform07.xi row*b*canonicalSlope Γ i B b)).mp
    G.canonicalPaymentRatio
  have hbound' := mul_le_mul_of_nonneg_right hbound halpha0
  have hscale' := mul_le_mul_of_nonneg_left hscale
    (by positivity : 0≤ canonicalDuplicate Γ i B b*(Uniform07.xi row*b))
  apply (le_div_iff₀ (by positivity : 0< Uniform07.xi row*b*referenceSlope m A b)).2
  have heq : 1+ReferencePaymentError Amin e19=(1+e19)*alpha := by
    dsimp [ReferencePaymentError,alpha]
    ring
  rw [heq]
  nlinarith

theorem RemoteKernels06.canonical_reference_payment
    (hLR : L< R) (hm : 0<(m:ℝ)) (hAmin : 0< Amin)
    (he19 : 0≤ e19) (he19Small : e19≤ Amin/4) :
    ∀ b∈Icc L R, canonicalDuplicate Γ i B b≤
      2*canonicalMarginal Γ i B b*(1+ReferencePaymentError Amin e19)/
        (Uniform07.xi row*b*referenceSlope m A b) := by
  have hC : ContinuousOn (canonicalMarginal Γ i B) (Icc L R) := by
    simpa only [uIcc_of_le E.interval] using E.canonicalAC.continuousOn
  have hD : ContinuousOn (canonicalDuplicate Γ i B) (Icc L R) := by
    simpa only [uIcc_of_le E.interval] using E.canonicalDuplicateAC.continuousOn
  apply continuous_le_on_Icc_of_ae hLR hD
    (((continuousOn_const.mul hC).mul continuousOn_const).div
      ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.mul E.rateContinuous))
      (fun b hb => (mul_pos (mul_pos (source_xi_pos row) (E.bid0.trans_le hb.1))
        (E.reference_slope_positive hm hAmin hb)).ne'))
  filter_upwards [E.canonicalAE] with b hG hb
  exact E.canonical_reference_payment_at hm hAmin he19 he19Small hb (hG hb)

theorem RemoteKernels06.actual_duplicate_budget
    (hLR : L< R) (hm : 1≤(m:ℝ)) (hAmin : 0< Amin)
    (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    (he : 0≤ e) (he1 : e<1) {b : ℝ} (hb : b∈Icc L R) :
    Uniform07.eta row*b*duplicate Γ i b≤
      actualPaymentBudget (Uniform07.eta row) (Uniform07.xi row) Amax
        (ReferencePaymentError Amin e19) e*q Γ i b/referenceSlope m A b := by
  have hm0 : 0<(m:ℝ) := by linarith
  have ha := E.reference_slope_positive hm0 hAmin hb
  have href0 := referencePaymentError_nonneg hAmin he19
  have hscale : referenceSlope m A b/(m:ℝ)≤ Amax+ReferencePaymentError Amin e19 := by
    have hid : referenceSlope m A b/(m:ℝ)=A b := by
      simp [referenceSlope,hm0.ne']
    rw [hid]
    linarith [(E.rateBounds b hb).2]
  have h := actual_duplicate_payment_budget (source_eta_mem row).1 (source_xi_pos row)
    (E.bid0.trans_le hb.1) (hb.2.trans E.bid1) ha hm0 (E.comparison_positive hb).le
    (E.canonical_le_comparison hb) he (by positivity : 0≤ 1+ReferencePaymentError Amin e19)
    (E.canonical_reference_payment hLR hm0 hAmin he19 he19Small b hb)
    (abs_le.mp (E.duplicateValueError b hb)).2 hscale
    (E.actual_marginal_lower hm he hb) he1
  have hid : canonicalDuplicate Γ i B b+duplicateError Γ i B b=duplicate Γ i b := by
    unfold duplicateError
    ring
  rw [hid] at h
  exact h

theorem literal_crossover_optimizer_from_safe_slope
    (hm : 1≤(m:ℝ)) (hAmin : 0< Amin) (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    (hRmax : 0≤ Rmax) (he : 0≤ e) (he1 : e<1)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {L' epsilon v : ℝ} (hLL' : L≤ L')
    (hepsilon : 0< epsilon) (hepsilon1 : epsilon<1)
    (a : JointAction 2) (haroute : a.routeCount=1)
    (habid : a.bid∈Icc L' R) (hav : a.bid≤ v)
    (hopt : ∀ a' : JointAction 2, a'.routeCount=1 → a'.bid≤ U →
      (problem Γ i).payoff v a'≤(problem Γ i).payoff v a)
    (hstep : L'≤ a.bid-(epsilon/4)/referenceSlope m A a.bid)
    (hfreeze : ∀ z∈Icc (a.bid-(epsilon/4)/referenceSlope m A a.bid) a.bid,
      referenceSlope m A z≤(1+epsilon/16)*referenceSlope m A a.bid)
    (hslope : ∀ᵐ z ∂(volume : Measure ℝ), z∈Icc L' R →
      deriv (q Γ i) z≤(1+epsilon/16)*referenceSlope m A z*q Γ i z)
    (hmargin : 0<(1-epsilon)*(1-(Rmax+e)/((m:ℝ)*(1-e)))-
      actualPaymentBudget (Uniform07.eta row) (Uniform07.xi row) Amax (ReferencePaymentError Amin e19) e) :
    (problem Γ i).payoff v a<(problem Γ i).payoff v (LowBody.addSecondRoute a) := by
  have hm0 : 0<(m:ℝ) := by linarith
  have hbI : a.bid∈Icc L R := ⟨hLL'.trans habid.1,habid.2⟩
  have haPos := E.reference_slope_positive hm0 hAmin hbI
  have hstepPos : 0<(epsilon/4)/referenceSlope m A a.bid := by positivity
  have hleftI : a.bid-(epsilon/4)/referenceSlope m A a.bid∈Icc L R :=
    ⟨hLL'.trans hstep,by linarith [habid.2]⟩
  have hleft0 : 0≤ a.bid-(epsilon/4)/referenceSlope m A a.bid := E.bid0.le.trans hleftI.1
  have hscalar := raw_singleton_optimum_scalar_below Γ hg i v U a haroute hopt
  have hoptScalar := hscalar _ ⟨hleft0,hleftI.2.trans E.feasible⟩
  have hAC := actual_marginal_ac Γ i
    (by rw [min_eq_left E.interval]; exact E.bid0.le) E.successAC E.duplicateAC
  have hsub : uIcc (a.bid-(epsilon/4)/referenceSlope m A a.bid) a.bid ⊆ uIcc L R := by
    rw [uIcc_of_le (by linarith : a.bid-(epsilon/4)/referenceSlope m A a.bid≤ a.bid),uIcc_of_le E.interval]
    exact fun z hz => ⟨hleftI.1.trans hz.1,hz.2.trans habid.2⟩
  have hslope' : ∀ᵐ z ∂(volume : Measure ℝ),
      z∈Icc (a.bid-(epsilon/4)/referenceSlope m A a.bid) a.bid →
      deriv (q Γ i) z≤((1+epsilon/4)*referenceSlope m A a.bid)*q Γ i z := by
    filter_upwards [hslope] with z hz hzI
    have hzJ : z∈Icc L' R := ⟨hstep.trans hzI.1,hzI.2.trans habid.2⟩
    have hq0 := q_nonneg Γ i z
    have hfr := mul_le_mul_of_nonneg_right (hfreeze z hzI) hq0
    have hfr' := mul_le_mul_of_nonneg_left hfr (by positivity : 0≤ 1+epsilon/16)
    have hcoef : (1+epsilon/16)*(1+epsilon/16)≤ 1+epsilon/4 := by
      nlinarith [mul_nonneg hepsilon.le (sub_nonneg.mpr hepsilon1.le)]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (mul_nonneg haPos.le hq0)
    nlinarith [hz hzJ]
  have hrent := singleton_relative_rent_of_integrated_slope haPos hepsilon hepsilon1 hav
    (E.actual_marginal_positive hm he he1 hleftI) hoptScalar (hAC.mono hsub) hslope'
  have hq := E.actual_marginal_positive hm he he1 hbI
  have hLR : L< R := by linarith [hstep,hstepPos,habid.2]
  have hdup := E.actual_duplicate_budget hLR hm hAmin he19 he19Small he he1 hbI
  have hratio := E.actual_duplicate_ratio hm he he1 hRmax hbI
  have hmargin' : 0<(1-epsilon)*(1-duplicate Γ i a.bid/q Γ i a.bid)-
      actualPaymentBudget (Uniform07.eta row) (Uniform07.xi row) Amax (ReferencePaymentError Amin e19) e := by
    have h := mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr hepsilon1.le)
    nlinarith
  have hgain := strict_route_gap_from_relative_rent haPos hq (duplicate_nonneg Γ i a.bid)
    (duplicate_le_q Γ i a.bid_nonneg) hepsilon1.le hrent hdup hmargin'
  have hone := one_payoff Γ hg i v a.bid_nonneg
  have htwo := two_payoff Γ (source_eta_mem row).1 (source_eta_mem row).2 hA hg i v a.bid_nonneg
  have hraw := raw_one_eq a haroute
  have hroute : LowBody.addSecondRoute a=two a.bid := by
    simpa only [LowBody.addSecondRoute] using raw_two_eq (LowBody.addSecondRoute a) rfl
  rw [hroute,htwo]
  calc
    (problem Γ i).payoff v a = utilityOne v a.bid (q Γ i a.bid) := by
      simpa only [← hraw] using hone
    _ < _ := hgain

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
