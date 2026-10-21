import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalDrift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem split_errors_to_uniform_budget
    {m q flow eS eD s d s' d' : ℝ}
    (hm : 0< m) (hq : 0≤ q) (hflow : 0≤ flow) (hS : 0≤ eS) (hD : 0≤ eD)
    (hs : |s|≤ eS*q) (hd : |d|≤ eD*q/m)
    (hs' : |s'|≤ eS*flow+eD*(flow/m+q))
    (hd' : |d'|≤ eD*(flow/m+q)) :
    |s|≤(m*eS+eD)*q/m ∧ |d|≤(m*eS+eD)*q/m ∧
    |s'|≤(m*eS+eD)*(flow/m+q) ∧
    |d'|≤(m*eS+eD)*(flow/m+q) := by
  have heD : eD≤ m*eS+eD := by nlinarith [mul_nonneg hm.le hS]
  have hidValue : (m*eS+eD)*q/m=eS*q+eD*q/m := by
    field_simp [hm.ne']
  have hidDerivative : (m*eS+eD)*(flow/m+q)=
      eS*flow+eD*(flow/m+q)+m*eS*q := by
    field_simp [hm.ne']
    ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [hidValue]
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · exact hd.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right heD hq) hm.le)
  · rw [hidDerivative]
    exact hs'.trans (le_add_of_nonneg_right (by positivity))
  · exact hd'.trans (mul_le_mul_of_nonneg_right heD (by positivity))

theorem split_signed_residual_bound
    {eta b delta q flow m eS eD s d s' d' : ℝ}
    (heta : eta∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1)
    (hdelta : delta∈Icc (0:ℝ) 1) (hq : 0≤ q) (hflow : 0≤ flow)
    (hm : 1≤ m) (_heS : 0≤ eS) (heD : 0≤ eD)
    (hs : |s|≤ eS*q) (hd : |d|≤ eD*q/m)
    (hs' : |s'|≤ eS*flow+eD*(flow/m+q))
    (hd' : |d'|≤ eD*(flow/m+q)) :
    |s+eta*d+eta*b*d'-delta*s'|≤
      (eS+3*eD)*q+2*eD*(flow/m)+eS*(delta*flow) := by
  have hm0 : 0< m := by linarith
  have hflowm : 0≤ flow/m := div_nonneg hflow hm0.le
  have hdscale : eD*q/m≤ eD*q := (div_le_iff₀ hm0).2 (by nlinarith [mul_nonneg heD hq])
  have hηb : 0≤ eta*b ∧ eta*b≤ 1 := by
    constructor
    · exact mul_nonneg heta.1 hb.1
    · calc
        eta*b ≤ 1*b := mul_le_mul_of_nonneg_right heta.2 hb.1
        _ = b := one_mul b
        _ ≤ 1 := hb.2
  have hD : |eta*d|≤ eD*q := by
    rw [abs_mul,abs_of_nonneg heta.1]
    have h₁ := mul_le_mul_of_nonneg_left (hd.trans hdscale) heta.1
    have h₂ := mul_le_mul_of_nonneg_right heta.2 (mul_nonneg heD hq)
    nlinarith
  have hD' : |eta*b*d'|≤ eD*(flow/m+q) := by
    rw [abs_mul,abs_of_nonneg hηb.1]
    have h₁ := mul_le_mul_of_nonneg_left hd' hηb.1
    have h₂ := mul_le_mul_of_nonneg_right hηb.2 (by positivity : 0≤ eD*(flow/m+q))
    nlinarith
  have hS' : |delta*s'|≤ eS*(delta*flow)+eD*(flow/m+q) := by
    rw [abs_mul,abs_of_nonneg hdelta.1]
    have h₁ := mul_le_mul_of_nonneg_left hs' hdelta.1
    have h₂ := mul_le_mul_of_nonneg_right hdelta.2 (by positivity : 0≤ eD*(flow/m+q))
    nlinarith
  have h₁ := abs_add_le s (eta*d)
  have h₂ := abs_add_le (s+eta*d) (eta*b*d')
  have h₃ := abs_sub (s+eta*d+eta*b*d') (delta*s')
  nlinarith

theorem split_IC_absorption
    {delta flow canonicalDen N err q m rent Nmax eS eD : ℝ}
    (hm : 0< m) (hrent : 0< rent) (hq : 0≤ q) (hflow : 0≤ flow)
    (hcanon : 0≤ canonicalDen) (hdelta : rent/m≤ delta)
    (heS : eS∈Icc (0:ℝ) 1) (heD : eD∈Icc (0:ℝ) 1)
    (hsmall : eS+2*eD/rent≤ 1)
    (hN : N≤ Nmax*q) (hIC : delta*(2*flow+canonicalDen)=N+err)
    (herr : |err|≤(eS+3*eD)*q+2*eD*(flow/m)+eS*(delta*flow)) :
    delta*flow≤(Nmax+4)*q ∧
    |err|≤(eS+3*eD+(eS+2*eD/rent)*(Nmax+4))*q := by
  have hδ0 : 0≤ delta := (div_pos hrent hm).le.trans hdelta
  have hδflow : 0≤ delta*flow := mul_nonneg hδ0 hflow
  have hflowRent : flow/m≤ delta*flow/rent := by
    apply (le_div_iff₀ hrent).2
    calc
      flow/m*rent = (rent/m)*flow := by ring
      _ ≤ delta*flow := mul_le_mul_of_nonneg_right hdelta hflow
  have herror : |err|≤(eS+3*eD)*q+(eS+2*eD/rent)*(delta*flow) := by
    have h := mul_le_mul_of_nonneg_left hflowRent
      (mul_nonneg (by norm_num : (0:ℝ)≤2) heD.1)
    have hid : 2*eD*(delta*flow/rent)=(2*eD/rent)*(delta*flow) := by ring
    nlinarith only [herr,h,hid]
  have hlow : 2*(delta*flow)≤ N+err := by
    nlinarith [mul_nonneg hδ0 hcanon]
  have hsmall' := mul_le_mul_of_nonneg_right hsmall hδflow
  have hrel : delta*flow≤(Nmax+eS+3*eD)*q := by
    nlinarith [(abs_le.mp herror).2]
  have hcoef : Nmax+eS+3*eD≤ Nmax+4 := by linarith [heS.2,heD.2]
  have hbound := hrel.trans (mul_le_mul_of_nonneg_right hcoef hq)
  refine ⟨hbound,?_⟩
  have hnorm : 0≤ eS+2*eD/rent := by have hS0 := heS.1; have hD0 := heD.1; positivity
  have h := mul_le_mul_of_nonneg_left hbound hnorm
  nlinarith

theorem split_absorbed_error_tendsto_zero
    {eS eD rent : ℕ→ℝ} {Nmax : ℝ}
    (hS : Tendsto eS atTop (𝓝 0)) (hD : Tendsto eD atTop (𝓝 0))
    (hDrent : Tendsto (fun m => eD m/rent m) atTop (𝓝 0)) :
    Tendsto (fun m => eS m+3*eD m+(eS m+2*eD m/rent m)*(Nmax+4)) atTop (𝓝 0) := by
  have h := (hS.add (hD.const_mul 3)).add ((hS.add (hDrent.const_mul 2)).mul_const (Nmax+4))
  convert h using 1 <;> try ring
  ext m
  ring

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

structure PureDerivativeBounds06 (Γ : FiniteGame m 2 c Seed) (i : Fin m)
    (B : CanonicalEvent Γ) (t L R eS eD : ℝ) where
  successValue : ∀ b∈Icc L R,
    |successError Γ i B t b|≤ eS*comparisonMarginal Γ i B t b
  duplicateValue : ∀ b∈Icc L R,
    |duplicateError Γ i B b|≤ eD*comparisonMarginal Γ i B t b/(m:ℝ)
  derivatives : ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
    |deriv (successError Γ i B t) b|≤ eS*physicalFlow Γ t b+
      eD*(physicalFlow Γ t b/(m:ℝ)+comparisonMarginal Γ i B t b) ∧
    |deriv (duplicateError Γ i B) b|≤
      eD*(physicalFlow Γ t b/(m:ℝ)+comparisonMarginal Γ i B t b)

def PureDerivativeBounds06.toRemoteKernels06
    {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
    {B : CanonicalEvent Γ} {L R U : ℝ}
    {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U} {A : ℝ→ℝ}
    {Amin Amax Rmax Dmax e19 ell eS eD : ℝ}
    (Y : RemoteCore06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 ell)
    (X : PureDerivativeBounds06 Γ i B (Uniform07.cutoff row) L R eS eD)
    (hm : 0<(m:ℝ)) (hS : 0≤ eS) (hD : 0≤ eD) :
    RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19
      ((m:ℝ)*eS+eD) ell where
  toRemoteCore06 := Y
  successValueError := by
    intro b hb
    have hq : 0≤ comparisonMarginal Γ i B (Uniform07.cutoff row) b :=
      (add_pos (Y.purePositive b hb) (Y.canonicalPositive b hb)).le
    have hid : ((m:ℝ)*eS+eD)*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ)=
        eS*comparisonMarginal Γ i B (Uniform07.cutoff row) b+
        eD*comparisonMarginal Γ i B (Uniform07.cutoff row) b/(m:ℝ) := by
      field_simp [hm.ne']
    rw [hid]
    exact (X.successValue b hb).trans (le_add_of_nonneg_right (by positivity))
  duplicateValueError := by
    intro b hb
    have hq : 0≤ comparisonMarginal Γ i B (Uniform07.cutoff row) b :=
      (add_pos (Y.purePositive b hb) (Y.canonicalPositive b hb)).le
    have hbudget : eD≤(m:ℝ)*eS+eD := by nlinarith [mul_nonneg hm.le hS]
    exact (X.duplicateValue b hb).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget hq) hm.le)
  derivativeErrors := by
    filter_upwards [X.derivatives] with b hb hbI
    have hq : 0≤ comparisonMarginal Γ i B (Uniform07.cutoff row) b :=
      (add_pos (Y.purePositive b hbI) (Y.canonicalPositive b hbI)).le
    have hflow : 0≤ physicalFlow Γ (Uniform07.cutoff row) b :=
      mul_nonneg (Y.pureDerivativePositive b hbI).le
        (rank_monotone Γ (Uniform07.cutoff row)).deriv_nonneg
    exact (split_errors_to_uniform_budget hm hq hflow hS hD
      (X.successValue b hbI) (X.duplicateValue b hbI) (hb hbI).1 (hb hbI).2).2.2

theorem unified_error_tendsto_zero
    {market : ℕ→ℕ} {eS eD : ℕ→ℝ}
    (hS : Tendsto (fun k => (market k:ℝ)*eS k) atTop (𝓝 0))
    (hD : Tendsto eD atTop (𝓝 0)) :
    Tendsto (fun k => (market k:ℝ)*eS k+eD k) atTop (𝓝 0) := by
  simpa only [add_zero] using hS.add hD

theorem weighted_success_error_tendsto_of_chernoff
    {market : ℕ→ℕ} {eS : ℕ→ℝ} {K gamma : ℝ}
    (hmarket : Tendsto market atTop atTop) (hgamma : 0< gamma)
    (hbound : ∀ᶠ k in atTop,
      0≤ eS k ∧ eS k≤ K*Real.exp (-gamma*(market k:ℝ))) :
    Tendsto (fun k => (market k:ℝ)*eS k) atTop (𝓝 0) := by
  have hm : Tendsto (fun k => (market k:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmarket
  have hexp : Tendsto (fun k => (market k:ℝ)*Real.exp (-gamma*(market k:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) gamma hgamma).comp hm
  have hupper : Tendsto (fun k => K*((market k:ℝ)*Real.exp (-gamma*(market k:ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hexp.const_mul K
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [hbound] with k hk
    exact mul_nonneg (Nat.cast_nonneg _) hk.1
  · filter_upwards [hbound] with k hk
    simpa only [mul_left_comm (market k:ℝ) K] using
      mul_le_mul_of_nonneg_left hk.2 (Nat.cast_nonneg (market k) : (0:ℝ)≤ market k)

variable {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
  {B : CanonicalEvent Γ} {L R U : ℝ}
  {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U}
  {A : ℝ→ℝ} {Amin Amax Rmax Dmax e19 e ell eS eD : ℝ}
variable (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell)
variable (X : PureDerivativeBounds06 Γ i B (Uniform07.cutoff row) L R eS eD)
include E X

theorem RemoteKernels06.source_signed_residual
    (hm : 1≤(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4)
    (hDmax : 0≤ Dmax) (hsize : Dmax/(m:ℝ)≤ Amin/2)
    (he : 0≤ e) (he1 : e<1) (hell : 0< ell)
    (heS : eS∈Icc (0:ℝ) 1) (heD : eD∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) (hsmall : eS+2*eD/((m:ℝ)*L*ell/2)≤ 1) :
    ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
      b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      |signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b|≤
        (eS+3*eD+(eS+2*eD/((m:ℝ)*L*ell/2))*(6+Dmax))*
          comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
  have hm0 : 0<(m:ℝ) := by linarith
  have hrent0 : 0<(m:ℝ)*L*ell/2 := by have hL := E.bid0; positivity
  filter_upwards [E.U22,X.derivatives,E.canonicalAE] with b hIC hX hG hb hbS
  let G := hG hb
  have hδ := E.actual_rent hm he he1 hell hA hg hb hbS
  have hδrange : rank Γ (Uniform07.cutoff row) b-b∈Icc (0:ℝ) 1 := by
    constructor
    · exact (by have hL := E.bid0; positivity : 0≤ L*ell/2).trans hδ.1
    · linarith [(E.rankRange b hb).2,Uniform07.cutoff_lt_one row,E.bid0.le.trans hb.1]
  have hflow : 0≤ physicalFlow Γ (Uniform07.cutoff row) b :=
    mul_nonneg (E.pureDerivativePositive b hb).le (rank_monotone Γ (Uniform07.cutoff row)).deriv_nonneg
  have hq := E.comparison_positive hb
  have hraw := split_signed_residual_bound (source_eta_mem row)
    ⟨E.bid0.le.trans hb.1,hb.2.trans E.bid1⟩ hδrange hq.le hflow hm heS.1 heD.1
    (X.successValue b hb) (X.duplicateValue b hb) (hX hb).1 (hX hb).2
  have hδscale : ((m:ℝ)*L*ell/2)/(m:ℝ)≤ rank Γ (Uniform07.cutoff row) b-b := by
    have hid : ((m:ℝ)*L*ell/2)/(m:ℝ)=L*ell/2 := by
      field_simp [hm0.ne']
    rw [hid]
    exact hδ.1
  have hcanon := (E.denominators hm0 hAmin he19 hsize hb G).1.le
  have hDq : canonicalDuplicate Γ i B b∈Icc (0:ℝ) (comparisonMarginal Γ i B (Uniform07.cutoff row) b) :=
    ⟨(E.canonicalDuplicateProbability b hb).1,
      (E.canonicalDuplicateProbability b hb).2.trans (E.canonical_le_comparison hb)⟩
  have hD'q : deriv (canonicalDuplicate Γ i B) b∈Icc (0:ℝ)
      (Dmax*comparisonMarginal Γ i B (Uniform07.cutoff row) b) :=
    ⟨G.canonicalDerivativeRatio.1,G.canonicalDerivativeRatio.2.trans
      (mul_le_mul_of_nonneg_left (E.canonical_le_comparison hb) hDmax)⟩
  have hN := (physical_barrier_numerator_bounds (source_eta_mem row)
    ⟨E.bid0.le.trans hb.1,hb.2.trans E.bid1⟩ hq.le hDq hD'q).2
  have hIC' : (rank Γ (Uniform07.cutoff row) b-b)*
      (2*physicalFlow Γ (Uniform07.cutoff row) b+
        (2*deriv (canonicalMarginal Γ i B) b-deriv (canonicalDuplicate Γ i B) b))=
      barrierNumerator (Uniform07.eta row) b (comparisonMarginal Γ i B (Uniform07.cutoff row) b)
        (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b)+
        signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b := by
    nlinarith [hIC hb hbS]
  have h := (split_IC_absorption hm0 hrent0 hq.le hflow hcanon hδscale heS heD hsmall hN hIC' hraw).2
  simpa only [show (2+Dmax)+4=6+Dmax by ring] using h

theorem RemoteKernels06.below_barrier_drift_split
    (hm : 1≤(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4) (he19Rate : e19≤ 1/10000)
    (hDmax : 0≤ Dmax) (hsize : Dmax/(m:ℝ)≤ Amin/2)
    (he : 0≤ e) (he1 : e<1) (hell : 0< ell)
    (heS : eS∈Icc (0:ℝ) 1) (heD : eD∈Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {eps : ℝ} (heps : 0< eps)
    (hsmall : eS+2*eD/((m:ℝ)*L*ell/2)≤ 1)
    (herror : eS+3*eD+(eS+2*eD/((m:ℝ)*L*ell/2))*(6+Dmax)≤ eps*(Amin/2)/4) :
    ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
      b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      rank Γ (Uniform07.cutoff row) b-b-
        finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b≤-eps/(2*(m:ℝ)) →
      (1/4:ℝ)≤ deriv (fun z => rank Γ (Uniform07.cutoff row) z-z) b ∧
        deriv (canonicalShare Γ i B (Uniform07.cutoff row)) b≤ 0 := by
  have hm0 : 0<(m:ℝ) := by linarith
  filter_upwards [E.density,E.U22,E.source_signed_residual X hm hAmin he19 hDmax hsize he he1 hell heS heD hA hg hsmall,E.canonicalAE]
    with b hb hIC herr hG hbI hbS hbelow
  let G := hG hbI
  have hM := (hb hbI).1
  have hδ := E.actual_rent hm he he1 hell hA hg hbI hbS
  have hδpos : 0< rank Γ (Uniform07.cutoff row) b-b :=
    (by have hL := E.bid0; positivity : 0< L*ell/2).trans_le hδ.1
  have hden := E.denominators hm0 hAmin he19 hsize hbI G
  have hdenPos := hden.1.trans_le hden.2.1
  have hbudget := relative_residual_implies_band_budget
    (errorCoefficient := eS+3*eD+(eS+2*eD/((m:ℝ)*L*ell/2))*(6+Dmax)) (e := 1)
    hm0 heps (E.comparison_positive hbI).le hden.2.2
    (by simpa only [mul_one] using herr hbI hbS) (by simpa only [mul_one] using herror)
  have hstrict := negative_band_error_budget
    (T := finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b)
    (delta := rank Γ (Uniform07.cutoff row) b-b)
    (err := signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b)
    hdenPos heps hm0 (by
      rw [neg_div] at hbelow
      linarith only [hbelow]) hbudget
  have hrate := finite_physical_rate_separation_from_source row (E.sourceInterval hbI)
    (E.sourceDerivative b hbI) hm0 (E.purePositive b hbI)
    (G.finiteSlope.trans he19Rate) (E.pureDerivativeUpper b hbI)
  have hCmul := E.slope_mul hbI
  have hsign := negative_band_derivative_signs hδpos (E.purePositive b hbI)
    (E.canonicalPositive b hbI) (E.pureDerivativePositive b hbI) hdenPos
    (by simpa only [physicalFlow,comparisonMarginal,← hCmul] using hIC hbI hbS) hstrict hrate
  have hdeltaDer := hM.sub (hasDerivAt_id b)
  have hqDer := ((E.pureDerivative b hbI).comp b hM).add G.canonicalDerivative
  have hshareDer := G.canonicalDerivative.div hqDer (E.comparison_positive hbI).ne'
  constructor
  · have hdeltaEq := hdeltaDer.deriv
    change deriv (fun z => rank Γ (Uniform07.cutoff row) z-z) b =
      deriv (rank Γ (Uniform07.cutoff row)) b-1 at hdeltaEq
    rw [hdeltaEq]
    linarith [hsign.1]
  · change deriv (fun z => canonicalMarginal Γ i B z/comparisonMarginal Γ i B (Uniform07.cutoff row) z) b≤ 0
    have hshareEq := hshareDer.deriv
    change deriv (fun z => canonicalMarginal Γ i B z/comparisonMarginal Γ i B (Uniform07.cutoff row) z) b = _ at hshareEq
    dsimp only [Pi.add_apply,Function.comp_apply] at hshareEq
    rw [hshareEq,← hCmul]
    exact hsign.2.le

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
