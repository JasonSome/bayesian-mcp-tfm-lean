import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalWindow

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

theorem source_eta_mem (row : Uniform07.Row) : Uniform07.eta row∈Icc (0:ℝ) 1 := by
  cases row <;> norm_num [Uniform07.eta,Uniform07.etaQ]

theorem source_xi_pos (row : Uniform07.Row) : 0< Uniform07.xi row :=
  Uniform07.xi_pos row

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
  {B : CanonicalEvent Γ} {L R U : ℝ}
  {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U}
  {A : ℝ→ℝ} {Amin Amax Rmax Dmax e19 e ell : ℝ}
variable (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell)
include E

theorem RemoteKernels06.comparison_positive {b : ℝ} (hb : b∈Icc L R) :
    0< comparisonMarginal Γ i B (Uniform07.cutoff row) b :=
  add_pos (E.purePositive b hb) (E.canonicalPositive b hb)

theorem RemoteKernels06.share_bounds {b : ℝ} (hb : b∈Icc L R) :
    canonicalShare Γ i B (Uniform07.cutoff row) b∈Icc (0:ℝ) 1 :=
  (canonical_share_bounds (E.purePositive b hb).le (E.canonicalPositive b hb)).2

theorem RemoteKernels06.canonical_le_comparison {b : ℝ} (hb : b∈Icc L R) :
    canonicalMarginal Γ i B b≤ comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
  change canonicalMarginal Γ i B b≤
    pureRank m c (Uniform07.cutoff row) (rank Γ (Uniform07.cutoff row) b)+canonicalMarginal Γ i B b
  linarith [E.purePositive b hb]

theorem RemoteKernels06.slope_mul {b : ℝ} (hb : b∈Icc L R) :
    canonicalSlope Γ i B b*canonicalMarginal Γ i B b=deriv (canonicalMarginal Γ i B) b :=
  div_mul_cancel₀ _ (E.canonicalPositive b hb).ne'

theorem RemoteKernels06.slope_lower
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4)
    {b : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b) :
    (Amin/2)*(m:ℝ)≤ canonicalSlope Γ i B b := by
  have he := (abs_le.mp G.finiteSlope).1
  have hA := (E.rateBounds b hb).1
  apply (le_div_iff₀ hm).mp
  linarith

theorem RemoteKernels06.denominators
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4)
    (hsize : Dmax/(m:ℝ)≤ Amin/2) {b : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b) :
    0<2*deriv (canonicalMarginal Γ i B) b-deriv (canonicalDuplicate Γ i B) b ∧
    2*deriv (canonicalMarginal Γ i B) b-deriv (canonicalDuplicate Γ i B) b≤
      barrierDenominator (canonicalSlope Γ i B b)
        (comparisonMarginal Γ i B (Uniform07.cutoff row) b) (deriv (canonicalDuplicate Γ i B) b) ∧
    (Amin/2)*(m:ℝ)*comparisonMarginal Γ i B (Uniform07.cutoff row) b≤
      barrierDenominator (canonicalSlope Γ i B b)
        (comparisonMarginal Γ i B (Uniform07.cutoff row) b) (deriv (canonicalDuplicate Γ i B) b) := by
  have h := U19_denominator_order hm (by positivity : 0< Amin/2)
    (E.purePositive b hb).le (E.canonicalPositive b hb)
    (E.slope_lower hm hAmin he19 hb G) G.canonicalDerivativeRatio.2
    ((div_le_iff₀ hm).mp hsize)
  rw [mul_assoc (2:ℝ) (canonicalSlope Γ i B b) (canonicalMarginal Γ i B b),
    E.slope_mul hb] at h
  simpa only [comparisonMarginal] using h

theorem RemoteKernels06.common_boundary_IC {b : ℝ} (hb : b∈Icc L R)
    (hbS : b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support) :
    ∀ z∈Icc (0:ℝ) U, (problem Γ i).payoff (rank Γ (Uniform07.cutoff row) b) (two z)≤
      (problem Γ i).payoff (rank Γ (Uniform07.cutoff row) b) (two b) := by
  let b' : Icc (0:ℝ) U := ⟨b,⟨E.bid0.le.trans hb.1,hb.2.trans E.feasible⟩⟩
  have hh := actual_common_boundary_broadcast_IC_local_at Γ U
    (P.lower : Measure (ℝ × Icc (0:ℝ) U))
    (fun x : Icc (0:ℝ) U => rank Γ (Uniform07.cutoff row) x.1)
    (P.rankContinuous.comp continuous_subtype_val) E.remote E.remoteOpen E.sorted
    P.broadcastIC (P.support_adapter hbS) (E.remoteContains b hb)
    (fun j => P.payoffContinuous j (rank Γ (Uniform07.cutoff row) b,b') (E.bid0.trans_le hb.1))
  intro z hz
  simpa only [sourceLowerBroadcastAction_eq_two] using hh i (⟨z,hz⟩ : Icc (0:ℝ) U)

theorem RemoteKernels06.actual_rent
    (hm : 1≤(m:ℝ)) (he : 0≤ e) (he1 : e<1) (hell : 0< ell)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {b : ℝ} (hb : b∈Icc L R)
    (hbS : b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support) :
    L*ell/2≤ rank Γ (Uniform07.cutoff row) b-b ∧
      b≤ rank Γ (Uniform07.cutoff row) b := by
  have hM := E.rankRange b hb
  have hS := actual_success_positive_of_relative_error Γ i B hm he he1
    (E.comparison_positive hb)
    ((E.canonicalDuplicateProbability b hb).2.trans (E.canonical_le_comparison hb))
    (E.successValueError b hb)
  have hb0 : 0< b := E.bid0.trans_le hb.1
  have hzero : (0:ℝ)∈Icc (0:ℝ) U :=
    ⟨le_refl 0,hb0.le.trans (hb.2.trans E.feasible)⟩
  have hbM := actual_bid_le_value_of_zero_bid_IC Γ i (source_eta_mem row) hA hg
    hM.1 hb0.le hS (E.common_boundary_IC hb hbS 0 hzero)
  have hMpositive : rank Γ (Uniform07.cutoff row) b∈Ioc (0:ℝ) (Uniform07.cutoff row) :=
    ⟨hb0.trans_le hbM,hM.2⟩
  have hhalf : rank Γ (Uniform07.cutoff row) b/2∈Icc (0:ℝ) U :=
    ⟨div_nonneg hM.1 (by norm_num),
      (div_le_div_of_nonneg_right hM.2 (by norm_num : (0:ℝ)≤ 2)).trans E.halfFeasible⟩
  have h := actual_rent_lower_of_half_value_IC Γ i (source_eta_mem row) hA hg hM.1
    (E.bid0.le.trans hb.1) hell (E.halfValueAcceptance _ hMpositive)
    (E.halfValueDuplicate _ hMpositive)
    hS (E.common_boundary_IC hb hbS _ hhalf)
  have hL := mul_le_mul_of_nonneg_right hb.1 (by positivity : 0≤ ell/2)
  exact ⟨by nlinarith,h.2⟩

omit E in
def U19Error (eta xi Amin Rmax Dmax e19 m : ℝ) : ℝ :=
  ((Rmax+((1+eta/xi)/Amin)*Dmax)/m+(eta+2*((1+eta/xi)/Amin))*e19)/Amin

theorem RemoteKernels06.U23
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : 0≤ e19) (he19Small : e19≤ Amin/4)
    (hRmax : 0≤ Rmax) (hDmax : 0≤ Dmax) (hsize : Dmax/(m:ℝ)≤ Amin/2)
    {b : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b) :
    0< barrierDenominator (canonicalSlope Γ i B b)
      (comparisonMarginal Γ i B (Uniform07.cutoff row) b) (deriv (canonicalDuplicate Γ i B) b) ∧
    |(m:ℝ)*finiteBarrier Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b-
      (1+(Uniform07.eta row/Uniform07.xi row)*canonicalShare Γ i B (Uniform07.cutoff row) b)/A b|≤
      U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax e19 m := by
  exact finite_U23_from_U19 (source_eta_mem row) (source_xi_pos row)
    ⟨E.bid0.trans_le hb.1,hb.2.trans E.bid1⟩ hm (E.purePositive b hb).le
    (E.canonicalPositive b hb) hAmin (E.rateBounds b hb) he19 he19Small G.finiteSlope
    hRmax hDmax ⟨(E.canonicalDuplicateProbability b hb).1,E.canonicalRatio b hb⟩
    G.canonicalDerivativeRatio G.canonicalDerivativeAsymptotic hsize

theorem RemoteKernels06.residual_derivatives
    {b : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b)
    (hM : HasDerivAt (rank Γ (Uniform07.cutoff row)) (deriv (rank Γ (Uniform07.cutoff row)) b) b)
    (hS : HasDerivAt (success Γ i) (deriv (success Γ i) b) b)
    (hD : HasDerivAt (duplicate Γ i) (deriv (duplicate Γ i) b) b) :
    HasDerivAt (successError Γ i B (Uniform07.cutoff row))
      (deriv (successError Γ i B (Uniform07.cutoff row)) b) b ∧
    HasDerivAt (duplicateError Γ i B) (deriv (duplicateError Γ i B) b) b := by
  have hq := ((E.pureDerivative b hb).comp b hM).add G.canonicalDerivative
  have hs := hS.sub ((hq.const_mul 2).sub G.duplicateDerivative)
  have hd := hD.sub G.duplicateDerivative
  exact ⟨hs.differentiableAt.hasDerivAt,hd.differentiableAt.hasDerivAt⟩

theorem RemoteKernels06.U22 :
    ∀ᵐ b ∂(volume : Measure ℝ), b∈Icc L R →
      b∈(lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      (rank Γ (Uniform07.cutoff row) b-b)*
        (2*(physicalFlow Γ (Uniform07.cutoff row) b+deriv (canonicalMarginal Γ i B) b)-
          deriv (canonicalDuplicate Γ i B) b)=
        barrierNumerator (Uniform07.eta row) b (comparisonMarginal Γ i B (Uniform07.cutoff row) b)
          (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b)+
          signedResidual Γ i B (Uniform07.eta row) (Uniform07.cutoff row) b := by
  filter_upwards [E.density,E.canonicalAE] with b hb hG hbI hbS
  let G := hG hbI
  rcases hb hbI with ⟨hM,hS,hD,hIC,_,_⟩
  exact actual_U22_density Γ i B (Uniform07.eta row) (Uniform07.cutoff row)
    hM (E.pureDerivative b hbI) G.canonicalDerivative G.duplicateDerivative
    hS hD (hIC hbS)

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
