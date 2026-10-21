import FCAppendix.Affine.Uniform07Finishing.Crossover.SplitErrorAbsorption
import FCAppendix.Affine.Uniform07Finishing.Crossover.ACEnvelope

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology

namespace Physical
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {row : Uniform07.Row} {Γ : FiniteGame m 2 c Seed} {i : Fin m}
  {B : CanonicalEvent Γ} {L R U : ℝ}
  {P : BroadcastLaw05 Γ (Uniform07.cutoff row) U}
  {A : ℝ→ℝ} {Amin Amax Rmax Dmax e19 e ell : ℝ}
variable (E : RemoteKernels06 row Γ i B L R U P A Amin Amax Rmax Dmax e19 e ell)
include E

theorem RemoteKernels06.comparison_monotone
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4) :
    MonotoneOn (comparisonMarginal Γ i B (Uniform07.cutoff row)) (Icc L R) := by
  have hAC := comparisonMarginal_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC
  intro x hx y hy hxy
  have hsub : uIcc x y ⊆ uIcc L R := by
    rw [uIcc_of_le hxy,uIcc_of_le E.interval]
    exact fun z hz => ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
  have hder : ∀ᵐ z ∂volume.restrict (Icc x y),
      0≤ deriv (comparisonMarginal Γ i B (Uniform07.cutoff row)) z := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [E.density,E.canonicalAE] with z hz hG hzxy
    have hzI : z∈Icc L R := ⟨hx.1.trans hzxy.1,hzxy.2.trans hy.2⟩
    let G := hG hzI
    have hM := (hz hzI).1
    have hq := ((E.pureDerivative z hzI).comp z hM).add G.canonicalDerivative
    change HasDerivAt (comparisonMarginal Γ i B (Uniform07.cutoff row)) _ z at hq
    rw [hq.deriv]
    have hflow : 0≤ deriv (pureRank m c (Uniform07.cutoff row)) (rank Γ (Uniform07.cutoff row) z)*
        deriv (rank Γ (Uniform07.cutoff row)) z :=
      mul_nonneg (E.pureDerivativePositive z hzI).le (rank_monotone Γ (Uniform07.cutoff row)).deriv_nonneg
    have hC : 0≤ deriv (canonicalMarginal Γ i B) z := by
      rw [← E.slope_mul hzI]
      exact mul_nonneg ((mul_pos (by positivity : 0< Amin/2) hm).le.trans
        (E.slope_lower hm hAmin he19 hzI G)) (E.canonicalPositive z hzI).le
    exact add_nonneg hflow hC
  have h := ac_increment_lower hxy (hAC.mono hsub) hder
  simpa using h

theorem RemoteKernels06.numerator_bounds (hDmax : 0≤ Dmax) {b : ℝ} (hb : b∈Icc L R)
    (G : CanonicalAt06 row Γ i B A Dmax e19 b) :
    comparisonMarginal Γ i B (Uniform07.cutoff row) b≤
      barrierNumerator (Uniform07.eta row) b (comparisonMarginal Γ i B (Uniform07.cutoff row) b)
        (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b) ∧
    barrierNumerator (Uniform07.eta row) b (comparisonMarginal Γ i B (Uniform07.cutoff row) b)
        (canonicalDuplicate Γ i B b) (deriv (canonicalDuplicate Γ i B) b)≤
      (2+Dmax)*comparisonMarginal Γ i B (Uniform07.cutoff row) b := by
  apply physical_barrier_numerator_bounds (source_eta_mem row)
    ⟨E.bid0.le.trans hb.1,hb.2.trans E.bid1⟩ (E.comparison_positive hb).le
  · exact ⟨(E.canonicalDuplicateProbability b hb).1,
      (E.canonicalDuplicateProbability b hb).2.trans (E.canonical_le_comparison hb)⟩
  · exact ⟨G.canonicalDerivativeRatio.1,G.canonicalDerivativeRatio.2.trans
      (mul_le_mul_of_nonneg_left (E.canonical_le_comparison hb) hDmax)⟩

theorem RemoteKernels06.zero_flow_gap_budget
    (hm : 0<(m:ℝ)) (hAmin : 0< Amin) (he19 : e19≤ Amin/4) (he : 0≤ e)
    {x y : ℝ} (hx : L≤ x) (hxy : x< y) (hy : y≤ R)
    (hgap : ∀ z∈Ioo x y, z∉(lowerBidMeasure Γ (Uniform07.cutoff row)).support) :
    ∀ᵐ z ∂(volume : Measure ℝ), z∈Ioo x y →
      HasDerivAt (successError Γ i B (Uniform07.cutoff row))
        (deriv (successError Γ i B (Uniform07.cutoff row)) z) z ∧
      HasDerivAt (duplicateError Γ i B) (deriv (duplicateError Γ i B) z) z ∧
      |successError Γ i B (Uniform07.cutoff row) z|≤
        e*comparisonMarginal Γ i B (Uniform07.cutoff row) y/(m:ℝ) ∧
      |duplicateError Γ i B z|≤ e*comparisonMarginal Γ i B (Uniform07.cutoff row) y/(m:ℝ) ∧
      |deriv (successError Γ i B (Uniform07.cutoff row)) z|≤
        e*comparisonMarginal Γ i B (Uniform07.cutoff row) y ∧
      |deriv (duplicateError Γ i B) z|≤ e*comparisonMarginal Γ i B (Uniform07.cutoff row) y := by
  letI : NullSingletonClass (lowerBidMeasure Γ (Uniform07.cutoff row)) := P.atomless
  have hmono := E.comparison_monotone hm hAmin he19
  filter_upwards [E.density,E.canonicalAE] with z hz hG hzxy
  have hzI : z∈Icc L R := ⟨hx.trans hzxy.1.le,hzxy.2.le.trans hy⟩
  have hyI : y∈Icc L R := ⟨hx.trans hxy.le,hy⟩
  let G := hG hzI
  rcases hz hzI with ⟨hM,hS,hD,_,hse,hde⟩
  have hd := E.residual_derivatives hzI G hM hS hD
  have hzero := rank_hasDerivAt_zero_on_gap Γ (Uniform07.cutoff row) hzxy hgap
  have hflow : physicalFlow Γ (Uniform07.cutoff row) z=0 := by
    unfold physicalFlow
    rw [hzero.deriv,mul_zero]
  rw [hflow,zero_div,zero_add] at hse hde
  have hq := mul_le_mul_of_nonneg_left (hmono hzI hyI hzxy.2.le) he
  have hqm := div_le_div_of_nonneg_right hq hm.le
  exact ⟨hd.1,hd.2,(E.successValueError z hzI).trans hqm,
    (E.duplicateValueError z hzI).trans hqm,hse.trans hq,hde.trans hq⟩

theorem RemoteKernels06.reference_slope_lower
    (hm : 0 < (m:ℝ)) {b : ℝ} (hb : b ∈ Icc L R) :
    Amin*(m:ℝ) ≤ referenceSlope m A b := by
  simpa only [referenceSlope,mul_comm] using
    mul_le_mul_of_nonneg_left (E.rateBounds b hb).1 hm.le

theorem RemoteKernels06.reference_slope_positive
    (hm : 0 < (m:ℝ)) (hAmin : 0 < Amin) {b : ℝ} (hb : b ∈ Icc L R) :
    0 < referenceSlope m A b :=
  (mul_pos hAmin hm).trans_le (E.reference_slope_lower hm hb)

omit E in
theorem RemoteKernels06.leading_scaled
    (hm : 0 < (m:ℝ)) {b : ℝ} :
    (m:ℝ)*leadingBarrier row Γ i B A b =
      (1+(Uniform07.eta row/Uniform07.xi row)*
        canonicalShare Γ i B (Uniform07.cutoff row) b)/A b := by
  simp only [leadingBarrier,referenceSlope]
  calc
    _ = ((m:ℝ)/(m:ℝ))*
        ((1+(Uniform07.eta row/Uniform07.xi row)*
          canonicalShare Γ i B (Uniform07.cutoff row) b)/A b) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ = _ := by rw [div_self hm.ne',one_mul]

theorem RemoteKernels06.leading_continuous
    (hm : 0 < (m:ℝ)) (hAmin : 0 < Amin) :
    ContinuousOn (leadingBarrier row Γ i B A) (Icc L R) := by
  have hw : ContinuousOn (canonicalShare Γ i B (Uniform07.cutoff row)) (Icc L R) := by
    change ContinuousOn (fun b => canonicalMarginal Γ i B b/
      comparisonMarginal Γ i B (Uniform07.cutoff row) b) (Icc L R)
    simpa only [uIcc_of_le E.interval] using
      (canonical_share_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC
        (fun b hb => E.comparison_positive (by simpa only [uIcc_of_le E.interval] using hb))).continuousOn
  unfold leadingBarrier referenceSlope
  exact (continuousOn_const.add (continuousOn_const.mul hw)).div
    (continuousOn_const.mul E.rateContinuous)
    (fun b hb => (mul_pos hm (hAmin.trans_le (E.rateBounds b hb).1)).ne')

omit E in

def GapLeadError (eta xi Amin Rmax e19 e m : ℝ) : ℝ :=
  (1+eta/xi)*e19/Amin^2+(Rmax/m+e19+4*e)/(2*Amin)

theorem RemoteKernels06.gap_leading_reset
    (hm : 1 ≤ (m:ℝ)) (hAmin : 0 < Amin)
    (he19 : 0 ≤ e19) (he19Small : e19 ≤ Amin/4) (hRmax : 0 ≤ Rmax)
    (he : 0 ≤ e) (he1 : e < 1) (hell : 0 < ell)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0)
    {x y : ℝ} (hx : L ≤ x) (hxy : x < y) (hy : y ≤ R)
    (hyS : y ∈ (lowerBidMeasure Γ (Uniform07.cutoff row)).support)
    (hgap : ∀ z ∈ Ioo x y, z ∉ (lowerBidMeasure Γ (Uniform07.cutoff row)).support) :
    leadingBarrier row Γ i B A y-
        GapLeadError (Uniform07.eta row) (Uniform07.xi row) Amin Rmax e19 e m/(m:ℝ) ≤
      rank Γ (Uniform07.cutoff row) y-y := by
  letI : NullSingletonClass (lowerBidMeasure Γ (Uniform07.cutoff row)) := P.atomless
  have hm0 : 0 < (m:ℝ) := by linarith
  have hyI : y ∈ Icc L R := ⟨hx.trans hxy.le,hy⟩
  have hyM := E.actual_rent hm he he1 hell hA hg hyI hyS
  have hq := E.comparison_positive hyI
  have hr := rank_constant_on_unused_gap Γ (Uniform07.cutoff row) hxy.le hgap
  let w := rank Γ (Uniform07.cutoff row) y
  let p := pureRank m c (Uniform07.cutoff row) w
  let f := gapPayoff (Uniform07.eta row) w p
    (canonicalMarginal Γ i B) (canonicalDuplicate Γ i B)
  let H : ℝ → ℝ := fun z => comparisonMarginal Γ i B (Uniform07.cutoff row) z*
    (2*(m:ℝ)*(A z+e19)*(w-z)-
      2*(1+(Uniform07.eta row/Uniform07.xi row)*canonicalShare Γ i B (Uniform07.cutoff row) z)+
      Rmax/(m:ℝ)+e19)
  have hsub : uIcc x y ⊆ uIcc L R := by
    rw [uIcc_of_le hxy.le,uIcc_of_le E.interval]
    exact fun z hz => ⟨hx.trans hz.1,hz.2.trans hy⟩
  have hsub' : Icc x y ⊆ Icc L R := fun z hz => ⟨hx.trans hz.1,hz.2.trans hy⟩
  have hC := E.canonicalAC.mono hsub
  have hD := E.canonicalDuplicateAC.mono hsub
  have hS := (contDiff_comp_absolutelyContinuous
    (show ContDiff ℝ 1 (fun r : ℝ => 2*(p+r)) by fun_prop) hC).fun_sub hD
  have hrentAC : AbsolutelyContinuousOnInterval (fun z : ℝ => w-z) x y :=
    (show ContDiffOn ℝ 1 (fun z : ℝ => w-z) (uIcc x y) by fun_prop).absolutelyContinuousOnInterval
  have hcostAC : AbsolutelyContinuousOnInterval (fun z : ℝ => Uniform07.eta row*z) x y :=
    (show ContDiffOn ℝ 1 (fun z : ℝ => Uniform07.eta row*z) (uIcc x y) by fun_prop).absolutelyContinuousOnInterval
  have hf : AbsolutelyContinuousOnInterval f x y :=
    (hrentAC.fun_mul hS).fun_sub (hcostAC.fun_mul hD)
  have hqcont : ContinuousOn (comparisonMarginal Γ i B (Uniform07.cutoff row)) (Icc x y) := by
    simpa only [uIcc_of_le hxy.le] using
      ((comparisonMarginal_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC).mono hsub).continuousOn
  have hwcont : ContinuousOn (canonicalShare Γ i B (Uniform07.cutoff row)) (Icc x y) := by
    change ContinuousOn (fun b => canonicalMarginal Γ i B b/
      comparisonMarginal Γ i B (Uniform07.cutoff row) b) (Icc x y)
    simpa only [uIcc_of_le hxy.le] using
      ((canonical_share_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC
        (fun z hz => E.comparison_positive (by simpa only [uIcc_of_le E.interval] using hz))).mono hsub).continuousOn
  have hH : ContinuousOn H (Icc x y) := by
    have hAA := E.rateContinuous.mono hsub'
    dsimp [H]
    fun_prop
  have hres := residuals_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC
    E.canonicalDuplicateAC E.successAC E.duplicateAC
  have hcorrection := pure_gap_correction_lipschitz (source_eta_mem row)
    (E.bid0.le.trans hx) hxy hyM.2
    ((E.rankRange y hyI).2.trans (Uniform07.cutoff_lt_one row).le) hq.le hm he
    (hres.1.mono hsub) (hres.2.mono hsub)
    (E.zero_flow_gap_budget hm0 hAmin he19Small he hx hxy hy hgap)
  have hopt : ∀ z ∈ Ioo x y,
      f z+gapCorrection Γ i B (Uniform07.eta row) (Uniform07.cutoff row) w z ≤
        f y+gapCorrection Γ i B (Uniform07.eta row) (Uniform07.cutoff row) w y := by
    intro z hz
    have hz0 := E.bid0.le.trans (hx.trans hz.1.le)
    have hh := E.common_boundary_IC hyI hyS z ⟨hz0,hz.2.le.trans (hy.trans E.feasible)⟩
    rw [actual_gap_payoff Γ i B (source_eta_mem row).1 (source_eta_mem row).2 hA hg
        (E.bid0.le.trans hyI.1) rfl,
      actual_gap_payoff Γ i B (source_eta_mem row).1 (source_eta_mem row).2 hA hg hz0
        (congrArg (pureRank m c (Uniform07.cutoff row)) (hr z ⟨hz.1.le,hz.2.le⟩))] at hh
    exact hh
  have hmax := left_canonical_comparison_of_total_optimum hopt
    (by simpa only [gapCorrection,w] using hcorrection)
  have hder : ∀ᵐ z ∂(volume : Measure ℝ), z ∈ Ioo x y → deriv f z ≤ H z := by
    filter_upwards [E.canonicalAE] with z hG hz
    have hzI := hsub' ⟨hz.1.le,hz.2.le⟩
    let G := hG hzI
    have hz0 := E.bid0.trans_le hzI.1
    have hCp : deriv (canonicalMarginal Γ i B) z ≤
        (m:ℝ)*(A z+e19)*canonicalMarginal Γ i B z := by
      have hsl := (div_le_iff₀ hm0).mp
        (show canonicalSlope Γ i B z/(m:ℝ) ≤ A z+e19 from by
          linarith [(abs_le.mp G.finiteSlope).2])
      have hh := mul_le_mul_of_nonneg_right hsl (E.canonicalPositive z hzI).le
      rw [E.slope_mul hzI] at hh
      nlinarith
    have hd := gapPayoff_hasDerivAt (eta := Uniform07.eta row) (w := w) (p := p)
      G.canonicalDerivative G.duplicateDerivative
    rw [hd.deriv]
    have hpe : p+canonicalMarginal Γ i B z=comparisonMarginal Γ i B (Uniform07.cutoff row) z := by
      dsimp [p,w,comparisonMarginal]
      rw [hr z ⟨hz.1.le,hz.2.le⟩]
    rw [hpe]
    exact canonical_gap_continuous_envelope (source_eta_mem row) (source_xi_pos row)
      ⟨hz0,hzI.2.trans E.bid1⟩ (by dsimp [w]; linarith [hyM.2,hz.2]) hm0
      (hAmin.trans_le (E.rateBounds z hzI).1) he19 (E.comparison_positive hzI)
      (E.canonicalPositive z hzI) (E.canonical_le_comparison hzI) hRmax
      (E.canonicalDuplicateProbability z hzI).1 (E.canonicalRatio z hzI) hCp
      G.canonicalDerivativeRatio.1 G.canonicalDerivativeAsymptotic
  have hend := ac_right_comparison_derivative_envelope hxy hf hH hmax hder
  have hscaled : 0 ≤ 2*(m:ℝ)*(A y+e19)*(w-y)-
      2*(1+(Uniform07.eta row/Uniform07.xi row)*canonicalShare Γ i B (Uniform07.cutoff row) y)+
      (Rmax/(m:ℝ)+e19+4*e) := by
    have hh : 0 ≤ comparisonMarginal Γ i B (Uniform07.cutoff row) y*
        (2*(m:ℝ)*(A y+e19)*(w-y)-
          2*(1+(Uniform07.eta row/Uniform07.xi row)*canonicalShare Γ i B (Uniform07.cutoff row) y)+
          (Rmax/(m:ℝ)+e19+4*e)) := by
      dsimp [H] at hend
      nlinarith
    exact (mul_nonneg_iff_of_pos_left hq).mp hh
  exact leading_gap_reset_algebra hm0 hAmin (E.rateBounds y hyI).1
    (div_nonneg (source_eta_mem row).1 (source_xi_pos row).le) (E.share_bounds hyI)
    he19 (by positivity) (sub_nonneg.mpr hyM.2) hscaled

theorem RemoteKernels06.gap_reset
    (hm : 1 ≤ (m:ℝ)) (hAmin : 0 < Amin)
    (he19 : 0 ≤ e19) (he19Small : e19 ≤ Amin/4) (hRmax : 0 ≤ Rmax)
    (he : 0 ≤ e) (he1 : e < 1) (hell : 0 < ell)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {eps : ℝ} (_heps : 0 < eps)
    (hgapSmall : GapLeadError (Uniform07.eta row) (Uniform07.xi row) Amin Rmax e19 e m < eps/2) :
    ∀ x y, L ≤ x → x < y → y ≤ R → y ∈ (lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      (∀ z ∈ Ioo x y, z ∉ (lowerBidMeasure Γ (Uniform07.cutoff row)).support) →
      -eps/(2*(m:ℝ)) < rank Γ (Uniform07.cutoff row) y-y-leadingBarrier row Γ i B A y := by
  intro x y hx hxy hy hyS hgap
  have hm0 : 0 < (m:ℝ) := by linarith
  have hh := E.gap_leading_reset hm hAmin he19 he19Small hRmax he he1 hell hA hg hx hxy hy hyS hgap
  have he := div_lt_div_of_pos_right hgapSmall hm0
  have hid : (eps/2)/(m:ℝ)=eps/(2*(m:ℝ)) := by ring
  rw [hid] at he
  rw [neg_div]
  linarith

theorem RemoteKernels06.below_leading_drift_split
    {eS eD : ℝ} (X : PureDerivativeBounds06 Γ i B (Uniform07.cutoff row) L R eS eD)
    (hm : 1 ≤ (m:ℝ)) (hAmin : 0 < Amin) (he19 : 0 ≤ e19)
    (he19Small : e19 ≤ Amin/4) (he19Rate : e19 ≤ 1/10000)
    (hRmax : 0 ≤ Rmax) (hDmax : 0 ≤ Dmax) (hsize : Dmax/(m:ℝ) ≤ Amin/2)
    (he : 0 ≤ e) (he1 : e < 1) (hell : 0 < ell)
    (heS : eS ∈ Icc (0:ℝ) 1) (heD : eD ∈ Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {eps : ℝ} (heps : 0 < eps)
    (habsorb : eS+2*eD/((m:ℝ)*L*ell/2) ≤ 1)
    (herror : eS+3*eD+(eS+2*eD/((m:ℝ)*L*ell/2))*(6+Dmax) ≤ eps*(Amin/2)/8)
    (hU23Small : U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax e19 m ≤ eps/4) :
    ∀ᵐ b ∂(volume : Measure ℝ), b ∈ Icc L R →
      b ∈ (lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      rank Γ (Uniform07.cutoff row) b-b-leadingBarrier row Γ i B A b ≤ -eps/(2*(m:ℝ)) →
      (1/4:ℝ) ≤ deriv (fun z => rank Γ (Uniform07.cutoff row) z-z) b ∧
        deriv (canonicalShare Γ i B (Uniform07.cutoff row)) b ≤ 0 := by
  have hm0 : 0 < (m:ℝ) := by linarith
  have hd := E.below_barrier_drift_split X hm hAmin he19Small he19Rate hDmax hsize
    he he1 hell heS heD hA hg (half_pos heps) habsorb
    (by convert herror using 1; ring)
  filter_upwards [hd,E.canonicalAE] with b hdb hG hb hbS hbelow
  have hu := (E.U23 hm0 hAmin he19 he19Small hRmax hDmax hsize hb (hG hb)).2
  rw [← RemoteKernels06.leading_scaled hm0] at hu
  apply hdb hb hbS
  have hscale := mul_le_mul_of_nonneg_left hbelow hm0.le
  have hid : (m:ℝ)*(-eps/(2*(m:ℝ)))= -eps/2 := by field_simp [hm0.ne']
  rw [mul_sub,hid] at hscale
  apply (le_div_iff₀ (by positivity : 0 < 2*(m:ℝ))).2
  nlinarith [(abs_le.mp hu).1]

theorem literal_finite_used_support_barrier
    {eS eD : ℝ}
    (X : PureDerivativeBounds06 Γ i B (Uniform07.cutoff row) L R eS eD)
    (hm : 1 ≤ (m:ℝ)) (hAmin : 0 < Amin) (he19 : 0 ≤ e19)
    (he19Small : e19 ≤ Amin/4) (he19Rate : e19 ≤ 1/10000)
    (hRmax : 0 ≤ Rmax) (hDmax : 0 ≤ Dmax) (hsize : Dmax/(m:ℝ) ≤ Amin/2)
    (he : 0 ≤ e) (heSmall : 4*e ≤ 1) (hell : 0 < ell)
    (heS : eS ∈ Icc (0:ℝ) 1) (heD : eD ∈ Icc (0:ℝ) 1)
    (hA : Γ.A=Schedule.affine 2 (Uniform07.eta row) (source_eta_mem row).1 (source_eta_mem row).2)
    (hg : Γ.g=0) {eps omega : ℝ} (heps : 0 < eps) (homega : 0 ≤ omega)
    (habsorb : eS+2*eD/((m:ℝ)*L*ell/2) ≤ 1)
    (herror : eS+3*eD+(eS+2*eD/((m:ℝ)*L*ell/2))*(6+Dmax) ≤ eps*(Amin/2)/8)
    (hgapSmall : GapLeadError (Uniform07.eta row) (Uniform07.xi row) Amin Rmax e19 e m < eps/2)
    (hU23Small : U19Error (Uniform07.eta row) (Uniform07.xi row) Amin Rmax Dmax e19 m ≤ eps/4)
    (hmodulus : ∀ a ∈ Icc L R, ∀ b ∈ Icc L R, a ≤ b →
      b-a ≤ ((1+Uniform07.eta row/Uniform07.xi row)/Amin+1)/((1/4:ℝ)*(m:ℝ)) →
      |1/A b-1/A a| ≤ omega)
    (hsmall : (1+Uniform07.eta row/Uniform07.xi row)*omega < eps/2) :
    ∀ b ∈ Icc L R, b ∈ (lowerBidMeasure Γ (Uniform07.cutoff row)).support →
      ((1+Uniform07.eta row/Uniform07.xi row)/Amin+1)/((1/4:ℝ)*(m:ℝ)) < b-L →
      leadingBarrier row Γ i B A b-eps/(m:ℝ) < rank Γ (Uniform07.cutoff row) b-b := by
  have hm0 : 0 < (m:ℝ) := by linarith
  have he1 : e < 1 := by linarith
  have hk : 0 ≤ Uniform07.eta row/Uniform07.xi row :=
    div_nonneg (source_eta_mem row).1 (source_xi_pos row).le
  have hdeltaAC : AbsolutelyContinuousOnInterval (fun b => rank Γ (Uniform07.cutoff row) b-b) L R :=
    E.rankAC.fun_sub
      (show ContDiffOn ℝ 1 (fun b : ℝ => b) (uIcc L R) by fun_prop).absolutelyContinuousOnInterval
  have hweightAC := canonical_share_ac Γ i B (Uniform07.cutoff row) E.rankAC E.canonicalAC
    (fun b hb => E.comparison_positive (by simpa only [uIcc_of_le E.interval] using hb))
  change AbsolutelyContinuousOnInterval
    (canonicalShare Γ i B (Uniform07.cutoff row)) L R at hweightAC
  have hF : ContinuousOn (fun b => rank Γ (Uniform07.cutoff row) b-b-leadingBarrier row Γ i B A b) (Icc L R) :=
    (P.rankContinuous.continuousOn.sub continuousOn_id).sub (E.leading_continuous hm0 hAmin)
  apply finite_closed_support_barrier_after_overlap (err := 0)
    Measure.isClosed_support E.interval hm0 heps (by norm_num : (0:ℝ) < 1/4)
    hk homega hF hdeltaAC hweightAC
    (E.gap_reset hm hAmin he19 he19Small hRmax he he1 hell hA hg heps hgapSmall)
    ?_ (E.below_leading_drift_split X hm hAmin he19 he19Small he19Rate hRmax hDmax hsize
      he he1 hell heS heD hA hg heps habsorb herror hU23Small)
    (fun b hb => E.share_bounds hb) ?_ ?_ hmodulus (by simpa using hsmall)
  · intro b hb hbS hbelow
    have hδ := E.actual_rent hm he he1 hell hA hg hb hbS
    have hlead := (U23_leading_bounds (source_eta_mem row).1 (source_xi_pos row)
      (E.share_bounds hb) hAmin (E.rateBounds b hb)).2
    have hT : (m:ℝ)*leadingBarrier row Γ i B A b ≤
        (1+Uniform07.eta row/Uniform07.xi row)/Amin+1 := by
      rw [RemoteKernels06.leading_scaled hm0]
      linarith [(abs_le.mp hlead).2]
    refine ⟨(by have hL := E.bid0; positivity : 0 ≤ L*ell/2).trans hδ.1,?_⟩
    apply (le_div_iff₀ hm0).2
    have hnegative : -eps/(2*(m:ℝ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heps.le) (by positivity)
    have hδT : rank Γ (Uniform07.cutoff row) b-b ≤ leadingBarrier row Γ i B A b := by linarith
    exact (mul_le_mul_of_nonneg_right hδT hm0.le).trans
      (by simpa only [mul_comm] using hT)
  · intro b hb
    exact div_nonneg zero_le_one (hAmin.trans_le (E.rateBounds b hb).1).le
  · intro b hb
    rw [RemoteKernels06.leading_scaled hm0]
    simp [div_eq_mul_inv,canonicalShare]

end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
