import FCAppendix.Affine.Uniform06.SourcePreciseFamily
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalWindow

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
open MeasureTheory Set Filter Topology
open Uniform06 Uniform06.LiteralExperiment

def u19Error (xi L Amax δ : ℝ) : ℝ := (Amax+1+2/(xi*L))*δ

theorem u19Error_nonnegative {xi L Amax δ : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hA : 0≤ Amax) (hδ : 0≤δ) :
    0≤ u19Error xi L Amax δ := by unfold u19Error; positivity

structure ScalarCanonicalEstimates (m xi L Amin Amax C R Cp Rp A δ : ℝ) : Prop where
  slopePositive : 0< Cp/C
  slopeError : |(Cp/C)/m-A|≤ u19Error xi L Amax δ
  payment : R≤ 2*C*(1+u19Error xi L Amax δ)/(xi*L*(Cp/C))
  derivative : Rp∈Icc (0:ℝ) ((4/(xi*L))*C)
  derivativeError : |Rp/C-2/(xi*L)|≤ u19Error xi L Amax δ
  ratio : R≤(4/(xi*L*Amin))*C/m

theorem relative_scalar_bounds {m xi L b Amin Amax C R Cp Rp A δ : ℝ}
    (hm : 0< m) (hxi : 0< xi) (hL : 0< L) (hb : L≤ b)
    (hAmin : 0< Amin) (hA : A∈Icc Amin Amax) (hC : 0< C)
    (hδ : δ∈Ioo (0:ℝ) 1)
    (hs : |Cp/(m*C*A)-1|<δ)
    (hr : |m*xi*b*A*R/(2*C)-1|<δ)
    (hd : |(xi*b/2)*(Rp/C)-1|<δ)
    (hf : |(xi*b/2)*(Cp/C)*(R/C)-1|<δ) :
    0< Cp/C ∧
    |(Cp/C)/m-A|≤ u19Error xi L Amax δ ∧
    R≤ 2*C*(1+u19Error xi L Amax δ)/(xi*b*(Cp/C)) ∧
    Rp∈Icc (0:ℝ) ((4/(xi*L))*C) ∧
    |Rp/C-2/(xi*b)|≤ u19Error xi L Amax δ ∧
    R≤(4/(xi*L*Amin))*C/m := by
  have hb0 : 0< b := hL.trans_le hb
  have hA0 : 0< A := hAmin.trans_le hA.1
  have hAmax : 0≤ Amax := hA0.le.trans hA.2
  have hD : 0< xi*b := mul_pos hxi hb0
  have hDL : 0< xi*L := mul_pos hxi hL
  have hscalar : Cp/(m*C*A)=(Cp/C)/(m*A) := by
    field_simp [hm.ne',hC.ne',hA0.ne']
  rw [hscalar] at hs
  have hp0 : 0< Cp/C := by
    have hlo := (abs_lt.mp hs).1
    have hh : 0<(Cp/C)/(m*A) := by linarith [hδ.2]
    exact (div_pos_iff.mp hh).elim (fun h=>h.1)
      (fun h=>False.elim (not_lt_of_ge (mul_pos hm hA0).le h.2))
  have hcoef0 : 0≤ 2/(xi*L) := by positivity
  have hcoeff1 : 1≤ Amax+1+2/(xi*L) := by linarith
  have hcoeffA : Amax≤ Amax+1+2/(xi*L) := by linarith
  have hcoeffD : 2/(xi*L)≤ Amax+1+2/(xi*L) := by linarith
  have hδe : δ≤ u19Error xi L Amax δ := by
    unfold u19Error
    nlinarith [mul_le_mul_of_nonneg_right hcoeff1 hδ.1.le]
  have hAe : Amax*δ≤ u19Error xi L Amax δ :=
    mul_le_mul_of_nonneg_right hcoeffA hδ.1.le
  have hDe : (2/(xi*L))*δ≤ u19Error xi L Amax δ :=
    mul_le_mul_of_nonneg_right hcoeffD hδ.1.le
  have hsE : |(Cp/C)/m-A|≤ u19Error xi L Amax δ := by
    have he : (Cp/C)/m-A=A*((Cp/C)/(m*A)-1) := by
      field_simp [hm.ne',hA0.ne']
    rw [he,abs_mul,abs_of_pos hA0]
    exact (mul_le_mul_of_nonneg_left hs.le hA0.le).trans
      ((mul_le_mul_of_nonneg_right hA.2 hδ.1.le).trans hAe)
  have hpay : R≤ 2*C*(1+u19Error xi L Amax δ)/(xi*b*(Cp/C)) := by
    apply (le_div_iff₀ (mul_pos hD hp0)).mpr
    have hh : (xi*b/2)*(Cp/C)*(R/C)≤ 1+u19Error xi L Amax δ := by
      linarith only [(abs_lt.mp hf).2,hδe]
    have hmul := mul_le_mul_of_nonneg_right hh (show 0≤ 2*C by positivity)
    have he : ((xi*b/2)*(Cp/C)*(R/C))*(2*C)=R*(xi*b*(Cp/C)) := by
      field_simp [hC.ne']
    rw [he] at hmul
    nlinarith
  have hRp : Rp∈Icc (0:ℝ) ((4/(xi*L))*C) := by
    have hlo := (abs_lt.mp hd).1
    have hhi := (abs_lt.mp hd).2
    have hquot0 : 0≤ Rp/C := by
      have he : 0<(xi*b/2)*(Rp/C) := by linarith [hδ.2]
      exact ((mul_pos_iff_of_pos_left (div_pos hD (by norm_num))).mp he).le
    have hr0 : 0≤ Rp := (div_nonneg_iff.mp hquot0).elim (fun h=>h.1)
      (fun h=>False.elim (not_le_of_gt hC h.2))
    have hquot : Rp/C≤ 4/(xi*b) := by
      apply (le_div_iff₀ hD).mpr
      nlinarith [hδ.2]
    have hmono : 4/(xi*b)≤ 4/(xi*L) :=
      div_le_div_of_nonneg_left (by norm_num) hDL
        (mul_le_mul_of_nonneg_left hb hxi.le)
    have hbound := (div_le_iff₀ hC).mp (hquot.trans hmono)
    exact ⟨hr0,by simpa only [mul_comm] using hbound⟩
  have hdE : |Rp/C-2/(xi*b)|≤ u19Error xi L Amax δ := by
    have he : Rp/C-2/(xi*b)=(2/(xi*b))*((xi*b/2)*(Rp/C)-1) := by
      field_simp [hD.ne']
    rw [he,abs_mul,abs_of_nonneg (div_nonneg (by norm_num) hD.le)]
    have hmono : 2/(xi*b)≤ 2/(xi*L) :=
      div_le_div_of_nonneg_left (by norm_num) hDL
        (mul_le_mul_of_nonneg_left hb hxi.le)
    exact (mul_le_mul_of_nonneg_left hd.le (by positivity)).trans
      ((mul_le_mul_of_nonneg_right hmono hδ.1.le).trans hDe)
  have hratio : R≤(4/(xi*L*Amin))*C/m := by
    have hhi : m*xi*b*A*R/(2*C)≤ 2 := by linarith [(abs_lt.mp hr).2,hδ.2]
    have hraw : R≤ 4*C/(m*xi*b*A) := by
      apply (le_div_iff₀ (by positivity : 0< m*xi*b*A)).mpr
      have hh := (div_le_iff₀ (by positivity : 0<2*C)).mp hhi
      nlinarith
    have hden : m*xi*L*Amin≤ m*xi*b*A := by
      have hprod : L*Amin≤ b*A := mul_le_mul hb hA.1 hAmin.le hb0.le
      have hh := mul_le_mul_of_nonneg_left hprod (show 0≤ m*xi by positivity)
      nlinarith
    have hh := div_le_div_of_nonneg_left (show 0≤ 4*C by positivity)
      (show 0< m*xi*L*Amin by positivity) hden
    refine hraw.trans (hh.trans_eq ?_)
    field_simp [hm.ne',hxi.ne',hL.ne',hAmin.ne']
  exact ⟨hp0,hsE,hpay,hRp,hdE,hratio⟩

theorem native_canonical_at {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (row : Uniform07.Row) (Γ : Bayes.FiniteGame m 2 c Seed) (i : Fin m)
    (B : Physical.CanonicalEvent Γ) (G : ProbabilityMeasure (ℝ×ℝ))
    (g : GuardData) (cm : (Fin (m-1)→ Fin 4)→ℝ)
    {L b Amin Amax δ : ℝ} (hm : 0< m) (hL : 0< L) (hb : L≤ b)
    (hAmin : 0< Amin)
    (hA : OptimizedPhysicalRate.A row b∈Icc Amin Amax)
    (hδ : δ∈Ioo (0:ℝ) 1)
    (hC : Physical.canonicalMarginal Γ i B =ᶠ[𝓝 b]
      sourceCanonicalMarginal row m (G:Measure (ℝ×ℝ)) g cm)
    (hR : Physical.canonicalDuplicate Γ i B =ᶠ[𝓝 b]
      sourceCanonicalDuplicate row m (G:Measure (ℝ×ℝ)) g cm)
    (H : SourcePreciseFamily.RelativeBounds row m G g cm b δ) :
    Physical.CanonicalAt06 row Γ i B (OptimizedPhysicalRate.A row)
      (4/(Uniform07.xi row*L)) (u19Error (Uniform07.xi row) L Amax δ) b ∧
      Physical.canonicalDuplicate Γ i B b≤
        (4/(Uniform07.xi row*L*Amin))*Physical.canonicalMarginal Γ i B b/(m:ℝ) := by
  have hCd := H.hasDeriv_C.congr_of_eventuallyEq hC
  have hRd := H.hasDeriv_R.congr_of_eventuallyEq hR
  have hc := hC.self_of_nhds
  have hr := hR.self_of_nhds
  have hbds := relative_scalar_bounds (Nat.cast_pos.mpr hm) (Uniform07.xi_pos row)
    hL hb hAmin hA H.canonical_pos hδ H.slope H.duplicate
      H.duplicate_derivative H.factor
  rw [←hc,←hr,←hCd.deriv,←hRd.deriv] at hbds
  refine ⟨?_,hbds.2.2.2.2.2⟩
  exact {
    canonicalDerivative:=by simpa only [hCd.deriv] using hCd
    duplicateDerivative:=by simpa only [hRd.deriv] using hRd
    finiteSlope:=hbds.2.1
    canonicalPaymentRatio:=hbds.2.2.1
    canonicalDerivativeRatio:=hbds.2.2.2.1
    canonicalDerivativeAsymptotic:=hbds.2.2.2.2.1 }

theorem u19Error_tendsto {xi L Amax : ℝ} {δ : ℕ→ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun m=>u19Error xi L Amax (δ m)) atTop (𝓝 0) := by
  simpa only [u19Error,mul_zero] using hδ.const_mul (Amax+1+2/(xi*L))

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received06
