import FCAppendix.Affine.Uniform06.EarlyCoarseUniform

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceCoarseIncrement
open MeasureTheory Set Filter Topology
open Uniform07 LiteralExperiment RawMixedSource EarlyCoarseUniform

theorem denormalize_bounds {C R I N A : ℝ} (hN : 0 < N) (hA : 0 < A)
    (hc : 1/A ≤ C*Real.exp I*N^2) (hC : C*Real.exp I*N^2 ≤ A)
    (hR : R*Real.exp I*N^3 ≤ A) (hr : 0 ≤ R*Real.exp I*N^3) :
    0 < C ∧ 0 ≤ R ∧ (1/A)*Real.exp (-I)/N^2 ≤ C ∧
      C ≤ A*Real.exp (-I)/N^2 ∧ R ≤ A*Real.exp (-I)/N^3 ∧
      R/C ≤ A^2/N := by
  have he : Real.exp I*Real.exp (-I)=1 := by rw [← Real.exp_add]; simp
  have h2 : 0 < Real.exp (-I)/N^2 := by positivity
  have h3 : 0 < Real.exp (-I)/N^3 := by positivity
  have ec : (C*Real.exp I*N^2)*(Real.exp (-I)/N^2)=C := by
    calc
      _ = C*(Real.exp I*Real.exp (-I)) := by field_simp [hN.ne']
      _ = C := by rw [he,mul_one]
  have er : (R*Real.exp I*N^3)*(Real.exp (-I)/N^3)=R := by
    calc
      _ = R*(Real.exp I*Real.exp (-I)) := by field_simp [hN.ne']
      _ = R := by rw [he,mul_one]
  have hcl := mul_le_mul_of_nonneg_right hc h2.le
  have hcu := mul_le_mul_of_nonneg_right hC h2.le
  have hru := mul_le_mul_of_nonneg_right hR h3.le
  have hr0 := mul_nonneg hr h3.le
  rw [ec] at hcl hcu
  rw [er] at hru hr0
  have hC0 : 0 < C := (mul_pos (one_div_pos.mpr hA) h2).trans_le hcl
  have hCN : 0 < C*Real.exp I*N^2 := by positivity
  have hnorm : (R*Real.exp I*N^3)/(C*Real.exp I*N^2) ≤ A/(1/A) := by
    calc
      _ ≤ A/(C*Real.exp I*N^2) := div_le_div_of_nonneg_right hR hCN.le
      _ ≤ _ := div_le_div_of_nonneg_left hA.le (one_div_pos.mpr hA) hc
  have eA : A/(1/A)=A^2 := by field_simp [hA.ne']
  have eR : (R*Real.exp I*N^3)/(C*Real.exp I*N^2)/N=R/C := by
    field_simp [hC0.ne',hN.ne',(Real.exp_pos I).ne']
  have hh := div_le_div_of_nonneg_right hnorm hN.le
  rw [eA,eR] at hh
  refine ⟨hC0,hr0,?_,?_,?_,hh⟩
  · simpa only [mul_div_assoc] using hcl
  · simpa only [mul_div_assoc] using hcu
  · simpa only [mul_div_assoc] using hru

theorem source_bounds (i : Row) {m : ℕ} (hm : 2 ≤ m)
    (G : Measure (ℝ × ℝ)) (g : GuardData) (cm : (Fin (m-1) → Fin 4) → ℝ)
    {z θ A : ℝ} (hA : 0 < A)
    (hl : 1/A ≤ normalizedC i m G g cm z θ)
    (hu : normalizedC i m G g cm z θ ≤ A)
    (hr : normalizedR i m G g cm z θ ≤ A)
    (h0 : 0 ≤ normalizedR i m G g cm z θ) :
    let C := sourceCanonicalMarginal i m G g cm (z*cutoff i)
    let R := sourceCanonicalDuplicate i m G g cm (z*cutoff i)
    let I := finiteCost i m G z θ
    0 < C ∧ 0 ≤ R ∧ (1/A)*Real.exp (-I)/((m-1:ℕ):ℝ)^2 ≤ C ∧
      C ≤ A*Real.exp (-I)/((m-1:ℕ):ℝ)^2 ∧
      R ≤ A*Real.exp (-I)/((m-1:ℕ):ℝ)^3 ∧ R/C ≤ A^2/((m-1:ℕ):ℝ) :=
  denormalize_bounds (Nat.cast_pos.mpr (by omega)) hA hl hu hr h0

theorem raw_matching_mean (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b θ q : ℝ} (hb : 0 < b)
    (h : SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b G)) Prod.fst θ=q) :
    (∫ r,demand (xi i) b r ∂(source i G).tilted (fun r => -θ*demand (xi i) b r))=q := by
  have hp := RawTiltedSource.tilted_point_preserving i G hb θ
  have he := integral_map (μ := RawTiltedSource.tiltedSource i G b θ)
    (f := Prod.fst) hp.measurable.aemeasurable measurable_fst.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans h

theorem actual_increment (i : Row) {m : ℕ} (hm : 2 ≤ m)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ ReceiptGap.cap i)
    (hactive : ∀ᵐ p ∂G,p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000)
    (g : GuardData) (cm : (Fin (m-1) → Fin 4) → ℝ)
    {z z' θ θ' τ Θ A : ℝ} (hA : 0 < A) (hτ : 0 < τ)
    (hz : 1/2 ≤ z) (hzz : z < z') (hz' : z'*cutoff i ≤ EarlyRankCeiling.prefixEnd i)
    (hθ' : θ' ∈ Icc τ Θ)
    (hmatch : SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i
      (z*cutoff i) G)) Prod.fst θ=(capacity m:ℝ)/((m-1:ℕ):ℝ))
    (hcoarse : 1/A ≤ normalizedC i m G g cm z θ ∧ normalizedC i m G g cm z θ ≤ A ∧
      normalizedR i m G g cm z θ ≤ A ∧ 0 ≤ normalizedR i m G g cm z θ)
    (hcoarse' : 1/A ≤ normalizedC i m G g cm z' θ' ∧ normalizedC i m G g cm z' θ' ≤ A ∧
      normalizedR i m G g cm z' θ' ≤ A ∧ 0 ≤ normalizedR i m G g cm z' θ') :
    (1/A^2)*Real.exp (((m-1:ℕ):ℝ)*
      (Real.exp (-Θ)*τ*TiltedGood.stripMass i/(xi i*ReceiptGap.cap i))*
        ((z'-z)*cutoff i)) ≤
      sourceCanonicalMarginal i m G g cm (z'*cutoff i)/
        sourceCanonicalMarginal i m G g cm (z*cutoff i) := by
  have hb : 0 < z*cutoff i := mul_pos (by linarith) (cutoff_pos i)
  have hbb : z*cutoff i < z'*cutoff i := mul_lt_mul_of_pos_right hzz (cutoff_pos i)
  have hN : 0 < m-1 := by omega
  have hNR : 0 < ((m-1:ℕ):ℝ) := Nat.cast_pos.mpr hN
  have hprice : (1-xi i)*ReceiptGap.cap i ≤ z*cutoff i := by
    have hh := (EarlyCoarseMargins.floorPrice_bounds i).2.le
    change (1-xi i)*ReceiptGap.cap i ≤ cutoff i/2 at hh
    exact hh.trans (by nlinarith [cutoff_pos i])
  have hmass := TiltedGood.early_original_strip_mass i G hvalue hcap hactive hz'
  have hgap := CostAmplification.original_cost_amplification i G hN hb hbb
    (ReceiptGap.cap_bounds i).1 hprice hτ hθ'.1 hθ'.2
    (TiltedGood.stripMass_pos i).le hmass (raw_matching_mean i G hb hmatch)
  have hlo := source_bounds i hm G g cm hA hcoarse.1 hcoarse.2.1 hcoarse.2.2.1 hcoarse.2.2.2
  have hhi := source_bounds i hm G g cm hA hcoarse'.1 hcoarse'.2.1 hcoarse'.2.2.1 hcoarse'.2.2.2
  have hamp := CostAmplification.finite_kernel_amplification hNR (one_div_pos.mpr hA) hA
    hlo.1 (by simpa only [mul_div_right_comm,finiteCost] using! hlo.2.2.2.1)
    (by simpa only [mul_div_right_comm,finiteCost] using! hhi.2.2.1) hgap
  convert! hamp using 1
  field_simp [hA.ne']

end FCAppendix.Affine.Uniform06.SourceCoarseIncrement
