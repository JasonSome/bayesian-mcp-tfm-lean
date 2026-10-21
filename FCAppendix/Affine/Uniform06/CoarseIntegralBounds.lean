import FCAppendix.Affine.Uniform06.AllImbalanceMoments
import FCAppendix.Affine.Uniform06.CanonicalCoarse
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement

noncomputable section
namespace FCAppendix.Affine.Uniform06.CoarseIntegralBounds

open MeasureTheory Set Filter
open scoped BigOperators Topology
open WeightedIntervalLLT ExponentialCellBounds AllImbalanceMoments

variable {Ω : Type*} [MeasurableSpace Ω]

def weighted (θ : ℝ) (W p : Ω → ℝ) : Ω → ℝ := fun ω => Real.exp (-θ*W ω)*p ω

lemma weighted_unit_bounds {θ : ℝ} (hθ : 0 ≤ θ) {w p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hpos : 0 < p → 0 ≤ w) :
    Real.exp (-θ*w)*p ∈ Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (Real.exp_pos _).le hp.1,?_⟩
  by_cases hz : p=0
  · simp [hz]
  · have hw : 0 ≤ w := hpos (lt_of_le_of_ne hp.1 (Ne.symm hz))
    have he : Real.exp (-θ*w) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    exact (mul_le_mul_of_nonneg_right he hp.1).trans (by simpa using hp.2)

lemma integrable_weighted (μ : Measure Ω) [IsFiniteMeasure μ]
    {W p : Ω → ℝ} (hW : Measurable W) (hp : Measurable p)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hb : ∀ᵐ ω ∂μ,p ω ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ᵐ ω ∂μ,0 < p ω → 0 ≤ W ω) :
    Integrable (weighted θ W p) μ := by
  apply Integrable.of_mem_Icc 0 1
    ((((hW.const_mul (-θ)).exp).mul hp).aemeasurable)
  filter_upwards [hb,hpos] with ω hω hpω
  exact weighted_unit_bounds hθ hω hpω

lemma weighted_le_exponentialTest {θ s w p A : ℝ} (k : ℕ) (hk : 0 < k)
    (_hs : 0 ≤ s) (hp : 0 ≤ p) (_hA : 0 < A)
    (hbound : p ≤ (max 0 (w-s))^k/A) :
    Real.exp (-θ*w)*p ≤ exponentialTest k θ s w/A := by
  by_cases hsw : s ≤ w
  · rw [exponentialTest,if_pos hsw,max_eq_right (sub_nonneg.mpr hsw)] at *
    have hh := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (-θ*w)).le
    convert! hh using 1
    ring
  · have hz : max 0 (w-s)=0 := max_eq_left (by linarith)
    rw [hz,zero_pow hk.ne',zero_div] at hbound
    have hpz : p=0 := le_antisymm hbound hp
    simp [exponentialTest,hsw,hpz]

theorem tilted_kernel_upper (μ : Measure Ω) [IsProbabilityMeasure μ]
    {W p : Ω → ℝ} {Y : Ω → ℤ}
    (hW : Measurable W) (hY : Measurable Y) (hp : Measurable p)
    {θ a A B : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hA : 0 < A) (hB : 0 ≤ B)
    (hWb : ∀ᵐ ω ∂μ,|W ω| ≤ B)
    (hpb : ∀ᵐ ω ∂μ,p ω ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ᵐ ω ∂μ,0 < p ω → 0 ≤ W ω)
    (G : Set Ω) (hG : MeasurableSet G) (k : ℕ) (hk : 0 < k)
    (hgood : ∀ᵐ ω ∂μ,ω ∈ G →
      p ω ≤ (max 0 (W ω-a*((Y ω).natAbs : ℝ)))^k/A) :
    (∫ ω,weighted θ W p ω ∂μ) ≤
      (∫ ω,exponentialTest k θ (a*(Y ω).natAbs) (W ω) ∂μ)/A+μ.real Gᶜ := by
  let T := fun ω => exponentialTest k θ (a*(Y ω).natAbs) (W ω)
  have hpi := integrable_weighted μ hW hp hθ.le hpb hpos
  have hTi : Integrable T μ :=
    integrable_variable_exponentialTest μ hW hY hB hθ.le ha hWb k
  have hbad : Integrable (Gᶜ.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hG.compl
  have hh := integral_mono_ae hpi ((hTi.div_const A).add hbad) (by
    filter_upwards [hpb,hpos,hgood] with ω hpω hposω hgω
    change weighted θ W p ω ≤ T ω/A+Gᶜ.indicator (fun _ => (1:ℝ)) ω
    by_cases hg : ω ∈ G
    · rw [indicator_of_notMem (show ω ∉ Gᶜ from by simpa using hg),add_zero]
      exact weighted_le_exponentialTest k hk (mul_nonneg ha (Nat.cast_nonneg _)) hpω.1 hA
        (hgω hg)
    · rw [indicator_of_mem (show ω ∈ Gᶜ from hg)]
      have hu := (weighted_unit_bounds hθ.le hpω hposω).2
      have ht : 0 ≤ T ω/A := div_nonneg (exponentialTest_nonneg _ _ _ _) hA.le
      dsimp [weighted] at *
      linarith)
  change (∫ ω, weighted θ W p ω ∂μ) ≤
    (∫ ω, T ω/A+Gᶜ.indicator (fun _ => (1:ℝ)) ω ∂μ) at hh
  rw [integral_add (hTi.div_const A) hbad,integral_div,
    integral_indicator hG.compl,setIntegral_const] at hh
  simpa only [smul_eq_mul,mul_one] using hh

theorem tilted_kernel_lower_window (μ : Measure Ω) [IsProbabilityMeasure μ]
    {W p : Ω → ℝ} {Y : Ω → ℤ}
    (hW : Measurable W) (hY : Measurable Y) (hp : Measurable p)
    {θ lo hi ℓ : ℝ} (hθ : 0 ≤ θ) (hℓ : 0 ≤ ℓ)
    (hpb : ∀ᵐ ω ∂μ,p ω ∈ Icc (0 : ℝ) 1)
    (hpos : ∀ᵐ ω ∂μ,0 < p ω → 0 ≤ W ω)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ᵐ ω ∂μ,ω ∈ G → Y ω=0 → W ω ∈ Icc lo hi → ℓ ≤ p ω) :
    Real.exp (-θ*hi)*ℓ*
      (μ.real {ω | W ω ∈ Icc lo hi ∧ Y ω=0}-μ.real Gᶜ) ≤
        ∫ ω,weighted θ W p ω ∂μ := by
  let E := {ω | W ω ∈ Icc lo hi ∧ Y ω=0}
  let L := Real.exp (-θ*hi)*ℓ
  have hL : 0 ≤ L := mul_nonneg (Real.exp_pos _).le hℓ
  have hE : MeasurableSet E := (measurableSet_Icc.preimage hW).inter
    (measurableSet_eq_fun hY measurable_const)
  have hpi := integrable_weighted μ hW hp hθ hpb hpos
  have hEi : Integrable (E.indicator (fun _ => L)) μ := (integrable_const L).indicator hE
  have hBi : Integrable (Gᶜ.indicator (fun _ => L)) μ := (integrable_const L).indicator hG.compl
  have hpoint : ∀ᵐ ω ∂μ,E.indicator (fun _ => L) ω ≤
      weighted θ W p ω+Gᶜ.indicator (fun _ => L) ω := by
    filter_upwards [hpb,hgood] with ω hpω hgω
    have hwp : 0 ≤ weighted θ W p ω := mul_nonneg (Real.exp_pos _).le hpω.1
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      by_cases hg : ω ∈ G
      · rw [indicator_of_notMem (show ω ∉ Gᶜ from by simpa using hg),add_zero]
        have hpℓ := hgω hg he.2 he.1
        have hexp : Real.exp (-θ*hi) ≤ Real.exp (-θ*W ω) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left he.1.2 (neg_nonpos.mpr hθ)
        exact mul_le_mul hexp hpℓ hℓ (Real.exp_pos _).le
      · rw [indicator_of_mem (show ω ∈ Gᶜ from hg)]
        linarith
    · rw [indicator_of_notMem he]
      have hb : 0 ≤ Gᶜ.indicator (fun _ => L) ω := by
        by_cases hg : ω ∈ Gᶜ <;> simp [hg,hL]
      linarith
  have hh := integral_mono_ae hEi (hpi.add hBi) hpoint
  change (∫ ω, E.indicator (fun _ => L) ω ∂μ) ≤
    (∫ ω, weighted θ W p ω+Gᶜ.indicator (fun _ => L) ω ∂μ) at hh
  rw [integral_indicator hE,setIntegral_const,
    integral_add hpi hBi,integral_indicator hG.compl,setIntegral_const] at hh
  dsimp [L,E] at hh
  nlinarith

theorem rare_ratio_of_tilted_bounds {C R CT RT I n c U : ℝ}
    (hscaleC : C=Real.exp (-I)*CT) (hscaleR : R=Real.exp (-I)*RT)
    (hn : 0 < n) (hc : 0 < c) (hU : 0 ≤ U)
    (hC : c/n^2 ≤ CT) (hR : RT ≤ U/n^3) (hR0 : 0 ≤ RT) :
    0 < C ∧ 0 ≤ R/C ∧ R/C ≤ (U/c)/n := by
  have hCT : 0 < CT := (div_pos hc (sq_pos_of_pos hn)).trans_le hC
  have hCpos : 0 < C := by rw [hscaleC]; exact mul_pos (Real.exp_pos _ ) hCT
  have hratio : R/C=RT/CT := by
    rw [hscaleC,hscaleR]
    field_simp [(Real.exp_pos (-I)).ne',hCT.ne']
  refine ⟨hCpos,?_,?_⟩
  · rw [hratio]
    exact div_nonneg hR0 hCT.le
  · rw [hratio]
    calc
      RT/CT ≤ (U/n^3)/CT := div_le_div_of_nonneg_right hR hCT.le
      _ ≤ (U/n^3)/(c/n^2) := div_le_div_of_nonneg_left
        (div_nonneg hU (pow_nonneg hn.le 3)) (div_pos hc (sq_pos_of_pos hn)) hC
      _ = (U/c)/n := by field_simp [hn.ne',hc.ne']

end FCAppendix.Affine.Uniform06.CoarseIntegralBounds
