import FCAppendix.Affine.Uniform06.RawPathRootReplacement
import FCAppendix.Affine.Uniform06.RootFlatFaces

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RawPathGlobalResponse

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMarkedLaplace RawTiltedSource RawMixedSource
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open FiniteSampledLaplace RawPathAdapter RawPathRootReplacement ZeroWeightFocal
open CanonicalCoarse ReciprocalSecantBounds RareEmpiricalReplacement

variable {N : ℕ} [Nonempty (Fin N)]

theorem actual_strict_positive_iff (i : Row) (c : ℕ) (g : GuardData)
    {b : ℝ} (hb : 0< b) (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ)< totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0<(pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p) :
    0< selectedResponse i c b ω k p ↔ 0< selectedDeficit i c b ω k p := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := selectedProfile c b ω (finalSet k ∅ p)
  have hB0 : B 0=b := selectedProfile_focal c b ω _
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have he := selected_deficit_identity i c g hb ω hc k hk hW p hp
  change (small T:ℝ)-remainingDemand (xi i) B {0} b=selectedDeficit i c b ω k p at he
  constructor
  · intro hpos
    have hh := actual_positive_implies_deficit_positive (xi_pos i) hξ1 (small T) B 0
      (by simpa only [hB0] using hb) hpos
    simpa only [hB0,he] using hh
  · intro hD
    have hP := (EqualCapacity.positiveMarginal_spec (xi i) (small T) (xi_pos i) hξ1 B).1 0
    apply lt_of_le_of_ne hP
    intro hzero
    have hu : Function.update B 0 b=B := by
      rw [← hB0]
      exact Function.update_eq_self _ _
    have hh := RootFlatFaces.zero_implies_capacity_le (xi_pos i) hξ1 (small T) B 0 hb
      (by simpa only [ActualRootDerivative.marginal,hu] using hzero.symm)
    have hnot : selectedDeficit i c b ω k p≤0 := by
      rw [← he]
      linarith
    exact (not_lt_of_ge hnot) hD

theorem selected_reciprocal_lower (i : Row) (c : ℕ) (g : GuardData)
    {lo b γ : ℝ} (hlo : 0< lo) (hlb : lo≤ b) (hN : 0< N)
    (ω : Fin N → RowRival) (k : ℕ)
    (hW : (k:ℝ)< totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0<(pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p)
    (hemp : γ+(k:ℝ)/(lo*(N:ℝ))≤ empirical (FullReciprocalMean.reciprocal b) N ω) :
    γ*(N:ℝ)≤ reciprocalSum (selectedProfile c b ω (finalSet k ∅ p)) {0} b := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hcard : (liftSet (finalSet k ∅ p)).card=k := by
    rw [liftSet_card]
    have hh := finalSet_card (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
      k ∅ (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW) p hp
    simpa only [Finset.card_empty,zero_add] using hh
  have he := MaskedReciprocal.masked_reciprocal_empirical_error c ω
    (liftSet (finalSet k ∅ p)) hlo hlb hN b
    (ν:=empirical (FullReciprocalMean.reciprocal b) N ω)
  simp only [sub_self,abs_zero,zero_add,hcard] at he
  have hl := (abs_le.mp he).1
  change -((k:ℝ)/(lo*(N:ℝ))) ≤
    reciprocalSum (selectedProfile c b ω (finalSet k ∅ p)) {0} b/(N:ℝ)-
      empirical (FullReciprocalMean.reciprocal b) N ω at hl
  apply (le_div_iff₀ hNr).mp
  change γ≤ reciprocalSum (selectedProfile c b ω (finalSet k ∅ p)) {0} b/(N:ℝ)
  linarith

theorem actual_global_response_bound (i : Row) (c : ℕ) (g : GuardData)
    {lo U b γ : ℝ} (hlo : 0< lo) (hU : 0≤ U) (hlb : lo< b)
    (hbU : b≤ U) (hclip : (1-xi i)*U≤ lo) (hγ : 0<γ) (hN : 0< N)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ)< totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0<(pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p)
    (hemp : γ+(k:ℝ)/(lo*(N:ℝ))≤ empirical (FullReciprocalMean.reciprocal b) N ω) :
    0≤(N:ℝ)*selectedResponse i c b ω k p ∧
      (N:ℝ)*selectedResponse i c b ω k p≤
        xi i/((b-lo)*γ)*max 0 (selectedDeficit i c b ω k p) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := selectedProfile c b ω (finalSet k ∅ p)
  let R := reciprocalSum B {0} b
  have hb : 0< b := hlo.trans hlb
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hB0 : B 0=b := selectedProfile_focal c b ω _
  have hR : γ*(N:ℝ)≤ R := selected_reciprocal_lower i c g hlo hlb.le hN ω k hW p hp hemp
  have hRpos : 0< R := (mul_pos hγ hNr).trans_le hR
  have he := selected_deficit_identity i c g hb ω hc k hk hW p hp
  change (small T:ℝ)-remainingDemand (xi i) B {0} b=selectedDeficit i c b ω k p at he
  have hu := actual_marginal_upper (xi_pos i) hξ1 hlo (small T) B 0
    (by simpa only [hB0] using hlb) (selectedProfile_cap c hU hbU ω hcap _)
    hclip (by simpa only [hB0] using hRpos)
  simp only [hB0,he] at hu
  have hgain : (b-lo)*γ*(N:ℝ)/(xi i)≤ gain (xi i) lo b R := by
    unfold gain
    apply div_le_div_of_nonneg_right _ (xi_pos i).le
    nlinarith [mul_le_mul_of_nonneg_left hR (sub_pos.mpr hlb).le]
  have hgpos : 0<(b-lo)*γ*(N:ℝ)/(xi i) :=
    div_pos (mul_pos (mul_pos (sub_pos.mpr hlb) hγ) hNr) (xi_pos i)
  have hup := hu.trans (div_le_div_of_nonneg_left (le_max_left _ _) hgpos hgain)
  have hh := mul_le_mul_of_nonneg_left hup hNr.le
  refine ⟨mul_nonneg hNr.le
    ((EqualCapacity.positiveMarginal_spec (xi i) (small T) (xi_pos i) hξ1 B).1 0),?_⟩
  convert! hh using 1
  field_simp [hNr.ne',(xi_pos i).ne',hγ.ne',(sub_pos.mpr hlb).ne']

end FCAppendix.Affine.Uniform06.RawPathGlobalResponse
