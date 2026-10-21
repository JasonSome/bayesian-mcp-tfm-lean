import FCAppendix.Affine.Uniform06.RawPathAdapter
import FCAppendix.Affine.Uniform06.FiniteRootReplacements

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawPathRootReplacement

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMarkedLaplace RawTiltedSource RawMixedSource
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open PathNumerator ZeroWeightFocal FiniteSampledLaplace RawPathAdapter
open FiniteMarkedExchangeability ReciprocalSecantBounds EntryOwnImpact CanonicalCoarse
open FiniteRootReplacements RareEmpiricalReplacement

variable {N : ℕ} [Nonempty (Fin N)]

def selectedDeficit (i : Row) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival)
    (k : ℕ) (p : Path (Fin N) k) : ℝ :=
  (c:ℝ)-sumX (RawMixedSource.demand (xi i) b) ω-∑ j,rawH (xi i) b (ω (tuple k p j))

def selectedVelocity (i : Row) (c : ℕ) (b : ℝ) (ω : Fin N → RowRival)
    (k : ℕ) (p : Path (Fin N) k) : ℝ :=
  ActualRootDerivative.derivative (xi i) (small (patternTemplate c (fun j => (ω j).1)))
    (selectedProfile c b ω (finalSet k ∅ p)) 0 b

lemma finite_window_small {ξ lo b R γ N H : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < lo) (hlb : lo < b) (hγ : 0 < γ) (hN : 0 < N)
    (hR : γ*N ≤ R) (hsmall : H*ξ^2*b < (b-lo)^2*γ*N) :
    H/gain ξ lo b R < (b-lo)/(ξ*b) := by
  have hb := hlo.trans hlb
  have hR0 := (mul_pos hγ hN).trans_le hR
  have hden := mul_pos (sub_pos.mpr hlb) hR0
  have he : H/gain ξ lo b R=H*ξ/((b-lo)*R) := by
    unfold gain
    field_simp [hξ.ne',hden.ne']
  rw [he]
  apply (div_lt_div_iff₀ hden (mul_pos hξ hb)).mpr
  have hm := mul_le_mul_of_nonneg_left hR (sq_nonneg (b-lo))
  nlinarith

theorem actual_path_window_errors (i : Row) (c : ℕ) (g : GuardData)
    {lo U b H γ ν a : ℝ} (hlo : 0 < lo) (hU : 0 < U) (hlb : lo < b)
    (hbU : b ≤ U) (hclip : (1-xi i)*U ≤ lo)
    (hγ : 0 < γ) (hγν : γ ≤ ν) (ha : 0 < a) (hN : 0 < N)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hcap : ∀ j,(ω j).1=0 → (ω j).2 ≤ U)
    (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ) < totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0 < (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p)
    (hemp : γ+(k:ℝ)/(lo*(N:ℝ)) ≤ empirical (FullReciprocalMean.reciprocal b) N ω)
    (hsmall : H*(xi i)^2*b < (b-lo)^2*γ*(N:ℝ))
    (haΛ : a ≤ b-xi i*H/(γ*(N:ℝ)))
    (hD : 0 < selectedDeficit i c b ω k p) (hDH : selectedDeficit i c b ω k p ≤ H) :
    let D := selectedDeficit i c b ω k p
    let P := selectedResponse i c b ω k p
    let V := selectedVelocity i c b ω k p
    let E := |empirical (FullReciprocalMean.reciprocal b) N ω-ν|+
      (k:ℝ)/(lo*(N:ℝ))+empirical (FullReciprocalMean.window a b) N ω/a
    P ∈ Ioo (0:ℝ) 1 ∧
      |(N:ℝ)*P-D/(b*ν)| ≤ H/(b^2*γ^2)*(1/(N:ℝ)+b*E) ∧
      (N:ℝ)*P ∈ Icc (0:ℝ) (H/(b*γ)) ∧
      |V-1/(xi i*b)| ≤ (H+1/xi i)/(b^2*γ*(N:ℝ)) ∧
      0 ≤ V ∧ V ≤ 1/(xi i*b) := by
  dsimp only
  let T := patternTemplate c (fun j => (ω j).1)
  let E := liftSet (finalSet k ∅ p)
  let B := selectedProfile c b ω (finalSet k ∅ p)
  let R := reciprocalSum B {0} b
  let P := selectedResponse i c b ω k p
  let D := selectedDeficit i c b ω k p
  have hb : 0 < b := hlo.trans hlb
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hH : 0 ≤ H := hD.le.trans hDH
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hB0 : B 0=b := selectedProfile_focal c b ω _
  have hBU : ∀ j,B j ≤ U := selectedProfile_cap c hU.le hbU ω hcap _
  have hEcard : E.card=k := by
    rw [liftSet_card]
    have hh := finalSet_card (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
      k ∅ (by simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hW) p hp
    simpa only [Finset.card_empty,zero_add] using hh
  have hidentity : (small T:ℝ)-remainingDemand (xi i) B {0} b=D :=
    selected_deficit_identity i c g hb ω hc k hk hW p hp
  have hRerror := MaskedReciprocal.masked_reciprocal_empirical_error c ω E hlo hlb.le hN b
    (ν:=empirical (FullReciprocalMean.reciprocal b) N ω)
  simp only [sub_self,abs_zero,zero_add,hEcard] at hRerror
  change |R/(N:ℝ)-empirical (FullReciprocalMean.reciprocal b) N ω| ≤
    (k:ℝ)/(lo*(N:ℝ)) at hRerror
  have hR : γ*(N:ℝ) ≤ R := by
    have hl : γ ≤ R/(N:ℝ) := by
      have he := (abs_le.mp hRerror).1
      linarith
    exact (le_div_iff₀ hNr).mp hl
  have hR0 := (mul_pos hγ hNr).trans_le hR
  have hsmall' := finite_window_small (xi_pos i) hlo hlb hγ hNr hR hsmall
  have hg := actual_window_geometry (xi_pos i) hξ1 hlo (small T) B 0
    (by simpa only [hB0] using hlb) hBU hclip
    (by simpa only [hB0] using hR0) (by simpa only [hB0,hidentity] using hD)
    (by simpa only [hB0,hidentity] using hDH) (by simpa only [hB0] using hsmall')
  dsimp only at hg
  simp only [hB0] at hg
  have hsec := actual_secant_boundary_replacement (xi_pos i) hξ1 hlo hNr ha hγ
    (small T) B 0 (by simpa only [hB0] using hlb) hBU hclip
    (by simpa only [hB0] using hR) (by simpa only [hB0,hidentity] using hD)
    (by simpa only [hB0,hidentity] using hDH) (by simpa only [hB0] using hsmall')
    (by simpa only [hB0] using haΛ) (ν:=ν)
  simp only [hB0] at hsec
  have hraw := MaskedReciprocal.masked_reciprocal_empirical_error c ω E hlo hlb.le hN b (ν:=ν)
  rw [hEcard] at hraw
  have hbd := MaskedReciprocal.masked_boundary_empirical_bound (b:=b) c ω E ha hN b
  have hsecb := hsec.trans (add_le_add hraw hbd)
  let Kbar := rightSecant (xi i) B {0} (b*(1-xi i*P)) b
  let K := ActualRootDerivative.reciprocal (xi i) B 0 (b*(1-xi i*P))
  have hKbar : γ ≤ Kbar/(N:ℝ) := (le_div_iff₀ hNr).mpr (hR.trans hg.2.2.2.1)
  have heq : P=D/(1+b*Kbar) := by
    have hresponse := hg.2.2.2.2.2.1
    rw [hidentity] at hresponse
    convert! hresponse using 1
  have hnorm := normalized_response_error hNr hb hγ hγν hKbar hD.le hDH heq
  have hPunit : P ∈ Icc (0:ℝ) 1 := ⟨hg.1.1.le,hg.1.2.le⟩
  have hK : γ*(N:ℝ) ≤ K := hR.trans hg.2.2.2.2.1
  have hPup : P ≤ D/(b*γ*(N:ℝ)) := by
    rw [heq]
    have hKbarN := (le_div_iff₀ hNr).mp hKbar
    apply div_le_div_of_nonneg_left hD.le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hKbarN hb.le]
  have hvel : selectedVelocity i c b ω k p=impact (xi i) b P K := hg.2.2.2.2.2.2
  have hv := impact_window_error hNr (xi_pos i) hξ1 hb hγ hK hPunit hPup hDH
  have hvb := impact_error (xi_pos i) hξ1 hb hPunit ((mul_pos hγ hNr).trans_le hK)
  refine ⟨hg.1,?_,hnorm.2,by simpa only [hvel] using hv,?_,?_⟩
  · exact hnorm.1.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsecb hb.le))
      (by positivity : 0 ≤ H/(b^2*γ^2)))
  · simpa only [hvel] using hvb.1
  · simpa only [hvel] using hvb.2.1

theorem actual_path_nonpositive (i : Row) (c : ℕ) (g : GuardData) {b : ℝ} (hb : 0 < b)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω) (k : ℕ) (hk : k=(imbalanceSum ω).natAbs)
    (hW : (k:ℝ) < totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (p : Path (Fin N) k)
    (hp : 0 < (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅).mass p)
    (hD : selectedDeficit i c b ω k p ≤ 0) :
    selectedResponse i c b ω k p=0 ∧ selectedVelocity i c b ω k p=0 := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := selectedProfile c b ω (finalSet k ∅ p)
  have hB0 : B 0=b := selectedProfile_focal c b ω _
  have hξ1 : xi i < 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hp0 := (EqualCapacity.positiveMarginal_spec (xi i) (small T) (xi_pos i) hξ1 B).1 0
  have heq := selected_deficit_identity i c g hb ω hc k hk hW p hp
  change (small T:ℝ)-remainingDemand (xi i) B {0} b=selectedDeficit i c b ω k p at heq
  have hzero : EqualCapacity.positiveMarginal (xi i) (small T) B 0=0 := by
    apply le_antisymm _ hp0
    by_contra hn
    have hpos := lt_of_not_ge hn
    have hh := actual_positive_implies_deficit_positive (xi_pos i) hξ1 (small T) B 0
      (by simpa only [hB0] using hb) hpos
    simp only [hB0] at hh
    rw [heq] at hh
    exact (not_lt_of_ge hD) hh
  refine ⟨hzero,?_⟩
  have hu : Function.update B 0 b=B := by rw [← hB0]; exact Function.update_eq_self _ _
  change ActualRootDerivative.derivative (xi i) (small T) B 0 b=0
  simp only [ActualRootDerivative.derivative,ActualRootDerivative.marginal,
    hu,hzero,lt_self_iff_false,false_and,if_false]

end FCAppendix.Affine.Uniform06.RawPathRootReplacement
