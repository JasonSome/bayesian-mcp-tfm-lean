import FCAppendix.Affine.Uniform06.GlobalDerivativeReplacement
import FCAppendix.Affine.Uniform06.FixedPriceCanonicalRows
import FCAppendix.Affine.Uniform06.ClampedMomentBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralDerivativeMoments

open Set MeasureTheory LowBody
open scoped BigOperators
open FixedPriceRawDerivative
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource
open LiteralCoarsePath LiteralKernelIdentity RawMomentPartition GlobalDerivativeReplacement
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open RawPathAdapter ReciprocalSecantBounds RareEmpiricalReplacement

variable {N : ℕ}

def rowStrictMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  branchWeight (xi i) g' T B*
    (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
      (fun p => strictPower q (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ p) 0))

def mainRowVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  branchWeight (xi i) g' T B*
    (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect (fun p =>
      (q:ℝ)*(complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^(q-1)*
        ActualRootDerivative.derivative (xi i) (small T)
          (maskedBids T B (finalSet (imbalance T) ∅ p)) 0 b)

lemma literalMoment_eq_exp_rowStrictMoment (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    literalMoment i c g cm b θ q ω=
      Real.exp (-θ*deficit i b c ω)*rowStrictMoment i c g cm b q ω := by
  dsimp only [literalMoment,rowStrictMoment]
  have hcost : deficit i b c ω=(c:ℝ)-FiniteMarkedExchangeability.sumX (RawMixedSource.demand (xi i) b) ω := rfl
  rw [hcost]
  ring

theorem original_path_reciprocal_lower (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo b γ : ℝ} (hlo : 0< lo) (hlb : lo≤ b)
    (hbL : b≤ g.multiplier) (hN : 0< N)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival)
    (hemp : γ+(imbalance (patternTemplate c (fun j => (ω j).1)):ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω)
    (hbranch : 0< branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω))
    (p : Path (Fin (N+1)) (imbalance (patternTemplate c (fun j => (ω j).1))))
    (hp : 0<(pathLaw (weights (xi i) g (patternTemplate c (fun j => (ω j).1))
      (rowBids b ω)) (imbalance (patternTemplate c (fun j => (ω j).1))) ∅).mass p) :
    γ*(N:ℝ)≤ reciprocalSum
      (maskedBids (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)
        (finalSet (imbalance (patternTemplate c (fun j => (ω j).1))) ∅ p)) {0} b := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let E := finalSet (imbalance T) ∅ p
  have hg := branch_path_geometry {g with countMargin:=cm (fun j => (ω j).1)} T B 0 hε hM hr
    (by change b≤g.multiplier; exact hbL) hbranch p hp
  have h := MaskedReciprocal.masked_reciprocal_empirical_error c ω E hlo hlb hN b
    (ν:=empirical (FullReciprocalMean.reciprocal b) N ω)
  simp only [sub_self,abs_zero,zero_add] at h
  change |reciprocalSum (maskedBids T B E) {0} b/(N:ℝ)-
    empirical (FullReciprocalMean.reciprocal b) N ω|≤(E.card:ℝ)/(lo*(N:ℝ)) at h
  rw [hg.1] at h
  have hh := (abs_le.mp h).1
  change γ+(imbalance T:ℝ)/(lo*(N:ℝ))≤empirical (FullReciprocalMean.reciprocal b) N ω at hemp
  change γ*(N:ℝ)≤reciprocalSum (maskedBids T B E) {0} b
  apply (le_div_iff₀ (Nat.cast_pos.mpr hN : (0:ℝ)< N)).mp
  linarith

theorem original_main_row_errors (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo b U γ : ℝ} (hlo : 0< lo) (hlb : lo< b)
    (hU : 0≤ U) (hbU : b≤ U) (hbL : b≤ g.multiplier) (hγ : 0<γ) (hN : 0< N)
    (hclip : (1-xi i)*U≤ lo)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (hemp : γ+(imbalance (patternTemplate c (fun j => (ω j).1)):ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω) :
    |mainRowVelocity i c g cm b 1 ω-rowStrictMoment i c g cm b 0 ω/(xi i*b)|≤
      originalRowMarginal (xi i) c g cm b ω/(b-lo)+
        rowStrictMoment i c g cm b 0 ω/(xi i*b^2*γ*(N:ℝ)) ∧
    |mainRowVelocity i c g cm b 2 ω-2*originalRowMarginal (xi i) c g cm b ω/(xi i*b)|≤
      2*originalRowDuplicate (xi i) c g cm b ω/(b-lo)+
        2*originalRowMarginal (xi i) c g cm b ω/(xi i*b^2*γ*(N:ℝ)) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g' T B) (imbalance T) ∅
  let a := branchWeight (xi i) g' T B
  let p := fun s : Path (Fin (N+1)) (imbalance T) => complementMarginal (xi i) T B
    (finalSet (imbalance T) ∅ s) 0
  let V := fun s : Path (Fin (N+1)) (imbalance T) => ActualRootDerivative.derivative (xi i)
    (small T) (maskedBids T B (finalSet (imbalance T) ∅ s)) 0 b
  let Z := fun s : Path (Fin (N+1)) (imbalance T) => strictPower 0
    (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ s) 0)
  have hb := hlo.trans hlb
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hnR : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have he := original_row_path_moments (xi_pos i) hξ1 c g cm b hε hM hr hbL ω
  dsimp only at he
  have hC : originalRowMarginal (xi i) c g cm b ω=a*P.expect p := he.1
  have hR : originalRowDuplicate (xi i) c g cm b ω=a*P.expect (fun s => (p s)^2) := he.2
  have hZ : rowStrictMoment i c g cm b 0 ω=a*P.expect Z := rfl
  have hV1 : mainRowVelocity i c g cm b 1 ω=a*P.expect V := by
    simp only [mainRowVelocity,Nat.cast_one,Nat.sub_self,pow_zero,one_mul]
    rfl
  have hV2 : mainRowVelocity i c g cm b 2 ω=a*P.expect (fun s => 2*p s*V s) := by
    simp only [mainRowVelocity,Nat.cast_ofNat,Nat.reduceSub,pow_one]
    rfl
  have ha := branchWeight_bounds (xi i) g' T B
  by_cases haz : a=0
  · simp only [hC,hR,hZ,hV1,hV2,haz,zero_mul,mul_zero,zero_div,sub_self,abs_zero,add_zero,le_refl,and_self]
  · have hap : 0< a := lt_of_le_of_ne ha.1 (Ne.symm haz)
    have hpoint (s) (hs : 0< P.mass s) :
        |V s-Z s/(xi i*b)|≤ p s/(b-lo)+Z s/(xi i*b^2*γ*(N:ℝ)) ∧
        |2*p s*V s-2*p s/(xi i*b)|≤2*(p s)^2/(b-lo)+2*p s/(xi i*b^2*γ*(N:ℝ)) := by
      let E := finalSet (imbalance T) ∅ s
      let B' := maskedBids T B E
      have hgeo := branch_path_geometry g' T B 0 hε hM hr
        (by change b≤g.multiplier; exact hbL) hap s hs
      have hB0 : B' 0=b := by
        change (if (0:Fin (N+1))∈T.support\E then B 0 else 0)=b
        rw [if_pos (Finset.mem_sdiff.mpr ⟨focal_mem c ω,hgeo.2⟩)]
        rfl
      have hBU : ∀ j,B' j≤ U := by
        intro j
        unfold B' maskedBids
        split_ifs
        · change rowBids b ω j≤U
          refine Fin.cases (by change b≤U; exact hbU) (fun z => ?_) j
          change (if (ω z).1=0 then (ω z).2 else 0)≤U
          by_cases ht : (ω z).1=0
          · simpa only [if_pos ht] using hcap z ht
          · simpa only [if_neg ht] using hU
        · exact hU
      have hrec := original_path_reciprocal_lower i c g cm hlo hlb.le hbL hN hε hM hr ω hemp hap s hs
      have hD : (small T:ℝ)-remainingDemand (xi i) B' {0} b=focalDeficit (xi i) T B E 0 := by
        rw [LiteralCoarsePath.masked_demand_eq (ξ:=xi i) T B E 0 hb (rowBids_outside c b ω)]
        rfl
      have hf := actual_global_velocity_error (xi_pos i) hξ1 hlo hγ hnR (small T) B' 0
        (by simpa only [hB0] using hlb) hBU hclip (by simpa only [hB0] using hrec)
      have hsquare := actual_global_square_velocity_error (xi_pos i) hξ1 hlo hγ hnR
        (small T) B' 0 (by simpa only [hB0] using hlb) hBU hclip (by simpa only [hB0] using hrec)
      dsimp only at hf hsquare
      rw [hB0,hD] at hf
      rw [hB0] at hsquare
      constructor
      · convert! hf using 1
      · convert! hsquare using 1
    have hfirst := (abs_expect_le P (fun s => V s-Z s/(xi i*b))).trans
      (expect_le_of_support P _ _ (fun s hs => (hpoint s hs).1))
    have hsecond := (abs_expect_le P (fun s => 2*p s*V s-2*p s/(xi i*b))).trans
      (expect_le_of_support P _ _ (fun s hs => (hpoint s hs).2))
    have hf := mul_le_mul_of_nonneg_left hfirst ha.1
    have hs := mul_le_mul_of_nonneg_left hsecond ha.1
    simp only [expect_sub,expect_add,div_eq_mul_inv,expect_mul_const,expect_const_mul] at hf hs
    constructor
    · rw [hC,hZ,hV1]
      convert! hf using 1
      · have hid : a*P.expect V-a*P.expect Z/(xi i*b)=
            a*(P.expect V-P.expect Z*(xi i*b)⁻¹) := by ring
        rw [hid,abs_mul,abs_of_nonneg ha.1]
      · ring
    · rw [hC,hR,hV2]
      convert! hs using 1
      · have hid : a*P.expect (fun s => 2*p s*V s)-2*(a*P.expect p)/(xi i*b)=
            a*(P.expect (fun s => 2*p s*V s)-2*P.expect p*(xi i*b)⁻¹) := by ring
        rw [hid,abs_mul,abs_of_nonneg ha.1]
      · ring

end FCAppendix.Affine.Uniform06.LiteralDerivativeMoments
