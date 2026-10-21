import FCAppendix.Affine.Uniform06.PhysicalSourceMoments

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralRootWindow

open MeasureTheory Set LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open LiteralCoarsePath
open RawMomentPartition RawPathAdapter RawPathRootReplacement PhysicalSourceMoments
open RelativeRootWindow FiniteSampledLaplace RareEmpiricalReplacement
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling

lemma finite_half_tail {Ω : Type*} [Fintype Ω] (P : FCAppendix.FiniteLaw Ω)
    (D : Ω → ℝ) {W α θ H : ℝ} (hα : 0≤α) (hθ : 0≤θ) (hH : 0≤ H)
    (hDW : ∀ p,0< P.mass p → D p≤ W) (q : ℕ) :
    Real.exp (-θ*W)*α*P.expect (fun p => tailPower q H (D p))≤
      Real.exp (-θ*H/2)*(Real.exp (-(θ/2)*W)*α*
        P.expect (fun p => strictPower q (D p))) := by
  rw [← FCAppendix.FiniteLaw.expect_const_mul,
    ← FCAppendix.FiniteLaw.expect_const_mul,
    ← FCAppendix.FiniteLaw.expect_const_mul]
  apply expect_le_of_support
  intro p hp
  by_cases hD : H< D p
  · have hDp : 0< D p := hH.trans_lt hD
    have he : Real.exp (-θ*W)≤ Real.exp (-θ*H/2)*Real.exp (-(θ/2)*W) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hD.le.trans (hDW p hp)) hθ]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hα)
      (pow_nonneg hDp.le q)
    simpa only [tailPower,if_pos hD,strictPower,if_pos hDp,mul_assoc] using hh
  · simp only [tailPower,if_neg hD,mul_zero]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hα) (strictPower_nonneg _ _))

variable {N : ℕ} [Nonempty (Fin N)]

theorem actual_literal_window (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo U b H γ ν z θ : ℝ}
    (hlo : 0< lo) (hU : 0< U) (hlb : lo< b) (hbU : b≤ U)
    (hclip : (1-xi i)*U≤ lo) (hγ : 0<γ) (hγν : γ≤ν)
    (hz : 0< z) (hH : 0≤ H) (hN : 0< N) (hθ : 0≤θ)
    (hbL : b≤ g.multiplier) (hr : 0< g.requiredDemand)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (hh : imbalanceSum ω=0 ∨ ∀ j,0≤ rawH (xi i) b (ω j))
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (hemp : γ+((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω)
    (hsmall : H*(xi i)^2*b<(b-lo)^2*γ*(N:ℝ))
    (hzΛ : z≤ b-xi i*H/(γ*(N:ℝ))) (q : Fin 2) :
    let K := xi i/((b-lo)*γ)
    let M := H/(b*γ)
    let E := H/(b^2*γ^2)*(1/(N:ℝ)+b*(
      |empirical (FullReciprocalMean.reciprocal b) N ω-ν|+
        ((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))+
          empirical (FullReciprocalMean.window z b) N ω/z))
    |(N:ℝ)^(q.val+1)*physicalMoment i c g cm b θ (q.val+1) ω-
      (1/(b*ν))^(q.val+1)*literalMoment i c g cm b θ (q.val+1) ω|≤
      (if q.val=0 then 1 else 2*M)*E*literalMoment i c g cm b θ 0 ω+
        (K^(q.val+1)+(1/(b*ν))^(q.val+1))*Real.exp (-θ*H/2)*
          literalMoment i c g cm b (θ/2) (q.val+1) ω := by
  dsimp only
  have hb : 0< b := hlo.trans hlb
  let k := (imbalanceSum ω).natAbs
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let α := branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)} T B
  let e := Real.exp (-θ*deficit i b c ω)*α
  let P := pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅
  let D := selectedDeficit i c b ω k
  have hα : 0≤α := (LiteralCoarsePath.branchWeight_bounds _ _ _ _).1
  have he : 0≤ e := mul_nonneg (Real.exp_pos _).le hα
  have hw := actual_path_power_window i c g hlo hU hlb hbU hclip hγ hγν hz hH he
    hN ω hc hcap k rfl hW hemp hsmall hzΛ q
  have hD (p : Path (Fin N) k) (_hp : 0< P.mass p) : D p≤ deficit i b c ω := by
    have hh' : 0≤∑ j,rawH (xi i) b (ω (PathNumerator.tuple k p j)) := by
      rcases hh with hzero | hpos
      · have hk0 : k=0 := by simp only [k,hzero,Int.natAbs_zero]
        haveI : IsEmpty (Fin k) := by rw [hk0]; infer_instance
        simp only [Finset.univ_eq_empty,Finset.sum_empty,le_refl]
      · exact Finset.sum_nonneg (fun j _ => hpos _)
    dsimp only [D,selectedDeficit,deficit,FCAppendix.ExponentialTilt.iidSum]
    change (c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω-
      (∑ j,rawH (xi i) b (ω (PathNumerator.tuple k p j)))≤
        (c:ℝ)-FiniteMarkedExchangeability.sumX (demand (xi i) b) ω
    linarith
  have ht := finite_half_tail P D hα hθ hH hD (q.val+1)
  have hq : (N:ℝ)^(q.val+1)*physicalMoment i c g cm b θ (q.val+1) ω=
      e*P.expect (fun p => ((N:ℝ)*selectedResponse i c b ω k p)^(q.val+1)) := by
    rw [physicalMoment_eq_rival i c g cm hbL hr θ _ ω hc hW]
    simp_rw [mul_pow]
    rw [FCAppendix.FiniteLaw.expect_const_mul]
    dsimp only [e,α,P,T,B,k]
    ring
  have hd (r : ℕ) (t : ℝ) : literalMoment i c g cm b t r ω=
      Real.exp (-t*deficit i b c ω)*α*P.expect (fun p => strictPower r (D p)) :=
    literalMoment_eq_rival_expect i c g cm hb hbL hr t r ω hc hW
  rw [hq,hd (q.val+1) θ,hd 0 θ,hd (q.val+1) (θ/2)]
  have hK : 0≤(xi i/((b-lo)*γ))^(q.val+1)+(1/(b*ν))^(q.val+1) := by
    have hν := hγ.trans_le hγν
    have hξ := xi_pos i
    positivity
  have htail := mul_le_mul_of_nonneg_left ht hK
  change |e*P.expect (fun p => ((N:ℝ)*selectedResponse i c b ω k p)^(q.val+1))-
      e*(1/(b*ν))^(q.val+1)*P.expect (fun p => strictPower (q.val+1) (D p))|≤ _ at hw
  dsimp only [e] at hw htail ⊢
  rw [show (1/(b*ν))^(q.val+1)*
      (Real.exp (-θ*deficit i b c ω)*α*P.expect (fun p => strictPower (q.val+1) (D p)))=
      Real.exp (-θ*deficit i b c ω)*α*(1/(b*ν))^(q.val+1)*
        P.expect (fun p => strictPower (q.val+1) (D p)) by ring]
  dsimp only [P,D,k] at hw htail ⊢
  nlinarith only [hw,htail]

end FCAppendix.Affine.Uniform06.LiteralRootWindow
