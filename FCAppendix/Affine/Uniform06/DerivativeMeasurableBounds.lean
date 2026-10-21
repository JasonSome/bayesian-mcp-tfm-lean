import FCAppendix.Affine.Uniform06.GuardVelocityRareBound
import FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral
import FCAppendix.Affine.Uniform06.EqualOnlyRareMoments

noncomputable section
namespace FCAppendix.Affine.Uniform06.DerivativeMeasurableBounds

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open LiteralCoarsePath LiteralKernelIdentity RawMomentPartition LiteralCoarseMeasurable
open LiteralGuardVelocity LiteralDerivativeMoments GlobalDerivativeReplacement
open FixedPriceCanonicalRows FixedPriceCanonicalIntegral FixedPriceRawDerivative
open GuardVelocityRareBound ClampedMomentBounds
open PhysicalSourceMoments RareEmpiricalReplacement LiteralPrefixStieltjes LiteralGuardRare
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling

variable {N : ℕ}

def tiltedMain (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  Real.exp (-θ*deficit i b c ω)*mainRowVelocity i c g cm b q ω

def tiltedGuard (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  Real.exp (-θ*deficit i b c ω)*guardRowVelocity i c g cm b q ω

def tiltedVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  Real.exp (-θ*deficit i b c ω)*rowVelocity (xi i) c g cm q b ω

lemma measurable_deficit (i : Row) (c : ℕ) (b : ℝ) : Measurable (deficit (N:=N) i b c) := by
  unfold deficit FCAppendix.ExponentialTilt.iidSum
  apply measurable_const.sub
  exact Finset.measurable_sum _ (fun j _ =>
    (measurable_demand (xi i) b).comp (measurable_pi_apply j))

theorem measurable_mainRowVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (q : ℕ) :
    Measurable (mainRowVelocity i c g cm b q) := by
  classical
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  apply measurable_pattern_choice (fun kind ω =>
    branchWeight (xi i) {g with countMargin:=cm kind} (patternTemplate c kind) (rowBids b ω)*
      (pathLaw (weights (xi i) {g with countMargin:=cm kind} (patternTemplate c kind)
        (rowBids b ω)) (imbalance (patternTemplate c kind)) ∅).expect (fun p =>
        (q:ℝ)*(complementMarginal (xi i) (patternTemplate c kind) (rowBids b ω)
          (finalSet (imbalance (patternTemplate c kind)) ∅ p) 0)^(q-1)*
        ActualRootDerivative.derivative (xi i) (small (patternTemplate c kind))
          (maskedBids (patternTemplate c kind) (rowBids b ω)
            (finalSet (imbalance (patternTemplate c kind)) ∅ p)) 0 b))
  intro kind
  let T := patternTemplate c kind
  let g' := {g with countMargin:=cm kind}
  have hB := measurable_raw_rowBids N b
  have hα : Measurable (fun ω : Fin N → RowRival => branchWeight (xi i) g' T (rowBids b ω)) := by
    by_cases he : T.residual₀=T.residual₁
    · simpa only [branchWeight,if_pos he] using
        (measurable_const : Measurable (fun _ : Fin N → RowRival => (1:ℝ)))
    · simpa only [branchWeight,if_neg he] using measurable_guard (xi i) g' T (rowBids b) hB
  apply hα.mul
  unfold FCAppendix.FiniteLaw.expect
  apply Finset.measurable_sum
  intro p _
  let E := finalSet (imbalance T) ∅ p
  have hm : Measurable (fun ω : Fin N → RowRival => maskedBids T (rowBids b ω) E) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j∈T.support\E
    · simpa only [maskedBids,if_pos hj] using hB j
    · simpa only [maskedBids,if_neg hj] using
        (measurable_const : Measurable (fun _ : Fin N → RowRival => (0:ℝ)))
  have hp := measurable_complement (xi_pos i) hξ1 T (rowBids b) hB E 0
  have hd := (RootDerivativeIntegral.measurable_derivative (xi i) (small T) 0
    (xi_pos i) hξ1).comp (show Measurable (fun ω : Fin N → RowRival => (maskedBids T (rowBids b ω) E,b)) from hm.prodMk measurable_const)
  exact (measurable_path_mass (fun ω => weights (xi i) g' T (rowBids b ω))
    (measurable_weights (xi i) g' T (rowBids b) hB) _ _ p).mul
      (((hp.pow_const (q-1)).const_mul (q:ℝ)).mul hd)

theorem measurable_guardRowVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (q : ℕ) :
    Measurable (guardRowVelocity i c g cm b q) := by
  classical
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  apply measurable_pattern_choice (fun kind ω =>
    if (patternTemplate c kind).residual₀=(patternTemplate c kind).residual₁ then 0 else
      GuardDerivative.velocity (xi i) {g with countMargin:=cm kind} (patternTemplate c kind)
        (rowBids 0 ω) 0 b * pathMoment (xi i) {g with countMargin:=cm kind}
          (patternTemplate c kind) (rowBids 0 ω) 0 q b)
  intro kind
  let T := patternTemplate c kind
  let g' := {g with countMargin:=cm kind}
  have hB := measurable_raw_rowBids N 0
  change Measurable (fun ω : Fin N → RowRival =>
    if T.residual₀=T.residual₁ then 0 else GuardDerivative.velocity (xi i) g' T
      (rowBids 0 ω) 0 b*pathMoment (xi i) g' T (rowBids 0 ω) 0 q b)
  by_cases he : T.residual₀=T.residual₁
  · simpa only [if_pos he] using
      (measurable_const : Measurable (fun _ : Fin N → RowRival => (0:ℝ)))
  · simp only [if_neg he]
    apply ((measurable_guard_velocity (xi i) g' T 0 b).comp
      (measurable_pi_lambda _ hB)).mul
    unfold pathMoment FCAppendix.FiniteLaw.expect
    apply Finset.measurable_sum
    intro p _
    exact (measurable_path_mass (fun ω => weights (xi i) g' T (rowBids 0 ω))
      (measurable_weights (xi i) g' T (rowBids 0) hB) _ _ p).mul
      ((measurable_complement (xi_pos i) hξ1 T
        (fun ω => Function.update (rowBids 0 ω) 0 b)
        (by
          have hu : Measurable (fun B : Fin (N+1)→ℝ => Function.update B 0 b) := measurable_update_left
          exact fun j => (measurable_pi_apply j).comp (hu.comp (measurable_pi_lambda _ hB)))
        _ 0).pow_const q)

theorem measurable_tiltedMain (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (tiltedMain i c g cm b θ q) :=
  (((measurable_deficit i c b).const_mul (-θ)).exp).mul (measurable_mainRowVelocity i c g cm b q)

theorem measurable_tiltedGuard (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (tiltedGuard i c g cm b θ q) :=
  (((measurable_deficit i c b).const_mul (-θ)).exp).mul (measurable_guardRowVelocity i c g cm b q)

theorem measurable_tiltedVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b θ : ℝ) (q : ℕ) :
    Measurable (tiltedVelocity i c g cm b θ q) := by
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  exact (((measurable_deficit i c b).const_mul (-θ)).exp).mul
    (measurable_rowVelocity (xi_pos i) hξ1 c g cm q b)

theorem main_bounded_by_strict_zero (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (q : ℕ) (ω : Fin N → RowRival) :
    0≤ mainRowVelocity i c g cm b q ω ∧
    mainRowVelocity i c g cm b q ω≤(q:ℝ)/(xi i*b)*rowStrictMoment i c g cm b 0 ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g' T B) (imbalance T) ∅
  let a := branchWeight (xi i) g' T B
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have ha := branchWeight_bounds (xi i) g' T B
  have hf0 (s : Path (Fin (N+1)) (imbalance T)) :
      0≤(q:ℝ)*(complementMarginal (xi i) T B (finalSet (imbalance T) ∅ s) 0)^(q-1)*
        ActualRootDerivative.derivative (xi i) (small T)
          (maskedBids T B (finalSet (imbalance T) ∅ s)) 0 b := by
    have hp := complement_bounds (xi_pos i) hξ1 T B (finalSet (imbalance T) ∅ s) 0
    have hv := ActualRootDerivative.actual_derivative_bounds (xi_pos i) hξ1 (small T)
      (maskedBids T B (finalSet (imbalance T) ∅ s)) 0 hb
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (pow_nonneg hp.1 _)) hv.1
  refine ⟨mul_nonneg ha.1 (expect_nonneg P _ hf0),?_⟩
  by_cases haz : a=0
  · change a*P.expect _≤(q:ℝ)/(xi i*b)*(a*P.expect _)
    simp only [haz,zero_mul,mul_zero,le_refl]
  have hap : 0< a := lt_of_le_of_ne ha.1 (Ne.symm haz)
  have hpoint (s : Path (Fin (N+1)) (imbalance T)) (hs : 0< P.mass s) :
      (q:ℝ)*(complementMarginal (xi i) T B (finalSet (imbalance T) ∅ s) 0)^(q-1)*
        ActualRootDerivative.derivative (xi i) (small T)
          (maskedBids T B (finalSet (imbalance T) ∅ s)) 0 b≤
      (q:ℝ)/(xi i*b)*strictPower 0 (focalDeficit (xi i) T B (finalSet (imbalance T) ∅ s) 0) := by
    let E := finalSet (imbalance T) ∅ s
    let B' := maskedBids T B E
    have he := branch_path_geometry g' T B 0 hε hM hr
      (by simpa only [B,rowBids,Fin.cons_zero] using hbL) hap s hs
    have hB0 : B' 0=b := by
      have hm : (0 : Fin (N+1)) ∈ T.support := focal_mem c ω
      have hn : (0 : Fin (N+1)) ∉ E := he.2
      simp only [B',maskedBids,if_pos (Finset.mem_sdiff.mpr ⟨hm,hn⟩)]
      rfl
    have hu : Function.update B' 0 b=B' := by rw [← hB0]; exact Function.update_eq_self _ _
    have hp := complement_bounds (xi_pos i) hξ1 T B E 0
    have hv := ActualRootDerivative.actual_derivative_bounds (xi_pos i) hξ1 (small T) B' 0 hb
    by_cases hD : 0< focalDeficit (xi i) T B E 0
    · rw [strictPower,if_pos hD,pow_zero,mul_one]
      have hp1 := pow_le_one₀ hp.1 hp.2 (n:=q-1)
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg q)) hv.2
        hv.1 (by positivity : 0≤(q:ℝ)*1)
      simpa only [div_eq_mul_inv,mul_one,one_mul] using! hh
    · have hp0 : complementMarginal (xi i) T B E 0=0 := by
        apply le_antisymm _ hp.1
        by_contra hn
        have hpos := (actual_positive_iff_deficit (xi_pos i) hξ1 (small T) B' 0
          (by simpa only [hB0] using hb)).mp (lt_of_not_ge hn)
        rw [hB0,masked_demand_eq (ξ := xi i) T B E 0 hb (rowBids_outside c b ω)] at hpos
        exact hD hpos
      have hd0 : ActualRootDerivative.derivative (xi i) (small T) B' 0 b=0 := by
        simp only [ActualRootDerivative.derivative,ActualRootDerivative.marginal,hu,
          show EqualCapacity.positiveMarginal (xi i) (small T) B' 0=0 from hp0,
          lt_self_iff_false,false_and,if_false]
      rw [hd0,mul_zero,strictPower,if_neg hD,mul_zero]
  have hh := mul_le_mul_of_nonneg_left (expect_le_of_support P _ _ hpoint) ha.1
  rw [FCAppendix.FiniteLaw.expect_const_mul] at hh
  convert! hh using 1
  dsimp only [mainRowVelocity,rowStrictMoment,a,P,g',T,B]
  ring

theorem tiltedMain_bounded_by_literal (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    0≤ tiltedMain i c g cm b θ q ω ∧
    tiltedMain i c g cm b θ q ω≤(q:ℝ)/(xi i*b)*literalMoment i c g cm b θ 0 ω := by
  have h := main_bounded_by_strict_zero i c g cm hb hbL hε hM hr q ω
  refine ⟨mul_nonneg (Real.exp_pos _).le h.1,?_⟩
  have hh := mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (-θ*deficit i b c ω)).le
  rw [literalMoment_eq_exp_rowStrictMoment]
  dsimp only [tiltedMain]
  nlinarith

theorem tiltedVelocity_eq_main_add_guard (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (ha : 0≤ g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    tiltedVelocity i c g cm b θ q ω=
      tiltedMain i c g cm b θ q ω+tiltedGuard i c g cm b θ q ω := by
  rw [tiltedVelocity,original_rowVelocity_eq_main_add_guard i c g cm hb hbL hlo ha hε hM hr q ω,
    mul_add]
  rfl

theorem tilted_main_row_errors (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo b U γ : ℝ} (hlo : 0< lo) (hlb : lo< b)
    (hU : 0≤ U) (hbU : b≤ U) (hbL : b≤ g.multiplier) (hγ : 0<γ) (hN : 0< N)
    (hclip : (1-xi i)*U≤ lo)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (ω : Fin N → RowRival) (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (hemp : γ+(imbalance (patternTemplate c (fun j => (ω j).1)):ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω) :
    |tiltedMain i c g cm b θ 1 ω-literalMoment i c g cm b θ 0 ω/(xi i*b)|≤
      physicalMoment i c g cm b θ 1 ω/(b-lo)+
        literalMoment i c g cm b θ 0 ω/(xi i*b^2*γ*(N:ℝ)) ∧
    |tiltedMain i c g cm b θ 2 ω-2*physicalMoment i c g cm b θ 1 ω/(xi i*b)|≤
      2*physicalMoment i c g cm b θ 2 ω/(b-lo)+
        2*physicalMoment i c g cm b θ 1 ω/(xi i*b^2*γ*(N:ℝ)) := by
  have h := original_main_row_errors i c g cm hlo hlb hU hbU hbL hγ hN hclip
    hε hM hr ω hcap hemp
  have hm := physicalMoment_one_two i c g cm hbL θ hε hM hr ω
  have he : 0≤ Real.exp (-θ*deficit i b c ω) := (Real.exp_pos _).le
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.1 he
    rw [literalMoment_eq_exp_rowStrictMoment,hm.1]
    dsimp only [tiltedMain]
    convert! hh using 1
    · rw [show Real.exp (-θ*deficit i b c ω)*rowStrictMoment i c g cm b 0 ω/(xi i*b)=
          Real.exp (-θ*deficit i b c ω)*(rowStrictMoment i c g cm b 0 ω/(xi i*b)) by ring,
        ← mul_sub,abs_mul,abs_of_nonneg he]
    · ring
  · have hh := mul_le_mul_of_nonneg_left h.2 he
    rw [hm.1,hm.2]
    dsimp only [tiltedMain]
    convert! hh using 1
    · rw [show 2*(Real.exp (-θ*deficit i b c ω)*originalRowMarginal (xi i) c g cm b ω)/(xi i*b)=
          Real.exp (-θ*deficit i b c ω)*(2*originalRowMarginal (xi i) c g cm b ω/(xi i*b)) by ring,
        ← mul_sub,abs_mul,abs_of_nonneg he]
    · ring

theorem tilted_main_error_envelopes (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (θ : ℝ) (ω : Fin N → RowRival) :
    |tiltedMain i c g cm b θ 1 ω-literalMoment i c g cm b θ 0 ω/(xi i*b)|≤
      2/(xi i*b)*literalMoment i c g cm b θ 0 ω ∧
    |tiltedMain i c g cm b θ 2 ω-2*physicalMoment i c g cm b θ 1 ω/(xi i*b)|≤
      4/(xi i*b)*literalMoment i c g cm b θ 0 ω := by
  have h1 := tiltedMain_bounded_by_literal i c g cm hb hbL hε hM hr θ 1 ω
  have h2 := tiltedMain_bounded_by_literal i c g cm hb hbL hε hM hr θ 2 ω
  have hp := physicalMoment_le_strict_zero i c g cm hb θ 1 (by omega) ω
  have hz : 0≤ literalMoment i c g cm b θ 0 ω := hp.1.trans hp.2
  have hden : 0< xi i*b := mul_pos (xi_pos i) hb
  constructor
  · have htri := abs_sub (tiltedMain i c g cm b θ 1 ω)
      (literalMoment i c g cm b θ 0 ω/(xi i*b))
    rw [abs_of_nonneg h1.1,abs_of_nonneg (div_nonneg hz hden.le)] at htri
    have hm : (1:ℝ)/(xi i*b)*literalMoment i c g cm b θ 0 ω=
        literalMoment i c g cm b θ 0 ω/(xi i*b) := by ring
    norm_num only [Nat.cast_one] at h1
    rw [hm] at h1
    calc
      _≤_ := htri
      _≤literalMoment i c g cm b θ 0 ω/(xi i*b)+literalMoment i c g cm b θ 0 ω/(xi i*b) := add_le_add h1.2 le_rfl
      _=_ := by ring
  · have htri := abs_sub (tiltedMain i c g cm b θ 2 ω)
      (2*physicalMoment i c g cm b θ 1 ω/(xi i*b))
    rw [abs_of_nonneg h2.1,abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hp.1) hden.le)] at htri
    have hm := mul_le_mul_of_nonneg_left hp.2 (show 0≤2/(xi i*b) by positivity)
    norm_num only [Nat.cast_ofNat] at h2
    calc
      _≤_ := htri
      _≤2/(xi i*b)*literalMoment i c g cm b θ 0 ω+2/(xi i*b)*literalMoment i c g cm b θ 0 ω :=
        add_le_add h2.2 (by convert! hm using 1; ring)
      _=_ := by ring

theorem tiltedGuard_high_bound (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hbz : b≤ g.rejectionRoot) (hseed : g.seedCutoff< b)
    (hgl : 0< g.multiplier-g.radius) (ha : 0≤ g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (hθ : 0≤θ) (q : ℕ) (hq : 0< q) (ω : Fin N → RowRival)
    (hh : ∀ j,0≤ rawH (xi i) b (ω j)) :
    tiltedGuard i c g cm b θ q ω∈Icc (0:ℝ)
      (1/(xi i*(g.multiplier-g.radius)*g.margin*g.population)) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let B0 := rowBids 0 ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let P := pathLaw (weights (xi i) g' T B) (imbalance T) ∅
  let e := Real.exp (-θ*deficit i b c ω)
  let K := 1/(xi i*(g.multiplier-g.radius)*g.margin*g.population)
  have hξ := xi_pos i
  have hK : 0< K := by dsimp [K]; positivity
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hg := guardRowVelocity_bounds i c g cm hb hbL hbz hseed hgl ha hε hM hr q ω
  refine ⟨mul_nonneg (Real.exp_pos _).le hg.1,?_⟩
  by_cases heq : T.residual₀=T.residual₁
  · change e*(if T.residual₀=T.residual₁ then 0 else _ )≤K
    rw [if_pos heq,mul_zero]
    exact hK.le
  by_cases hα : rawGuard (xi i) g c cm b ω=0
  · rw [if_pos hα,mul_zero] at hg
    simp only [tiltedGuard,le_antisymm hg.2 hg.1,mul_zero]
    exact hK.le
  have hαp : 0< guardAlpha (xi i) g' T B :=
    lt_of_le_of_ne (rawGuard_bounds (xi i) g c cm b ω).1 (Ne.symm hα)
  have hbranch : 0< branchWeight (xi i) g' T B := by
    simpa only [branchWeight,if_neg heq] using hαp
  have hu : Function.update B0 0 b=B := (rowBids_update ω b 0).symm
  have hw : weights (xi i) g' T B=weights (xi i) g' T B0 := by
    rw [← hu]
    exact weights_frozen g' T B0 0 (by simp [B0,rowBids]) (hb.le.trans hbL) hr hbL
  have hpath : e*pathMoment (xi i) g' T B0 0 q b≤1 := by
    unfold pathMoment
    rw [hu,← hw,← FCAppendix.FiniteLaw.expect_const_mul]
    apply expect_le_const
    intro p hp
    let E := finalSet (imbalance T) ∅ p
    have hpp := complement_bounds (xi_pos i) hξ1 T B E 0
    by_cases hpos : 0< complementMarginal (xi i) T B E 0
    · have hD := complement_positive_deficit (xi_pos i) hξ1 T B E 0
        (by simpa only [B,rowBids,Fin.cons_zero] using hb) (rowBids_outside c b ω) hpos
      have hW := actual_positive_deficit_le_raw i c g cm hb hbL hε hM hr ω hh hbranch p hp hD
      have he : e≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hθ hW.2.le])
      exact (mul_le_mul_of_nonneg_right he (pow_nonneg hpp.1 q)).trans
        (by simpa only [one_mul] using pow_le_one₀ hpp.1 hpp.2 (n:=q))
    · have hz := le_antisymm (le_of_not_gt hpos) hpp.1
      rw [hz,zero_pow hq.ne',mul_zero]
      norm_num
  rw [if_neg hα] at hg
  have hbnd := mul_le_mul_of_nonneg_left hg.2 (Real.exp_pos (-θ*deficit i b c ω)).le
  have hh' := mul_le_mul_of_nonneg_left hpath hK.le
  dsimp only [tiltedGuard,e,K] at *
  nlinarith

theorem tiltedGuard_low_zero (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : b≤ g.multiplier-g.radius)
    (θ : ℝ) (q : ℕ) (ω : Fin N → RowRival) :
    tiltedGuard i c g cm b θ q ω=0 := by
  unfold tiltedGuard guardRowVelocity GuardDerivative.velocity
  simp only [not_lt.mpr hb,if_false,zero_mul,ite_self,mul_zero]

end FCAppendix.Affine.Uniform06.DerivativeMeasurableBounds
