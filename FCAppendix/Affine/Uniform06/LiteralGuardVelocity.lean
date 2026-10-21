import FCAppendix.Affine.Uniform06.LiteralDerivativeMoments

noncomputable section
namespace FCAppendix.Affine.Uniform06.LiteralGuardVelocity

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralDerivativeMoments FixedPriceCanonicalRows FixedPriceRawDerivative
open LiteralCoarsePath LiteralKernelIdentity RawMomentPartition GuardDerivative LiteralGuardRare GuardPrefix
open GlobalDerivativeReplacement SourceGuardGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma masked_slope_eq_actual_profile (ξ : ℝ) (T : PureTemplate ι) (B : ι → ℝ)
    (E : Finset ι) (j : ι) (b : ℝ) (hj : j∈T.support\E) :
    MaskedRootDerivative.slope ξ T B E j b=
      ActualRootDerivative.derivative ξ (small T) (maskedBids T (Function.update B j b) E) j b := by
  rw [MaskedRootDerivative.slope,if_pos hj,MaskedRootDerivative.masked_update T B E j hj b]
  exact (derivative_update ξ (small T) (maskedBids T B E) j b b).symm

lemma ramp_inside {e s : ℝ} (he : 0< e) (hs : e< s ∧ s<2*e) :
    0< FiniteGuards.ramp (2*e) e s := by
  unfold FiniteGuards.ramp
  rw [show 2*e-e=e by ring,FiniteGuards.clip01_self ⟨div_nonneg (sub_nonneg.mpr hs.1.le) he.le,
    (div_le_iff₀ he).mpr (by linarith [hs.2])⟩]
  exact div_pos (sub_pos.mpr hs.1) he

theorem velocity_zero_of_alpha_zero {ξ : ℝ} (g : GuardData)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι) (hj : j∈T.support)
    (ha : 0≤ g.radius) (hr : 0< g.requiredDemand) (hε : 0< g.margin) (hM : 0< g.population)
    {b : ℝ} (hseed : g.seedCutoff< b) (hbL : b≤ g.multiplier) (hbz : b≤ g.rejectionRoot)
    (hα : guardAlpha ξ g T (Function.update B j b)=0) :
    GuardDerivative.velocity ξ g T B j b=0 := by
  rw [alpha_eq_fixedCoefficient g T B j hj ha hr hseed hbL hbz] at hα
  by_cases hlo : g.multiplier-g.radius< b
  · by_cases hs : g.margin*g.population<
        rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b ∧
        rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b<2*(g.margin*g.population)
    · have hrp := ramp_inside (mul_pos hε hM) hs
      have hz : fixedCoefficient ξ g T B j=0 :=
        (mul_eq_zero.mp (by simpa only [mul_assoc] using hα)).resolve_right hrp.ne'
      simp only [GuardDerivative.velocity,if_pos hlo,hz,zero_mul,zero_div]
    · simp only [GuardDerivative.velocity,if_pos hlo,rampSlope,if_neg hs,mul_zero,zero_mul,zero_div]
  · simp only [GuardDerivative.velocity,if_neg hlo]

variable {N : ℕ}

def guardRowVelocity (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) (b : ℝ) (q : ℕ) (ω : Fin N → RowRival) : ℝ :=
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids 0 ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  if T.residual₀=T.residual₁ then 0 else
    GuardDerivative.velocity (xi i) g' T B 0 b*pathMoment (xi i) g' T B 0 q b

lemma mainRowVelocity_eq_frozen (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hbL : b≤ g.multiplier)
    (hL : 0≤ g.multiplier) (hε : 0< g.margin) (hM : 0< g.population)
    (hr : 0< g.requiredDemand) (q : ℕ) (ω : Fin N → RowRival) :
    mainRowVelocity i c g cm b q ω=
      branchWeight (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids b ω)*
      pathVelocity (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids 0 ω) 0 q b := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B0 := rowBids 0 ω
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  let a := branchWeight (xi i) g' T B
  have hu : Function.update B0 0 b=B := LowBody.rowBids_update 0 b ω
  have hw : weights (xi i) g' T B=weights (xi i) g' T B0 := by
    rw [← hu]
    exact weights_frozen g' T B0 0 (by simp [B0,rowBids]) hL hr hbL
  change a*(pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect _=
    a*pathVelocity (xi i) g' T B0 0 q b
  by_cases ha : a=0
  · rw [ha,zero_mul,zero_mul]
  · have hap : 0< a := lt_of_le_of_ne (branchWeight_bounds (xi i) g' T B).1 (Ne.symm ha)
    apply congrArg (fun z => a*z)
    unfold pathVelocity
    rw [← hw]
    apply expect_eq_of_support
    intro p hp
    have he := branch_path_geometry g' T B 0 hε hM hr
      (by simpa only [B,rowBids,Fin.cons_zero] using hbL) hap p hp
    have hE : 0∈T.support\finalSet (imbalance T) ∅ p := Finset.mem_sdiff.mpr ⟨focal_mem c ω,he.2⟩
    rw [masked_slope_eq_actual_profile (xi i) T B0 _ 0 b hE,hu]

lemma mainRowVelocity_zero_below_lower (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (_hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (hblo : b≤ g.multiplier-g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (q : ℕ) (ω : Fin N → RowRival)
    (hne : (patternTemplate c (fun j => (ω j).1)).residual₀≠
      (patternTemplate c (fun j => (ω j).1)).residual₁) :
    mainRowVelocity i c g cm b q ω=0 := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids b ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  change T.residual₀≠T.residual₁ at hne
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  change branchWeight (xi i) g' T B*
    (pathLaw (weights (xi i) g' T B) (imbalance T) ∅).expect
      (fun p => (q:ℝ)*(complementMarginal (xi i) T B (finalSet (imbalance T) ∅ p) 0)^(q-1)*
        ActualRootDerivative.derivative (xi i) (small T) (maskedBids T B (finalSet (imbalance T) ∅ p)) 0 b)=0
  by_cases hα : guardAlpha (xi i) g' T B=0
  · simp only [branchWeight,if_neg hne,hα,zero_mul]
  · have hαp := lt_of_le_of_ne (guardAlpha_bounds (xi i) g' T B).1 (Ne.symm hα)
    have ha : 0< branchWeight (xi i) g' T B := by simpa only [branchWeight,if_neg hne] using hαp
    apply mul_eq_zero_of_right
    apply expect_zero_of_support
    intro p hp
    have he := branch_path_geometry g' T B 0 hε hM hr
      (by simpa only [B,rowBids,Fin.cons_zero] using hbL) ha p hp
    let E := finalSet (imbalance T) ∅ p
    have hzero := complement_rejects_below_lower_guard (xi_pos i) hξ1 g' T B hε hM hlo
      (rowBids_outside c b ω) hαp E he.1.le 0 (by simpa only [B,rowBids,Fin.cons_zero] using hblo)
    have hB0 : maskedBids T B E 0=b := by
      change (if (0:Fin (N+1))∈T.support\E then B 0 else 0)=b
      rw [if_pos (Finset.mem_sdiff.mpr ⟨focal_mem c ω,he.2⟩)]
      rfl
    have hu : Function.update (maskedBids T B E) 0 b=maskedBids T B E := by
      rw [← hB0]
      exact Function.update_eq_self _ _
    have hder : ActualRootDerivative.derivative (xi i) (small T) (maskedBids T B E) 0 b=0 := by
      simp only [ActualRootDerivative.derivative,ActualRootDerivative.marginal,hu,
        show EqualCapacity.positiveMarginal (xi i) (small T) (maskedBids T B E) 0=0 from hzero,
        lt_self_iff_false,false_and,if_false]
    rw [hder,mul_zero]

theorem original_rowVelocity_eq_main_add_guard (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b) (hbL : b≤ g.multiplier)
    (hlo : 0< g.multiplier-g.radius) (_ha : 0≤ g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (q : ℕ) (ω : Fin N → RowRival) :
    rowVelocity (xi i) c g cm q b ω=mainRowVelocity i c g cm b q ω+guardRowVelocity i c g cm b q ω := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids 0 ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  have hL : 0≤ g.multiplier := by linarith
  have hm := mainRowVelocity_eq_frozen i c g cm hbL hL hε hM hr q ω
  change weightedVelocity (xi i) g' T B 0 q b=mainRowVelocity i c g cm b q ω+
    (if T.residual₀=T.residual₁ then 0 else GuardDerivative.velocity (xi i) g' T B 0 b*
      pathMoment (xi i) g' T B 0 q b)
  change mainRowVelocity i c g cm b q ω=branchWeight (xi i) g' T (rowBids b ω)*
    pathVelocity (xi i) g' T B 0 q b at hm
  have hu : Function.update B 0 b=rowBids b ω := LowBody.rowBids_update 0 b ω
  by_cases he : T.residual₀=T.residual₁
  · rw [hm]
    simp only [weightedVelocity,branchWeight,if_pos he,one_mul,add_zero]
  · by_cases hl : g.multiplier-g.radius< b
    · rw [hm]
      have hl' : g'.multiplier-g'.radius<b := hl
      simp only [weightedVelocity,branchWeight,if_neg he,if_pos hl',hu]
    · have hz := mainRowVelocity_zero_below_lower i c g cm hb hbL hlo (le_of_not_gt hl)
        hε hM hr q ω he
      have hl' : ¬g'.multiplier-g'.radius<b := hl
      simp only [weightedVelocity,if_neg he,if_neg hl',hz,
        GuardDerivative.velocity,zero_mul,zero_add]

theorem guardRowVelocity_bounds (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (_hb : 0< b) (hbL : b≤ g.multiplier)
    (hbz : b≤ g.rejectionRoot) (hseed : g.seedCutoff< b)
    (hlo : 0< g.multiplier-g.radius) (ha : 0≤ g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (q : ℕ) (ω : Fin N → RowRival) :
    0≤ guardRowVelocity i c g cm b q ω ∧
    guardRowVelocity i c g cm b q ω≤
      (1/(xi i*(g.multiplier-g.radius)*g.margin*g.population))*
        (if rawGuard (xi i) g c cm b ω=0 then 0 else
          pathMoment (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
            (patternTemplate c (fun j => (ω j).1)) (rowBids 0 ω) 0 q b) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let B := rowBids 0 ω
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hp : 0≤ pathMoment (xi i) g' T B 0 q b := by
    apply expect_nonneg
    intro p
    exact pow_nonneg ((EqualCapacity.positiveMarginal_spec (xi i) (small T) (xi_pos i) hξ1
      (maskedBids T (Function.update B 0 b) (finalSet (imbalance T) ∅ p))).1 0) q
  have hv := velocity_bounds (xi_pos i) g' hlo hε hM T B 0 (b:=b)
  have hcoeff : 0≤1/(xi i*(g.multiplier-g.radius)*g.margin*g.population) := by
    have hx := xi_pos i
    positivity
  change 0≤(if T.residual₀=T.residual₁ then 0 else GuardDerivative.velocity (xi i) g' T B 0 b*
      pathMoment (xi i) g' T B 0 q b) ∧
    (if T.residual₀=T.residual₁ then 0 else GuardDerivative.velocity (xi i) g' T B 0 b*
      pathMoment (xi i) g' T B 0 q b)≤
      (1/(xi i*(g.multiplier-g.radius)*g.margin*g.population))*
        (if rawGuard (xi i) g c cm b ω=0 then 0 else pathMoment (xi i) g' T B 0 q b)
  by_cases he : T.residual₀=T.residual₁
  · rw [if_pos he]
    refine ⟨le_rfl,mul_nonneg hcoeff ?_⟩
    split_ifs
    · rfl
    · exact hp
  · rw [if_neg he]
    by_cases hα : rawGuard (xi i) g c cm b ω=0
    · rw [if_pos hα]
      have hzero : GuardDerivative.velocity (xi i) g' T B 0 b=0 := by
        apply velocity_zero_of_alpha_zero g' T B 0 (focal_mem c ω) ha hr hε hM hseed hbL hbz
        rw [show Function.update B 0 b=rowBids b ω from LowBody.rowBids_update 0 b ω]
        exact hα
      rw [hzero,zero_mul,mul_zero]
      exact ⟨le_rfl,le_rfl⟩
    · rw [if_neg hα]
      exact ⟨mul_nonneg hv.1 hp,mul_le_mul_of_nonneg_right hv.2 hp⟩

end FCAppendix.Affine.Uniform06.LiteralGuardVelocity
