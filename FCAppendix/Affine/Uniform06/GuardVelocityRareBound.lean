import FCAppendix.Affine.Uniform06.LiteralGuardVelocity
import FCAppendix.Affine.Uniform06.UnguardedRareMoment
import FCAppendix.Affine.Uniform06.RawPathGlobalResponse

noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardVelocityRareBound

open Set MeasureTheory LowBody
open scoped BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralGuardVelocity LiteralDerivativeMoments FixedPriceCanonicalRows
open RawMomentPartition RawPathAdapter RawPathRootReplacement RawPathGlobalResponse
open LiteralCoarsePath LiteralGuardRare FiniteSampledLaplace SampledCellDomination
open UnguardedRareMoment ZeroWeightFocal FiniteMarkedExchangeability RareEmpiricalReplacement
open FixedPriceRawDerivative

variable {N : ℕ} [Nonempty (Fin N)]

lemma unguardedRow_eq_rival (i : Row) (c : ℕ) (g : GuardData) (b θ : ℝ)
    (q : ℕ) (ω : Fin N → RowRival) (hy : imbalanceSum ω≠0)
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)) :
    unguardedRow i c g b θ q ω=
      Real.exp (-θ*deficit i b c ω)*
        (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
          (imbalanceSum ω).natAbs ∅).expect
            (fun p => strictPower q (selectedDeficit i c b ω (imbalanceSum ω).natAbs p)) := by
  rw [unguardedRow,if_neg hy,safeRow,if_pos hW,sampledRow]
  rw [← FCAppendix.FiniteLaw.expect_const_mul]
  apply FCAppendix.FiniteLaw.expect_congr
  intro p
  simp only [tupleTest,show sumY integerSign ω=imbalanceSum ω from rfl,true_and,
    selectedDeficit,deficit,FCAppendix.ExponentialTilt.iidSum,sumX,strictPower]
  split_ifs <;> simp_all

lemma frozen_pathMoment_eq_rival (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {b : ℝ} (hb : 0< b)
    (hbL : b≤ g.multiplier) (hr : 0< g.requiredDemand) (q : ℕ)
    (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)) :
    pathMoment (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids 0 ω) 0 q b=
        (pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω)
          (imbalanceSum ω).natAbs ∅).expect
            (fun p => (selectedResponse i c b ω (imbalanceSum ω).natAbs p)^q) := by
  let T := patternTemplate c (fun j => (ω j).1)
  let g' := {g with countMargin:=cm (fun j => (ω j).1)}
  have hu : Function.update (rowBids 0 ω) 0 b=rowBids b ω := (rowBids_update ω b 0).symm
  have hw : weights (xi i) g' T (rowBids b ω)=weights (xi i) g' T (rowBids 0 ω) := by
    rw [← hu]
    exact weights_frozen g' T (rowBids 0 ω) 0 (by simp [rowBids]) (hb.le.trans hbL) hr hbL
  have hk := literal_imbalance_eq c ω hc
  unfold pathMoment
  rw [hu,← hw,hk,actual_rival_path_transport (xi i) g' c b hbL hr ω _ hW]
  apply FCAppendix.FiniteLaw.expect_congr
  intro p
  rw [show (∅:Finset (Fin (N+1)))=liftSet (∅:Finset (Fin N)) by simp [liftSet],
    finalSet_lift]
  rfl

theorem unguarded_physical_le_deficit (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo U b γ θ : ℝ}
    (hlo : 0< lo) (hU : 0≤ U) (hlb : lo< b) (hbU : b≤ U)
    (hclip : (1-xi i)*U≤ lo) (hγ : 0<γ) (hN : 0< N)
    (hbL : b≤ g.multiplier) (hr : 0< g.requiredDemand)
    (q : ℕ) (hq : 0< q) (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hy : imbalanceSum ω≠0) (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω))
    (hemp : γ+((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω) :
    Real.exp (-θ*deficit i b c ω)*
      pathMoment (xi i) {g with countMargin:=cm (fun j => (ω j).1)}
        (patternTemplate c (fun j => (ω j).1)) (rowBids 0 ω) 0 q b≤
      (xi i/((b-lo)*γ*(N:ℝ)))^q*unguardedRow i c g b θ q ω := by
  have hb : 0< b := hlo.trans hlb
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  let k := (imbalanceSum ω).natAbs
  let P := pathLaw (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) k ∅
  let K := xi i/((b-lo)*γ*(N:ℝ))
  have hK : 0< K := by dsimp [K]; exact div_pos (xi_pos i) (by positivity)
  rw [frozen_pathMoment_eq_rival i c g cm hb hbL hr q ω hc hW,
    unguardedRow_eq_rival i c g b θ q ω hy hW]
  have hpoint (p : Path (Fin N) k) (hp : 0< P.mass p) :
      (selectedResponse i c b ω k p)^q≤ K^q*strictPower q (selectedDeficit i c b ω k p) := by
    have h := actual_global_response_bound i c g hlo hU hlb hbU hclip hγ hN
      ω hc hcap k rfl hW p hp hemp
    by_cases hD : 0< selectedDeficit i c b ω k p
    · have hpK : selectedResponse i c b ω k p≤ K*selectedDeficit i c b ω k p := by
        have hh : selectedResponse i c b ω k p≤
            (xi i/((b-lo)*γ)*max 0 (selectedDeficit i c b ω k p))/(N:ℝ) :=
          (le_div_iff₀ hNr).mpr (by nlinarith [h.2])
        rw [max_eq_right hD.le] at hh
        convert! hh using 1
        dsimp [K]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      have hp0 : 0≤ selectedResponse i c b ω k p :=
        (nonneg_of_mul_nonneg_right h.1 hNr)
      simpa only [strictPower,if_pos hD,mul_pow] using pow_le_pow_left₀ hp0 hpK q
    · have hp0 : selectedResponse i c b ω k p=0 := by
        have hn : ¬0< selectedResponse i c b ω k p :=
          fun hpos => hD ((actual_strict_positive_iff i c g hb ω hc k rfl hW p hp).mp hpos)
        exact le_antisymm (le_of_not_gt hn) (nonneg_of_mul_nonneg_right h.1 hNr)
      simp only [hp0,zero_pow hq.ne',strictPower,if_neg hD,mul_zero,le_refl]
  have hh := mul_le_mul_of_nonneg_left (expect_le_of_support P _ _ hpoint)
    (Real.exp_pos (-θ*deficit i b c ω)).le
  rw [FCAppendix.FiniteLaw.expect_const_mul] at hh
  convert! hh using 1
  dsimp only [K,P,k]
  ring

theorem actual_guard_velocity_majorant (i : Row) (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo U b γ θ : ℝ}
    (hlo : 0< lo) (hU : 0≤ U) (hlb : lo< b) (hbU : b≤ U)
    (hclip : (1-xi i)*U≤ lo) (hγ : 0<γ) (hN : 0< N)
    (hbL : b≤ g.multiplier) (hbz : b≤ g.rejectionRoot) (hseed : g.seedCutoff< b)
    (hglo : 0< g.multiplier-g.radius) (ha : 0≤ g.radius)
    (hε : 0< g.margin) (hM : 0< g.population) (hr : 0< g.requiredDemand)
    (q : ℕ) (hq : 0< q) (ω : Fin N → RowRival) (hc : ValidCounts c ω)
    (hcap : ∀ j,(ω j).1=0 → (ω j).2≤ U)
    (hemp : γ+((imbalanceSum ω).natAbs:ℝ)/(lo*(N:ℝ))≤
      empirical (FullReciprocalMean.reciprocal b) N ω) :
    0≤ Real.exp (-θ*deficit i b c ω)*guardRowVelocity i c g cm b q ω ∧
    Real.exp (-θ*deficit i b c ω)*guardRowVelocity i c g cm b q ω≤
      (1/(xi i*(g.multiplier-g.radius)*g.margin*g.population))*
        (xi i/((b-lo)*γ*(N:ℝ)))^q*unguardedRow i c g b θ q ω := by
  have hb : 0< b := hlo.trans hlb
  have hξ := xi_pos i
  have hg := guardRowVelocity_bounds i c g cm hb hbL hbz hseed hglo ha hε hM hr q ω
  refine ⟨mul_nonneg (Real.exp_pos _).le hg.1,?_⟩
  by_cases hy : imbalanceSum ω=0
  · have he := (imbalance_zero_iff_equal c ω hc).mp hy
    simp only [guardRowVelocity,if_pos he,mul_zero]
    exact mul_nonneg (by positivity) (unguardedRow_nonneg i c g b θ q ω)
  by_cases hα : rawGuard (xi i) g c cm b ω=0
  · rw [if_pos hα,mul_zero] at hg
    rw [le_antisymm hg.2 hg.1,mul_zero]
    exact mul_nonneg (by positivity) (unguardedRow_nonneg i c g b θ q ω)
  have hαp : 0< rawGuard (xi i) g c cm b ω :=
    lt_of_le_of_ne (rawGuard_bounds (xi i) g c cm b ω).1 (Ne.symm hα)
  have hW : ((imbalanceSum ω).natAbs:ℝ)<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) := by
    have hw := SourceGuardGeometry.positive_guard_weight
      {g with countMargin:=cm (fun j => (ω j).1)}
      (patternTemplate c (fun j => (ω j).1)) (rowBids b ω) hε hM hαp
    rw [literal_weights_eq_lift (xi i) {g with countMargin:=cm (fun j => (ω j).1)} c b hbL hr ω,lift_total,
      literal_imbalance_eq c ω hc] at hw
    have he := mul_pos hε hM
    change ((imbalanceSum ω).natAbs:ℝ)+g.margin*g.population<
      totalWeight (rowWeights (rawWeight (xi i) g) (rawWeight_bounds (xi i) g) ω) at hw
    linarith
  rw [if_neg hα] at hg
  have hm := unguarded_physical_le_deficit (θ := θ) i c g cm hlo hU hlb hbU hclip hγ hN
    hbL hr q hq ω hc hy hcap hW hemp
  have hbound := mul_le_mul_of_nonneg_left hg.2 (Real.exp_pos (-θ*deficit i b c ω)).le
  have hmul := mul_le_mul_of_nonneg_left hm
    (show 0≤1/(xi i*(g.multiplier-g.radius)*g.margin*g.population) by positivity)
  nlinarith

end FCAppendix.Affine.Uniform06.GuardVelocityRareBound
