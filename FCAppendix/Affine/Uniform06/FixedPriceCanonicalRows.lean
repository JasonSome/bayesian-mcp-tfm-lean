import FCAppendix.Affine.Uniform06.GuardDerivative
import FCAppendix.Affine.Uniform06.LiteralCoarseMeasurable

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.FixedPriceCanonicalRows

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual FCAppendix.Affine.WeightedSampling
open LiteralExperiment LiteralPrefixStieltjes LiteralCoarsePath LiteralCoarseMeasurable
open LiteralKernelIdentity LiteralKernelDecomposition SourceGuardGeometry GuardPrefix
open ActualRootDerivative FixedPriceRawDerivative
open Uniform07

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def pathMoment (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (q : ℕ) (a : ℝ) : ℝ :=
  (pathLaw (weights ξ g T B) (imbalance T) ∅).expect (fun p =>
    (complementMarginal ξ T (Function.update B j a) (finalSet (imbalance T) ∅ p) j)^q)

def pathVelocity (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (q : ℕ) (a : ℝ) : ℝ :=
  (pathLaw (weights ξ g T B) (imbalance T) ∅).expect (fun p =>
    (q:ℝ)*(complementMarginal ξ T (Function.update B j a) (finalSet (imbalance T) ∅ p) j)^(q-1)*
      MaskedRootDerivative.slope ξ T B (finalSet (imbalance T) ∅ p) j a)

def weightedMoment (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (q : ℕ) (a : ℝ) : ℝ :=
  branchWeight ξ g T (Function.update B j a)*pathMoment ξ g T B j q a

def weightedVelocity (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (q : ℕ) (a : ℝ) : ℝ :=
  if T.residual₀=T.residual₁ then pathVelocity ξ g T B j q a
  else if g.multiplier-g.radius< a then
    guardAlpha ξ g T (Function.update B j a)*pathVelocity ξ g T B j q a+
      GuardDerivative.velocity ξ g T B j a*pathMoment ξ g T B j q a
  else 0

omit [Fintype ι] [Nonempty ι] in
theorem weights_frozen {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (hB0 : B j=0)
    (hL : 0 ≤ g.multiplier) (hr : 0 < g.requiredDemand)
    {a : ℝ} (ha : a≤ g.multiplier) : weights ξ g T (Function.update B j a)=weights ξ g T B := by
  have hz (b : ℝ) (hb : b≤ g.multiplier) : FiniteGuards.eligibility ξ g.multiplier g.requiredDemand b=0 := by
    apply FiniteGuards.eligibility_zero hr
    rw [exposure_zero hb]
    positivity
  simpa only [← hB0,Function.update_eq_self] using
    weights_update_eq ξ g T B j (hz a ha) (hz 0 hL)

theorem actual_moments_eq_frozen {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) (j : ι)
    (hB0 : B j=0) (hL : 0 ≤ g.multiplier)
    (hε : 0 < g.margin) (hM : 0 < g.population) (hr : 0 < g.requiredDemand)
    {a : ℝ} (ha : a≤ g.multiplier) :
    numericMarginal ξ g T (Function.update B j a) j=weightedMoment ξ g T B j 1 a ∧
    numericDuplicate ξ g T (Function.update B j a) j=weightedMoment ξ g T B j 2 a := by
  have he := numeric_path_moments hξ hξ1 g T (Function.update B j a) j
    hε hM hr (by simpa using ha)
  rw [weights_frozen g T B j hB0 hL hr ha] at he
  simpa only [weightedMoment,pathMoment,pow_one] using he

theorem pathMoment_hasDerivAt (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (q : ℕ) (a : ℝ)
    (hd : ∀ E : Finset ι,HasDerivAt
      (fun z => complementMarginal ξ T (Function.update B j z) E j)
      (MaskedRootDerivative.slope ξ T B E j a) a) :
    HasDerivAt (pathMoment ξ g T B j q) (pathVelocity ξ g T B j q a) a := by
  unfold pathMoment pathVelocity FCAppendix.FiniteLaw.expect
  have hh := HasDerivAt.sum (u:=Finset.univ) fun (p : Path ι (imbalance T)) _=>
    ((hd (finalSet (imbalance T) ∅ p)).pow q).const_mul
      ((pathLaw (weights ξ g T B) (imbalance T) ∅).mass p)
  convert! hh using 1
  funext z
  simp only [Finset.sum_apply,Pi.pow_apply]

theorem expect_zero_of_support {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ a,0< P.mass a → f a=0) : P.expect f=0 := by
  unfold FCAppendix.FiniteLaw.expect
  apply Finset.sum_eq_zero
  intro a _
  by_cases hp : 0< P.mass a
  · rw [hf a hp,mul_zero]
  · rw [le_antisymm (le_of_not_gt hp) (P.nonneg a),zero_mul]

theorem path_moments_zero_at_lower {ξ H : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData)
    (hg : PrefixConditions ξ g H) (T : PureTemplate ι) (B : ι → ℝ)
    (j : ι) (hB0 : B j=0) (hout : ∀ k,k ∉ T.support → B k=0)
    (hj : j ∈ T.support) (q : ℕ) (hq : 0< q)
    (hα : 0< guardAlpha ξ g T (Function.update B j (g.multiplier-g.radius))) :
    pathMoment ξ g T B j q (g.multiplier-g.radius)=0 ∧
      pathVelocity ξ g T B j q (g.multiplier-g.radius)=0 := by
  let a := g.multiplier-g.radius
  let B' := Function.update B j a
  have hL : 0≤ g.multiplier := by linarith [hg.lower_pos,hg.radius_nonneg]
  have haw : weights ξ g T B'=weights ξ g T B :=
    weights_frozen g T B j hB0 hL hg.requiredDemand_pos (by dsimp [a]; linarith [hg.radius_nonneg])
  have hW : (imbalance T:ℝ)< totalWeight (weights ξ g T B') := by
    have hh := positive_guard_weight g T B' hg.margin_pos hg.population_pos hα
    nlinarith [mul_pos hg.margin_pos hg.population_pos]
  have hout' : ∀ k,k ∉ T.support → B' k=0 := by
    intro k hk
    have hkj : k≠j := fun he => hk (he ▸ hj)
    simp only [B',Function.update_of_ne hkj,hout k hk]
  have hp0 (p : Path ι (imbalance T))
      (hp : 0<(pathLaw (weights ξ g T B) (imbalance T) ∅).mass p) :
      complementMarginal ξ T B' (finalSet (imbalance T) ∅ p) j=0 := by
    have hp' : 0<(pathLaw (weights ξ g T B') (imbalance T) ∅).mass p := by simpa only [haw] using hp
    have hcard := finalSet_card (weights ξ g T B') (imbalance T) ∅ (by simpa using hW) p hp'
    exact complement_rejects_below_lower_guard hξ hξ1 g T B' hg.margin_pos hg.population_pos
      hg.lower_pos hout' hα _ (by simpa using hcard.le) j (by simp [B',a])
  constructor
  · apply expect_zero_of_support
    intro p hp
    rw [hp0 p hp,zero_pow (Nat.ne_of_gt hq)]
  · apply expect_zero_of_support
    intro p hp
    have hz := hp0 p hp
    have hd : MaskedRootDerivative.slope ξ T B (finalSet (imbalance T) ∅ p) j a=0 := by
      unfold MaskedRootDerivative.slope
      split_ifs with hjE
      · have hm := MaskedRootDerivative.masked_update T B (finalSet (imbalance T) ∅ p) j hjE a
        have hpz : marginal ξ (small T) (maskedBids T B (finalSet (imbalance T) ∅ p)) j a=0 := by
          simpa only [complementMarginal,hm,marginal,B'] using hz
        simp only [ActualRootDerivative.derivative,hpz,lt_self_iff_false,false_and,if_false]
      · rfl
    change (q:ℝ)*(complementMarginal ξ T B' (finalSet (imbalance T) ∅ p) j)^(q-1)*
      MaskedRootDerivative.slope ξ T B (finalSet (imbalance T) ∅ p) j a=0
    rw [hd,mul_zero]

theorem weightedMoment_hasDerivAt {ξ U b H : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData)
    (hg : PrefixConditions ξ g H) (ha : 0< g.radius)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι) (hB0 : B j=0)
    (hj : j ∈ T.support) (hout : ∀ k,k ∉ T.support → B k=0)
    (hb : 0< b) (hbL : b< g.multiplier) (hbz : b< g.rejectionRoot)
    (hbU : b< U) (hclip : (1-ξ)*U≤ g.multiplier-g.radius)
    (q : ℕ) (hq : 0< q)
    (hd : ∀ E : Finset ι,HasDerivAt
      (fun z => complementMarginal ξ T (Function.update B j z) E j)
      (MaskedRootDerivative.slope ξ T B E j b) b)
    (hc0 : rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b ≠ g.margin*g.population)
    (hc1 : rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b ≠ 2*g.margin*g.population) :
    HasDerivAt (weightedMoment ξ g T B j q) (weightedVelocity ξ g T B j q b) b := by
  have hp := pathMoment_hasDerivAt ξ g T B j q b hd
  by_cases he : T.residual₀=T.residual₁
  · have heq : weightedMoment ξ g T B j q=pathMoment ξ g T B j q := by
      funext a
      simp only [weightedMoment,branchWeight,if_pos he,one_mul]
    rw [heq,weightedVelocity,if_pos he]
    exact hp
  · have heq : weightedMoment ξ g T B j q=
        fun a => guardAlpha ξ g T (Function.update B j a)*pathMoment ξ g T B j q a := by
      funext a
      simp only [weightedMoment,branchWeight,if_neg he]
    rw [heq]
    by_cases hlow : b< g.multiplier-g.radius
    · have hz : (fun a => guardAlpha ξ g T (Function.update B j a)*pathMoment ξ g T B j q a)=ᶠ[𝓝 b]
          fun _ => (0:ℝ) := by
        filter_upwards [eventually_lt_nhds hlow,eventually_gt_nhds hb] with a hal ha0
        by_cases hα : guardAlpha ξ g T (Function.update B j a)=0
        · simp only [hα,zero_mul]
        · have hαp := lt_of_le_of_ne (guardAlpha_bounds ξ g T (Function.update B j a)).1 (Ne.symm hα)
          have haw := weights_frozen (ξ:=ξ) g T B j hB0
            (by linarith [hg.lower_pos,hg.radius_nonneg]) hg.requiredDemand_pos
              (show a≤ g.multiplier by linarith [hg.radius_nonneg])
          have hW : (imbalance T:ℝ)< totalWeight (weights ξ g T (Function.update B j a)) := by
            have hh := positive_guard_weight g T (Function.update B j a) hg.margin_pos hg.population_pos hαp
            nlinarith [mul_pos hg.margin_pos hg.population_pos]
          have hout' : ∀ k,k ∉ T.support → Function.update B j a k=0 := by
            intro k hk
            simp only [Function.update_of_ne (show k≠j from fun he => hk (he ▸ hj)),hout k hk]
          have hpm : pathMoment ξ g T B j q a=0 := by
            apply expect_zero_of_support
            intro p hpp
            have hpp' : 0<(pathLaw (weights ξ g T (Function.update B j a)) (imbalance T) ∅).mass p :=
              by simpa only [haw] using hpp
            have hcard := finalSet_card (weights ξ g T (Function.update B j a)) (imbalance T) ∅
              (by simpa using hW) p hpp'
            have hp0 := complement_rejects_below_lower_guard hξ hξ1 g T (Function.update B j a)
              hg.margin_pos hg.population_pos hg.lower_pos hout' hαp _
                (by simpa using hcard.le) j (by simpa using hal.le)
            rw [hp0,zero_pow (Nat.ne_of_gt hq)]
          rw [hpm,mul_zero]
      simpa only [weightedVelocity,if_neg he,if_neg (not_lt.mpr hlow.le)] using
        (hasDerivAt_const b 0).congr_of_eventuallyEq hz
    · by_cases hb0 : b=g.multiplier-g.radius
      · have hseed : g.seedCutoff< b := by simpa only [hb0] using hg.seed_below_lower
        by_cases hα : guardAlpha ξ g T (Function.update B j b)=0
        · have he0 := GuardDerivative.alpha_zero_eventually_at_lower g hg T B j hj hξ ha
            (by simpa only [hb0] using hbz)
            (by simpa only [hb0,exposure_zero le_rfl,add_zero] using hc0)
            (by simpa only [hb0] using hα)
          have hezero : (fun a => guardAlpha ξ g T (Function.update B j a)*pathMoment ξ g T B j q a)=ᶠ[𝓝 b]
              fun _ => (0:ℝ) := by
            filter_upwards [show (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 b] fun _ => (0:ℝ)
              by simpa only [hb0] using he0] with a ha0
            rw [ha0,zero_mul]
          simpa only [weightedVelocity,if_neg he,hb0,lt_self_iff_false,if_false] using
            (hasDerivAt_const b 0).congr_of_eventuallyEq hezero
        · have hαp := lt_of_le_of_ne (guardAlpha_bounds ξ g T (Function.update B j b)).1 (Ne.symm hα)
          have hzero := path_moments_zero_at_lower hξ hξ1 g hg T B j hB0 hout hj q hq
            (by simpa only [hb0] using hαp)
          have hpzero : pathMoment ξ g T B j q b=0 := by simpa only [hb0] using hzero.1
          have hd0 : pathVelocity ξ g T B j q b=0 := by simpa only [hb0] using hzero.2
          rw [hd0] at hp
          have hc : ContinuousAt (fun a => guardAlpha ξ g T (Function.update B j a)) b := by
            let f := fun a => GuardDerivative.fixedCoefficient ξ g T B j*
              FiniteGuards.ramp (2*g.margin*g.population) (g.margin*g.population)
                (rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) a)
            have hfc : Continuous f := by
              unfold f FiniteGuards.ramp
              exact continuous_const.mul (FiniteGuards.continuous_clip01.comp
                (((continuous_const.add (continuous_exposure hξ hg.lower_pos)).sub continuous_const).div_const _))
            have hfe : (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 b] f := by
              filter_upwards [eventually_gt_nhds hseed,eventually_lt_nhds hbL,eventually_lt_nhds hbz]
                with a has haL haz
              exact GuardDerivative.alpha_eq_fixedCoefficient g T B j hj hg.radius_nonneg
                hg.requiredDemand_pos has haL.le haz.le
            exact hfc.continuousAt.congr_of_eventuallyEq hfe
          simpa only [weightedVelocity,if_neg he,hb0,lt_self_iff_false,if_false] using
            GuardDerivative.mul_hasDerivAt_zero hp hpzero hc
      · have hlo : g.multiplier-g.radius< b := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hb0)
        have hseed := hg.seed_below_lower.trans hlo
        have hα := GuardDerivative.alpha_hasDerivAt hξ hξ1 g hg T B j hj hseed hbL hbz hbU hclip hb0 hc0 hc1
        convert! hα.mul hp using 1
        simp only [weightedVelocity,if_neg he,if_pos hlo]
        ring

section Original
variable {N : ℕ}

def rowMoment (ξ : ℝ) (C : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (q : ℕ) (b : ℝ) (r : Fin N → RowRival) : ℝ :=
  weightedMoment ξ {g with countMargin := margin (fun j => (r j).1)}
    (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) 0 q b

def rowVelocity (ξ : ℝ) (C : ℕ) (g : GuardData)
    (margin : (Fin N → Fin 4) → ℝ) (q : ℕ) (b : ℝ) (r : Fin N → RowRival) : ℝ :=
  weightedVelocity ξ {g with countMargin := margin (fun j => (r j).1)}
    (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) 0 q b

theorem original_row_moment_identities {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (C : ℕ) (g : GuardData) (margin : (Fin N → Fin 4) → ℝ)
    (hL : 0≤ g.multiplier) (hε : 0< g.margin) (hM : 0< g.population)
    (hr : 0< g.requiredDemand) {b : ℝ} (hb : b≤ g.multiplier) (r : Fin N → RowRival) :
    originalRowMarginal ξ C g margin b r=rowMoment ξ C g margin 1 b r ∧
    originalRowDuplicate ξ C g margin b r=rowMoment ξ C g margin 2 b r := by
  have he := actual_moments_eq_frozen hξ hξ1 {g with countMargin := margin (fun j => (r j).1)}
    (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) 0 (by simp [rowBids]) hL hε hM hr hb
  simpa only [originalRowMarginal,originalRowDuplicate,rowMoment,LowBody.rowBids_update] using he

theorem original_lower_slack_identity (i : Row) (C : ℕ) (g : GuardData)
    (r : Fin N → RowRival) {b : ℝ} (hlo : 0< g.multiplier-g.radius) :
    rivalSlacks (xi i) g (patternTemplate C (fun j => (r j).1)) (rowBids 0 r) 0 0+
      exposure (xi i) (g.multiplier-g.radius) b=
        exposure (xi i) (g.multiplier-g.radius) b+
          (∑ j,RivalGood.lowerTest (exposure (xi i) (g.multiplier-g.radius)) (r j))-
            ((small (patternTemplate C (fun j => (r j).1))+
              imbalance (patternTemplate C (fun j => (r j).1)):ℕ):ℝ) := by
  have he := congrFun (slackVector_update (xi i) g (patternTemplate C (fun j => (r j).1))
    (rowBids 0 r) 0 (focal_mem C r) b) 0
  have hD : LiteralExperiment.demand (xi i) (patternTemplate C (fun j => (r j).1)) (rowBids b r)
      (g.multiplier-g.radius)=exposure (xi i) (g.multiplier-g.radius) b+
        ∑ j,RivalGood.lowerTest (exposure (xi i) (g.multiplier-g.radius)) (r j) := by
    rw [demand_eq_full hlo _ _ (rowBids_outside C b r),Fin.sum_univ_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases ht : (r j).1=0 <;> simp [rowBids,RivalGood.lowerTest,ht,exposure_zero hlo.le]
  simp only [slackVector,FiniteGuards.slacks,Matrix.cons_val_zero,LowBody.rowBids_update,hD] at he
  push_cast
  linarith

theorem original_every_fixed_bid_row_derivative (i : Row) (G : Measure (ℝ × ℝ))
    [IsProbabilityMeasure G] (hnull : ∀ a : ℝ,(G.map Prod.snd) {a}=0)
    (hnon : ∀ᵐ p ∂G,0≤ p.2) {U H b : ℝ} (hcap : ∀ᵐ p ∂G,p.2≤ U)
    (g : GuardData) (hg : PrefixConditions (xi i) g H) (ha : 0< g.radius)
    (hεM : 1< g.margin*g.population) (hb : 0< b) (hbL : b< g.multiplier)
    (hbz : b< g.rejectionRoot) (hbU : b< U)
    (hclip : (1-xi i)*U≤ g.multiplier-g.radius) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => RawMixedSource.source i G),
      ∀ (C : ℕ) (margin : (Fin N → Fin 4) → ℝ) (q : ℕ),0< q →
        HasDerivAt (fun a => rowMoment (xi i) C g margin q a r)
          (rowVelocity (xi i) C g margin q b r) b := by
  have hξ1 : xi i<1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  filter_upwards [FixedPriceAllFaces.original_every_fixed_bid_derivatives i G hnull hnon hb,
    GuardCornerNull.original_guard_ramp_corners i G hnull hcap N g hg.lower_pos hclip
      hg.rejectionScale_pos hεM b] with r hroot hguard
  intro C margin q hq
  let g' := {g with countMargin := margin (fun j => (r j).1)}
  let T := patternTemplate C (fun j => (r j).1)
  have hslack := original_lower_slack_identity i C g' r hg.lower_pos (b:=b)
  have hc0 : rivalSlacks (xi i) g' T (rowBids 0 r) 0 0+
      exposure (xi i) (g.multiplier-g.radius) b ≠ g.margin*g.population := by
    intro he
    have hh := (hguard (small T+imbalance T) (0:Fin 2)).1
    norm_num only [Fin.val_zero,Nat.cast_one,one_mul] at hh
    exact hh (by linarith)
  have hc1 : rivalSlacks (xi i) g' T (rowBids 0 r) 0 0+
      exposure (xi i) (g.multiplier-g.radius) b ≠ 2*g.margin*g.population := by
    intro he
    have hh := (hguard (small T+imbalance T) (1:Fin 2)).1
    norm_num only [Fin.val_one,Nat.cast_ofNat] at hh
    exact hh (by linarith)
  apply weightedMoment_hasDerivAt (xi_pos i) hξ1 g' (hg.update_countMargin _) ha T (rowBids 0 r) 0
    (by simp [rowBids]) (focal_mem C r) (rowBids_outside C 0 r) hb hbL hbz hbU hclip q hq
  · intro E
    simpa only [LowBody.rowBids_update] using (hroot C E).1
  · exact hc0
  · exact hc1

end Original
end FCAppendix.Affine.Uniform06.FixedPriceCanonicalRows
