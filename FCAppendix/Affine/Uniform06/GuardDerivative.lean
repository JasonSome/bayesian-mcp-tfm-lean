import FCAppendix.Affine.Uniform06.FixedPriceAllFaces
import FCAppendix.Affine.Uniform06.GuardCornerNull
import FCAppendix.Affine.Uniform06.CanonicalPrefixLipschitz
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardDerivative

open Set Filter Topology MeasureTheory
open scoped BigOperators
open FCAppendix.Affine.ClippedResidual
open LowBody LiteralExperiment LiteralPrefixStieltjes GuardPrefix FiniteGuards

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def rampSlope (e s : ℝ) : ℝ := if e< s ∧ s<2*e then 1/e else 0

theorem rampSlope_bounds {e : ℝ} (he : 0 < e) (s : ℝ) :
    rampSlope e s ∈ Icc (0:ℝ) (1/e) := by
  unfold rampSlope
  split_ifs
  · exact ⟨by positivity,le_rfl⟩
  · exact ⟨le_rfl,by positivity⟩

theorem normalized_ramp_hasDerivAt {e s : ℝ} (he : 0 < e)
    (hs0 : s ≠ e) (hs1 : s ≠ 2*e) :
    HasDerivAt (ramp (2*e) e) (rampSlope e s) s := by
  by_cases hlow : s< e
  · have heq : ramp (2*e) e=ᶠ[𝓝 s] fun _ => (0:ℝ) :=
      (eventually_lt_nhds hlow).mono fun a ha => ramp_zero (by linarith) ha.le
    have hn : ¬(e<s ∧ s<2*e) := fun h=>(lt_asymm hlow h.1).elim
    rw [rampSlope,if_neg hn]
    exact (hasDerivAt_const s 0).congr_of_eventuallyEq heq
  · have hslo : e< s := lt_of_le_of_ne (le_of_not_gt hlow) (Ne.symm hs0)
    by_cases hhigh : 2*e< s
    · have heq : ramp (2*e) e=ᶠ[𝓝 s] fun _ => (1:ℝ) := by
        filter_upwards [eventually_gt_nhds hhigh] with a ha
        unfold ramp
        apply clip01_one
        apply (le_div_iff₀ (by linarith : 0 < 2*e-e)).mpr
        linarith
      have hn : ¬(e<s ∧ s<2*e) := fun h=>(lt_asymm hhigh h.2).elim
      rw [rampSlope,if_neg hn]
      exact (hasDerivAt_const s 1).congr_of_eventuallyEq heq
    · have hshi : s<2*e := lt_of_le_of_ne (le_of_not_gt hhigh) hs1
      have heq : ramp (2*e) e=ᶠ[𝓝 s] fun a => (a-e)/e := by
        filter_upwards [eventually_gt_nhds hslo,eventually_lt_nhds hshi] with a ha0 ha1
        unfold ramp
        rw [show 2*e-e=e by ring]
        apply clip01_self
        exact ⟨div_nonneg (sub_nonneg.mpr ha0.le) he.le,
          (div_le_iff₀ he).mpr (by linarith)⟩
      rw [rampSlope,if_pos (show e<s ∧ s<2*e from ⟨hslo,hshi⟩)]
      exact (((hasDerivAt_id s).sub_const e).div_const e).congr_of_eventuallyEq heq

def fixedCoefficient (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) : ℝ :=
  if ∃ k ∈ T.support.erase j,B k ≤ g.seedCutoff then
    ∏ k : Fin 4,ramp (2*g.margin*g.population) (g.margin*g.population)
      (rivalSlacks ξ g T B j k.succ)
  else 0

omit [Fintype ι] [Nonempty ι] in
theorem fixedCoefficient_bounds (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) : fixedCoefficient ξ g T B j ∈ Icc (0:ℝ) 1 := by
  unfold fixedCoefficient
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun _ _ => (ramp_bounds _ _ _).1),
      Finset.prod_le_one (fun _ _ => (ramp_bounds _ _ _).1) (fun _ _ => (ramp_bounds _ _ _).2)⟩
  · norm_num

omit [Nonempty ι] in

theorem alpha_eq_fixedCoefficient {ξ : ℝ} (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (hj : j ∈ T.support)
    (ha : 0 ≤ g.radius) (hr : 0 < g.requiredDemand)
    {b : ℝ} (hseed : g.seedCutoff< b) (hbL : b≤ g.multiplier)
    (hbz : b≤ g.rejectionRoot) :
    guardAlpha ξ g T (Function.update B j b)=fixedCoefficient ξ g T B j*
      ramp (2*g.margin*g.population) (g.margin*g.population)
        (rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b) := by
  classical
  have hseedEq := seed_availability_rival_only T.support B j hseed
  have hw : eligibility ξ g.multiplier g.requiredDemand b=0 := by
    apply eligibility_zero hr
    rw [exposure_zero hbL]
    positivity
  have hhi : exposure ξ (g.multiplier+g.radius) b=0 := exposure_zero (by linarith)
  have hψ : PrefixRoot.psi g.rejectionScale g.rejectionRoot b=0 := by
    simp only [PrefixRoot.psi,max_eq_left (sub_nonpos.mpr hbz),zero_div]
  unfold guardAlpha FiniteGuards.alpha fixedCoefficient
  rw [slackVector_update ξ g T B j hj b]
  change (if seeded g T (Function.update B j b) then _ else _)=_
  rw [show seeded g T (Function.update B j b) ↔
      ∃ k ∈ T.support.erase j,B k≤ g.seedCutoff from hseedEq]
  split_ifs
  · simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,slacks,Matrix.cons_val_zero,
      Matrix.cons_val_succ,hhi,hw,hψ,sub_zero,add_zero,mul_one]
    norm_num only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,Fin.succ_mk]
    norm_num only [show Fin.succ (2:Fin 3)=(3:Fin 4) by decide,
      show Fin.succ (2:Fin 4)=(3:Fin 5) by decide,
      show Fin.succ (3:Fin 4)=(4:Fin 5) by decide]
    ring
  · ring

def velocity (ξ : ℝ) (g : GuardData) (T : PureTemplate ι)
    (B : ι → ℝ) (j : ι) (b : ℝ) : ℝ :=
  if g.multiplier-g.radius< b then
    fixedCoefficient ξ g T B j*
      rampSlope (g.margin*g.population)
        (rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b)*
          (g.multiplier-g.radius)/(ξ*b^2)
  else 0

theorem exposure_bid_hasDerivAt {ξ z b : ℝ} (hξ : 0 < ξ)
    (hz : 0 < z) (hzb : z< b) (hclip : (1-ξ)*b< z) :
    HasDerivAt (fun a => exposure ξ z a) (z/(ξ*b^2)) b := by
  have hb : 0 < b := hz.trans hzb
  have heq : (fun a => exposure ξ z a)=ᶠ[𝓝 b] fun a => (a-z)/(ξ*a) := by
    have hc : ContinuousAt (fun a : ℝ => (1-ξ)*a) b := by fun_prop
    filter_upwards [eventually_gt_nhds hzb,
      hc.preimage_mem_nhds (Iio_mem_nhds hclip)] with a haz haκ
    rw [exposure_of_between hξ hz haz haκ.le]
    field_simp [hξ.ne',(hz.trans haz).ne']
  have hd := ((hasDerivAt_id b).sub_const z).div
    ((hasDerivAt_id b).const_mul ξ) (mul_pos hξ hb).ne'
  convert! hd.congr_of_eventuallyEq heq using 1
  dsimp only [id]
  field_simp [hξ.ne',hb.ne']
  ring

omit [Nonempty ι] in
theorem alpha_hasDerivAt {ξ U b H : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (g : GuardData)
    (hg : PrefixConditions ξ g H) (T : PureTemplate ι) (B : ι → ℝ)
    (j : ι) (hj : j ∈ T.support) (hseed : g.seedCutoff< b)
    (hbL : b< g.multiplier) (hbz : b< g.rejectionRoot)
    (hbU : b< U) (hclip : (1-ξ)*U≤ g.multiplier-g.radius)
    (hblo : b ≠ g.multiplier-g.radius)
    (hc0 : rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b ≠ g.margin*g.population)
    (hc1 : rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b ≠ 2*g.margin*g.population) :
    HasDerivAt (fun a => guardAlpha ξ g T (Function.update B j a))
      (velocity ξ g T B j b) b := by
  let A := rivalSlacks ξ g T B j 0
  let lo := g.multiplier-g.radius
  have heq : (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 b]
      fun a => fixedCoefficient ξ g T B j*
        ramp (2*g.margin*g.population) (g.margin*g.population) (A+exposure ξ lo a) := by
    filter_upwards [eventually_gt_nhds hseed,eventually_lt_nhds hbL,
      eventually_lt_nhds hbz] with a hsa haL haz
    exact alpha_eq_fixedCoefficient g T B j hj hg.radius_nonneg hg.requiredDemand_pos hsa haL.le haz.le
  by_cases hlo : lo< b
  · have hκb : (1-ξ)*b< lo :=
      (mul_lt_mul_of_pos_left hbU (sub_pos.mpr hξ1)).trans_le hclip
    have he := (exposure_bid_hasDerivAt hξ hg.lower_pos hlo hκb).const_add A
    have hramp := normalized_ramp_hasDerivAt (mul_pos hg.margin_pos hg.population_pos) hc0
      (by simpa only [mul_assoc] using hc1)
    rw [show 2*(g.margin*g.population)=2*g.margin*g.population by ring] at hramp
    have hd := (hramp.comp b he).const_mul (fixedCoefficient ξ g T B j)
    convert! hd.congr_of_eventuallyEq heq using 1
    have hlo' : g.multiplier-g.radius<b := hlo
    rw [velocity,if_pos hlo']
    ring
  · have hbl : b< lo := lt_of_le_of_ne (le_of_not_gt hlo) hblo
    have he0 : (fun a => exposure ξ lo a)=ᶠ[𝓝 b] fun _ => (0:ℝ) :=
      (eventually_lt_nhds hbl).mono fun a ha => exposure_zero ha.le
    have hc : (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 b]
        fun _ => fixedCoefficient ξ g T B j*ramp (2*g.margin*g.population) (g.margin*g.population) A := by
      filter_upwards [heq,he0] with a ha he
      simpa only [he,add_zero] using ha
    have hnot : ¬g.multiplier-g.radius<b := hlo
    rw [velocity,if_neg hnot]
    exact (hasDerivAt_const b _).congr_of_eventuallyEq hc

omit [Fintype ι] [Nonempty ι] in
theorem velocity_bounds {ξ b : ℝ} (hξ : 0 < ξ)
    (g : GuardData) (hlo : 0 < g.multiplier-g.radius)
    (hε : 0 < g.margin) (hM : 0 < g.population)
    (T : PureTemplate ι) (B : ι → ℝ) (j : ι) :
    velocity ξ g T B j b ∈ Icc (0:ℝ)
      (1/(ξ*(g.multiplier-g.radius)*g.margin*g.population)) := by
  unfold velocity
  split_ifs with hb
  · have hc := fixedCoefficient_bounds ξ g T B j
    have hr := rampSlope_bounds (mul_pos hε hM)
      (rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b)
    have hb0 := hlo.trans hb
    have hprod : fixedCoefficient ξ g T B j*
        rampSlope (g.margin*g.population)
          (rivalSlacks ξ g T B j 0+exposure ξ (g.multiplier-g.radius) b) ≤
        1/(g.margin*g.population) := by nlinarith [hc.1,hc.2,hr.1,hr.2]
    constructor
    · exact div_nonneg (mul_nonneg (mul_nonneg hc.1 hr.1) hlo.le) (by positivity)
    · calc
        _ ≤ (1/(g.margin*g.population))*(g.multiplier-g.radius)/(ξ*b^2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hlo.le) (by positivity)
        _ ≤ 1/(ξ*(g.multiplier-g.radius)*g.margin*g.population) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          have hs : (g.multiplier-g.radius)^2 ≤ b^2 := by nlinarith
          field_simp [(mul_pos hε hM).ne']
          nlinarith [mul_nonneg (mul_pos hξ (mul_pos hε hM)).le (sub_nonneg.mpr hs)]
  · exact ⟨le_rfl,by positivity⟩

theorem mul_hasDerivAt_zero {f a : ℝ → ℝ} {b : ℝ}
    (hf : HasDerivAt f 0 b) (hf0 : f b=0) (ha : ContinuousAt a b) :
    HasDerivAt (fun x => a x*f x) 0 b := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hh := (ha.tendsto.mono_left nhdsWithin_le_nhds).mul hf.tendsto_slope
  have heq : slope (fun x => a x*f x) b=ᶠ[𝓝[≠] b] fun x => a x*slope f b x := by
    exact Eventually.of_forall fun x => by simp only [slope_fun_def_field,hf0,mul_zero,sub_zero]; ring
  simpa only [mul_zero] using hh.congr' heq.symm

omit [Nonempty ι] in

theorem alpha_zero_eventually_at_lower {ξ H : ℝ} (g : GuardData)
    (hg : PrefixConditions ξ g H) (T : PureTemplate ι) (B : ι → ℝ)
    (j : ι) (hj : j ∈ T.support) (hξ : 0 < ξ) (ha : 0 < g.radius)
    (hz : g.multiplier-g.radius< g.rejectionRoot)
    (hc : rivalSlacks ξ g T B j 0 ≠ g.margin*g.population)
    (hzero : guardAlpha ξ g T (Function.update B j (g.multiplier-g.radius))=0) :
    (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 (g.multiplier-g.radius)]
      fun _ => (0:ℝ) := by
  let lo := g.multiplier-g.radius
  let A := rivalSlacks ξ g T B j 0
  let d := fixedCoefficient ξ g T B j
  have heq : (fun a => guardAlpha ξ g T (Function.update B j a))=ᶠ[𝓝 lo]
      fun a => d*ramp (2*g.margin*g.population) (g.margin*g.population) (A+exposure ξ lo a) := by
    filter_upwards [eventually_gt_nhds hg.seed_below_lower,
      eventually_lt_nhds (show lo< g.multiplier by dsimp [lo]; linarith),eventually_lt_nhds hz]
      with a hsa haL haz
    exact alpha_eq_fixedCoefficient g T B j hj hg.radius_nonneg hg.requiredDemand_pos hsa haL.le haz.le
  have hbase : d*ramp (2*g.margin*g.population) (g.margin*g.population) A=0 := by
    have he := alpha_eq_fixedCoefficient (ξ:=ξ) g T B j hj hg.radius_nonneg hg.requiredDemand_pos
      hg.seed_below_lower (show lo≤ g.multiplier by dsimp [lo]; linarith) hz.le
    simpa only [hzero,exposure_zero le_rfl,add_zero] using he.symm
  rcases mul_eq_zero.mp hbase with hd | hramp
  · filter_upwards [heq] with a he
    simpa only [hd,zero_mul] using he
  · have hA : A< g.margin*g.population := by
      by_contra hn
      have hgt : g.margin*g.population< A :=
        lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hc)
      have hpos : 0< ramp (2*g.margin*g.population) (g.margin*g.population) A := by
        unfold ramp clip01
        apply lt_max_of_lt_right
        exact lt_min (by norm_num) (div_pos (sub_pos.mpr hgt) (by nlinarith [mul_pos hg.margin_pos hg.population_pos]))
      rw [hramp] at hpos
      exact lt_irrefl _ hpos
    have hcont : ContinuousAt (fun a => A+exposure ξ lo a) lo :=
      (continuous_exposure hξ hg.lower_pos).continuousAt.const_add A
    have he0 : ∀ᶠ a in 𝓝 lo,A+exposure ξ lo a< g.margin*g.population :=
      hcont.preimage_mem_nhds (Iio_mem_nhds (by simpa only [exposure_zero le_rfl,add_zero] using hA))
    filter_upwards [heq,he0] with a he ha'
    simpa only [ramp_zero (show g.margin*g.population<2*g.margin*g.population by
      nlinarith [mul_pos hg.margin_pos hg.population_pos]) ha'.le,mul_zero] using he

end FCAppendix.Affine.Uniform06.GuardDerivative
