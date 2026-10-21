import FCAppendix.Affine.Uniform06.WeightedBorelContraction
import FCAppendix.Affine.Uniform06.ICSourceLocalAC

noncomputable section
namespace FCAppendix.Affine.Uniform06.SharpICAbsorption

open MeasureTheory Set Filter Topology
open Rank ScaledMeasure ICAbsorption WeightedBorelContraction

theorem min_rent_geometry {m a : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < min a (1/m) ∧ a ≤ m*min a (1/m) ∧
      1/(m*min a (1/m)) ≤ rentWeight m a := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hd : 0 < min a (1/m) := lt_min ha (by positivity)
  refine ⟨hd,?_,?_⟩
  · by_cases hh : a ≤ 1/m
    · rw [min_eq_left hh]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hh)]
      simpa [hm0.ne'] using ha1
  · by_cases hh : a ≤ 1/m
    · rw [min_eq_left hh]
      unfold rentWeight
      linarith
    · rw [min_eq_right (le_of_not_ge hh)]
      simp only [mul_one_div_cancel hm0.ne',div_one]
      unfold rentWeight
      exact le_add_of_nonneg_right (by positivity)

set_option maxHeartbeats 1000000 in

theorem sharp_finite_IC_absorb
    {η r P m L₀ Q B L a b v Sa Sb Da Db u z : ℝ}
    (hη : η ∈ Icc (0:ℝ) 1) (hr : 0 < r) (hP : 0 < P)
    (hm : 1 ≤ m) (hL₀ : 0 < L₀) (hQ : L₀ ≤ Q)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hLQ : L ≤ Q)
    (ha : 0 < a) (ha1 : a ≤ 1) (hab : a ≤ b) (hb2 : b ≤ 2*a)
    (hstep : b-a ≤ r*min a (1/m)/2)
    (hrent : r*min a (1/m) ≤ v-a)
    (hu : 0 ≤ u) (hz : 0 ≤ z)
    (hIC : payoff η v b Sb Db ≤ payoff η v a Sa Da)
    (hfirst : (m/P)*Q*u ≤ Sb-Sa)
    (hdup : Db-Da ≤ B*(u+z)+L*(b-a)/a)
    (hlevel : Sa+η*Da ≤ 4*Q)
    (hsmall : 8*P*B < r*L₀) :
    u ≤ (24*P/r)*rentWeight m a*(b-a)+(8*P*B/(r*L₀))*z := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hQ0 : 0 < Q := hL₀.trans_le hQ
  obtain ⟨hd,had,hweight⟩ := min_rent_geometry hm ha ha1
  let d := min a (1/m)
  let c := r*m*d*Q/(4*P)
  have hc : 0 < c := by dsimp [c,d]; positivity
  have hb : 0 < b := ha.trans_le hab
  have hΔ : 0 ≤ b-a := sub_nonneg.mpr hab
  have hvb : r*d/2 ≤ v-b := by dsimp only [d]; linarith
  have hS0 : 0 ≤ Sb-Sa := (show 0 ≤ (m/P)*Q*u by positivity).trans hfirst
  have hhlo := mul_le_mul hvb hfirst (show 0 ≤ (m/P)*Q*u by positivity)
    (show 0 ≤ v-b by linarith [mul_pos hr hd])
  have hic := IC_increment_upper hIC
  have hlev := mul_le_mul_of_nonneg_left hlevel hΔ
  have hdup' := mul_le_mul_of_nonneg_left hdup (mul_nonneg hη.1 hb.le)
  have hηb : η*b ≤ 2*a := by
    have hh := mul_le_mul_of_nonneg_right hη.2 hb.le
    nlinarith
  have hBp : η*b*B*(u+z) ≤ 2*a*B*(u+z) := by
    have hh := mul_le_mul_of_nonneg_right hηb (show 0 ≤ B*(u+z) by positivity)
    nlinarith
  have hLp : η*b*(L*(b-a)/a) ≤ 2*L*(b-a) := by
    have hh := mul_le_mul_of_nonneg_right hηb (show 0 ≤ L*(b-a)/a by positivity)
    convert! hh using 1
    field_simp [ha.ne']
  have hcoef : 2*a*B ≤ c := by
    apply (le_div_iff₀ (by positivity : 0 < 4*P)).mpr
    have hh := mul_le_mul_of_nonneg_left hQ hr.le
    have hsmall' : 8*P*B ≤ r*Q := hsmall.le.trans hh
    have h₁ := mul_le_mul_of_nonneg_right had (show 0 ≤ 8*P*B by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ m*d by dsimp [d]; positivity)
    nlinarith
  have hlower : 2*c*u ≤ (v-b)*(Sb-Sa) := by
    have he : r*d/2*((m/P)*Q*u)=2*c*u := by
      dsimp only [c]
      field_simp [hP.ne']
      ring
    rwa [he] at hhlo
  have hcost : c*u ≤ 6*Q*(b-a)+2*a*B*z := by
    have hcu := mul_le_mul_of_nonneg_right hcoef hu
    have hLΔ := mul_le_mul_of_nonneg_right hLQ hΔ
    nlinarith only [hic,hlev,hdup',hBp,hLp,hlower,hcu,hLΔ]
  have hquot : u ≤ (6*Q/c)*(b-a)+(2*a*B/c)*z := by
    have hh : u ≤ (6*Q*(b-a)+2*a*B*z)/c :=
      (le_div_iff₀ hc).mpr (by nlinarith only [hcost])
    convert! hh using 1
    field_simp [hc.ne']
  have hcosteq : 6*Q/c=(24*P/r)*(1/(m*d)) := by
    dsimp only [c]
    field_simp [hr.ne',hP.ne',hm0.ne',hd.ne',hQ0.ne']
    ring
  have hcostbd : 6*Q/c ≤ (24*P/r)*rentWeight m a := by
    rw [hcosteq]
    exact mul_le_mul_of_nonneg_left hweight (by positivity)
  have hscale : 2*a*B/c ≤ 8*P*B/(r*L₀) := by
    have h₁ : a/(m*d) ≤ 1 := (div_le_one (by dsimp [d]; positivity)).mpr had
    have h₂ : B/Q ≤ B/L₀ := div_le_div_of_nonneg_left hB hL₀ hQ
    have h₃ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ B/Q by positivity)
    have h₄ := mul_le_mul_of_nonneg_left (h₃.trans (by simpa using h₂))
      (show 0 ≤ 8*P/r by positivity)
    dsimp only [c]
    convert! h₄ using 1 <;>
      field_simp [hr.ne',hP.ne',hm0.ne',hd.ne',hQ0.ne',hL₀.ne']
    ring
  exact hquot.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcostbd hΔ) (mul_le_mul_of_nonneg_right hscale hz))

theorem sharp_IC_weighted_Borel
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hatom : ∀ x : ℝ, μ {x}=0)
    (M ℓ cap S D Q : ℝ → ℝ) (η κ r P m L₀ B L hi δS : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hScont : ContinuousOn S (Ioi 0)) (hDcont : ContinuousOn D (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b))
    (hfloor : ∀ᵐ b ∂μ, ℓ (M b) ≤ b)
    (hcapLegal : ∀ v b : ℝ, b < v → b ≤ hi → b < cap v)
    (hη : η ∈ Icc (0:ℝ) 1) (hκ : 0 < κ) (hr : 0 < r) (hP : 0 < P)
    (hm : 1 ≤ m) (hL₀ : 0 < L₀) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hsmall : 8*P*B < r*L₀) (hLsmall : L ≤ L₀) (hhi : hi ≤ 1) (hδS : 0 < δS)
    (hQ : ∀ a ∈ Ioc 0 hi, L₀ ≤ Q a)
    (hrent : ∀ a ∈ μ.support, a ∈ Ioc 0 hi → r*min a (1/m) ≤ M a-a)
    (hlevel : ∀ a ∈ Ioc 0 hi, S a+η*D a ≤ 4*Q a)
    (hfirst : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi → b-a ≤ δS →
      (m/P)*Q a*μ.real (Ioc a b) ≤ S b-S a)
    (hdup : ∀ a b : ℝ, 0 < a → a < b → b ≤ hi →
      D b-D a ≤ B*(μ.real (Ioc a b)+μ.real (Ioc (κ*a) (κ*b)))+L*(b-a)/a) :
    ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo hi →
      μ.real A ≤ (48*P/r)*(∫ b in A, rentWeight m b)+
        (8*P*B/(r*L₀))*μ.real (scaledSet κ A) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hfloorS := continuous_le_on_closed_support μ (fun b => ℓ (M b)) id
    (hℓ.comp hM) continuous_id hfloor
  intro lo hlo A hAm hA
  let lo' := lo/2
  have hlo' : 0 < lo' := half_pos hlo
  let δ := min δS (min lo' (r*min lo' (1/m)/2))
  have hδ : 0 < δ := by dsimp [δ,lo']; positivity
  have hδlo : δ ≤ lo' := (min_le_right _ _).trans (min_le_left _ _)
  have hC : 0 ≤ 24*P/r := by positivity
  have hε : 0 ≤ 8*P*B/(r*L₀) := by positivity
  have hborel := weighted_Borel_of_anchored_intervals (hi := hi) μ hatom hκ hC hε hm0 hlo' hδ hδlo
  have hanc : ∀ a ∈ μ.support, ∀ b : ℝ,
      a ∈ Icc lo' hi → b ∈ Icc lo' hi → a ≤ b → b-a ≤ δ →
        μ.real (Ioc a b) ≤ (24*P/r)*rentWeight m a*(b-a)+
          (8*P*B/(r*L₀))*μ.real (Ioc (κ*a) (κ*b)) := by
    intro a ha b haI hbI hab hstep
    by_cases heq : a=b
    · subst b
      simp only [Ioc_self,measureReal_empty,sub_self,mul_zero,zero_add]
      exact le_rfl
    have hab' : a < b := lt_of_le_of_ne hab heq
    have ha0 : 0 < a := hlo'.trans_le haI.1
    have haHi : a ∈ Ioc 0 hi := ⟨ha0,haI.2⟩
    have hrenta := hrent a ha haHi
    have hstep' : b-a ≤ r*min a (1/m)/2 := by
      have hh : b-a ≤ r*min lo' (1/m)/2 :=
        hstep.trans ((min_le_right _ _).trans (min_le_right _ _))
      exact hh.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_min_right _ haI.1) hr.le) (by norm_num))
    have hbM : b < M a := by
      have hp : 0 < r*min a (1/m)/2 := by positivity
      linarith
    have hic := IC_on_closed_used_support μ M ℓ cap S D η
      hM hℓ hcap hScont hDcont hIC a ha ha0 b (ha0.trans hab')
      ((hfloorS a ha).trans_lt hab') (hcapLegal (M a) b hbM hbI.2)
    exact sharp_finite_IC_absorb hη hr hP hm hL₀ (hQ a haHi) hB hL
      (hLsmall.trans (hQ a haHi)) ha0 (haI.2.trans hhi) hab
      (by linarith [hstep.trans hδlo,haI.1]) hstep' hrenta
      measureReal_nonneg measureReal_nonneg hic
      (hfirst a b ha0 hab' hbI.2 (hstep.trans (min_le_left _ _)))
      (hdup a b ha0 hab' hbI.2) (hlevel a haHi) hsmall
  have hh := hborel hanc A hAm (fun b hb =>
    ⟨(show lo' < lo by dsimp [lo']; linarith).trans_le (hA hb).1,(hA hb).2⟩)
  convert! hh using 1
  ring

theorem sharp_IC_integrated_density
    (μ : Measure ℝ) [IsFiniteMeasure μ] {κ ε C m hi : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε < 1)
    (hC : 0 ≤ C) (hm : 0 < m)
    (hBorel : ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo hi →
      μ.real A ≤ C*(∫ b in A, rentWeight m b)+ε*μ.real (scaledSet κ A)) :
    μ.restrict (Ioc 0 hi) ≪ volume ∧
      ∀ lo : ℝ, 0 < lo → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc lo hi →
        μ.real A ≤ C*(volume.real A/(1-ε*κ)+(∫ b in A, 1/(m*b))/(1-ε)) := by
  refine ⟨local_ac_of_weighted_Borel_contraction μ hκ hκ1 hε hε1 hBorel,?_⟩
  intro lo hlo A hAm hA
  exact integrated_density_bound μ hκ hκ1 hε hε1 hC hm hBorel hlo hAm hA

end FCAppendix.Affine.Uniform06.SharpICAbsorption
