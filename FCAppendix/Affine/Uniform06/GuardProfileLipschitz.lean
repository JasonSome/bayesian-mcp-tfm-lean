import FCAppendix.Affine.Uniform06.ZeroWeightFocal

noncomputable section
namespace FCAppendix.Affine.Uniform06.GuardProfileLipschitz

open MeasureTheory Set
open scoped BigOperators
open LowBody LiteralExperiment FiniteGuards

lemma max_l1 (a b c d : ℝ) :
    |max a b-max c d| ≤ |a-c|+|b-d| := by
  rw [abs_le]
  constructor
  · have h1 : c ≤ max a b+|a-c|+|b-d| := by
      linarith [le_max_left a b,(abs_le.mp (le_refl |a-c|)).1,abs_nonneg (b-d)]
    have h2 : d ≤ max a b+|a-c|+|b-d| := by
      linarith [le_max_right a b,(abs_le.mp (le_refl |b-d|)).1,abs_nonneg (a-c)]
    linarith [max_le h1 h2]
  · have h1 : a ≤ max c d+|a-c|+|b-d| := by
      linarith [le_max_left c d,le_abs_self (a-c),abs_nonneg (b-d)]
    have h2 : b ≤ max c d+|a-c|+|b-d| := by
      linarith [le_max_right c d,le_abs_self (b-d),abs_nonneg (a-c)]
    linarith [max_le h1 h2]

lemma min_l1 (a b c d : ℝ) :
    |min a b-min c d| ≤ |a-c|+|b-d| := by
  have h1 : min a b-(|a-c|+|b-d|) ≤ c := by
    linarith [min_le_left a b,le_abs_self (a-c),abs_nonneg (b-d)]
  have h2 : min a b-(|a-c|+|b-d|) ≤ d := by
    linarith [min_le_right a b,le_abs_self (b-d),abs_nonneg (a-c)]
  have h3 : min c d-(|a-c|+|b-d|) ≤ a := by
    linarith [min_le_left c d,neg_le_abs (a-c),abs_nonneg (b-d)]
  have h4 : min c d-(|a-c|+|b-d|) ≤ b := by
    linarith [min_le_right c d,neg_le_abs (b-d),abs_nonneg (a-c)]
  rw [abs_le]
  constructor <;> linarith [le_min h1 h2,le_min h3 h4]

def clampedResidual (lower capacity upper : ℝ) : ℝ :=
  min lower (max 0 (capacity-upper))

lemma clampedResidual_l1 (l c u l' c' u' : ℝ) :
    |clampedResidual l c u-clampedResidual l' c' u'| ≤
      |l-l'|+|c-c'|+|u-u'| := by
  have hm := min_l1 l (max 0 (c-u)) l' (max 0 (c'-u'))
  have hx := max_l1 0 (c-u) 0 (c'-u')
  have hd : |(c-u)-(c'-u')| ≤ |c-c'|+|u-u'| := by
    have he : (c-u)-(c'-u')=(c-c')-(u-u') := by ring
    rw [he]
    exact abs_sub _ _
  simp only [sub_self,abs_zero,zero_add] at hx
  unfold clampedResidual
  linarith

lemma nat_sub_cast (c u : ℕ) : ((c-u:ℕ):ℝ)=max 0 ((c:ℝ)-(u:ℝ)) := by
  by_cases hu : u ≤ c
  · rw [Nat.cast_sub hu,max_eq_right (sub_nonneg.mpr (by exact_mod_cast hu))]
  · have hu' : c ≤ u := le_of_lt (lt_of_not_ge hu)
    rw [Nat.sub_eq_zero_of_le hu',Nat.cast_zero,
      max_eq_left (sub_nonpos.mpr (by exact_mod_cast hu'))]

lemma min_div_pos (a b M : ℝ) (hM : 0 < M) :
    min a b/M=min (a/M) (b/M) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (div_le_div_of_nonneg_right h hM.le)]
  · rw [min_eq_right h,min_eq_right (div_le_div_of_nonneg_right h hM.le)]

lemma max_div_pos (a b M : ℝ) (hM : 0 < M) :
    max a b/M=max (a/M) (b/M) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h,max_eq_right (div_le_div_of_nonneg_right h hM.le)]
  · rw [max_eq_left h,max_eq_left (div_le_div_of_nonneg_right h hM.le)]

lemma normalized_residual (l c u : ℕ) {M : ℝ} (hM : 0 < M) :
    ((min l (c-u):ℕ):ℝ)/M=clampedResidual ((l:ℝ)/M) ((c:ℝ)/M) ((u:ℝ)/M) := by
  rw [Nat.cast_min,nat_sub_cast,min_div_pos _ _ _ hM,max_div_pos _ _ _ hM]
  simp only [zero_div,sub_div,clampedResidual]

def profileSlacks (v : Fin 7 → ℝ) : Fin 5 → ℝ :=
  ![v 0-max (v 4) (v 5),min (v 4) (v 5)-v 1,
    v 2-(max (v 4) (v 5)-min (v 4) (v 5)),v 3-v 4-v 5,v 6]

def normalizedProfile {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ) : Fin 7 → ℝ :=
  ![demand ξ T B (g.multiplier-g.radius)/g.population,
    demand ξ T B (g.multiplier+g.radius)/g.population,
    FCAppendix.Affine.WeightedSampling.totalWeight (weights ξ g T B)/g.population,
    (∑ j ∈ T.support,PrefixRoot.psi g.rejectionScale g.rejectionRoot (B j))/g.population,
    (T.residual₀:ℝ)/g.population,(T.residual₁:ℝ)/g.population,g.countMargin/g.population]

theorem actual_normalized_slacks {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ)
    (hM : 0 < g.population) (j : Fin 5) :
    slackVector ξ g T B j/g.population=profileSlacks (normalizedProfile ξ g T B) j := by
  have hmin : ((small T:ℕ):ℝ)/g.population=
      min ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population) := by
    rw [small,Nat.cast_min,min_div_pos _ _ _ hM]
  have himb : (imbalance T:ℝ)/g.population=
      max ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population)-
      min ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population) := by
    have hm : min T.residual₀ T.residual₁ ≤ max T.residual₀ T.residual₁ :=
      (min_le_left _ _).trans (le_max_left _ _)
    rw [imbalance,small,Nat.cast_sub hm,Nat.cast_max,Nat.cast_min,sub_div,
      max_div_pos _ _ _ hM,min_div_pos _ _ _ hM]
  fin_cases j
  · change (demand ξ T B (g.multiplier-g.radius)-(small T:ℝ)-(imbalance T:ℝ))/g.population =
      demand ξ T B (g.multiplier-g.radius)/g.population -
        max ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population)
    rw [sub_div, sub_div, hmin, himb]
    ring
  · change ((small T:ℝ)-demand ξ T B (g.multiplier+g.radius))/g.population =
      min ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population) -
        demand ξ T B (g.multiplier+g.radius)/g.population
    rw [sub_div,hmin]
  · change (FCAppendix.Affine.WeightedSampling.totalWeight (weights ξ g T B)-(imbalance T:ℝ))/g.population =
      FCAppendix.Affine.WeightedSampling.totalWeight (weights ξ g T B)/g.population -
        (max ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population) -
          min ((T.residual₀:ℝ)/g.population) ((T.residual₁:ℝ)/g.population))
    rw [sub_div,himb]
  · change ((∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (B j))-
        (T.residual₀:ℝ)-(T.residual₁:ℝ))/g.population =
      (∑ j ∈ T.support, PrefixRoot.psi g.rejectionScale g.rejectionRoot (B j))/g.population -
        (T.residual₀:ℝ)/g.population-(T.residual₁:ℝ)/g.population
    simp only [sub_div]
  · rfl

theorem profileSlacks_l1 (u v : Fin 7 → ℝ) :
    (∑ j : Fin 5,|profileSlacks u j-profileSlacks v j|) ≤
      5*(∑ j : Fin 7,|u j-v j|) := by
  have hmx := max_l1 (u 4) (u 5) (v 4) (v 5)
  have hmn := min_l1 (u 4) (u 5) (v 4) (v 5)
  have h0 : |(u 0-max (u 4) (u 5))-(v 0-max (v 4) (v 5))| ≤
      |u 0-v 0|+|u 4-v 4|+|u 5-v 5| := by
    have he : (u 0-max (u 4) (u 5))-(v 0-max (v 4) (v 5))=
        (u 0-v 0)-(max (u 4) (u 5)-max (v 4) (v 5)) := by ring
    rw [he]
    linarith [abs_sub (u 0-v 0) (max (u 4) (u 5)-max (v 4) (v 5))]
  have h1 : |(min (u 4) (u 5)-u 1)-(min (v 4) (v 5)-v 1)| ≤
      |u 1-v 1|+|u 4-v 4|+|u 5-v 5| := by
    have he : (min (u 4) (u 5)-u 1)-(min (v 4) (v 5)-v 1)=
        (min (u 4) (u 5)-min (v 4) (v 5))-(u 1-v 1) := by ring
    rw [he]
    linarith [abs_sub (min (u 4) (u 5)-min (v 4) (v 5)) (u 1-v 1)]
  have h2 : |(u 2-(max (u 4) (u 5)-min (u 4) (u 5)))-
      (v 2-(max (v 4) (v 5)-min (v 4) (v 5)))| ≤
      |u 2-v 2|+2*(|u 4-v 4|+|u 5-v 5|) := by
    have he : (u 2-(max (u 4) (u 5)-min (u 4) (u 5)))-
        (v 2-(max (v 4) (v 5)-min (v 4) (v 5)))=
        (u 2-v 2)-((max (u 4) (u 5)-max (v 4) (v 5))-
          (min (u 4) (u 5)-min (v 4) (v 5))) := by ring
    rw [he]
    linarith [abs_sub (u 2-v 2)
      ((max (u 4) (u 5)-max (v 4) (v 5))-(min (u 4) (u 5)-min (v 4) (v 5))),
      abs_sub (max (u 4) (u 5)-max (v 4) (v 5)) (min (u 4) (u 5)-min (v 4) (v 5))]
  have h3 : |(u 3-u 4-u 5)-(v 3-v 4-v 5)| ≤ |u 3-v 3|+|u 4-v 4|+|u 5-v 5| := by
    have he : (u 3-u 4-u 5)-(v 3-v 4-v 5)=(u 3-v 3)-(u 4-v 4)-(u 5-v 5) := by ring
    rw [he]
    linarith [abs_sub ((u 3-v 3)-(u 4-v 4)) (u 5-v 5),abs_sub (u 3-v 3) (u 4-v 4)]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,profileSlacks,Matrix.cons_val_zero,
    Matrix.cons_val_succ,add_zero]
  change _ ≤ 5*(|u 0-v 0|+(|u 1-v 1|+(|u 2-v 2|+(|u 3-v 3|+
    (|u 4-v 4|+(|u 5-v 5|+|u 6-v 6|))))))
  linarith [abs_nonneg (u 0-v 0),abs_nonneg (u 1-v 1),abs_nonneg (u 2-v 2),
    abs_nonneg (u 3-v 3),abs_nonneg (u 6-v 6)]

lemma ramp_rescale {ε M s : ℝ} (hM : 0 < M) :
    ramp (2*ε*M) (ε*M) s=ramp (2*ε) ε (s/M) := by
  unfold ramp
  congr 1
  by_cases hε : ε=0
  · simp [hε]
  · field_simp [hM.ne',hε]

def profileAlpha (ε : ℝ) (v : Fin 7 → ℝ) : ℝ :=
  ∏ j : Fin 5,ramp (2*ε) ε (profileSlacks v j)

theorem profileAlpha_bounds (ε : ℝ) (v : Fin 7 → ℝ) : profileAlpha ε v ∈ Icc (0:ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (ramp_bounds _ _ _).1),
    Finset.prod_le_one (fun _ _ => (ramp_bounds _ _ _).1) (fun _ _ => (ramp_bounds _ _ _).2)⟩

theorem profileAlpha_l1 {ε : ℝ} (hε : 0 < ε) (u v : Fin 7 → ℝ) :
    |profileAlpha ε u-profileAlpha ε v| ≤ (5/ε)*(∑ j : Fin 7,|u j-v j|) := by
  have hh := alpha_increment hε (by norm_num : (0:ℝ) < 1) True (profileSlacks u) (profileSlacks v)
  simp only [alpha,if_true,mul_one] at hh
  change |profileAlpha ε u-profileAlpha ε v| ≤ _ at hh
  exact hh.trans (by
    have hp := div_le_div_of_nonneg_right (profileSlacks_l1 u v) hε.le
    convert! hp using 1
    ring)

open scoped Classical in
theorem actual_guard_profile {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ)
    (hM : 0 < g.population) :
    guardAlpha ξ g T B=if seeded g T B then
      profileAlpha g.margin (normalizedProfile ξ g T B) else 0 := by
  classical
  unfold guardAlpha alpha profileAlpha
  split_ifs
  · apply Finset.prod_congr rfl
    intro j _
    rw [ramp_rescale hM,actual_normalized_slacks ξ g T B hM j]
  · rfl

open scoped Classical in

theorem actual_guard_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι → ℝ)
    (hM : 0 < g.population) (hε : 0 < g.margin) (v : Fin 7 → ℝ) :
    |guardAlpha ξ g T B-profileAlpha g.margin v| ≤
      (5/g.margin)*(∑ j : Fin 7,|normalizedProfile ξ g T B j-v j|)+
        (if seeded g T B then 0 else 1) := by
  classical
  rw [actual_guard_profile ξ g T B hM]
  split_ifs with hs
  · simpa only [add_zero] using profileAlpha_l1 hε (normalizedProfile ξ g T B) v
  · rw [zero_sub,abs_neg,abs_of_nonneg (profileAlpha_bounds g.margin v).1]
    have hp := (profileAlpha_bounds g.margin v).2
    have he : 0 ≤ (5/g.margin)*(∑ j : Fin 7,|normalizedProfile ξ g T B j-v j|) := by positivity
    linarith

end FCAppendix.Affine.Uniform06.GuardProfileLipschitz
