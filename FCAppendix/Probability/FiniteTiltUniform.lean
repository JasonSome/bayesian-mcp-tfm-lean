import FCAppendix.Probability.FiniteTiltCalculus

namespace FCAppendix.FiniteCramer

open Real Set
open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem tilt_mass_ge_exp_neg (μ : FiniteLaw Ω) (X : Ω → ℝ) {B θ : ℝ}
    (hX0 : ∀ x, 0 ≤ X x) (hXB : ∀ x, X x ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : Ω) :
    exp (-B) * μ.mass x ≤ (tilted μ X θ).mass x := by
  have hZ : Z μ X θ ≤ exp B := by
    apply μ.expect_le_const
    intro y
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hθ1 (hX0 y)
    have hh' : θ * X y ≤ X y := by simpa only [one_mul] using hh
    exact hh'.trans (hXB y)
  have hE : 1 ≤ exp (θ * X x) := one_le_exp (mul_nonneg hθ0 (hX0 x))
  have hprod : exp (-B) * Z μ X θ ≤ 1 := by
    calc
      _ ≤ exp (-B) * exp B := mul_le_mul_of_nonneg_left hZ (exp_pos _).le
      _ = 1 := by rw [← exp_add]; simp
  change exp (-B) * μ.mass x ≤ μ.mass x * exp (θ * X x) / Z μ X θ
  apply (le_div_iff₀ (Z_pos μ X θ)).mpr
  have h1 := mul_le_mul_of_nonneg_left hprod (μ.nonneg x)
  have h2 := mul_le_mul_of_nonneg_left hE (μ.nonneg x)
  nlinarith

theorem tilt_prob_ge_exp_neg (μ : FiniteLaw Ω) (X : Ω → ℝ) {B θ : ℝ}
    (hX0 : ∀ x, 0 ≤ X x) (hXB : ∀ x, X x ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (E : Ω → Prop) :
    exp (-B) * μ.prob E ≤ (tilted μ X θ).prob E := by
  classical
  unfold FiniteLaw.prob FiniteLaw.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : E x
  · simp only [if_pos hx, mul_one]
    exact tilt_mass_ge_exp_neg μ X hX0 hXB hθ0 hθ1 x
  · simp [hx]

theorem variance_ge_separated_classes (ν : FiniteLaw Ω) (X : Ω → ℝ)
    {a b : ℝ} (ha : a ≤ ν.prob (fun x => X x = 1))
    (hb : b ≤ ν.prob (fun x => 2 ≤ X x)) :
    min a b / 4 ≤ variance ν X := by
  classical
  by_cases hm : ν.expect X ≤ 3 / 2
  · have hpoint : ∀ x, (if 2 ≤ X x then (1 : ℝ) else 0) / 4 ≤
        (X x - ν.expect X) ^ 2 := by
      intro x
      by_cases hx : 2 ≤ X x
      · rw [if_pos hx]
        have hd : 1 / 2 ≤ X x - ν.expect X := by linarith
        nlinarith [sq_nonneg (X x - ν.expect X - 1 / 2)]
      · simp only [if_neg hx, zero_div]
        exact sq_nonneg _
    have he := ν.expect_mono hpoint
    simp_rw [div_eq_mul_inv] at he
    rw [ν.expect_mul_const] at he
    rw [← FiniteLaw.prob_eq_expect] at he
    change ν.prob (fun x => 2 ≤ X x) * (4 : ℝ)⁻¹ ≤ variance ν X at he
    have hmin := min_le_right a b
    linarith
  · have hm' : 3 / 2 < ν.expect X := lt_of_not_ge hm
    have hpoint : ∀ x, (if X x = 1 then (1 : ℝ) else 0) / 4 ≤
        (X x - ν.expect X) ^ 2 := by
      intro x
      by_cases hx : X x = 1
      · rw [if_pos hx, hx]
        nlinarith [sq_nonneg (ν.expect X - 3 / 2)]
      · simp only [if_neg hx, zero_div]
        exact sq_nonneg _
    have he := ν.expect_mono hpoint
    simp_rw [div_eq_mul_inv] at he
    rw [ν.expect_mul_const] at he
    rw [← FiniteLaw.prob_eq_expect] at he
    change ν.prob (fun x => X x = 1) * (4 : ℝ)⁻¹ ≤ variance ν X at he
    have hmin := min_le_left a b
    linarith

theorem tilted_variance_ge (μ : FiniteLaw Ω) (X : Ω → ℝ) {B a b θ : ℝ}
    (hX0 : ∀ x, 0 ≤ X x) (hXB : ∀ x, X x ≤ B)
    (ha : a ≤ μ.prob (fun x => X x = 1))
    (hb : b ≤ μ.prob (fun x => 2 ≤ X x))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    exp (-B) * min a b / 4 ≤ variance (tilted μ X θ) X := by
  have hpa := tilt_prob_ge_exp_neg μ X hX0 hXB hθ0 hθ1 (fun x => X x = 1)
  have hpb := tilt_prob_ge_exp_neg μ X hX0 hXB hθ0 hθ1 (fun x => 2 ≤ X x)
  have hh := variance_ge_separated_classes (tilted μ X θ) X
    ((mul_le_mul_of_nonneg_left ha (exp_pos _).le).trans hpa)
    ((mul_le_mul_of_nonneg_left hb (exp_pos _).le).trans hpb)
  have hmin : min (exp (-B) * a) (exp (-B) * b) = exp (-B) * min a b := by
    rcases le_total a b with hab | hba
    · rw [min_eq_left hab, min_eq_left (mul_le_mul_of_nonneg_left hab (exp_pos _).le)]
    · rw [min_eq_right hba, min_eq_right (mul_le_mul_of_nonneg_left hba (exp_pos _).le)]
  simpa only [hmin] using hh

theorem mean_ge_initial_add (μ : FiniteLaw Ω) (X : Ω → ℝ) {v θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, v ≤ variance (tilted μ X t) X) :
    μ.expect X + v * θ ≤ mean μ X θ := by
  rcases hθ0.eq_or_lt with hθ | hθ
  · subst θ
    simp
  · obtain ⟨t, ht, hd⟩ := exists_deriv_eq_slope (mean μ X) hθ
      (differentiable_mean μ X).continuous.continuousOn
      (differentiable_mean μ X).differentiableOn
    rw [deriv_mean, mean_zero, sub_zero] at hd
    have hv' := hv t ⟨ht.1.le, ht.2.le.trans hθ1⟩
    rw [hd] at hv'
    have hprod := (le_div_iff₀ hθ).mp hv'
    linarith

theorem mean_ge_of_separated_classes (μ : FiniteLaw Ω) (X : Ω → ℝ)
    {B a b θ : ℝ} (hX0 : ∀ x, 0 ≤ X x) (hXB : ∀ x, X x ≤ B)
    (ha : a ≤ μ.prob (fun x => X x = 1))
    (hb : b ≤ μ.prob (fun x => 2 ≤ X x))
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    μ.expect X + (exp (-B) * min a b / 4) * θ ≤ mean μ X θ :=
  mean_ge_initial_add μ X hθ0 hθ1 (fun _ ht =>
    tilted_variance_ge μ X hX0 hXB ha hb ht.1 ht.2)

end FCAppendix.FiniteCramer

namespace FCAppendix.SimultaneousCongestion

open Real CommonList Proposer
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem one_le_mgf (μ : FiniteLaw (Finset ι)) (K : Finset ι) {θ : ℝ} (hθ : 0 ≤ θ) :
    1 ≤ mgf μ K θ := by
  apply μ.const_le_expect
  intro S
  exact one_le_exp (mul_nonneg hθ (Nat.cast_nonneg _))

theorem congestionProb_ge_reverse_density (μ : FiniteLaw (Finset ι))
    (K : Finset ι) (N c : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    exp (-(θ * N * K.card)) * congestionProb (selTilt μ K θ) K N c ≤
      congestionProb μ K N c := by
  classical
  let ν := selTilt μ K θ
  have hchange := expect_iid_eq_tilt μ (fun S => θ * selected K S) N
    (fun T => if Congested K c T then (1 : ℝ) else 0)
  have hmono : exp (-(θ * N * K.card)) * (iid ν N).prob (Congested K c) ≤
      (iid ν N).expect (fun T => (if Congested K c T then (1 : ℝ) else 0) *
        exp (-(∑ i, θ * (selected K (T i) : ℝ)))) := by
    rw [FiniteLaw.prob_eq_expect, ← FiniteLaw.expect_const_mul]
    apply FiniteLaw.expect_mono
    intro T
    by_cases hT : Congested K c T
    · simp only [if_pos hT, mul_one, one_mul]
      apply exp_le_exp.mpr
      have hs : ∑ i, (selected K (T i) : ℝ) ≤ (N : ℝ) * K.card := by
        calc
          _ ≤ ∑ _ : Fin N, (K.card : ℝ) := Finset.sum_le_sum (fun i _ => by
            exact_mod_cast selected_le K (T i))
          _ = _ := by simp
      rw [← Finset.mul_sum]
      have hh := mul_le_mul_of_nonneg_left hs hθ
      nlinarith
    · simp [hT]
  have hP : congestionProb μ K N c = (mgf μ K θ) ^ N *
      (iid ν N).expect (fun T => (if Congested K c T then (1 : ℝ) else 0) *
        exp (-(∑ i, θ * (selected K (T i) : ℝ)))) := by
    exact hchange
  rw [hP]
  have hZ : 1 ≤ (mgf μ K θ) ^ N := one_le_pow₀ (one_le_mgf μ K hθ)
  have hp0 : 0 ≤ (iid ν N).expect (fun T =>
      (if Congested K c T then (1 : ℝ) else 0) * exp (-(∑ i, θ * (selected K (T i) : ℝ)))) := by
    apply FiniteLaw.expect_nonneg
    intro T
    exact mul_nonneg (by split <;> norm_num) (exp_pos _).le
  exact hmono.trans (by nlinarith)

theorem congestionProb_ge_half_exp_of_tilt_gap {μ : FiniteLaw (Finset ι)}
    {K : Finset ι} (hK : SwapInvariant μ K) (N c : ℕ) {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 < η) (hN : (K.card : ℝ) ≤ 2 * N * η ^ 2)
    (hc : (c : ℝ) ≤ N * (tiltMean μ K θ / K.card - η)) :
    exp (-(θ * N * K.card)) / 2 ≤ congestionProb μ K N c := by
  let ν := selTilt μ K θ
  have hnear := prob_all_near_ge ν K N hη hN
  have hsub : ∀ T : Fin N → Finset ι,
      (∀ s ∈ K, |(includers s T : ℝ) - N * marginal ν s| < N * η) →
      Congested K c T := by
    intro T hT s hs
    have hh := (abs_lt.mp (hT s hs)).1
    have hm : marginal ν s = tiltMean μ K θ / K.card := marginal_selTilt hK θ hs
    rw [hm] at hh
    have ht : (c : ℝ) < includers s T := by linarith
    exact_mod_cast ht.le
  have hhalf : (1 / 2 : ℝ) ≤ congestionProb ν K N c :=
    hnear.trans ((iid ν N).prob_mono hsub)
  have hr := congestionProb_ge_reverse_density μ K N c hθ
  have hh := mul_le_mul_of_nonneg_left hhalf (exp_pos (-(θ * N * K.card))).le
  dsimp only [ν] at hh
  linarith

end FCAppendix.SimultaneousCongestion
