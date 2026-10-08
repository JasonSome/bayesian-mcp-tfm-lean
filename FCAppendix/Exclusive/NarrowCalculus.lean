import FCAppendix.Exclusive.NarrowKernel
import FCAppendix.Exclusive.TariffInterim
import FCAppendix.PayOnce.SupportedFOC

namespace FCAppendix.Exclusive.Narrow
open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable def binomialPolynomial : ℕ → (ℕ → ℝ) → ℝ → ℝ
  | 0, f, _ => f 0
  | n + 1, f, p => (1 - p) * binomialPolynomial n f p +
      p * binomialPolynomial n (fun r => f (1 + r)) p

noncomputable def binomialPolynomialDerivative : ℕ → (ℕ → ℝ) → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, f, p => -binomialPolynomial n f p +
      (1 - p) * binomialPolynomialDerivative n f p +
      binomialPolynomial n (fun r => f (1 + r)) p +
      p * binomialPolynomialDerivative n (fun r => f (1 + r)) p

theorem binomialPolynomial_eq_expect (n : ℕ) (f : ℕ → ℝ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialPolynomial n f p =
      (IndependentCounts.binomial n p hp0 hp1).expect (fun r => f r.val) := by
  induction n generalizing f with
  | zero => simp [binomialPolynomial, IndependentCounts.binomial,
      IndependentCounts.independentCount]
  | succ n ih =>
    rw [binomialPolynomial, IndependentCounts.expect_binomial_succ]
    simp only [IndependentCounts.val_add_false, IndependentCounts.val_add_true]
    rw [ih f, ih (fun r => f (1 + r))]

theorem hasDerivAt_binomialPolynomial (n : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    HasDerivAt (binomialPolynomial n f) (binomialPolynomialDerivative n f p) p := by
  induction n generalizing f with
  | zero => exact hasDerivAt_const p (f 0)
  | succ n ih =>
    have h := (((hasDerivAt_id p).const_sub 1).mul (ih f)).add
      ((hasDerivAt_id p).mul (ih (fun r => f (1 + r))))
    apply h.congr_deriv
    dsimp only [binomialPolynomialDerivative, id_eq]
    ring

theorem binomialPolynomial_const (n : ℕ) (a p : ℝ) :
    binomialPolynomial n (fun _ => a) p = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binomialPolynomial, ih]; ring

theorem binomialPolynomial_once (n : ℕ) (p : ℝ) :
    binomialPolynomial n successIndicator p = PayOnce.success n p := by
  induction n with
  | zero => simp [binomialPolynomial, PayOnce.success, successIndicator]
  | succ n ih =>
    have hshift : (fun r => successIndicator (1 + r)) = fun _ : ℕ => (1 : ℝ) := by
      funext r
      simp [successIndicator]
    rw [binomialPolynomial, hshift, binomialPolynomial_const, ih]
    simp only [PayOnce.success, pow_succ]
    ring

noncomputable def referenceBid (d : ℕ) (lam p : ℝ) : ℝ := lam / (1 - p) ^ d
noncomputable def fUnique (d : ℕ) (p : ℝ) : ℝ := 1 / (1 - p) ^ d
noncomputable def fOnce (d : ℕ) (p : ℝ) : ℝ :=
  ((d : ℝ) + (1 - p) ^ (d + 1)) / (((d + 1 : ℕ) : ℝ) * (1 - p) ^ (2 * d + 1))
noncomputable def fPerInclusion (d : ℕ) (p : ℝ) : ℝ :=
  ((d : ℝ) - ((d : ℝ) - 1) * (1 - p)) / (1 - p) ^ (2 * d + 1)
noncomputable def fTariff (d : ℕ) (a : UserTariff) (p : ℝ) : ℝ :=
  match a with
  | .unique => fUnique d p
  | .affine eta => (1 - eta) * fOnce d p + eta * fPerInclusion d p

noncomputable def baseMarginalCost (d : ℕ) (G : Schedule (d + 1)) (p : ℝ) : ℝ :=
  binomialPolynomialDerivative (d + 1) G.charge p / (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d)

noncomputable def referenceBidCost (d : ℕ) (a : UserTariff) (lam p : ℝ) : ℝ :=
  match a with
  | .unique => lam * ((d + 1 : ℕ) : ℝ) * p
  | .affine eta => (1 - eta) * (referenceBid d lam p * PayOnce.success (d + 1) p) +
      eta * (referenceBid d lam p * (((d + 1 : ℕ) : ℝ) * p))

theorem referenceBidCost_eq_actual (d : ℕ) (a : UserTariff) (lam p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p < 1) :
    referenceBidCost d a lam p = referenceBid d lam p *
      a.expected (IndependentCounts.binomial (d + 1) p hp0 hp1.le) := by
  have hq : (1 - p) ^ d ≠ 0 := pow_ne_zero _ (sub_pos.mpr hp1).ne'
  cases a with
  | unique =>
    rw [UserTariff.expected_unique_binomial]
    simp only [referenceBidCost, referenceBid, Nat.add_sub_cancel]
    field_simp [hq]
  | affine eta =>
    rw [UserTariff.expected_affine_binomial]
    simp only [referenceBidCost]
    ring

theorem hasDerivAt_success (d : ℕ) (p : ℝ) :
    HasDerivAt (PayOnce.success (d + 1)) (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d) p := by
  have h := (((hasDerivAt_id p).const_sub 1).pow (d + 1)).const_sub 1
  apply h.congr_deriv
  simp only [Nat.add_sub_cancel, id_eq]
  ring

theorem hasDerivAt_referenceBid (d : ℕ) (hd : 1 ≤ d) (lam p : ℝ) (hp : p < 1) :
    HasDerivAt (referenceBid d lam)
      (lam * (d : ℝ) / (1 - p) ^ (d + 1)) p := by
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp).ne'
  have hpow : (1 - p) ^ (d - 1) = (1 - p) ^ d / (1 - p) := by
    apply (eq_div_iff hq).mpr
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have h := (hasDerivAt_const p lam).div
    (((hasDerivAt_id p).const_sub 1).pow d) (pow_ne_zero _ hq)
  apply h.congr_deriv
  change (0 * (1 - p) ^ d - lam * ((d : ℝ) * (1 - p) ^ (d - 1) * -1)) /
    ((1 - p) ^ d) ^ 2 = lam * (d : ℝ) / (1 - p) ^ (d + 1)
  rw [hpow, pow_succ]
  field_simp [hq, pow_ne_zero d hq]
  ring

theorem hasDerivAt_referenceBidCost (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (lam p : ℝ) (hp : p < 1) :
    HasDerivAt (referenceBidCost d a lam)
      (lam * fTariff d a p * (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d)) p := by
  have hq : 1 - p ≠ 0 := (sub_pos.mpr hp).ne'
  have hn : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpower : (1 - p) ^ (2 * d + 1) = ((1 - p) ^ d) ^ 2 * (1 - p) := by
    rw [pow_succ, show 2 * d = d * 2 by omega, pow_mul]
  have hB := hasDerivAt_referenceBid d hd lam p hp
  have hS := hasDerivAt_success d p
  have h0 : HasDerivAt (fun x => referenceBid d lam x * PayOnce.success (d + 1) x)
      (lam * fOnce d p * (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d)) p := by
    apply (hB.mul hS).congr_deriv
    simp only [fOnce, referenceBid, PayOnce.success, hpower, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp [hn, hq, pow_ne_zero d hq]
    ring
  have h1 : HasDerivAt (fun x => referenceBid d lam x * (((d + 1 : ℕ) : ℝ) * x))
      (lam * fPerInclusion d p * (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d)) p := by
    apply (hB.mul ((hasDerivAt_id p).const_mul ((d + 1 : ℕ) : ℝ))).congr_deriv
    simp only [fPerInclusion, referenceBid, id_eq, hpower, pow_succ, Nat.cast_add, Nat.cast_one]
    field_simp [hn, hq, pow_ne_zero d hq]
    ring
  cases a with
  | unique =>
    apply ((hasDerivAt_id p).const_mul (lam * ((d + 1 : ℕ) : ℝ))).congr_deriv
    simp only [fTariff, fUnique]
    field_simp [pow_ne_zero d hq]
  | affine eta =>
    apply ((h0.const_mul (1 - eta)).add (h1.const_mul eta)).congr_deriv
    simp only [fTariff]
    ring

theorem reference_first_order (d : ℕ) (hd : 1 ≤ d) (a : UserTariff)
    (G : Schedule (d + 1)) (lam g v p : ℝ) (hp : p < 1) (T : Set ℝ)
    (hl : (𝓝[T ∩ Iio p] p).NeBot) (hr : (𝓝[T ∩ Ioi p] p).NeBot)
    (hmax : ∀ x ∈ T,
      v * PayOnce.success (d + 1) x - referenceBidCost d a lam x -
        g * binomialPolynomial (d + 1) G.charge x ≤
      v * PayOnce.success (d + 1) p - referenceBidCost d a lam p -
        g * binomialPolynomial (d + 1) G.charge p) :
    v = lam * fTariff d a p + g * baseMarginalCost d G p := by
  have hder := (((hasDerivAt_success d p).const_mul v).sub
    (hasDerivAt_referenceBidCost d hd a lam p hp)).sub
      ((hasDerivAt_binomialPolynomial (d + 1) G.charge p).const_mul g)
  have hz := PayOnce.SupportedFOC.derivative_zero_on_two_sided_set hder hl hr hmax
  have hden : (((d + 1 : ℕ) : ℝ) * (1 - p) ^ d) ≠ 0 :=
    mul_ne_zero (by positivity) (pow_ne_zero _ (sub_pos.mpr hp).ne')
  apply mul_right_cancel₀ hden
  unfold baseMarginalCost
  rw [add_mul, mul_assoc g, div_mul_cancel₀ _ hden]
  linarith [hz]

theorem baseMarginalCost_once (d : ℕ) (p : ℝ) (hp : p < 1) :
    baseMarginalCost d (Schedule.once (d + 1)) p = 1 := by
  have hfun : binomialPolynomial (d + 1) (Schedule.once (d + 1)).charge =
      PayOnce.success (d + 1) := by
    funext x
    exact binomialPolynomial_once (d + 1) x
  have hg := hasDerivAt_binomialPolynomial (d + 1) (Schedule.once (d + 1)).charge p
  rw [hfun] at hg
  have he := hg.unique (hasDerivAt_success d p)
  unfold baseMarginalCost
  rw [he, div_self]
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (sub_pos.mpr hp).ne')

theorem reference_unique_once_bid (d : ℕ) {lam g v p : ℝ} (hp : p < 1)
    (hFOC : v = lam * fTariff d .unique p +
      g * baseMarginalCost d (Schedule.once (d + 1)) p) :
    referenceBid d lam p = v - g := by
  rw [baseMarginalCost_once d p hp] at hFOC
  simp only [fTariff, fUnique, mul_one, mul_one_div] at hFOC
  dsimp only [referenceBid]
  linarith

end FCAppendix.Exclusive.Narrow
