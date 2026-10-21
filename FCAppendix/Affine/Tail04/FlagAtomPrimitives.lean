import FCAppendix.Probability.IndependentCounts

noncomputable section
namespace FCAppendix.Affine.Tail04
open Set Classical
open scoped BigOperators

def mixedFlagProbability (e0 B b : ℝ) : ℝ :=
  e0 * ((B - b) / (B - 1)) ^ 2

theorem mixedFlagProbability_nonneg {e0 B b : ℝ} (he : 0 ≤ e0) :
    0 ≤ mixedFlagProbability e0 B b := mul_nonneg he (sq_nonneg _)

theorem mixedFlagProbability_le_base {e0 B b : ℝ}
    (he : 0 ≤ e0) (hB : 1 < B) (hb : b ∈ Icc 1 B) :
    mixedFlagProbability e0 B b ≤ e0 := by
  have hd : 0 < B - 1 := sub_pos.mpr hB
  have hq0 : 0 ≤ (B - b) / (B - 1) := div_nonneg (sub_nonneg.mpr hb.2) hd.le
  have hq1 : (B - b) / (B - 1) ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith [hb.1]
  have hsq : ((B - b) / (B - 1)) ^ 2 ≤ 1 := by nlinarith
  simpa only [mixedFlagProbability, mul_one] using mul_le_mul_of_nonneg_left hsq he

theorem mixedFlagProbability_le_one {e0 B b : ℝ}
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hB : 1 < B) (hb : b ∈ Icc 1 B) :
    mixedFlagProbability e0 B b ≤ 1 :=
  (mixedFlagProbability_le_base he0 hB hb).trans he1

theorem continuous_mixedFlagProbability (e0 B : ℝ) :
    Continuous (mixedFlagProbability e0 B) := by
  unfold mixedFlagProbability
  fun_prop

theorem mixedFlagProbability_lipschitz {e0 B x y : ℝ}
    (he : 0 ≤ e0) (hB : 1 < B) (hx : x ∈ Icc 1 B) (hy : y ∈ Icc 1 B) :
    |mixedFlagProbability e0 B x - mixedFlagProbability e0 B y| ≤
      (2 * e0 / (B - 1)) * |x - y| := by
  have hd : 0 < B - 1 := sub_pos.mpr hB
  have hid : mixedFlagProbability e0 B x - mixedFlagProbability e0 B y =
      (e0 / (B - 1) ^ 2) * (y - x) * ((B - x) + (B - y)) := by
    unfold mixedFlagProbability
    field_simp [ne_of_gt hd]
    ring
  have hp : 0 ≤ e0 / (B - 1) ^ 2 := div_nonneg he (sq_nonneg _)
  have hsum : |(B - x) + (B - y)| ≤ 2 * (B - 1) := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  calc
    _ = (e0 / (B - 1) ^ 2) * |x - y| * |(B - x) + (B - y)| := by
      rw [hid, abs_mul, abs_mul, abs_of_nonneg hp, abs_sub_comm y x]
    _ ≤ (e0 / (B - 1) ^ 2) * |x - y| * (2 * (B - 1)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hp (abs_nonneg _))
    _ = _ := by
      field_simp [ne_of_gt hd]

theorem mixedFlagProbability_moving_cap_lower {e0 B b k t : ℝ}
    (he : 0 ≤ e0) (hB : 1 < B) (hk : 0 < k) (ht : 0 < t)
    (hcap : b ≤ B - k / t) :
    e0 * k ^ 2 / ((B - 1) ^ 2 * t ^ 2) ≤ mixedFlagProbability e0 B b := by
  have hd : 0 < B - 1 := sub_pos.mpr hB
  have hbase : k / t ≤ B - b := by linarith
  have hratio : k / (t * (B - 1)) ≤ (B - b) / (B - 1) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hbase hd.le
  have hleft : 0 ≤ k / (t * (B - 1)) := by positivity
  have hsquare : (k / (t * (B - 1))) ^ 2 ≤ ((B - b) / (B - 1)) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hratio hratio hleft (hleft.trans hratio)
  have hh := mul_le_mul_of_nonneg_left hsquare he
  calc
    e0 * k ^ 2 / ((B - 1) ^ 2 * t ^ 2) =
        e0 * (k / (t * (B - 1))) ^ 2 := by
      field_simp [ne_of_gt hd, ne_of_gt ht]
    _ ≤ mixedFlagProbability e0 B b := hh

section FlagLaw
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentFlagLaw (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteLaw (ι → Bool) where
  mass f := ∏ i, (IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)).mass (f i)
  nonneg f := Finset.prod_nonneg (fun i _ =>
    (IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)).nonneg (f i))
  total := by
    rw [← Fintype.prod_sum (fun i z =>
      (IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)).mass z)]
    simp only [FiniteLaw.total, Finset.prod_const_one]

theorem independentFlagLaw_expect_prod (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (f : ι → Bool → ℝ) :
    (independentFlagLaw p hp0 hp1).expect (fun flags => ∏ i, f i (flags i)) =
      ∏ i, ((1 - p i) * f i false + p i * f i true) := by
  change (∑ flags : ι → Bool,
    (∏ i, (IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)).mass (flags i)) *
      (∏ i, f i (flags i))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i z =>
    (IndependentCounts.bernoulli (p i) (hp0 i) (hp1 i)).mass z * f i z)]
  apply Finset.prod_congr rfl
  intro i _
  exact IndependentCounts.expect_bernoulli (p i) (hp0 i) (hp1 i) (f i)

def bidDependentFlagLaw (e0 B : ℝ) (b : ι → ℝ)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hB : 1 < B)
    (hb : ∀ i, b i ∈ Icc 1 B) : FiniteLaw (ι → Bool) :=
  independentFlagLaw (fun i => mixedFlagProbability e0 B (b i))
    (fun _ => mixedFlagProbability_nonneg he0)
    (fun i => mixedFlagProbability_le_one he0 he1 hB (hb i))

end FlagLaw

def twoMixedFavoredGain (v b eta q1 q2 : ℝ) : ℝ :=
  (v - b) * (1 - q1) * (1 - q2) + eta * b * q1 * q2

theorem twoMixedFavoredGain_lower {v b eta q1 q2 L qmin : ℝ}
    (hvb : b ≤ v) (heta : 0 ≤ eta) (hL : 0 ≤ L) (hb : L ≤ b)
    (hqmin : 0 ≤ qmin) (hq1 : qmin ≤ q1) (hq2 : qmin ≤ q2)
    (hq1one : q1 ≤ 1) (hq2one : q2 ≤ 1) :
    eta * L * qmin ^ 2 ≤ twoMixedFavoredGain v b eta q1 q2 := by
  have hq1zero : 0 ≤ q1 := hqmin.trans hq1
  have hq2zero : 0 ≤ q2 := hqmin.trans hq2
  have hfirst : 0 ≤ (v - b) * (1 - q1) * (1 - q2) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hvb) (sub_nonneg.mpr hq1one))
      (sub_nonneg.mpr hq2one)
  have hqq : qmin ^ 2 ≤ q1 * q2 := by
    simpa only [pow_two] using mul_le_mul hq1 hq2 hqmin hq1zero
  have hLb : eta * L ≤ eta * b := mul_le_mul_of_nonneg_left hb heta
  have hprod := mul_le_mul hLb hqq (sq_nonneg qmin) (mul_nonneg heta (hL.trans hb))
  unfold twoMixedFavoredGain
  nlinarith only [hprod, hfirst]

theorem twoMixedFavoredGain_pos {v b eta q1 q2 L qmin : ℝ}
    (hvb : b ≤ v) (heta : 0 < eta) (hL : 0 < L) (hb : L ≤ b)
    (hqmin : 0 < qmin) (hq1 : qmin ≤ q1) (hq2 : qmin ≤ q2)
    (hq1one : q1 ≤ 1) (hq2one : q2 ≤ 1) :
    0 < twoMixedFavoredGain v b eta q1 q2 :=
  lt_of_lt_of_le (by positivity)
    (twoMixedFavoredGain_lower hvb heta.le hL.le hb hqmin.le hq1 hq2 hq1one hq2one)

theorem two_flag_expected_gain (p1 p2 gain : ℝ)
    (hp10 : 0 ≤ p1) (hp11 : p1 ≤ 1) (hp20 : 0 ≤ p2) (hp21 : p2 ≤ 1) :
    ((IndependentCounts.bernoulli p1 hp10 hp11).prod
      (IndependentCounts.bernoulli p2 hp20 hp21)).expect
        (fun z => if z.1 = true ∧ z.2 = true then gain else 0) = p1 * p2 * gain := by
  simp [FiniteLaw.expect_prod, IndependentCounts.expect_bernoulli, mul_assoc]

theorem two_flag_moving_scale {p1 p2 gain gamma g t : ℝ}
    (ht : 0 < t) (hgamma : 0 ≤ gamma) (hg : 0 ≤ g)
    (hp1 : gamma / t ^ 2 ≤ p1) (hp2 : gamma / t ^ 2 ≤ p2)
    (hgain : g ≤ gain) :
    (gamma ^ 2 / t ^ 4) * g ≤ p1 * p2 * gain := by
  have hbase : 0 ≤ gamma / t ^ 2 := by positivity
  have hp10 : 0 ≤ p1 := hbase.trans hp1
  have hp20 : 0 ≤ p2 := hbase.trans hp2
  have hprod : (gamma / t ^ 2) ^ 2 ≤ p1 * p2 := by
    simpa only [pow_two] using mul_le_mul hp1 hp2 hbase hp10
  have hh := mul_le_mul hprod hgain hg (mul_nonneg hp10 hp20)
  have hid : (gamma/t^2)^2=gamma^2/t^4 := by
    rw [div_pow, ←pow_mul]
  rw [hid] at hh
  exact hh

end FCAppendix.Affine.Tail04
