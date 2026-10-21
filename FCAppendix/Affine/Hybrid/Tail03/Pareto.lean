import FCAppendix.Affine.Hybrid.Tail03.Law
import FCAppendix.Affine.Hybrid.Tail03.PowerIntegrals
import FCAppendix.Affine.Hybrid.Tail03.MovingScale
import FCAppendix.Affine.Hybrid.UpperFiniteError
import FCAppendix.Affine.Hybrid.UpperNativeAttainment
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open MeasureTheory ProbabilityTheory Filter Topology Set Real
open Existence.RankEnvelope
open scoped BigOperators

theorem binomial_pgf (n : ℕ) (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (IndependentCounts.binomial n p hp0 hp1).expect (fun j => z^j.val) =
      (1-p+p*z)^n := by
  induction n with
  | zero =>
      simp [IndependentCounts.binomial, IndependentCounts.independentCount]
  | succ n ih =>
      rw [IndependentCounts.expect_binomial_succ]
      simp only [IndependentCounts.val_add_false, IndependentCounts.val_add_true,
        pow_add, FiniteLaw.expect_const_mul, ih, pow_succ]
      ring

theorem rank_failure_eq_prob (n c : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    1-rankSuccess n c p =
      (IndependentCounts.binomial n p hp.1 hp.2).prob (fun j => c ≤ j.val) := by
  rw [rankSuccess_eq_prob n c hp, ← FiniteLaw.prob_compl]
  congr 1
  funext j
  exact propext (by omega)

theorem rank_failure_mgf_bound (n c : ℕ) {p z : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hz : 1 ≤ z) :
    1-rankSuccess n c p ≤
      exp ((n:ℝ)*p*(z-1)-(c:ℝ)*log z) := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  let nu := IndependentCounts.binomial n p hp.1 hp.2
  have hpoint : ∀ j : Fin (n+1),
      z^c*(if c ≤ j.val then (1:ℝ) else 0) ≤ z^j.val := by
    intro j
    by_cases hj : c ≤ j.val
    · simp only [if_pos hj, mul_one]
      exact pow_le_pow_right₀ hz hj
    · simp only [if_neg hj, mul_zero]
      positivity
  have hmark := nu.expect_mono hpoint
  rw [FiniteLaw.expect_const_mul, binomial_pgf] at hmark
  rw [← FiniteLaw.prob_eq_expect] at hmark
  have hbase : 1-p+p*z ≤ exp (p*(z-1)) := by
    have he := Real.add_one_le_exp (p*(z-1))
    nlinarith
  have hnonneg : 0 ≤ 1-p+p*z := by nlinarith [hp.1, hp.2, hz]
  have hpow := pow_le_pow_left₀ hnonneg hbase n
  have heq : exp (p*(z-1))^n / z^c =
      exp ((n:ℝ)*p*(z-1)-(c:ℝ)*log z) := by

    have hzpow : z^c = exp ((c:ℝ)*log z) := by
      rw [Real.exp_nat_mul, Real.exp_log hz0]
    rw [← Real.exp_nat_mul, hzpow, ← Real.exp_sub]
    congr 1
    ring
  rw [rank_failure_eq_prob n c hp]
  have hh : nu.prob (fun j => c ≤ j.val) ≤ exp (p*(z-1))^n/z^c := by
    apply (le_div_iff₀ (pow_pos hz0 c)).2
    simpa only [mul_comm] using hmark.trans hpow
  exact hh.trans_eq heq

theorem rank_failure_poisson_bound (n c : ℕ) (hc : 1 ≤ c) {p : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hmean : (n:ℝ)*p ≤ c) :
    1-rankSuccess n c p ≤ (exp 1*(n:ℝ)*p/(c:ℝ))^c := by
  by_cases hpz : p=0
  · subst p
    simp [rankSuccess_zero n c hc, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hc)]
  by_cases hn : n=0
  · subst n
    simp [rankSuccess, Exclusive.Narrow.binomialPolynomial,
      show 0< c by omega, Nat.ne_of_gt (show 0< c by omega)]
  have hp0 : 0 < p := lt_of_le_of_ne hp.1 (Ne.symm hpz)
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc0 : 0 < (c:ℝ) := by exact_mod_cast (show 0< c by omega)
  let z := (c:ℝ)/((n:ℝ)*p)
  have hz : 1 ≤ z := (one_le_div (mul_pos hn0 hp0)).2 hmean
  have hchernoff := rank_failure_mgf_bound n c hp hz
  have hz0 : 0 < z := by dsimp [z]; positivity
  have he : (n:ℝ)*p*(z-1) ≤ (c:ℝ) := by
    dsimp [z]
    field_simp
    nlinarith [mul_nonneg hn0.le hp0.le]
  have hupper : exp ((n:ℝ)*p*(z-1)-(c:ℝ)*log z) ≤
      exp ((c:ℝ)-(c:ℝ)*log z) := Real.exp_le_exp.mpr (by linarith)
  have hid : exp ((c:ℝ)-(c:ℝ)*log z) =
      (exp 1*(n:ℝ)*p/(c:ℝ))^c := by
    have hcexp : exp (c:ℝ) = (exp 1)^c := by
      calc
        exp (c:ℝ) = exp ((c:ℝ)*1) := by rw [mul_one]
        _ = (exp 1)^c := by rw [Real.exp_nat_mul]
    rw [Real.exp_sub, hcexp, Real.exp_nat_mul, Real.exp_log hz0, ← div_pow]
    congr 1
    dsimp [z]
    field_simp
  exact hchernoff.trans (hupper.trans_eq hid)

def weightedPareto (h t : ℝ) : Measure ℝ :=
  ENNReal.ofReal h • paretoMeasure t 10

theorem weightedPareto_contactTail {h t v : ℝ}
    (hh : 0 ≤ h) (ht : 0 < t) (hv : t ≤ v) :
    contactTail (weightedPareto h t) 2 v = (h/2)*(t/v)^10 := by
  unfold contactTail weightedPareto
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hh, Nat.cast_ofNat]
  rw [show ((paretoMeasure t 10) (Ioi v)).toReal=(t/v)^10 from pareto_tail ht hv]
  ring

theorem relative_tail_pow (t v : ℝ) (c : ℕ) (ht : 0 < t) (hv : 0 < v) :
    ((t/v)^10)^c = powerTail t (10*(c:ℝ)) v := by
  unfold powerTail
  have he : 10*(c:ℝ)=((10*c:ℕ):ℝ) := by push_cast; ring
  calc
    ((t/v)^10)^c = (t/v)^(10*c) := (pow_mul _ _ _).symm
    _ = ((v/t)^(10*c))⁻¹ := by simp only [div_pow, inv_div]
    _ = (v/t)^(-(10*(c:ℝ))) := by
      rw [Real.rpow_neg (div_nonneg hv.le ht.le), he, Real.rpow_natCast]

def rankCoefficient (n c : ℕ) (h : ℝ) : ℝ :=
  (exp 1*(n:ℝ)*h/(2*(c:ℝ)))^c

theorem native_rank_failure_power_bound (n c : ℕ) (hc : 1 ≤ c)
    {h t : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (ht : 0 < t)
    (hmean : (n:ℝ)*h/2 ≤ c) (v : ℝ) (hv : t ≤ v) :
    0 ≤ 1-rank (weightedPareto h t) n c 2 v ∧
    1-rank (weightedPareto h t) n c 2 v ≤
      rankCoefficient n c h * powerTail t (10*(c:ℝ)) v := by
  have hv0 : 0 < v := ht.trans_le hv
  have hratio : 0 ≤ (t/v)^10 := by positivity
  have hr1 : (t/v)^10 ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    exact (div_le_one hv0).2 hv
  have hp : (h/2)*(t/v)^10 ∈ Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · nlinarith
  have hpmean : (n:ℝ)*((h/2)*(t/v)^10) ≤ c := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hm := mul_le_mul_of_nonneg_left hr1 (by positivity : 0 ≤ (n:ℝ)*h/2)
    nlinarith
  rw [rank, weightedPareto_contactTail hh0 ht hv]
  refine ⟨by linarith [(rankSuccess_bounds n c hp).2], ?_⟩
  have hbound := rank_failure_poisson_bound n c hc hp hpmean
  convert! hbound using 1
  rw [rankCoefficient, ← relative_tail_pow t v c ht hv0, ← mul_pow]
  congr 1
  ring

def movingPrivateMass (a zeta M : ℝ) (m : ℕ) : ℝ :=
  a*zeta*(M/movingThreshold m)^10

def movingPrivateShare (h a zeta M : ℝ) (m : ℕ) : ℝ :=
  movingPrivateMass a zeta M m/(h+movingPrivateMass a zeta M m)

theorem movingPrivateMass_exact (a zeta M : ℝ) (m : ℕ) :
    movingPrivateMass a zeta M m = a*zeta*M^10/(m:ℝ)^2 := by
  rw [movingPrivateMass, div_pow, movingThreshold_pow_ten]
  ring

theorem movingPrivateMass_nonneg (a zeta M : ℝ) (m : ℕ)
    (ha : 0 ≤ a) (hz : 0 ≤ zeta) : 0 ≤ movingPrivateMass a zeta M m := by
  rw [movingPrivateMass_exact]
  positivity

theorem movingPrivateMass_tendsto_zero (a zeta M : ℝ) :
    Tendsto (movingPrivateMass a zeta M) atTop (𝓝 0) := by
  have hi := (tendsto_natCast_atTop_atTop :
    Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop).inv_tendsto_atTop
  have hh := (hi.pow 2).const_mul (a*zeta*M^10)
  simp only [zero_pow (by omega : 2≠0),mul_zero] at hh
  apply hh.congr'
  exact Eventually.of_forall fun m => by
    change a*zeta*M^10*((m:ℝ)⁻¹)^2=movingPrivateMass a zeta M m
    rw [movingPrivateMass_exact]
    ring

theorem private_share_scaled_bound (h a zeta M : ℝ) (m : ℕ)
    (hh : 0< h) (ha : 0≤ a) (hz : 0≤ zeta) (hm : 0< m) :
    0 ≤ (m:ℝ)*movingPrivateShare h a zeta M m ∧
    (m:ℝ)*movingPrivateShare h a zeta M m ≤ a*zeta*M^10/(h*(m:ℝ)) := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast hm
  have hn := movingPrivateMass_nonneg a zeta M m ha hz
  have hd : 0 < h+movingPrivateMass a zeta M m := by linarith
  have hs : movingPrivateShare h a zeta M m ≤ movingPrivateMass a zeta M m/h := by
    unfold movingPrivateShare
    exact div_le_div_of_nonneg_left hn hh (by linarith)
  refine ⟨by unfold movingPrivateShare; positivity, ?_⟩
  have hb := mul_le_mul_of_nonneg_left hs hm0.le
  rw [movingPrivateMass_exact] at hb
  convert! hb using 1 ; field_simp

theorem private_share_scaled_tendsto (h a zeta M : ℝ)
    (hh : 0< h) (ha : 0≤ a) (hz : 0≤ zeta) :
    Tendsto (fun m : ℕ => (m:ℝ)*movingPrivateShare h a zeta M m) atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => a*zeta*M^10/(h*(m:ℝ))) atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop :
      Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).inv_tendsto_atTop
    have hl := hi.const_mul (a*zeta*M^10/h)
    simp only [mul_zero] at hl
    apply hl.congr'
    exact Eventually.of_forall fun m => by
      change (a*zeta*M^10/h)*(m:ℝ)⁻¹=a*zeta*M^10/(h*(m:ℝ))
      ring
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    exact (private_share_scaled_bound h a zeta M m hh ha hz hm).1
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    exact (private_share_scaled_bound h a zeta M m hh ha hz hm).2

theorem private_mass_exact_and_O_m_neg_two (h a zeta M : ℝ)
    (hh : 0< h) (ha : 0≤ a) (hz : 0≤ zeta) :
    (∀m,movingPrivateMass a zeta M m=a*zeta*M^10/(m:ℝ)^2) ∧
    (movingPrivateMass a zeta M =O[atTop] (fun m:ℕ=>1/(m:ℝ)^2)) ∧
    ((fun m:ℕ=>(m:ℝ)*movingPrivateShare h a zeta M m)
      =O[atTop] (fun m:ℕ=>1/(m:ℝ))) := by
  refine ⟨movingPrivateMass_exact a zeta M,?_,?_⟩
  · apply Asymptotics.IsBigO.of_bound (a*zeta*M^10)
    filter_upwards [] with m
    have hm0 := movingPrivateMass_nonneg a zeta M m ha hz
    have hden : 0≤1/(m:ℝ)^2 := by positivity
    change |movingPrivateMass a zeta M m| ≤ a*zeta*M^10*|1/(m:ℝ)^2|
    rw [abs_of_nonneg hm0,abs_of_nonneg hden,movingPrivateMass_exact]
    exact le_of_eq (by ring)
  · apply Asymptotics.IsBigO.of_bound (a*zeta*M^10/h)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    have hb := private_share_scaled_bound h a zeta M m hh ha hz hm
    have hden : 0≤1/(m:ℝ) := by positivity
    simp only [Real.norm_eq_abs,abs_of_nonneg hb.1,abs_of_nonneg hden]
    have hm0 : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
    convert! hb.2 using 1 ; field_simp [hh.ne',hm0]

theorem moving_original_law_identity (p : LawInput) (m : ℕ)
    (hm : p.M ≤ movingThreshold m) :
    (mixtureMeasure p).restrict (Ioi (movingThreshold m)) =
      weightedPareto (movingPrivateMass p.a p.zeta p.M m) (movingThreshold m) := by
  simpa only [weightedPareto, movingPrivateMass] using commonLaw_restrict_tail p hm

def sourceCapacity (m : ℕ) : ℕ := Nat.floor ((99/200:ℝ)*(m:ℝ))

theorem sourceCapacity_bounds (m : ℕ) (hm : 200 ≤ m) :
    (49/100:ℝ)*(m:ℝ) ≤ (sourceCapacity m:ℝ) ∧
    (sourceCapacity m:ℝ) ≤ (99/200:ℝ)*(m:ℝ) ∧ 1 ≤ sourceCapacity m := by
  have hm0 : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
  have hm200 : (200:ℝ) ≤ m := by exact_mod_cast hm
  have hl := Nat.lt_floor_add_one ((99/200:ℝ)*(m:ℝ))
  have hu := Nat.floor_le (by positivity : 0 ≤ (99/200:ℝ)*(m:ℝ))
  change (99/200:ℝ)*(m:ℝ) < (sourceCapacity m:ℝ)+1 at hl
  change (sourceCapacity m:ℝ) ≤ (99/200:ℝ)*(m:ℝ) at hu
  have hlow : (49/100:ℝ)*(m:ℝ) ≤ (sourceCapacity m:ℝ) := by linarith
  refine ⟨hlow, hu, ?_⟩
  have hp : (1:ℝ) ≤ sourceCapacity m := by linarith
  exact_mod_cast hp

theorem sourceCapacity_ratio_tendsto :
    Tendsto (fun m : ℕ => (sourceCapacity m:ℝ)/(m:ℝ)) atTop (𝓝 (99/200:ℝ)) := by
  have hi : Tendsto (fun m : ℕ => 1/(m:ℝ)) atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop :
      Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop).inv_tendsto_atTop
    convert! hi using 1
    funext m
    change 1/(m:ℝ)=(m:ℝ)⁻¹
    exact one_div _
  have hdiff : Tendsto (fun m : ℕ => (99/200:ℝ)-(sourceCapacity m:ℝ)/(m:ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hi
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
      have hm0 : 0 < (m:ℝ) := by exact_mod_cast hm
      have hu := Nat.floor_le (by positivity : 0≤(99/200:ℝ)*(m:ℝ))
      have hh : (sourceCapacity m:ℝ)/(m:ℝ) ≤ 99/200 := (div_le_iff₀ hm0).2 hu
      linarith
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
      have hm0 : 0 < (m:ℝ) := by exact_mod_cast hm
      have hl := Nat.lt_floor_add_one ((99/200:ℝ)*(m:ℝ))
      apply (le_div_iff₀ hm0).2
      have he : ((99/200:ℝ)-(sourceCapacity m:ℝ)/(m:ℝ))*(m:ℝ) =
          (99/200:ℝ)*(m:ℝ)-(sourceCapacity m:ℝ) := by field_simp
      rw [he]
      change (99/200:ℝ)*(m:ℝ) < (sourceCapacity m:ℝ)+1 at hl
      linarith
  have hh := (tendsto_const_nhds (x:=(99/200:ℝ))).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using hh

def movingRankCoefficient (a zeta M : ℝ) (m : ℕ) : ℝ :=
  rankCoefficient (m-1) (sourceCapacity m) (movingPrivateMass a zeta M m)

theorem movingRankCoefficient_nonneg (a zeta M : ℝ) (ha : 0≤ a) (hz : 0≤ zeta) (m : ℕ) :
    0 ≤ movingRankCoefficient a zeta M m := by
  unfold movingRankCoefficient rankCoefficient
  have hh := movingPrivateMass_nonneg a zeta M m ha hz
  positivity

theorem moving_coefficient_base_bound (a zeta M : ℝ) (ha : 0≤ a) (hz : 0≤ zeta)
    (m : ℕ) (hm : 200≤ m) :
    exp 1*((m-1:ℕ):ℝ)*movingPrivateMass a zeta M m /
      (2*(sourceCapacity m:ℝ)) ≤
      (100*exp 1*a*zeta*M^10/98)/(m:ℝ)^2 := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0< m by omega)
  have hc := sourceCapacity_bounds m hm
  have hc0 : 0 < (sourceCapacity m:ℝ) := by exact_mod_cast (show 0< sourceCapacity m by omega)
  have hNm : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  have hK : 0 ≤ a*zeta*M^10 := by positivity
  have hratio : ((m-1:ℕ):ℝ)/(2*(sourceCapacity m:ℝ)) ≤ 100/98 := by
    apply (div_le_iff₀ (by positivity : 0<2*(sourceCapacity m:ℝ))).2
    linarith [hc.1]
  have hmul := mul_le_mul_of_nonneg_left hratio
    (show 0≤ exp 1*(a*zeta*M^10)/(m:ℝ)^2 by positivity)
  rw [movingPrivateMass_exact]
  convert! hmul using 1 <;> field_simp [hm0.ne',hc0.ne']

theorem moving_rank_superexponential (a zeta M : ℝ) (ha : 0≤ a) (hz : 0≤ zeta) :
    ∀ᶠ m : ℕ in atTop, movingRankCoefficient a zeta M m ≤
      exp (-(49/100:ℝ)*(m:ℝ)*log (m:ℝ)) := by
  let C := 100*exp 1*a*zeta*M^10/98
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_ge_atTop (200:ℕ),
    (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop).eventually_ge_atTop C]
    with m hm hCm
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0< m by omega)
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1≤ m by omega)
  have hc := sourceCapacity_bounds m hm
  have hbase := moving_coefficient_base_bound a zeta M ha hz m hm
  have hsmall : C/(m:ℝ)^2 ≤ 1/(m:ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hm0)).2
    field_simp
    nlinarith
  have hnn : 0 ≤ exp 1*((m-1:ℕ):ℝ)*movingPrivateMass a zeta M m /
      (2*(sourceCapacity m:ℝ)) := by
    have hmass := movingPrivateMass_nonneg a zeta M m ha hz
    positivity
  have hpow := pow_le_pow_left₀ hnn (hbase.trans hsmall) (sourceCapacity m)
  have hexact : (1/(m:ℝ))^(sourceCapacity m) =
      exp (-(sourceCapacity m:ℝ)*log (m:ℝ)) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm0]
    simp only [one_div, inv_pow]
  have hlog : 0 ≤ log (m:ℝ) := Real.log_nonneg hm1
  exact hpow.trans (hexact.trans_le
    (Real.exp_le_exp.mpr (by nlinarith [hc.1])))

theorem moving_rank_eventually_exp (a zeta M : ℝ) (ha : 0≤ a) (hz : 0≤ zeta) :
    ∀ᶠ m : ℕ in atTop, movingRankCoefficient a zeta M m ≤ exp (-(m:ℝ)) := by
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop)).eventually_ge_atTop 3
  filter_upwards [moving_rank_superexponential a zeta M ha hz, hlog] with m hD hlogm
  apply hD.trans
  apply Real.exp_le_exp.mpr
  change 3≤log (m:ℝ) at hlogm
  nlinarith [Nat.cast_nonneg (α:=ℝ) m]

theorem superexponential_error_dominates_all_polynomials
    (a zeta M : ℝ) (ha : 0≤ a) (hz : 0≤ zeta) (k : ℕ) :
    Tendsto (fun m : ℕ => (m:ℝ)^k*movingRankCoefficient a zeta M m) atTop (𝓝 0) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) 1 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m:ℕ => (m:ℝ)) atTop atTop)
  have hlim' : Tendsto (fun m:ℕ => (m:ℝ)^k*exp (-(m:ℝ))) atTop (𝓝 0) := by
    convert! hlim using 1
    funext m
    simp only [Function.comp_apply,Real.rpow_natCast,neg_one_mul]
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    mul_nonneg (by positivity) (movingRankCoefficient_nonneg a zeta M ha hz m))) _ hlim'
  filter_upwards [moving_rank_eventually_exp a zeta M ha hz] with m hm
  exact mul_le_mul_of_nonneg_left hm (by positivity)

theorem moving_rank_eventual_primitives (p : LawInput) :
    ∀ᶠ m : ℕ in atTop,
      0 < movingThreshold m ∧ p.M ≤ movingThreshold m ∧
      0 ≤ movingPrivateMass p.a p.zeta p.M m ∧
      movingPrivateMass p.a p.zeta p.M m ≤ 1/2 ∧
      ((m-1:ℕ):ℝ)*movingPrivateMass p.a p.zeta p.M m/2 ≤ (sourceCapacity m:ℝ) ∧
      1 ≤ sourceCapacity m := by
  filter_upwards [eventually_ge_atTop (200:ℕ), movingThreshold_tendsto.eventually_ge_atTop p.M,
    (movingPrivateMass_tendsto_zero p.a p.zeta p.M).eventually
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))] with m hm hMt hmass
  have ht0 := movingThreshold_pos m (by omega)
  have hh0 := movingPrivateMass_nonneg p.a p.zeta p.M m p.a_pos.le p.zeta_pos.le
  have hc := sourceCapacity_bounds m hm
  have hNm : ((m-1:ℕ):ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.sub_le m 1
  refine ⟨ht0, hMt, hh0, hmass.le, ?_, hc.2.2⟩
  have hprod := mul_le_mul_of_nonneg_left hmass.le (by positivity : 0≤((m-1:ℕ):ℝ))
  nlinarith [hc.1]

theorem moving_original_rank_failure (p : LawInput) :
    ∀ᶠ m : ℕ in atTop, ∀ v : ℝ, movingThreshold m ≤ v →
      0 ≤ 1-rank ((mixtureMeasure p).restrict (Ioi (movingThreshold m)))
        (m-1) (sourceCapacity m) 2 v ∧
      1-rank ((mixtureMeasure p).restrict (Ioi (movingThreshold m)))
        (m-1) (sourceCapacity m) 2 v ≤
        movingRankCoefficient p.a p.zeta p.M m *
          powerTail (movingThreshold m) (10*(sourceCapacity m:ℝ)) v := by
  filter_upwards [moving_rank_eventual_primitives p] with m hm
  intro v hv
  rw [moving_original_law_identity p m hm.2.1]
  exact native_rank_failure_power_bound (m-1) (sourceCapacity m) hm.2.2.2.2.2
    hm.2.2.1 (by linarith [hm.2.2.2.1]) hm.1 hm.2.2.2.2.1 v hv

theorem exact_tail_integral_bounds (p : LawInput) :
    ∀ᶠ m : ℕ in atTop,
      let t := movingThreshold m
      let c := sourceCapacity m
      let D := movingRankCoefficient p.a p.zeta p.M m
      let q := rank ((mixtureMeasure p).restrict (Ioi t)) (m-1) c 2
      IntegrableOn (fun v => 1-q v) (Ioi t) ∧
      IntegrableOn (fun v => v*(1-q v)) (Ioi t) ∧
      (∫ v in Ioi t, 1-q v) ≤ t*D/(10*(c:ℝ)-1) ∧
      (∫ v in Ioi t, v*(1-q v)) ≤ t^2*D/(10*(c:ℝ)-2) := by
  filter_upwards [moving_original_rank_failure p, moving_rank_eventual_primitives p]
    with m hfail hprim
  dsimp only
  have hcR : (1:ℝ) ≤ sourceCapacity m := by exact_mod_cast hprim.2.2.2.2.2
  have hh := failure_integrals
    (fun v => 1-rank ((mixtureMeasure p).restrict (Ioi (movingThreshold m)))
      (m-1) (sourceCapacity m) 2 v)
    (movingRankCoefficient p.a p.zeta p.M m) (movingThreshold m)
    (10*(sourceCapacity m:ℝ)) hprim.1 (by linarith)
    (movingRankCoefficient_nonneg p.a p.zeta p.M p.a_pos.le p.zeta_pos.le m)
    ((continuous_const.sub (continuous_rank _ _ _ _)).aestronglyMeasurable.restrict)
    (fun v hv => hfail v hv.le)
  simpa only [mul_comm] using hh

theorem powerTail_le_one {t v p : ℝ} (ht : 0< t) (hv : t≤ v) (hp : 0≤ p) :
    powerTail t p v ≤ 1 := by
  unfold powerTail
  exact Real.rpow_le_one_of_one_le_of_nonpos ((one_le_div ht).2 hv) (by linarith)

theorem conditional_pareto_failure_moment (f : ℝ→ℝ) {D t p : ℝ}
    (ht : 0< t) (hp : 0≤ p) (hD : 0≤ D) (hf : Measurable f)
    (hb : ∀ v, t≤ v → 0≤ f v ∧ f v≤ D*powerTail t p v) :
    Integrable (fun v => v*f v) (paretoMeasure t 10) ∧
      (∫ v, v*f v ∂paretoMeasure t 10) ≤ (10/9:ℝ)*t*D := by
  have hi := (pareto_integrable_id ht).const_mul D
  have hpoint : ∀ᵐ v ∂paretoMeasure t 10, 0≤ v*f v ∧ v*f v≤ D*v := by
    filter_upwards [pareto_supported t] with v hv
    have hv0 := ht.le.trans hv
    have hfv : f v ≤ D := (hb v hv).2.trans
      (by simpa using mul_le_mul_of_nonneg_left (powerTail_le_one ht hv hp) hD)
    exact ⟨mul_nonneg hv0 (hb v hv).1, by nlinarith⟩
  have hInt : Integrable (fun v => v*f v) (paretoMeasure t 10) := by
    apply hi.mono' (measurable_id.mul hf).aestronglyMeasurable
    filter_upwards [hpoint] with v hv
    change |v*f v| ≤ D*v
    rw [abs_of_nonneg hv.1]
    exact hv.2
  refine ⟨hInt, ?_⟩
  calc
    _ ≤ ∫ v, D*v ∂paretoMeasure t 10 := integral_mono_ae hInt hi (hpoint.mono fun _ hv => hv.2)
    _ = (10/9:ℝ)*t*D := by rw [integral_const_mul, integral_pareto_id ht]; ring

theorem moving_conditional_failure_moment (p : LawInput) :
    ∀ᶠ m : ℕ in atTop,
      let t := movingThreshold m
      let c := sourceCapacity m
      let D := movingRankCoefficient p.a p.zeta p.M m
      let q := rank ((mixtureMeasure p).restrict (Ioi t)) (m-1) c 2
      Integrable (fun v => v*(1-q v)) (paretoMeasure t 10) ∧
      (∫ v, v*(1-q v) ∂paretoMeasure t 10) ≤ (10/9:ℝ)*t*D := by
  filter_upwards [moving_original_rank_failure p, moving_rank_eventual_primitives p]
    with m hfail hprim
  dsimp only
  apply conditional_pareto_failure_moment _ hprim.1 (by positivity)
    (movingRankCoefficient_nonneg p.a p.zeta p.M p.a_pos.le p.zeta_pos.le m)
    (continuous_const.sub (continuous_rank _ _ _ _)).measurable hfail

end FCAppendix.Affine.Hybrid.Tail03
