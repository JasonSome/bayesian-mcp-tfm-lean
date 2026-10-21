import FCAppendix.Finite.BinomialLogBounds
import FCAppendix.Affine.Tail04.ParetoTail
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Tail04
open Finset Set Real Filter Topology
open scoped BigOperators

def marketCapacity (m : ℕ) : ℕ := ⌊(99 / 200 : ℝ) * (m : ℝ)⌋₊

def rankSuccess (N c : ℕ) (p : ℝ) : ℝ := Bayes.binomBelow N p c

private theorem mass_nonneg (N r : ℕ) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ PiBinomial.pmf N p r := by
  dsimp [PiBinomial.pmf]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    (pow_nonneg (sub_nonneg.mpr hp.2) _)

private theorem binomial_mass_sum (N : ℕ) (p : ℝ) :
    (∑ r ∈ range (N + 1), PiBinomial.pmf N p r) = 1 := by
  have h := add_pow p (1 - p) N
  simpa [PiBinomial.pmf, mul_assoc, mul_comm, mul_left_comm] using h.symm

private theorem choose_sum (N : ℕ) :
    (∑ r ∈ range (N + 1), (N.choose r : ℝ)) = (2 : ℝ) ^ N := by
  simpa only [one_pow, mul_one, one_mul, one_add_one_eq_two] using (add_pow (1 : ℝ) 1 N).symm

private theorem tail_sum_identity (N c : ℕ) (p : ℝ) (hc : c ≤ N + 1) :
    1 - rankSuccess N c p =
      ∑ r ∈ range (N + 1) \ range c, PiBinomial.pmf N p r := by
  have hs : range c ⊆ range (N + 1) := range_mono hc
  have h := sum_sdiff hs (f := fun r => PiBinomial.pmf N p r)
  rw [binomial_mass_sum] at h
  change _ + rankSuccess N c p = 1 at h
  linarith only [h]

theorem rankSuccess_bounds (N c : ℕ) (p : ℝ)
    (hc : c ≤ N + 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    0 ≤ rankSuccess N c p ∧ rankSuccess N c p ≤ 1 := by
  constructor
  · dsimp [rankSuccess, Bayes.binomBelow]
    exact sum_nonneg fun r _ => mass_nonneg N r p hp
  · have h : 0 ≤ 1 - rankSuccess N c p := by
      rw [tail_sum_identity N c p hc]
      exact sum_nonneg fun r _ => mass_nonneg N r p hp
    linarith

private theorem power_le_of_le_exponent (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (c r : ℕ) (hcr : c ≤ r) : p ^ r ≤ p ^ c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hcr
  rw [pow_add]
  have hpk : p ^ k ≤ 1 := pow_le_one₀ hp.1 hp.2
  simpa using mul_le_mul_of_nonneg_left hpk (pow_nonneg hp.1 c)

theorem rank_failure_le_power (N c : ℕ) (p : ℝ)
    (hc : c ≤ N + 1) (hp : p ∈ Icc (0 : ℝ) 1) :
    1 - rankSuccess N c p ≤ (2 : ℝ) ^ N * p ^ c := by
  rw [tail_sum_identity N c p hc]
  have hf (r : ℕ) (hr : r ∈ range (N + 1) \ range c) :
      PiBinomial.pmf N p r ≤ (N.choose r : ℝ) * p ^ c := by
    have hcr : c ≤ r := by simpa using (mem_sdiff.mp hr).2
    have hpow := power_le_of_le_exponent p hp c r hcr
    have hcomp : (1 - p) ^ (N - r) ≤ 1 :=
      pow_le_one₀ (by linarith [hp.2]) (by linarith [hp.1])
    dsimp [PiBinomial.pmf]
    calc
      _ ≤ (N.choose r : ℝ) * p ^ c * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)) hcomp
          (pow_nonneg (sub_nonneg.mpr hp.2) _)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
      _ = _ := mul_one _
  calc
    _ ≤ ∑ r ∈ range (N + 1) \ range c, (N.choose r : ℝ) * p ^ c :=
      sum_le_sum hf
    _ ≤ ∑ r ∈ range (N + 1), (N.choose r : ℝ) * p ^ c := by
      exact sum_le_sum_of_subset_of_nonneg sdiff_subset
        (fun r _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp.1 _))
    _ = (2 : ℝ) ^ N * p ^ c := by rw [← sum_mul, choose_sum]

theorem rank_failure_chernoff (N c : ℕ) (p z : ℝ)
    (hc : c ≤ N + 1) (hp : p ∈ Icc (0 : ℝ) 1) (hz : 1 ≤ z) :
    1 - rankSuccess N c p ≤ (1 - p + p * z) ^ N / z ^ c := by
  have hz0 : 0 < z := by linarith
  have hzpow : 0 < z ^ c := pow_pos hz0 c
  apply (le_div_iff₀ hzpow).2
  rw [tail_sum_identity N c p hc, sum_mul]
  calc
    _ ≤ ∑ r ∈ range (N + 1) \ range c, PiBinomial.pmf N p r * z ^ r := by
      apply sum_le_sum
      intro r hr
      have hcr : c ≤ r := by simpa using (mem_sdiff.mp hr).2
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz hcr) (mass_nonneg N r p hp)
    _ ≤ ∑ r ∈ range (N + 1), PiBinomial.pmf N p r * z ^ r := by
      exact sum_le_sum_of_subset_of_nonneg sdiff_subset
        (fun r _ _ => mul_nonneg (mass_nonneg N r p hp) (pow_nonneg hz0.le r))
    _ = (1 - p + p * z) ^ N := by
      have h := add_pow (p * z) (1 - p) N
      simpa [PiBinomial.pmf, mul_pow, mul_assoc, mul_comm, mul_left_comm, add_comm] using h.symm

theorem capacity_bounds (m : ℕ) (hm : 200 ≤ m) :
    (49 / 100 : ℝ) * m ≤ (marketCapacity m : ℝ) ∧
    (marketCapacity m : ℝ) ≤ (99 / 200 : ℝ) * m ∧
    1 ≤ marketCapacity m ∧ marketCapacity m < m := by
  have hm' : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 0 ≤ (99 / 200 : ℝ) * m := by positivity
  have hhi := Nat.floor_le hx
  have hlo := Nat.lt_floor_add_one ((99 / 200 : ℝ) * m)
  change (marketCapacity m : ℝ) ≤ (99 / 200 : ℝ) * m at hhi
  change (99 / 200 : ℝ) * m < (marketCapacity m : ℝ) + 1 at hlo
  have hc1 : (1 : ℝ) ≤ marketCapacity m := by linarith
  have hcm : (marketCapacity m : ℝ) < m := by linarith
  exact ⟨by linarith, hhi, by exact_mod_cast hc1, by exact_mod_cast hcm⟩

def lowerRankRate : ℝ := (49 / 100 : ℝ) * Real.log 2 - Real.log (27 / 20 : ℝ)

theorem lowerRankRate_pos : 0 < lowerRankRate := by
  have hnum : (27 / 20 : ℝ) ^ 100 < (2 : ℝ) ^ 49 := by norm_num
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (27 / 20 : ℝ) ^ 100) hnum
  rw [Real.log_pow, Real.log_pow] at hlog
  dsimp [lowerRankRate]
  linarith

theorem rank_failure_fixed_gap (m : ℕ) (hm : 200 ≤ m) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 7 / 20) :
    1 - rankSuccess (m - 1) (marketCapacity m) p ≤
      Real.exp (-lowerRankRate * m) := by
  obtain ⟨hclo, _hchi, _hcpos, hcm⟩ := capacity_bounds m hm
  have hm0 : 0 < m := by omega
  have hcN : marketCapacity m ≤ m - 1 + 1 := by omega
  have h := rank_failure_chernoff (m - 1) (marketCapacity m) p 2 hcN
    ⟨hp0, by linarith⟩ (by norm_num)
  have hbase : 1 - p + p * 2 ≤ (27 / 20 : ℝ) := by linarith
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hpow : (1 - p + p * 2) ^ (m - 1) ≤ (27 / 20 : ℝ) ^ m := by
    calc
      _ ≤ (27 / 20 : ℝ) ^ (m - 1) := by gcongr; linarith
      _ ≤ (27 / 20 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  refine h.trans ((div_le_div_of_nonneg_right hpow (by positivity)).trans ?_)
  have hexp1 : (27 / 20 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (27 / 20 : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hexp2 : (2 : ℝ) ^ marketCapacity m =
      Real.exp ((marketCapacity m : ℝ) * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  rw [hexp1, hexp2, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hg := mul_le_mul_of_nonneg_right hclo hlog2
  dsimp [lowerRankRate]
  nlinarith

theorem powerTail_nat_power (t p v : ℝ) (c : ℕ) (ht : 0 < t) (hv : 0 < v) :
    powerTail t p v ^ c = powerTail t (p * c) v := by
  dsimp [powerTail]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hv.le ht.le)]
  congr 1
  ring

theorem rank_failure_pareto (N c : ℕ) (h t v : ℝ)
    (hc : c ≤ N + 1) (hh : h ∈ Icc (0 : ℝ) 1)
    (ht : 0 < t) (hv : t ≤ v) :
    1 - rankSuccess N c (h / 2 * powerTail t 10 v) ≤
      ((2 : ℝ) ^ N * (h / 2) ^ c) * powerTail t (10 * c) v := by
  have hv0 : 0 < v := ht.trans_le hv
  have hr1 : 1 ≤ v / t := (le_div_iff₀ ht).2 (by simpa using hv)
  have htail : powerTail t 10 v ≤ 1 := by
    dsimp [powerTail]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num)
  have htail0 := powerTail_nonneg t 10 v ht hv0.le
  have hp : h / 2 * powerTail t 10 v ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (by linarith [hh.1]) htail0
    · nlinarith [hh.1, hh.2]
  have hbound := rank_failure_le_power N c _ hc hp
  rw [mul_pow, powerTail_nat_power t 10 v c ht hv0] at hbound
  simpa [mul_assoc] using hbound

def movingRankMajorant (K : ℝ) (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (m - 1) * (K / (m : ℝ) ^ 2) ^ marketCapacity m

theorem movingRankMajorant_superexp (K : ℝ) (m : ℕ)
    (hK : 0 ≤ K) (hm : 256 ≤ m) (hKm : K ≤ (m : ℝ)) :
    movingRankMajorant K m ≤ Real.exp (-((m : ℝ) * Real.log (m : ℝ)) / 8) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm256 : (256 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hclo, _hchi, _hcpos, _hcm⟩ := capacity_bounds m (by omega)
  have hcquarter : (m : ℝ) / 4 ≤ marketCapacity m := by nlinarith
  have hprob : K / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hm0).2
    nlinarith
  have hlogm : 8 * Real.log 2 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 256) hm256
    have he : Real.log (256 : ℝ) = 8 * Real.log 2 := by
      rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at h
  have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by linarith)
  calc
    movingRankMajorant K m ≤ (2 : ℝ) ^ m * (1 / (m : ℝ)) ^ marketCapacity m := by
      dsimp [movingRankMajorant]
      exact mul_le_mul (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
        (pow_le_pow_left₀ (by positivity) hprob _) (by positivity) (by positivity)
    _ = Real.exp ((m : ℝ) * Real.log 2 -
        (marketCapacity m : ℝ) * Real.log (m : ℝ)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
        Real.exp_nat_mul, Real.exp_log hm0, one_div_pow]
      ring
    _ ≤ Real.exp (-((m : ℝ) * Real.log (m : ℝ)) / 8) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_right hcquarter hlogm0
      have h2 := mul_le_mul_of_nonneg_left hlogm hm0.le
      nlinarith

end FCAppendix.Affine.Tail04
