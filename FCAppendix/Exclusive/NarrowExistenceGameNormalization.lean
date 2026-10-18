import FCAppendix.Exclusive.NarrowExistenceGameUtility
import FCAppendix.Exclusive.NarrowKernel
import FCAppendix.Exclusive.NarrowRivalCalculus

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set
open scoped BigOperators

theorem referenceBidScale_mul_sourceValueFactor (d : ℕ) (hd : 1 ≤ d)
    (a : UserTariff) (ha : a.Allowed) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    referenceBidScale d a p*sourceValueFactor d a p = 1 := by
  have hf := (fTariff_pos_and_derivative_pos d hd a ha hp0 hp1).1.ne'
  have hq := (pow_pos (sub_pos.mpr hp1) d).ne'
  dsimp [referenceBidScale, sourceValueFactor]
  field_simp

theorem inverseBid_scaled_exp (d : ℕ) (B z : ℝ) (hB : 0 < B) :
    inverseBid (d+1) (B*Real.exp z) = B^(-(1/(d:ℝ)))*Real.exp (-(1/(d:ℝ))*z) := by
  simp only [inverseBid, rate, Nat.add_sub_cancel_right]
  rw [Real.mul_rpow hB.le (Real.exp_pos _).le, ← Real.exp_mul]
  rw [mul_comm z (-(1/(d:ℝ)))]

def rawRivalInverseSum {m : ℕ} {V : Type*} (d : ℕ) (B : ℝ)
    (beta : V → ℝ) (omega : RivalProfile m V) : ℝ :=
  ∑ i, activeBit (omega i).1*inverseBid (d+1) (B*Real.exp (beta (omega i).2))

theorem rawRivalInverseSum_eq {m : ℕ} {V : Type*} (d : ℕ) (B : ℝ) (hB : 0 < B)
    (beta : V → ℝ) (omega : RivalProfile m V) :
    rawRivalInverseSum d B beta omega = B^(-(1/(d:ℝ)))*rivalInverseSum (1/(d:ℝ)) beta omega := by
  unfold rawRivalInverseSum rivalInverseSum
  simp_rw [inverseBid_scaled_exp d B _ hB]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem focalMarginal_scaled_exp (r A B W z : ℝ) (hB : 0 < B) :
    focalMarginal r A (B^(-r)*W) (B*Real.exp z) = logAllocation r A W z := by
  have hpow := (Real.rpow_pos_of_pos hB (-r)).ne'
  have he : (B*Real.exp z)^(-r) = B^(-r)*Real.exp (-r*z) := by
    rw [Real.mul_rpow hB.le (Real.exp_pos _).le, ← Real.exp_mul]
    rw [mul_comm z (-r)]
  dsimp [focalMarginal, logAllocation, logShare]
  rw [he, ← mul_add,
    show A*(B^(-r)*Real.exp (-r*z)) = B^(-r)*(A*Real.exp (-r*z)) by ring,
    mul_div_mul_left _ _ hpow]
  ring

theorem sampled_raw_allocation_eq {m : ℕ} {V : Type*} (d c : ℕ) (B : ℝ) (hB : 0 < B)
    (beta : V → ℝ) (z : ℝ) (omega : RivalProfile m V) :
    focalMarginal (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
      (rawRivalInverseSum d B beta omega) (B*Real.exp z) =
        logAllocation (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
          (rivalInverseSum (1/(d:ℝ)) beta omega) z := by
  rw [rawRivalInverseSum_eq d B hB]
  exact focalMarginal_scaled_exp _ _ _ _ _ hB

theorem finiteRowUtility_normalization {m : ℕ} {V : Type*}
    (d c : ℕ) (hd : 1 ≤ d) (a : UserTariff) (ha : a.Allowed) (G : Schedule (d+1))
    (p0 H baseRatio : ℝ) (hp0 : 0 ≤ p0) (hp1 : p0 < 1) (hH : 0 < H)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    let B := H*referenceBidScale d a p0
    let p := focalMarginal (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
      (rawRivalInverseSum d B beta omega) (B*Real.exp z)
    H*v*binomialPolynomial (d+1) successIndicator p-
      (B*Real.exp z)*binomialPolynomial (d+1) a.charge p-
        (H*baseRatio)*binomialPolynomial (d+1) G.charge p =
      B*finiteRowUtility d c a G p0 baseRatio beta v z omega := by
  have hB := mul_pos hH (referenceBidScale_pos d hd a ha p0 hp0 hp1)
  dsimp only
  rw [sampled_raw_allocation_eq d c _ hB]
  have hfactor := referenceBidScale_mul_sourceValueFactor d hd a ha p0 hp0 hp1
  dsimp [finiteRowUtility, utility]
  calc
    _ = H*(referenceBidScale d a p0*sourceValueFactor d a p0)*v*
        binomialPolynomial (d+1) successIndicator
          (logAllocation (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ) (rivalInverseSum (1/(d:ℝ)) beta omega) z)-
      (H*referenceBidScale d a p0*Real.exp z)*binomialPolynomial (d+1) a.charge
        (logAllocation (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ) (rivalInverseSum (1/(d:ℝ)) beta omega) z)-
      (H*(referenceBidScale d a p0*sourceValueFactor d a p0)*baseRatio)*
        binomialPolynomial (d+1) G.charge
          (logAllocation (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ) (rivalInverseSum (1/(d:ℝ)) beta omega) z) := by rw [hfactor]; ring
    _ = _ := by ring

theorem log_bid_spread (d M c : ℕ) (hM : 0 < M) (B delta : ℝ) (hB : 0 < B)
    (hsafe : (1-(c:ℝ)/(M:ℝ))*Real.exp (2*(1/(d:ℝ))*delta) < 1) :
    ((M:ℝ)-c)*inverseBid (d+1) (B*Real.exp (-delta)) <
      (M:ℝ)*inverseBid (d+1) (B*Real.exp delta) := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hpow := Real.rpow_pos_of_pos hB (-(1/(d:ℝ)))
  have hratio : (M:ℝ)*(1-(c:ℝ)/(M:ℝ)) = (M:ℝ)-c := by field_simp
  have h1 := mul_lt_mul_of_pos_left hsafe hMr
  rw [← mul_assoc, hratio, mul_one] at h1
  have h2 := mul_lt_mul_of_pos_right h1 (Real.exp_pos (-(1/(d:ℝ))*delta))
  have hex : Real.exp (2*(1/(d:ℝ))*delta)*Real.exp (-(1/(d:ℝ))*delta) =
      Real.exp ((1/(d:ℝ))*delta) := by rw [← Real.exp_add]; congr 1; ring
  rw [mul_assoc, hex] at h2
  rw [inverseBid_scaled_exp d B _ hB, inverseBid_scaled_exp d B _ hB]
  have he : -(1/(d:ℝ))*(-delta) = (1/(d:ℝ))*delta := by ring
  rw [he]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_lt_mul_of_pos_left h2 hpow

def logCorridor (d M c : ℕ) (hd : 1 ≤ d) (hM : 0 < M) (hc : 0 < c)
    (B delta : ℝ) (hB : 0 < B) (hdelta : 0 < delta)
    (hsafe : (1-(c:ℝ)/(M:ℝ))*Real.exp (2*(1/(d:ℝ))*delta) < 1) :
    Exclusive.Narrow.Finite.Corridor (d+1) M c where
  lower := B*Real.exp (-delta)
  upper := B*Real.exp delta
  lower_pos := mul_pos hB (Real.exp_pos _)
  width := mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (by linarith)) hB
  proposers := by omega
  population := hM
  capacity := hc
  spread := log_bid_spread d M c hM B delta hB hsafe

theorem mem_logCorridor (d M c : ℕ) (hd : 1 ≤ d) (hM : 0 < M) (hc : 0 < c)
    (B delta : ℝ) (hB : 0 < B) (hdelta : 0 < delta)
    (hsafe : (1-(c:ℝ)/(M:ℝ))*Real.exp (2*(1/(d:ℝ))*delta) < 1)
    (z : ℝ) (hz : z ∈ Icc (-delta) delta) :
    B*Real.exp z ∈ Icc (logCorridor d M c hd hM hc B delta hB hdelta hsafe).lower
      (logCorridor d M c hd hM hc B delta hB hdelta hsafe).upper :=
  ⟨mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz.1) hB.le,
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hz.2) hB.le⟩

end FCAppendix.Exclusive.Narrow.Existence
