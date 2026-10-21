import FCAppendix.Affine.Uniform06.RawMarkedLaplace
import FCAppendix.Affine.Uniform06.RawArrayRareBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.ArrayRecount

open MeasureTheory Filter Set
open scoped Topology
open MixedIntervalLLT

variable {Ω : Type*} [MeasurableSpace Ω]

def recount (A : CenteredArray Ω) (M : ℕ → ℕ)
    (hM : ∀ n,0 < M n) (hmarket : Tendsto M atTop atTop) : CenteredArray Ω where
  law := A.law
  probability := A.probability
  X := A.X
  Y := A.Y
  N := M
  d := fun n => (Real.sqrt (M n:ℝ))⁻¹
  measurable_X := A.measurable_X
  measurable_Y := A.measurable_Y
  bounded := A.bounded
  mean_X := A.mean_X
  mean_Y := A.mean_Y
  covariance := A.covariance
  d_nonneg := fun n => inv_nonneg.mpr (Real.sqrt_nonneg _)
  d_zero := tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hmarket))
  scale := by
    intro n
    have hn : 0 < (M n:ℝ) := Nat.cast_pos.mpr (hM n)
    rw [inv_pow,Real.sq_sqrt hn.le,mul_inv_cancel₀ hn.ne']
  market := hmarket
  vX := A.vX
  vY := A.vY
  lowerVariance := A.lowerVariance
  lowerVariance_pos := A.lowerVariance_pos
  variance_X_lower := A.variance_X_lower
  variance_Y_lower := A.variance_Y_lower
  variance_X_limit := A.variance_X_limit
  variance_Y_limit := A.variance_Y_limit

theorem recount_gap (A : CenteredArray Ω) (hgap : A.CompactGap)
    (M : ℕ → ℕ) (hM : ∀ n,0 < M n) (hmarket : Tendsto M atTop atTop) :
    (recount A M hM hmarket).CompactGap := hgap

def remaining (A : CenteredArray Ω) (k : ℕ) (n : ℕ) : ℕ := max 1 (A.N n-k)

theorem remaining_positive (A : CenteredArray Ω) (k n : ℕ) : 0 < remaining A k n :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem remaining_market (A : CenteredArray Ω) (k : ℕ) : Tendsto (remaining A k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  filter_upwards [A.market.eventually (eventually_ge_atTop (K+k))] with n hn
  dsimp [remaining]
  omega

theorem remaining_eventually (A : CenteredArray Ω) (k : ℕ) :
    ∀ᶠ n in atTop,k+remaining A k n=A.N n := by
  filter_upwards [A.market.eventually (eventually_ge_atTop (k+1))] with n hn
  dsimp [remaining]
  omega

def deleteFixed (A : CenteredArray Ω) (k : ℕ) : CenteredArray Ω :=
  recount A (remaining A k) (remaining_positive A k) (remaining_market A k)

theorem deleteFixed_gap (A : CenteredArray Ω) (hgap : A.CompactGap) (k : ℕ) :
    (deleteFixed A k).CompactGap := hgap

theorem full_to_remaining (A : CenteredArray Ω) (k : ℕ) :
    Tendsto (fun n => (A.N n:ℝ)/(remaining A k n:ℝ)) atTop (𝓝 1) := by
  have hN : Tendsto (fun n => (remaining A k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (remaining_market A k)
  have hinv := tendsto_inv_atTop_zero.comp hN
  have hh : Tendsto (fun n => 1+(k:ℝ)*(remaining A k n:ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero,Function.comp_def] using! tendsto_const_nhds.add (hinv.const_mul (k:ℝ))
  apply hh.congr'
  filter_upwards [remaining_eventually A k] with n hn
  rw [← hn,Nat.cast_add]
  have hpos : (remaining A k n:ℝ) ≠ 0 := by exact_mod_cast (remaining_positive A k n).ne'
  field_simp [hpos]
  ring

theorem descFactorial_ratio (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (k : ℕ) :
    Tendsto (fun n => ((N n).descFactorial k:ℝ)/(N n:ℝ)^k) atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hNR : Tendsto (fun n => (N n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
    have hinv := tendsto_inv_atTop_zero.comp hNR
    have hfirst : Tendsto (fun n => ((N n-k:ℕ):ℝ)/(N n:ℝ)) atTop (𝓝 1) := by
      have hh : Tendsto (fun n => 1-(k:ℝ)*(N n:ℝ)⁻¹) atTop (𝓝 1) := by
        simpa only [mul_zero,sub_zero,Function.comp_def] using! tendsto_const_nhds.sub (hinv.const_mul (k:ℝ))
      apply hh.congr'
      filter_upwards [hN.eventually (eventually_ge_atTop (k+1))] with n hn
      have hn0 : (N n:ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
      rw [Nat.cast_sub (by omega : k ≤ N n)]
      field_simp [hn0]
    have hh := hfirst.mul ih
    simpa only [one_mul] using hh.congr' (Eventually.of_forall fun n => by
      rw [Nat.descFactorial_succ,Nat.cast_mul,pow_succ]
      rw [div_mul_div_comm]
      congr 1
      ring)

theorem selected_shift_zero (A : CenteredArray Ω) (k : ℕ)
    (cap r : ℕ → ℝ)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hmatch : ∀ᶠ n in atTop,cap n=(A.N n:ℝ)*r n) :
    Tendsto (fun n => (deleteFixed A k).d n*
      (cap n-(k:ℝ)/2-((deleteFixed A k).N n:ℝ)*r n)) atTop (𝓝 0) := by
  have hh := UniformMarkedLLT.bounded_multiplier_tendsto_zero
    (show 0 ≤ (k:ℝ) by positivity) (deleteFixed A k).d_zero
    (fun n => show |(k:ℝ)*(r n-1/2)| ≤ (k:ℝ) by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg k)]
      have hrabs : |r n-1/2| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hr n).1,(hr n).2]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hrabs (Nat.cast_nonneg k))
  apply hh.congr'
  filter_upwards [remaining_eventually A k,hmatch] with n hn hm
  rw [hm,← hn,Nat.cast_add]
  dsimp only [deleteFixed,recount]
  ring

end FCAppendix.Affine.Uniform06.ArrayRecount
