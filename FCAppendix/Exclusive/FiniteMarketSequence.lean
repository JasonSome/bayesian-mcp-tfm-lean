import FCAppendix.Exclusive.ScarceAssembly
import Mathlib.Analysis.SpecificLimits.Basic

namespace FCAppendix.Exclusive.Construction
open Filter Topology

def marketPopulation (t : ℕ) : ℕ := t+1
noncomputable def marketCapacity (rho : ℝ) (t : ℕ) : ℕ :=
  ⌊rho*(marketPopulation t : ℝ)⌋₊

theorem marketPopulation_tendsto : Tendsto marketPopulation atTop atTop :=
  tendsto_add_atTop_nat 1

theorem marketCapacity_tendsto {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (marketCapacity rho) atTop atTop := by
  exact (tendsto_nat_floor_mul_atTop rho hrho).comp marketPopulation_tendsto

theorem marketDensity_tendsto {rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto (fun t => (marketCapacity rho t : ℝ)/(marketPopulation t : ℝ))
      atTop (𝓝 rho) :=
  (tendsto_nat_floor_mul_div_atTop hrho).comp
    (tendsto_natCast_atTop_atTop.comp marketPopulation_tendsto)

theorem marketCapacity_le {rho : ℝ} (hrho : 0 ≤ rho) (t : ℕ) :
    (marketCapacity rho t : ℝ) ≤ rho*(marketPopulation t : ℝ) :=
  Nat.floor_le (mul_nonneg hrho (Nat.cast_nonneg _))

theorem eventually_marker_room (n : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (hscarce : (n : ℝ)*rho < 1) :
    ∀ᶠ t in atTop, 0 < marketCapacity rho t ∧
      n*marketCapacity rho t+(n-1) ≤ marketPopulation t := by
  have hgap : 0 < 1-(n : ℝ)*rho := sub_pos.mpr hscarce
  obtain ⟨K, hK⟩ := exists_nat_gt ((n : ℝ)/(1-(n : ℝ)*rho))
  filter_upwards [(marketCapacity_tendsto hrho).eventually_ge_atTop 1,
    marketPopulation_tendsto.eventually_ge_atTop K] with t hc hM
  refine ⟨by omega, ?_⟩
  have hKR : (n : ℝ)/(1-(n : ℝ)*rho) < (marketPopulation t : ℝ) :=
    hK.trans_le (by exact_mod_cast hM)
  have hnum := (div_lt_iff₀ hgap).mp hKR
  have hfloor := mul_le_mul_of_nonneg_left (marketCapacity_le hrho.le t) (Nat.cast_nonneg n)
  have hroom : (n*marketCapacity rho t+n : ℕ) < marketPopulation t := by
    have hR : (n : ℝ)*(marketCapacity rho t : ℝ)+(n : ℝ) < marketPopulation t := by
      nlinarith
    exact_mod_cast hR
  omega

theorem exists_marker_market_sequence (n : ℕ) {rho : ℝ} (hrho : 0 < rho)
    (hscarce : (n : ℝ)*rho < 1) :
    ∃ M C : ℕ → ℕ, Tendsto M atTop atTop ∧
      Tendsto (fun t => (C t : ℝ)/(M t : ℝ)) atTop (𝓝 rho) ∧
      ∀ t, 0 < C t ∧ n*C t+(n-1) ≤ M t := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_marker_room n hrho hscarce)
  refine ⟨fun t => marketPopulation (t+T), fun t => marketCapacity rho (t+T),
    marketPopulation_tendsto.comp (tendsto_add_atTop_nat T),
    (marketDensity_tendsto hrho.le).comp (tendsto_add_atTop_nat T), ?_⟩
  intro t
  exact hT (t+T) (by omega)

end FCAppendix.Exclusive.Construction
