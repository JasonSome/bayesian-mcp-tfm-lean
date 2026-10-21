import FCAppendix.Affine.Tail04.Underfill
import FCAppendix.Affine.Tail04.CountLaws
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace FCAppendix.Affine.Tail04.Markets
open MeasureTheory ProbabilityTheory Game Bayes Filter Topology

def capacity (m : ℕ) : ℕ := ⌊(99/200:ℝ)*m⌋₊

theorem capacity_le (m : ℕ) : (capacity m:ℝ)≤(99/200:ℝ)*m :=
  Nat.floor_le (mul_nonneg (by norm_num) (Nat.cast_nonneg m))

theorem capacity_le_half (m : ℕ) : (capacity m:ℝ)≤(m:ℝ)/2 := by
  have hm : (0:ℝ)≤ m := Nat.cast_nonneg m
  have hh := capacity_le m
  nlinarith

theorem capacity_density :
    Tendsto (fun m : ℕ => (capacity m:ℝ)/(m:ℝ)) atTop (𝓝 (99/200:ℝ)) := by
  exact (tendsto_nat_floor_mul_div_atTop (by norm_num : (0:ℝ)≤99/200)).comp
    tendsto_natCast_atTop_atTop

theorem eventually_capacity_positive : ∀ᶠ m in atTop,0< capacity m := by
  have h := (tendsto_nat_floor_mul_atTop (99/200:ℝ) (by norm_num)).eventually_ge_atTop 1
  simpa only [capacity,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero] using h

theorem source_exponential_tendsto_zero (N : ℕ→ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => Real.exp (-(N k:ℝ)/50)) atTop (𝓝 0) := by
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop (by norm_num : (0:ℝ)<1/50))
  convert! hh using 1
  funext k
  congr 1
  simp only [Function.comp_def]
  ring

theorem source_population_exponential_tendsto_zero (N : ℕ→ℕ)
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun k => (N k:ℝ)*Real.exp (-(N k:ℝ)/50)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/50:ℝ)
    (by norm_num)).comp (tendsto_natCast_atTop_atTop.comp hN)
  simpa only [Real.rpow_one,Function.comp_def,show ∀ x : ℝ,-(1/50)*x=-x/50 by
    intro x; ring] using hh

section Native
variable (N c : ℕ→ℕ) (Seed : ℕ→ Type*) [∀ k,MeasurableSpace (Seed k)]
variable (Γ : ∀ k,FiniteGame (N k) 2 (c k) (Seed k))
variable (hN0 : ∀ k,0< N k) (hN : Tendsto N atTop atTop)
variable (hc : ∀ k,(c k:ℝ)≤(N k:ℝ)/2)
variable (hunused : ∀ k j,
  (∫ ω,unusedCapacity (Γ k) j ω ∂backgroundLaw (Γ k)) ≤
    (c k:ℝ)*Real.exp (-(N k:ℝ)/50))

include hN hc hunused in
theorem expected_unused_tendsto_zero (j : Fin 2) :
    Tendsto (fun k => ∫ ω,unusedCapacity (Γ k) j ω ∂backgroundLaw (Γ k))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun k =>
    integral_nonneg (unusedCapacity_nonneg (Γ k) j))) _
      (by simpa only [zero_div] using (source_population_exponential_tendsto_zero N hN).div_const 2)
  exact Eventually.of_forall (fun k =>
    (hunused k j).trans (by
      have hh := mul_le_mul_of_nonneg_right (hc k) (Real.exp_nonneg (-(N k:ℝ)/50))
      convert! hh using 1
      ring))

include hN0 hN hc hunused in
theorem actual_load_gap_tendsto_zero :
    Tendsto (fun k => 2*((c k:ℝ)/(N k:ℝ))-finiteLoad (Γ k))
      atTop (𝓝 0) := by
  have hgap (k : ℕ) := Underfill.native_load_gap_bound (Γ k) (hN0 k)
    ((c k:ℝ)*Real.exp (-(N k:ℝ)/50)) (hunused k)
  apply squeeze_zero' (Eventually.of_forall (fun k => (hgap k).1)) _
    (source_exponential_tendsto_zero N hN)
  refine Eventually.of_forall (fun k => (hgap k).2.trans ?_)
  have hNk : (0:ℝ)< N k := Nat.cast_pos.mpr (hN0 k)
  apply (div_le_iff₀ hNk).mpr
  have hh := mul_le_mul_of_nonneg_right (hc k) (Real.exp_nonneg (-(N k:ℝ)/50))
  nlinarith

include hN0 hN hc hunused in
theorem actual_load_tendsto (ρ : ℝ)
    (hdensity : Tendsto (fun k => (c k:ℝ)/(N k:ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (2*ρ)) := by
  have hh := (hdensity.const_mul 2).sub
    (actual_load_gap_tendsto_zero N c Seed Γ hN0 hN hc hunused)
  simpa only [sub_sub_cancel,sub_zero] using hh

include hN0 hN hc hunused in
theorem source_load_tendsto (hcap : ∀ k,c k=capacity (N k)) :
    Tendsto (fun k => finiteLoad (Γ k)) atTop (𝓝 (99/100:ℝ)) := by
  have hdensity : Tendsto (fun k => (c k:ℝ)/(N k:ℝ)) atTop (𝓝 (99/200:ℝ)) := by
    simp_rw [hcap]
    exact capacity_density.comp hN
  convert! actual_load_tendsto N c Seed Γ hN0 hN hc hunused (99/200) hdensity using 1
  norm_num

end Native
end FCAppendix.Affine.Tail04.Markets
