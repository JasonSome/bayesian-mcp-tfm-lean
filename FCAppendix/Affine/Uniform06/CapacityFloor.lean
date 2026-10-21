import FCAppendix.Affine.Uniform07.Parameters
import Mathlib

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.PhysicalRates
open FCAppendix.Affine.Uniform07 Set Filter

theorem capacity_floor_bounds (m : ℕ) :
    rho*(m:ℝ)-1 < (capacity m:ℝ) ∧ (capacity m:ℝ) ≤ rho*(m:ℝ) := by
  have hmod : (999*m)%2000 < 2000 := Nat.mod_lt _ (by norm_num)
  have heq := Nat.mod_add_div (999*m) 2000
  have hmodR : (((999*m)%2000:ℕ):ℝ) < 2000 := by exact_mod_cast hmod
  have heqR : (((999*m)%2000:ℕ):ℝ)+2000*(capacity m:ℝ)=999*(m:ℝ) := by
    exact_mod_cast heq
  have hmod0 : (0:ℝ) ≤ (((999*m)%2000:ℕ):ℝ) := Nat.cast_nonneg _
  norm_num only [rho]
  constructor <;> nlinarith

theorem capacity_positive {m : ℕ} (hm : 3 ≤ m) : 0 < capacity m := by
  unfold capacity
  omega

theorem capacity_strictly_below_rivals {m : ℕ} (hm : 4 ≤ m) :
    capacity m < m-1 := by
  unfold capacity
  omega

theorem capacity_density_error {m : ℕ} (hm : 0 < m) :
    |(capacity m:ℝ)/(m:ℝ)-rho| ≤ 1/(m:ℝ) := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hf := capacity_floor_bounds m
  apply abs_le.mpr
  constructor
  · have h := div_le_div_of_nonneg_right hf.1.le hmr.le
    have he : (rho*(m:ℝ)-1)/(m:ℝ)=rho-1/(m:ℝ) := by
      field_simp [hmr.ne']
    rw [he] at h
    linarith
  · have h := (div_le_iff₀ hmr).mpr hf.2
    have hnon : (0:ℝ) ≤ 1/(m:ℝ) := by positivity
    linarith

theorem capacity_density_tendsto :
    Tendsto (fun m : ℕ => (capacity m:ℝ)/(m:ℝ)) atTop (nhds rho) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt (1/ε)
  refine ⟨max M 1,?_⟩
  intro m hm
  have hm1 : 1 ≤ m := (le_max_right _ _).trans hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hMm : (M:ℝ) ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have hprod : 1 < (m:ℝ)*ε := (div_lt_iff₀ hε).mp (hM.trans_le hMm)
  have hsmall : 1/(m:ℝ) < ε := (div_lt_iff₀ hm0).mpr (by nlinarith)
  rw [Real.dist_eq]
  exact (capacity_density_error (by omega)).trans_lt hsmall

theorem rival_capacity_density_error {m : ℕ} (hm : 2 ≤ m) :
    |(capacity m:ℝ)/((m-1:ℕ):ℝ)-rho| ≤ 1/((m-1:ℕ):ℝ) := by
  have hmr : (0:ℝ) < ((m-1:ℕ):ℝ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hf := capacity_floor_bounds m
  have hlo : rho*((m-1:ℕ):ℝ)-1 ≤ (capacity m:ℝ) := by
    rw [hcast]
    norm_num only [rho] at *
    nlinarith
  have hhi : (capacity m:ℝ) ≤ rho*((m-1:ℕ):ℝ)+1 := by
    rw [hcast]
    norm_num only [rho] at *
    nlinarith
  apply abs_le.mpr
  constructor
  · have h := div_le_div_of_nonneg_right hlo hmr.le
    have he : (rho*((m-1:ℕ):ℝ)-1)/((m-1:ℕ):ℝ)=
        rho-1/((m-1:ℕ):ℝ) := by field_simp [hmr.ne']
    rw [he] at h
    linarith
  · have h := div_le_div_of_nonneg_right hhi hmr.le
    have he : (rho*((m-1:ℕ):ℝ)+1)/((m-1:ℕ):ℝ)=
        rho+1/((m-1:ℕ):ℝ) := by field_simp [hmr.ne']
    rw [he] at h
    linarith

theorem rival_capacity_density_tendsto :
    Tendsto (fun m : ℕ => (capacity m:ℝ)/((m-1:ℕ):ℝ)) atTop (nhds rho) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt (1/ε+1)
  refine ⟨max M 2,?_⟩
  intro m hm
  have hm2 : 2 ≤ m := (le_max_right _ _).trans hm
  have hm0 : (0:ℝ) < ((m-1:ℕ):ℝ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hMm : (M:ℝ) ≤ m := by exact_mod_cast (le_max_left _ _).trans hm
  have hcast : ((m-1:ℕ):ℝ)=(m:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hlarge : 1/ε < ((m-1:ℕ):ℝ) := by rw [hcast]; linarith
  have hprod : 1 < ((m-1:ℕ):ℝ)*ε := (div_lt_iff₀ hε).mp hlarge
  have hsmall : 1/((m-1:ℕ):ℝ) < ε := (div_lt_iff₀ hm0).mpr (by nlinarith)
  rw [Real.dist_eq]
  exact (rival_capacity_density_error hm2).trans_lt hsmall

theorem rivals_tendsto : Tendsto (fun m : ℕ => m-1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro K
  exact eventually_atTop.mpr ⟨K+1,fun m hm => by omega⟩

end FCAppendix.Affine.Uniform06.PhysicalRates
