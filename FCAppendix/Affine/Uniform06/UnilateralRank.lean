import FCAppendix.Affine.Uniform06.RankRent
import FCAppendix.Affine.LowBody.CategoricalRateGuards
import FCAppendix.Finite.RankConcentration

noncomputable section
namespace FCAppendix.Affine.Uniform06.UnilateralRank

open MeasureTheory Set Filter Topology

def rankLower (c : ℕ → ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  Bayes.binomBelow (m-1) p (c m)

theorem ell_eq_rankLower (c : ℕ → ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {m : ℕ} (hm : 0 < m) (hc : 0 < c m) (hcm : c m ≤ m) :
    LowBody.ell c p hp0 hp1 m = rankLower c p m := by
  rw [rankLower,Bayes.binomBelow_eq_prob (m-1) (c m) (by omega) p hp0 hp1]
  unfold LowBody.ell
  congr 1
  funext r
  apply propext
  omega

theorem eventual_capacity_interior (c : ℕ → ℕ) {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0:ℝ) 1)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ)) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 0 < c m ∧ c m ≤ m := by
  filter_upwards [hc.eventually_const_lt hρ.1,hc.eventually_lt_const hρ.2,
    eventually_gt_atTop (0:ℕ)] with m hl hu hm
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hcl : (0:ℝ) < c m := (div_pos_iff_of_pos_right hmR).mp hl
  have hcu : (c m:ℝ) < m := (div_lt_one hmR).mp hu
  exact ⟨hm,Nat.cast_pos.mp hcl,(Nat.cast_lt.mp hcu).le⟩

theorem eventually_rankLower_ge_exp
    (c : ℕ → ℕ) (p ρ : ℝ)
    (hp : p ∈ Ioo (0:ℝ) 1) (hρ : ρ ∈ Ioo (0:ℝ) 1)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    {r : ℝ} (hr : Ample.binaryKL ρ p < r) :
    ∀ᶠ m : ℕ in atTop, Real.exp (-(m:ℝ)*r) ≤ rankLower c p m := by
  have h := LowBody.eventually_binomial_lower c p ρ hp.1 hp.2 hρ.1 hρ.2 hc r hr
  filter_upwards [h,eventual_capacity_interior c hρ hc] with m hm hcap
  rw [ell_eq_rankLower c p hp.1.le hp.2.le hcap.1 hcap.2.1 hcap.2.2] at hm
  exact hm.1

theorem eventually_relative_rank_bound
    {A : Type*} (c : ℕ → ℕ) (p ρ : ℝ)
    (hp : p ∈ Ioo (0:ℝ) 1) (hρ : ρ ∈ Ioo (0:ℝ) 1)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (D : ℕ → A → ℝ) {J r : ℝ}
    (hr : Ample.binaryKL ρ p < r) (_hgap : r < J)
    (hD : ∀ᶠ m : ℕ in atTop, ∀ a, D m a ≤ Real.exp (-(m:ℝ)*J)) :
    ∀ᶠ m : ℕ in atTop, 0 < rankLower c p m ∧
      ∀ a, D m a/rankLower c p m ≤ Real.exp (-(m:ℝ)*(J-r)) := by
  filter_upwards [eventually_rankLower_ge_exp c p ρ hp hρ hc hr,hD]
    with m hL hD
  have hL0 : 0 < rankLower c p m := (Real.exp_pos _).trans_le hL
  refine ⟨hL0,fun a => ?_⟩
  apply (div_le_iff₀ hL0).mpr
  have hmult := mul_le_mul_of_nonneg_left hL (Real.exp_pos (-(m:ℝ)*(J-r))).le
  have he : Real.exp (-(m:ℝ)*(J-r))*Real.exp (-(m:ℝ)*r) =
      Real.exp (-(m:ℝ)*J) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hmult
  exact (hD a).trans hmult

theorem eventually_relative_rank_small
    {A : Type*} (c : ℕ → ℕ) (p ρ : ℝ)
    (hp : p ∈ Ioo (0:ℝ) 1) (hρ : ρ ∈ Ioo (0:ℝ) 1)
    (hc : Tendsto (fun m => (c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (D : ℕ → A → ℝ) {J r ε : ℝ}
    (hr : Ample.binaryKL ρ p < r) (hgap : r < J) (hε : 0 < ε)
    (hD : ∀ᶠ m : ℕ in atTop, ∀ a, D m a ≤ Real.exp (-(m:ℝ)*J)) :
    ∀ᶠ m : ℕ in atTop, 0 < rankLower c p m ∧
      ∀ a, D m a < ε*rankLower c p m := by
  have he : Tendsto (fun m : ℕ => Real.exp (-(m:ℝ)*(J-r))) atTop (𝓝 0) := by
    have hm : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hm.const_mul_atTop (sub_pos.mpr hgap)) using 1
    funext m
    congr 1
    ring
  filter_upwards [eventually_relative_rank_bound c p ρ hp hρ hc D hr hgap hD,
    he.eventually_lt_const hε] with m hm he
  refine ⟨hm.1,fun a => ?_⟩
  exact (div_lt_iff₀ hm.1).mp ((hm.2 a).trans_lt he)

end FCAppendix.Affine.Uniform06.UnilateralRank
