import FCAppendix.Affine.Hybrid.Finishing01ClusterPointwise

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology

theorem tendsto_fourth_power_times_count_exp {delta : ℝ} (hd : 0< delta) :
    Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)^4*Real.exp (-(N:ℝ)*delta^2/2))
      atTop (𝓝 0) := by
  let a := delta^2/2
  have ha : 0< a := by dsimp [a];positivity
  have ht : Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)*a) atTop atTop :=
    by simpa only [mul_comm,Function.comp_def] using
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).const_mul_atTop ha)
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 4).comp ht).const_mul
    (Real.exp a/a^4)
  convert! h using 1
  · funext N
    have he : Real.exp (-(N:ℝ)*delta^2/2)=
        Real.exp a*Real.exp (-(((N+1:ℕ):ℝ)*a)) := by
      rw [←Real.exp_add]
      congr 1
      dsimp [a]
      push_cast
      ring
    rw [he]
    simp only [Function.comp_apply,mul_pow]
    field_simp [ha.ne']
  · simp

namespace Finish01.Primitives
variable (P : Primitives)

def clusterPositiveCoefficient (N : ℕ) : ℝ :=
  P.clusterRankGain/(32*((N+1:ℕ):ℝ)^3)

def clusterPureCoefficient (delta : ℝ) (N : ℕ) : ℝ :=
  P.eta*P.U*(N:ℝ)*(8*Real.exp (-(N:ℝ)*delta^2/2))

theorem clusterPositiveCoefficient_pos (N : ℕ) : 0< P.clusterPositiveCoefficient N := by
  unfold clusterPositiveCoefficient
  exact div_pos P.clusterRankGain_pos (by positivity)

theorem clusterPureCoefficient_nonneg (delta : ℝ) (N : ℕ) :
    0≤ P.clusterPureCoefficient delta N := by
  unfold clusterPureCoefficient
  have hEta := P.eta_pos
  have hU := P.U_pos
  positivity

theorem exponential_dominates_cluster_coefficient {delta : ℝ} (hd : 0< delta) :
    ∀ᶠN : ℕ in atTop,
      P.clusterPureCoefficient delta N< P.clusterPositiveCoefficient N/2 := by
  have hz : Tendsto (fun N : ℕ => 512*P.eta*P.U*(((N+1:ℕ):ℝ)^4*Real.exp (-(N:ℝ)*delta^2/2))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_fourth_power_times_count_exp hd).const_mul (512*P.eta*P.U)
  have hsmall : ∀ᶠN : ℕ in atTop,
      512*P.eta*P.U*(((N+1:ℕ):ℝ)^4*Real.exp (-(N:ℝ)*delta^2/2))< P.clusterRankGain := by
    exact hz.eventually_lt_const P.clusterRankGain_pos
  filter_upwards [hsmall] with N hN
  have hden : 0<64*((N+1:ℕ):ℝ)^3 := by positivity
  have hp : (N:ℝ)*((N+1:ℕ):ℝ)^3≤((N+1:ℕ):ℝ)^4 := by
    have h := mul_le_mul_of_nonneg_right (show (N:ℝ)≤((N+1:ℕ):ℝ) by
      exact_mod_cast Nat.le_succ N) (show 0≤((N+1:ℕ):ℝ)^3 by positivity)
    simpa only [pow_succ,mul_comm] using h
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0≤512*P.eta*P.U*Real.exp (-(N:ℝ)*delta^2/2) by
      have hEta := P.eta_pos
      have hU := P.U_pos
      positivity)
  have hprod : P.clusterPureCoefficient delta N*(64*((N+1:ℕ):ℝ)^3)< P.clusterRankGain := by
    unfold clusterPureCoefficient
    nlinarith
  have hdv := (lt_div_iff₀ hden).mpr hprod
  have he : P.clusterPositiveCoefficient N/2=P.clusterRankGain/(64*((N+1:ℕ):ℝ)^3) := by
    unfold clusterPositiveCoefficient
    ring
  rw [he]
  exact hdv

end Finish01.Primitives
end FCAppendix.Affine.Hybrid
