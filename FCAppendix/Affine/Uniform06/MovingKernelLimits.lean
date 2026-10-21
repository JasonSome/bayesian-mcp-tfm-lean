import FCAppendix.Affine.Uniform06.KernelLeadingTerms

noncomputable section
namespace FCAppendix.Affine.Uniform06.MovingKernelLimits

open Filter Set
open scoped Topology

theorem bounded_mul_zero {f g : ℕ → ℝ} {B : ℝ} (hB : 0≤ B)
    (hf : ∀ᶠ n in atTop,|f n|≤ B) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => f n*g n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0<ε/(B+1) := div_pos hε (by linarith)
  have hh := (Metric.tendsto_nhds.mp hg) _ hδ
  filter_upwards [hf,hh] with n hfn hgn
  rw [Real.dist_eq,sub_zero,abs_mul]
  rw [Real.dist_eq,sub_zero] at hgn
  calc
    |f n| *|g n| ≤ B*|g n| := mul_le_mul_of_nonneg_right hfn (abs_nonneg _)
    _ ≤ (B+1)*|g n| := by nlinarith [abs_nonneg (g n)]
    _ < (B+1)*(ε/(B+1)) := mul_lt_mul_of_pos_left hgn (by linarith)
    _ = ε := by field_simp [ne_of_gt (show 0< B+1 by linarith)]

theorem gamma_mul_zero {Γ g : ℕ → ℝ} {B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n => Γ n*g n) atTop (𝓝 0) := by
  apply bounded_mul_zero (B:=max 0 B) (le_max_left _ _) _ hg
  filter_upwards [hΓ] with n hn
  rw [abs_of_nonneg (by linarith [hn.1] : 0≤Γ n)]
  exact hn.2.trans (le_max_right _ _)

theorem gamma_error_div {Γ F : ℕ → ℝ} {L B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hF : Tendsto (fun n => F n-L*Γ n) atTop (𝓝 0)) :
    Tendsto (fun n => F n/Γ n) atTop (𝓝 L) := by
  have hb : ∀ᶠ n in atTop,|(Γ n)⁻¹|≤(1:ℝ) := by
    filter_upwards [hΓ] with n hn
    have hp : 0<Γ n := by linarith [hn.1]
    rw [abs_of_pos (inv_pos.mpr hp)]
    simpa only [one_div,inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hn.1
  have hz := bounded_mul_zero (by norm_num : (0:ℝ)≤1) hb hF
  have hh : Tendsto (fun n => (Γ n)⁻¹*(F n-L*Γ n)+L) atTop (𝓝 L) := by
    simpa only [zero_add] using hz.add_const L
  apply hh.congr'
  filter_upwards [hΓ] with n hn
  have hn0 : Γ n≠0 := ne_of_gt (by linarith [hn.1])
  field_simp [hn0]
  ring

theorem varying_multiplier {Γ F a : ℕ → ℝ} {L a0 B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hF : Tendsto (fun n => F n-L*Γ n) atTop (𝓝 0))
    (ha : Tendsto a atTop (𝓝 a0)) :
    Tendsto (fun n => a n*F n-(a0*L)*Γ n) atTop (𝓝 0) := by
  have h1 := ha.mul hF
  have hdelta : Tendsto (fun n => (a n-a0)*L) atTop (𝓝 0) := by
    simpa only [sub_self,zero_mul] using (ha.sub_const a0).mul_const L
  have h2 := gamma_mul_zero hΓ hdelta
  have h := h1.add h2
  convert! h using 1
  · funext n
    ring
  · simp

theorem shared_ratio {Γ F H : ℕ → ℝ} {p q B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hF : Tendsto (fun n => F n-p*Γ n) atTop (𝓝 0))
    (hH : Tendsto (fun n => H n-q*Γ n) atTop (𝓝 0)) (hq : q≠0) :
    Tendsto (fun n => F n/H n) atTop (𝓝 (p/q)) := by
  have h := (gamma_error_div hΓ hF).div (gamma_error_div hΓ hH) hq
  apply h.congr'
  filter_upwards [hΓ] with n hn
  have hn0 : Γ n≠0 := ne_of_gt (by linarith [hn.1])
  change (F n/Γ n)/(H n/Γ n)=F n/H n
  exact div_div_div_cancel_right₀ hn0 (F n) (H n)

theorem shared_positive {Γ F : ℕ → ℝ} {p B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hF : Tendsto (fun n => F n-p*Γ n) atTop (𝓝 0)) (hp : 0< p) :
    ∀ᶠ n in atTop,0< F n := by
  have hf := (gamma_error_div hΓ hF).eventually (Ioi_mem_nhds hp)
  filter_upwards [hΓ,hf] with n hn hf
  rcases div_pos_iff.mp hf with hpos | hneg
  · exact hpos.1
  · linarith [hneg.2, hn.1]

theorem shared_eventually_bounded {Γ F : ℕ → ℝ} {p B : ℝ}
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hF : Tendsto (fun n => F n-p*Γ n) atTop (𝓝 0)) :
    ∃ C>0,∀ᶠ n in atTop,|F n|≤ C := by
  let C := |p| *max 1 B+1
  have hC : 0< C := by dsimp [C]; positivity
  have herr := hF.eventually (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1))
  refine ⟨C,hC,?_⟩
  filter_upwards [hΓ,herr] with n hn he
  have hγ0 : 0≤Γ n := by linarith [hn.1]
  have hγB : |Γ n|≤ max 1 B := by rw [abs_of_nonneg hγ0]; exact hn.2.trans (le_max_right _ _)
  have he' : |F n-p*Γ n|<1 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using he
  calc
    |F n| = |(F n-p*Γ n)+p*Γ n| := by congr 1; ring
    _ ≤ |F n-p*Γ n|+|p*Γ n| := abs_add_le _ _
    _ ≤ 1+|p| *max 1 B := by rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_left hγB (abs_nonneg p)]
    _ = C := by dsimp [C]; ring

theorem four_kernel_ratios {Γ C R Cp Rp N b : ℕ → ℝ}
    {d ν θ ξ b0 B : ℝ} (hd : 0< d) (hν : 0<ν) (hθ : 0<θ)
    (hξ : 0<ξ) (hb0 : 0< b0) (hN : ∀ n,0< N n)
    (hb : Tendsto b atTop (𝓝 b0))
    (hΓ : ∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B)
    (hC : Tendsto (fun n => (N n)^2*C n-(d/(b0*ν*θ^2))*Γ n) atTop (𝓝 0))
    (hR : Tendsto (fun n => (N n)^3*R n-(2*d/(b0^2*ν^2*θ^3))*Γ n) atTop (𝓝 0))
    (hCp : Tendsto (fun n => N n*Cp n-(d/(ξ*b0*θ))*Γ n) atTop (𝓝 0))
    (hRp : Tendsto (fun n => (N n)^2*Rp n-(2*d/(ξ*b0^2*ν*θ^2))*Γ n) atTop (𝓝 0)) :
    (∀ᶠ n in atTop,0< C n) ∧
    Tendsto (fun n => (Cp n/C n)/N n) atTop (𝓝 (θ*ν/ξ)) ∧
    Tendsto (fun n => N n*(R n/C n)) atTop (𝓝 (2/(b0*ν*θ))) ∧
    Tendsto (fun n => Rp n/C n) atTop (𝓝 (2/(ξ*b0))) ∧
    Tendsto (fun n => (R n/C n)*(ξ*b n*(Cp n/C n))/2) atTop (𝓝 1) := by
  have hCcoef : 0< d/(b0*ν*θ^2) := by positivity
  have hpos := shared_positive hΓ hC hCcoef
  have hpos' : ∀ᶠ n in atTop,0< C n := by
    filter_upwards [hpos] with n hn
    by_contra hc
    have hh := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (hN n).le 2) (le_of_not_gt hc)
    linarith
  have ha := shared_ratio hΓ hCp hC hCcoef.ne'
  have hr := shared_ratio hΓ hR hC hCcoef.ne'
  have hrp := shared_ratio hΓ hRp hC hCcoef.ne'
  have hca : (d/(ξ*b0*θ))/(d/(b0*ν*θ^2))=θ*ν/ξ := by
    field_simp [hd.ne',hν.ne',hθ.ne',hξ.ne',hb0.ne']
  have hcr : (2*d/(b0^2*ν^2*θ^3))/(d/(b0*ν*θ^2))=2/(b0*ν*θ) := by
    field_simp [hd.ne',hν.ne',hθ.ne',hξ.ne',hb0.ne']
  have hcrp : (2*d/(ξ*b0^2*ν*θ^2))/(d/(b0*ν*θ^2))=2/(ξ*b0) := by
    field_simp [hd.ne',hν.ne',hθ.ne',hξ.ne',hb0.ne']
  have ha' : Tendsto (fun n => (Cp n/C n)/N n) atTop (𝓝 (θ*ν/ξ)) := by
    rw [hca] at ha
    apply ha.congr'
    filter_upwards [hpos'] with n hn
    field_simp [(hN n).ne',hn.ne']
  have hr' : Tendsto (fun n => N n*(R n/C n)) atTop (𝓝 (2/(b0*ν*θ))) := by
    rw [hcr] at hr
    apply hr.congr'
    filter_upwards [hpos'] with n hn
    field_simp [(hN n).ne',hn.ne']
  have hrp' : Tendsto (fun n => Rp n/C n) atTop (𝓝 (2/(ξ*b0))) := by
    rw [hcrp] at hrp
    apply hrp.congr'
    filter_upwards [hpos'] with n hn
    field_simp [(hN n).ne',hn.ne']
  refine ⟨hpos',ha',hr',hrp',?_⟩
  have h := ((hr'.mul ((hb.const_mul ξ).mul ha')).div_const 2)
  convert! h using 1
  · funext n
    by_cases hc : C n=0
    · simp only [hc,div_zero,mul_zero,zero_div]
    · field_simp [(hN n).ne',hc]
  · field_simp [hν.ne',hθ.ne',hξ.ne',hb0.ne']

end FCAppendix.Affine.Uniform06.MovingKernelLimits
