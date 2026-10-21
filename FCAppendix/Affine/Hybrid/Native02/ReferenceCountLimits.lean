import FCAppendix.Affine.Hybrid.Native02.ConditionalGraph

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

def activeMass (z q : ℝ) (r : Fin 3) : ℝ :=
  if r=0 then (1-z)*(1-q)^2
  else if r=1 then z+2*(1-z)*q*(1-q)
  else (1-z)*q^2

theorem activeLimitLaw_mass (z q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hq0 : 0≤ q) (hq1 : q≤1) (r : Fin 3) :
    (activeLimitLaw z q hz0 hz1 hq0 hq1).mass r=activeMass z q r := by
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [show r = 0 from Fin.ext hr, two_count_zero_mass,activeLimitLaw_success]
    norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
    ring
  · rw [show r = 1 from Fin.ext hr, two_count_one_mass,activeLimitLaw_success,activeLimitLaw_duplicates]
    norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
    ring
  · rw [show r = 2 from Fin.ext hr, ←two_count_duplicate_mass,activeLimitLaw_duplicates]
    norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]

theorem continuous_activeMass (z : ℝ) (r : Fin 3) :
    Continuous (fun q=> activeMass z q r) := by
  unfold activeMass
  split_ifs <;> fun_prop

theorem activeMass_abs_sub (z p q : ℝ) (hz0 : 0≤ z) (hz1 : z≤1)
    (hp : p∈ Icc (0:ℝ) 1) (hq : q∈ Icc (0:ℝ) 1) (r : Fin 3) :
    |activeMass z p r-activeMass z q r|≤4*|p-q| := by
  have he : |1-z|≤1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hpq : |p+q|≤2 := by rw [abs_of_nonneg (by linarith [hp.1,hq.1])]; linarith [hp.2,hq.2]
  have hsum : |2-p-q|≤2 := by rw [abs_of_nonneg (by linarith [hp.2,hq.2])]; linarith [hp.1,hq.1]
  have hmid : |1-p-q|≤1 := by rw [abs_le]; constructor <;> linarith [hp.1,hp.2,hq.1,hq.2]
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  rcases hr with hr | hr | hr
  · rw [show r = 0 from Fin.ext hr]
    have heq : activeMass z p 0-activeMass z q 0=-(1-z)*(p-q)*(2-p-q) := by
      norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
      ring
    rw [heq,abs_mul,abs_mul,abs_neg]
    have hm := mul_le_mul (mul_le_mul_of_nonneg_right he (abs_nonneg (p-q))) hsum
      (abs_nonneg (2-p-q)) (by positivity : 0≤1*|p-q|)
    nlinarith [abs_nonneg (p-q)]
  · rw [show r = 1 from Fin.ext hr]
    have heq : activeMass z p 1-activeMass z q 1=2*(1-z)*(p-q)*(1-p-q) := by
      norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
      ring
    rw [heq,abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hm := mul_le_mul (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2)) (abs_nonneg (p-q))) hmid
      (abs_nonneg (1-p-q)) (by positivity : 0≤(2*1)*|p-q|)
    nlinarith [abs_nonneg (p-q)]
  · rw [show r = 2 from Fin.ext hr]
    have heq : activeMass z p 2-activeMass z q 2=(1-z)*(p-q)*(p+q) := by
      norm_num [activeMass, show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide]
      ring
    rw [heq,abs_mul,abs_mul]
    have hm := mul_le_mul (mul_le_mul_of_nonneg_right he (abs_nonneg (p-q))) hpq
      (abs_nonneg (p+q)) (by positivity : 0≤1*|p-q|)
    nlinarith [abs_nonneg (p-q)]

theorem exposure_abs_sub_price (xi L b lam lam' : ℝ)
    (hxi : 0< xi) (hL : 0< L) (hb : L≤ b) :
    |exposure xi lam b-exposure xi lam' b|≤|lam-lam'|/(xi*L) := by
  have hb0 : 0< b := hL.trans_le hb
  have heq : exposure xi lam b-exposure xi lam' b=-(lam-lam')/(xi*b) := by
    unfold exposure
    field_simp [hxi.ne',hb0.ne']
    ring
  rw [heq,abs_div,abs_neg,abs_of_pos (mul_pos hxi hb0)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hxi hL)
    (mul_le_mul_of_nonneg_left hb hxi.le)

theorem continuousOn_reference_mass (xi lam L U z : ℝ)
    (hL : 0< L) (r : Fin 3) :
    ContinuousOn (fun b=> activeMass z (exposure xi lam b) r) (Icc L U) := by
  apply (continuous_activeMass z r).comp_continuousOn
  unfold exposure
  exact (continuousOn_const.sub (continuousOn_const.div continuousOn_id
    (fun b hb=>(hL.trans_le hb.1).ne'))).div_const xi

theorem uniform_native_count_limit_of_price {M C : ℕ→ℕ}
    {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed)
    (xi L U z lam : ℝ) (price : ℕ→ℝ)
    (hxi : 0< xi) (hL : 0< L) (hz0 : 0≤ z) (hz1 : z≤1)
    (hprice : Tendsto price atTop (𝓝 lam))
    (hq : ∀ k,∀ b∈ Icc L U,exposure xi (price k) b∈ Icc (0:ℝ) 1)
    (hqlim : ∀ b∈ Icc L U,exposure xi lam b∈ Icc (0:ℝ) 1)
    (hraw : ∀ eps>0,∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,
      a.bid∈ Icc L U→ a.routeCount=2→∀ r,
        |((problem (G k) i).outcome a).mass r-
          activeMass z (exposure xi (price k) a.bid) r|< eps) :
    ∀ eps>0,∀ᶠk in atTop,∀ i : Fin (M k),∀ a : JointAction 2,
      a.bid∈ Icc L U→ a.routeCount=2→∀ r,
        |((problem (G k) i).outcome a).mass r-
          activeMass z (exposure xi lam a.bid) r|< eps := by
  intro eps heps
  have hsmall : ∀ᶠk in atTop,|price k-lam|< eps*(xi*L)/8 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hprice
      (eps*(xi*L)/8) (by positivity)
  filter_upwards [hraw (eps/2) (by positivity),hsmall] with k hk hp
  intro i a ha hroute r
  have hr := activeMass_abs_sub z (exposure xi (price k) a.bid)
    (exposure xi lam a.bid) hz0 hz1 (hq k a.bid ha) (hqlim a.bid ha) r
  have hqdiff := exposure_abs_sub_price xi L a.bid (price k) lam hxi hL ha.1
  have hterm : 4*|price k-lam|/(xi*L)< eps/2 := by
    apply (div_lt_iff₀ (mul_pos hxi hL)).2
    nlinarith
  calc
    _≤|((problem (G k) i).outcome a).mass r-
        activeMass z (exposure xi (price k) a.bid) r|+
      |activeMass z (exposure xi (price k) a.bid) r-
        activeMass z (exposure xi lam a.bid) r| := abs_sub_le _ _ _
    _< eps := by
      have hterm' : |activeMass z (exposure xi (price k) a.bid) r-
          activeMass z (exposure xi lam a.bid) r|< eps/2 :=
        (hr.trans (mul_le_mul_of_nonneg_left hqdiff (by norm_num))).trans_lt
          (by simpa only [mul_div_assoc] using hterm)
      linarith [hk i a ha hroute r]

end FCAppendix.Affine.Hybrid.Native02
