import FCAppendix.PayOnce.ResponseFactor
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace FCAppendix.PayOnce.DerivativeRootMoment
open MeasureTheory Set Real ResponseFactor RareSuccessSlope
open scoped ENNReal

noncomputable def rootedSlope (n : ℕ) (p w : ℝ) : ℝ :=
  if 0 < p then rootFactor n p*(1-w)^(1/((n:ℝ)-1)) else 0

theorem rootedSlope_nonneg {n : ℕ} (hn : 2 ≤ n) {p w : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ≤ 1) : 0 ≤ rootedSlope n p w := by
  unfold rootedSlope
  split_ifs
  · exact mul_nonneg (rootFactor_nonneg hn hp) (rpow_nonneg (by linarith) _)
  · rfl

theorem rootedSlope_le {n : ℕ} (hn : 2 ≤ n) {p w : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) :
    rootedSlope n p w ≤ ((n:ℝ)^2)^(1/((n:ℝ)-1)) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold rootedSlope
  split_ifs
  · exact (mul_le_of_le_one_right (rootFactor_nonneg hn hp)
      (rpow_le_one (by linarith [hw.2]) (by linarith [hw.1])
        (by exact (one_div_pos.mpr (by linarith)).le))).trans (rootFactor_bounds hn hp).2
  · positivity

theorem rootedSlope_pow {n : ℕ} (hn : 2 ≤ n) {p w : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ≤ 1) :
    rootedSlope n p w^(n-1) = weightedSlope n p w := by
  have hcast : ((n-1:ℕ):ℝ) = (n:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hexp : 1/((n:ℝ)-1) = (((n-1:ℕ):ℝ))⁻¹ := by rw [hcast,one_div]
  by_cases hp0 : 0 < p
  · by_cases hp1 : p < 1
    · rw [rootedSlope,if_pos hp0,mul_pow,rootFactor_pow hn hp,hexp,
        rpow_inv_natCast_pow (by linarith : 0 ≤ 1-w) (by omega),weightedSlope,if_pos ⟨hp0,hp1⟩]
    · have he : p = 1 := by linarith [hp.2]
      subst p
      simp [rootedSlope,rootFactor,weightedSlope,show n-1 ≠ 0 by omega]
  · simp [rootedSlope,weightedSlope,hp0,show n-1 ≠ 0 by omega]

theorem measurable_rootedSlope (n : ℕ) : Measurable (fun z : ℝ × ℝ => rootedSlope n z.1 z.2) := by
  unfold rootedSlope
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (((measurable_rootFactor n).comp measurable_fst).mul
      ((measurable_const.sub measurable_snd).pow_const _)) measurable_const

theorem exists_weight_root_lipschitz (γ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ K : ℝ, 0 < K ∧ ∀ w ∈ Icc (0:ℝ) (1-κ), |(1-w)^γ-1| ≤ K*w := by
  have hs : ContDiffOn ℝ 1 (fun x : ℝ => x^γ) (Icc κ 1) :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => (hκ.trans_le hx.1).ne')
  obtain ⟨K,hK⟩ := hs.exists_lipschitzOnWith (by norm_num) (convex_Icc κ 1) isCompact_Icc
  refine ⟨(K:ℝ)+1,by positivity,?_⟩
  intro w hw
  have hκ1 : κ ≤ 1 := by linarith [hw.1,hw.2]
  have hh := hK.dist_le_mul (1-w) ⟨by linarith [hw.2],by linarith [hw.1]⟩ 1 ⟨hκ1,le_rfl⟩
  simp only [Real.dist_eq,one_rpow,sub_sub_cancel_left,abs_neg,abs_of_nonneg hw.1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : (K:ℝ) ≤ K+1) hw.1)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem memLp_rootedSlope (μ : Measure Ω) [IsFiniteMeasure μ] {n : ℕ} (hn : 2 ≤ n)
    {p w : Ω → ℝ} (hp : Measurable p) (hw : Measurable w)
    (hp01 : ∀ z, p z ∈ Icc (0:ℝ) 1) (hw01 : ∀ z, w z ∈ Icc (0:ℝ) 1)
    (q : ENNReal) : MemLp (fun z => rootedSlope n (p z) (w z)) q μ := by
  apply MemLp.of_bound ((measurable_rootedSlope n).comp (hp.prodMk hw)).aestronglyMeasurable
    (((n:ℝ)^2)^(1/((n:ℝ)-1)))
  exact .of_forall fun z => by
    change ‖rootedSlope n (p z) (w z)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (rootedSlope_nonneg hn (hp01 z) (hw01 z).2)]
    exact rootedSlope_le hn (hp01 z) (hw01 z)

private theorem lpNorm_nat_eq (μ : Measure Ω) {a : ℕ} (ha : 0 < a)
    {f : Ω → ℝ} (hf : Measurable f) :
    lpNorm f (a:ENNReal) μ = (∫ z, |f z|^a ∂μ)^((a:ℝ)⁻¹) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast ha.ne') (by simp)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast,Real.norm_eq_abs,rpow_natCast]

private theorem lpNorm_const_mul_nonneg (μ : Measure Ω) (q : ENNReal)
    (f : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun z => c*f z) q μ = c*lpNorm f q μ := by
  simpa [Pi.smul_def,smul_eq_mul,Real.norm_eq_abs,abs_of_nonneg hc] using
    lpNorm_const_smul c f μ (p := q)

private theorem abs_lpNorm_sub_const_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    {q : ENNReal} (hq : 1 ≤ q) (hqtop : q ≠ ∞) {f : Ω → ℝ} (hf : MemLp f q μ)
    {c : ℝ} (hc : 0 ≤ c) : |lpNorm f q μ-c| ≤ lpNorm (fun z => f z-c) q μ := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hq)
  have hcLp : MemLp (fun _ : Ω => c) q μ := memLp_const c
  have h₁ := lpNorm_le_lpNorm_add_lpNorm_sub' hcLp (f := f) hq
  have h₂ := lpNorm_le_lpNorm_add_lpNorm_sub' hf (f := fun _ : Ω => c) hq
  rw [lpNorm_sub_comm] at h₂
  simp only [lpNorm_const' hq0 hqtop,Real.norm_eq_abs,abs_of_nonneg hc,
    probReal_univ,one_rpow,mul_one,Pi.sub_def] at h₁ h₂
  apply abs_sub_le_iff.mpr
  exact ⟨by linarith,by linarith⟩

theorem rootedSlope_error_le {n : ℕ} (hn : 2 ≤ n) {p p₀ w K T κ : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) (1-κ))
    (hT : 0 ≤ T) (hroot : |rootFactor n p-rootFactor n p₀| ≤ K*|p-p₀|)
    (hweight : |(1-w)^(1/((n:ℝ)-1))-1| ≤ T*w) :
    |rootedSlope n p w-rootFactor n p₀| ≤
      K*|p-p₀|+(((n:ℝ)^2)^(1/((n:ℝ)-1)))*T*w+
        (((n:ℝ)^2)^(1/((n:ℝ)-1)))*(if p = 0 then 1 else 0) := by
  let D := ((n:ℝ)^2)^(1/((n:ℝ)-1))
  have hD := (rootFactor_bounds hn hp).2
  have hf := rootFactor_nonneg hn hp
  by_cases hp0 : 0 < p
  · have hpne : p ≠ 0 := hp0.ne'
    rw [rootedSlope,if_pos hp0,if_neg hpne,mul_zero,add_zero]
    have hdiff : |rootFactor n p*(1-w)^(1/((n:ℝ)-1))-rootFactor n p| ≤ D*T*w := by
      rw [← mul_sub_one,abs_mul,abs_of_nonneg hf]
      exact ((mul_le_mul_of_nonneg_left hweight hf).trans
        (mul_le_mul_of_nonneg_right hD (mul_nonneg hT hw.1))).trans_eq (by ring)
    have hh := (abs_sub_le (rootFactor n p*(1-w)^(1/((n:ℝ)-1)))
      (rootFactor n p) (rootFactor n p₀)).trans (add_le_add hdiff hroot)
    linarith
  · have hpz : p = 0 := by linarith [hp.1]
    rw [rootedSlope,if_neg hp0,if_pos hpz,mul_one]
    have hh := abs_sub_le (0:ℝ) (rootFactor n p) (rootFactor n p₀)
    simp only [zero_sub,abs_neg,abs_of_nonneg hf] at hh ⊢
    have hnonneg : 0 ≤ D*T*w := mul_nonneg (mul_nonneg (rpow_nonneg (sq_nonneg _) _) hT) hw.1
    linarith

universe u

theorem exists_derivative_root_moment_bound {n : ℕ} (hn : 2 ≤ n)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p w : Ω → ℝ),
      Measurable p → Measurable w →
      (∀ z, p z ∈ Icc (0:ℝ) 1) → (∀ z, w z ∈ Icc (0:ℝ) (1-κ)) →
      ∀ p₀ ∈ Icc (0:ℝ) 1,
      |(∫ z, weightedSlope n (p z) (w z) ∂μ)^(1/((n:ℝ)-1))-rootFactor n p₀| ≤
        C*((∫ z, |p z-p₀|^(n-1) ∂μ)^(1/((n:ℝ)-1))+
          (∫ z, w z^(n-1) ∂μ)^(1/((n:ℝ)-1))+
          (μ.real {z | p z = 0})^(1/((n:ℝ)-1))) := by
  obtain ⟨K,hK,hroot⟩ := exists_lipschitz_rootFactor hn
  obtain ⟨T,hT,hweight⟩ := exists_weight_root_lipschitz (1/((n:ℝ)-1)) hκ
  let D := ((n:ℝ)^2)^(1/((n:ℝ)-1))
  have hD : 0 < D := rpow_pos_of_pos (sq_pos_of_pos (Nat.cast_pos.mpr (by omega))) _
  let C := K+D*T+D+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro Ω _ μ _ p w hp hw hp01 hwκ p₀ hp₀
  let a := n-1
  have ha : 0 < a := by dsimp [a]; omega
  have haE : (1:ENNReal) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have ha0 : (a:ENNReal) ≠ 0 := by exact_mod_cast ha.ne'
  have hcast : (a:ℝ) = (n:ℝ)-1 := by dsimp [a]; rw [Nat.cast_sub (by omega),Nat.cast_one]
  have hγ : 1/((n:ℝ)-1) = (a:ℝ)⁻¹ := by rw [hcast,one_div]
  have hw01 (z : Ω) : w z ∈ Icc (0:ℝ) 1 := ⟨(hwκ z).1,by linarith [(hwκ z).2]⟩
  let Y := fun z => rootedSlope n (p z) (w z)
  let e := fun z => |p z-p₀|
  let E : Set Ω := {z | p z = 0}
  let I := E.indicator (fun _ : Ω => (1:ℝ))
  have hY : Measurable Y := (measurable_rootedSlope n).comp (hp.prodMk hw)
  have hYLp : MemLp Y (a:ENNReal) μ := memLp_rootedSlope μ hn hp hw hp01 hw01 _
  have he : Measurable e := (hp.sub_const p₀).abs
  have heLp : MemLp e (a:ENNReal) μ := by
    apply MemLp.of_bound he.aestronglyMeasurable 1
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (abs_nonneg _)]
      exact abs_sub_le_iff.mpr ⟨by linarith [(hp01 z).2,hp₀.1],by linarith [(hp01 z).1,hp₀.2]⟩
  have hwLp : MemLp w (a:ENNReal) μ := memLp_of_bounded (.of_forall hw01) hw.aestronglyMeasurable _
  have hE : MeasurableSet E := measurableSet_eq_fun hp measurable_const
  have hI : Measurable I := measurable_const.indicator hE
  have hILp : MemLp I (a:ENNReal) μ := (memLp_const 1).indicator hE
  let d₁ := fun z => K*e z
  let d₂ := fun z => (D*T)*w z
  let d₃ := fun z => D*I z
  have hd₁ : MemLp d₁ (a:ENNReal) μ := heLp.const_mul K
  have hd₂ : MemLp d₂ (a:ENNReal) μ := hwLp.const_mul (D*T)
  have hd₃ : MemLp d₃ (a:ENNReal) μ := hILp.const_mul D
  have hpoint (z : Ω) : ‖Y z-rootFactor n p₀‖ ≤ (d₁+d₂+d₃) z := by
    rw [Real.norm_eq_abs]
    have hh := rootedSlope_error_le hn (hp01 z) (hwκ z) hT.le
      (hroot (p z) (hp01 z) p₀ hp₀) (hweight (w z) (hwκ z))
    by_cases hz : p z = 0 <;>
      simpa [Y,d₁,d₂,d₃,e,I,E,D,hz,mul_assoc] using hh
  have hmono := lpNorm_mono_real ((hd₁.add hd₂).add hd₃) hpoint
  have hsum := (lpNorm_add_le (hd₁.add hd₂) (g := d₃) haE).trans
    (add_le_add (lpNorm_add_le hd₁ (g := d₂) haE) le_rfl)
  have hscale : lpNorm (d₁+d₂+d₃) (a:ENNReal) μ ≤
      K*lpNorm e (a:ENNReal) μ+(D*T)*lpNorm w (a:ENNReal) μ+D*lpNorm I (a:ENNReal) μ := by
    simpa only [d₁,d₂,d₃,lpNorm_const_mul_nonneg μ (a:ENNReal) e hK.le,
      lpNorm_const_mul_nonneg μ (a:ENNReal) w (mul_pos hD hT).le,
      lpNorm_const_mul_nonneg μ (a:ENNReal) I hD.le] using hsum
  have hrev := abs_lpNorm_sub_const_le μ haE (by simp) hYLp (rootFactor_nonneg hn hp₀)
  have htotal := hrev.trans (hmono.trans hscale)
  have hcoeff : K*lpNorm e (a:ENNReal) μ+(D*T)*lpNorm w (a:ENNReal) μ+D*lpNorm I (a:ENNReal) μ ≤
      C*(lpNorm e (a:ENNReal) μ+lpNorm w (a:ENNReal) μ+lpNorm I (a:ENNReal) μ) := by
    have hKC : K ≤ C := by dsimp [C]; linarith [mul_pos hD hT]
    have hTC : D*T ≤ C := by dsimp [C]; linarith
    have hDC : D ≤ C := by dsimp [C]; linarith [mul_pos hD hT]
    have h₁ := mul_le_mul_of_nonneg_right hKC (lpNorm_nonneg (f := e) (p := (a:ENNReal)) (μ := μ))
    have h₂ := mul_le_mul_of_nonneg_right hTC (lpNorm_nonneg (f := w) (p := (a:ENNReal)) (μ := μ))
    have h₃ := mul_le_mul_of_nonneg_right hDC (lpNorm_nonneg (f := I) (p := (a:ENNReal)) (μ := μ))
    nlinarith
  have hYn : lpNorm Y (a:ENNReal) μ =
      (∫ z, weightedSlope n (p z) (w z) ∂μ)^(1/((n:ℝ)-1)) := by
    rw [lpNorm_nat_eq μ ha hY,hγ]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun z => by
      change |rootedSlope n (p z) (w z)|^a = _
      rw [abs_of_nonneg (rootedSlope_nonneg hn (hp01 z) (hw01 z).2)]
      exact rootedSlope_pow hn (hp01 z) (hw01 z).2
  have hen : lpNorm e (a:ENNReal) μ = (∫ z, |p z-p₀|^(n-1) ∂μ)^(1/((n:ℝ)-1)) := by
    rw [lpNorm_nat_eq μ ha he,hγ]
    simp only [e,abs_abs,a]
  have hwn : lpNorm w (a:ENNReal) μ = (∫ z, w z^(n-1) ∂μ)^(1/((n:ℝ)-1)) := by
    rw [lpNorm_nat_eq μ ha hw,hγ]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun z => by
      change |w z|^a = w z^a
      rw [abs_of_nonneg (hwκ z).1]
  have hIn : lpNorm I (a:ENNReal) μ = (μ.real E)^(1/((n:ℝ)-1)) := by
    rw [lpNorm_nat_eq μ ha hI,hγ]
    have hiPow : (fun z => |I z|^a) = I := by
      funext z
      by_cases hz : z ∈ E <;> simp [I,hz,ha.ne']
    rw [hiPow]
    congr 1
    change (∫ z, E.indicator (fun _ : Ω => (1:ℝ)) z ∂μ) = μ.real E
    rw [integral_indicator hE,setIntegral_const,smul_eq_mul,mul_one]
  rw [hYn] at htotal
  rw [hen,hwn,hIn] at htotal hcoeff
  exact htotal.trans hcoeff

end FCAppendix.PayOnce.DerivativeRootMoment
