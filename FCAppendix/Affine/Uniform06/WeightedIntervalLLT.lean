import FCAppendix.Affine.Uniform06.MixedIntervalLLT
import FCAppendix.Affine.Uniform06.ExponentialMoments

noncomputable section

namespace FCAppendix.Affine.Uniform06.WeightedIntervalLLT

open MeasureTheory Filter Set
open scoped Topology
open IntervalRecovery MixedIntervalLLT MixedCellSmoothing ExponentialMoments

def tailTest (g : ℝ → ℝ) (s w : ℝ) : ℝ :=
  ∫ u in Ici s, g u * intervalIndicator s u w

lemma measurable_tail_joint {g : ℝ → ℝ} (hg : Measurable g) (s : ℝ) :
    Measurable (fun z : ℝ × ℝ => g z.1 * intervalIndicator s z.1 z.2) := by
  have hset : MeasurableSet {z : ℝ × ℝ | s ≤ z.2 ∧ z.2 ≤ z.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  exact (hg.comp measurable_fst).mul
    (Measurable.ite hset measurable_const measurable_const)

lemma integrable_tail_joint (ν : Measure ℝ) [IsFiniteMeasure ν]
    {g : ℝ → ℝ} (hg : Measurable g) {s : ℝ} (hgi : IntegrableOn g (Ici s)) :
    Integrable (fun z : ℝ × ℝ => g z.1 * intervalIndicator s z.1 z.2)
      ((volume.restrict (Ici s)).prod ν) := by
  apply (hgi.norm.comp_fst ν).mono' (measurable_tail_joint hg s).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [norm_mul]
    apply mul_le_of_le_one_right (norm_nonneg _)
    rw [Real.norm_of_nonneg (intervalIndicator_bounds _ _ _).1]
    exact (intervalIndicator_bounds _ _ _).2

lemma tailTest_eq {g : ℝ → ℝ} (s w : ℝ) :
    tailTest g s w = if s ≤ w then ∫ u in Ici w, g u else 0 := by
  by_cases hw : s ≤ w
  · rw [if_pos hw]
    have heq : (fun u => g u * intervalIndicator s u w) = (Ici w).indicator g := by
      funext u
      by_cases hu : w ≤ u <;> simp [intervalIndicator, hw, hu]
    rw [tailTest, heq, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hs : Ici w ∩ Ici s = Ici w := inter_eq_left.mpr (Ici_subset_Ici.mpr hw)
    rw [hs]
  · rw [if_neg hw, tailTest]
    simp [intervalIndicator, hw]

theorem integral_tailTest (ν : Measure ℝ) [IsFiniteMeasure ν]
    {g : ℝ → ℝ} (hg : Measurable g) {s : ℝ} (hgi : IntegrableOn g (Ici s)) :
    (∫ w, tailTest g s w ∂ν) =
      ∫ u in Ici s, g u * intervalMass ν s u := by
  have hi : Integrable (Function.uncurry (fun u w => g u*intervalIndicator s u w))
      ((volume.restrict (Ici s)).prod ν) := by
    convert! integrable_tail_joint ν hg hgi using 1
  have hF := integral_integral_swap hi
  dsimp [tailTest]
  rw [← hF]
  simp only [intervalMass, integral_const_mul]

lemma measurable_intervalMass_right (ν : Measure ℝ) [IsFiniteMeasure ν] (s : ℝ) :
    Measurable (fun u => intervalMass ν s u) := by
  have hset : MeasurableSet {z : ℝ × ℝ | s ≤ z.2 ∧ z.2 ≤ z.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hm : Measurable (fun z : ℝ × ℝ => intervalIndicator s z.1 z.2) :=
    Measurable.ite hset measurable_const measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

variable {Ω : Type*} [MeasurableSpace Ω]

theorem tendsto_scaled_tailTest (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {g : ℝ → ℝ} (hg : Measurable g) {s : ℝ}
    (hgi : IntegrableOn g (Ici s))
    (hweighted : IntegrableOn (fun u => g u * (u - s + 1)) (Ici s)) :
    Tendsto (fun n => (A.N n : ℝ) * ∫ w, tailTest g s w ∂A.cell c j y n)
      atTop (𝓝 (density A.vX A.vY * ∫ u in Ici s, g u * (u - s))) := by
  obtain ⟨C, δ, hC, hδ, hconcentration⟩ := exists_interval_concentration A hgap
  have hbound := hconcentration (2 * δ) (by positivity)
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ici s))
    (bound := fun u : ℝ => C * ‖g u * (u - s + 1)‖)
    (F := fun n u => g u * ((A.N n : ℝ) * intervalMass (A.cell c j y n) s u))
    (f := fun u => g u * ((u - s) * density A.vX A.vY))
    (Eventually.of_forall fun n =>
      (hg.mul (measurable_const.mul
        (measurable_intervalMass_right (A.cell c j y n) s))).aestronglyMeasurable)
    (by
      filter_upwards [hbound] with n hn
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
      have hcell := hn (c n) (j n) (y n) s u hu
      have hw : 2 * δ / (2 * δ) = 1 := div_self (by positivity)
      rw [hw] at hcell
      have hscaled : (A.N n : ℝ) * intervalMass (A.cell c j y n) s u ≤
          C * (u - s + 1) := by
        have h := mul_le_mul_of_nonneg_left hcell (A.N_pos n).le
        change (A.N n : ℝ)*intervalMass (A.cell c j y n) s u ≤
          (A.N n : ℝ)*(C/(A.N n : ℝ)*(u-s+1)) at h
        have hcancel : (A.N n : ℝ)*(C/(A.N n : ℝ)*(u-s+1))=C*(u-s+1) := by
          field_simp [(A.N_pos n).ne']
        exact h.trans_eq hcancel
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (A.N_pos n).le
        (intervalMass_nonneg _ _ _)), norm_mul,
        Real.norm_of_nonneg (by linarith [show s ≤ u from hu] : 0 ≤ u - s + 1)]
      calc
        ‖g u‖ * ((A.N n : ℝ) * intervalMass (A.cell c j y n) s u) ≤
            ‖g u‖ * (C * (u - s + 1)) :=
          mul_le_mul_of_nonneg_left hscaled (norm_nonneg _)
        _ = _ := by ring)
    (hweighted.norm.const_mul C)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
      have h := (tendsto_scaled_interval A hgap c j y hc he hu).const_mul (g u)
      simpa only [intervalMass_eq_measure] using h)
  have hfun (n : ℕ) :
      (A.N n : ℝ) * (∫ w, tailTest g s w ∂A.cell c j y n) =
        ∫ u in Ici s, g u * ((A.N n : ℝ) * intervalMass (A.cell c j y n) s u) := by
    rw [integral_tailTest _ hg hgi, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by ring
  have hlimit : (∫ u in Ici s, g u * ((u - s) * density A.vX A.vY)) =
      density A.vX A.vY * ∫ u in Ici s, g u * (u - s) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by ring
  rw [hlimit] at hD
  simpa only [hfun] using hD

theorem tendsto_scaled_tailTest_varying (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    (g : ℕ → ℝ → ℝ) (g₀ H : ℝ → ℝ) (s : ℝ)
    (hg : ∀ n, Measurable (g n)) (hgi : ∀ n, IntegrableOn (g n) (Ici s))
    (hpoint : ∀ u ∈ Ici s, Tendsto (fun n => g n u) atTop (𝓝 (g₀ u)))
    (hH : IntegrableOn H (Ici s))
    (hdom : ∀ n u, s ≤ u → ‖g n u‖ * (u - s + 1) ≤ H u) :
    Tendsto (fun n => (A.N n : ℝ) * ∫ w, tailTest (g n) s w ∂A.cell c j y n)
      atTop (𝓝 (density A.vX A.vY * ∫ u in Ici s, g₀ u * (u - s))) := by
  obtain ⟨C, δ, hC, hδ, hconcentration⟩ := exists_interval_concentration A hgap
  have hD := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ici s)) (bound := fun u : ℝ => C * H u)
    (F := fun n u => g n u * ((A.N n : ℝ) * intervalMass (A.cell c j y n) s u))
    (f := fun u => g₀ u * ((u - s) * density A.vX A.vY))
    (Eventually.of_forall fun n => ((hg n).mul (measurable_const.mul
      (measurable_intervalMass_right (A.cell c j y n) s))).aestronglyMeasurable)
    (by
      filter_upwards [hconcentration (2 * δ) (by positivity)] with n hn
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
      have hcell := hn (c n) (j n) (y n) s u hu
      rw [div_self (show 2 * δ ≠ 0 by positivity)] at hcell
      have hscaled : (A.N n : ℝ) * intervalMass (A.cell c j y n) s u ≤
          C * (u - s + 1) := by
        have h := mul_le_mul_of_nonneg_left hcell (A.N_pos n).le
        change (A.N n : ℝ)*intervalMass (A.cell c j y n) s u ≤
          (A.N n : ℝ)*(C/(A.N n : ℝ)*(u-s+1)) at h
        have hcancel : (A.N n : ℝ)*(C/(A.N n : ℝ)*(u-s+1))=C*(u-s+1) := by
          field_simp [(A.N_pos n).ne']
        exact h.trans_eq hcancel
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (A.N_pos n).le
        (intervalMass_nonneg _ _ _))]
      calc
        _ ≤ ‖g n u‖ * (C * (u - s + 1)) :=
          mul_le_mul_of_nonneg_left hscaled (norm_nonneg _)
        _ = C * (‖g n u‖ * (u - s + 1)) := by ring
        _ ≤ C * H u := mul_le_mul_of_nonneg_left (hdom n u hu) hC.le)
    (hH.const_mul C)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
      simpa only [intervalMass_eq_measure] using
        (hpoint u hu).mul (tendsto_scaled_interval A hgap c j y hc he hu))
  have hfun (n : ℕ) :
      (A.N n : ℝ) * (∫ w, tailTest (g n) s w ∂A.cell c j y n) =
        ∫ u in Ici s, g n u * ((A.N n : ℝ) * intervalMass (A.cell c j y n) s u) := by
    rw [integral_tailTest _ (hg n) (hgi n), ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by ring
  have hlimit : (∫ u in Ici s, g₀ u * ((u - s) * density A.vX A.vY)) =
      density A.vX A.vY * ∫ u in Ici s, g₀ u * (u - s) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by ring
  rw [hlimit] at hD
  simpa only [hfun] using hD

def exponentialTest (k : ℕ) (θ s w : ℝ) : ℝ :=
  if s ≤ w then (w - s) ^ k * Real.exp (-(θ * w)) else 0

def reverseFirst (θ s u : ℝ) : ℝ :=
  (θ * (u - s) - 1) * Real.exp (-(θ * u))

def reverseSecond (θ s u : ℝ) : ℝ :=
  (θ * (u - s) ^ 2 - 2 * (u - s)) * Real.exp (-(θ * u))

def reverseZero (θ u : ℝ) : ℝ := θ * Real.exp (-(θ * u))

lemma laplace_Ici (k : ℕ) {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    (∫ u in Ici s, (u - s) ^ k * Real.exp (-(θ * u))) =
      Real.exp (-(θ * s)) * (k.factorial : ℝ) / θ ^ (k + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  exact shifted_laplace_moment k hθ s

lemma laplace_Ici_integrable (k : ℕ) {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (fun u => (u - s) ^ k * Real.exp (-(θ * u))) (Ici s) := by
  apply Integrable.of_integral_ne_zero
  rw [laplace_Ici k hθ s]
  exact (div_pos (mul_pos (Real.exp_pos _) (by exact_mod_cast Nat.factorial_pos k))
    (pow_pos hθ _)).ne'

lemma reverseZero_integrable {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (reverseZero θ) (Ici s) := by
  change Integrable (reverseZero θ) (volume.restrict (Ici s))
  convert! (laplace_Ici_integrable 0 hθ s).const_mul θ using 1
  funext u
  simp only [reverseZero,pow_zero,one_mul]

lemma tailTest_reverseZero {θ : ℝ} (hθ : 0 < θ) (s w : ℝ) :
    tailTest (reverseZero θ) s w = exponentialTest 0 θ s w := by
  rw [tailTest_eq, exponentialTest]
  split_ifs with hw
  · simp only [reverseZero, integral_const_mul, pow_zero, one_mul]
    have h0 := laplace_Ici 0 hθ w
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one,
      mul_one, Nat.zero_add, pow_one] at h0
    rw [h0]
    field_simp [hθ.ne']
  · rfl

lemma reverseZero_weighted_integral {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    (∫ u in Ici s, reverseZero θ u * (u - s)) =
      Real.exp (-(θ * s)) / θ := by
  have heq : (fun u => reverseZero θ u * (u - s)) =
      fun u => θ * ((u - s) ^ 1 * Real.exp (-(θ * u))) := by
    funext u
    simp only [reverseZero, pow_one]
    ring
  rw [heq, integral_const_mul, laplace_Ici 1 hθ s]
  norm_num
  field_simp [hθ.ne']

lemma reverseFirst_integrable {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (reverseFirst θ s) (Ici s) := by
  change Integrable (reverseFirst θ s) (volume.restrict (Ici s))
  convert! ((laplace_Ici_integrable 1 hθ s).const_mul θ).sub
    (laplace_Ici_integrable 0 hθ s) using 1
  funext u
  simp only [reverseFirst,Pi.sub_apply,pow_one]
  ring

lemma reverseFirst_weighted_integrable {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (fun u => reverseFirst θ s u * (u - s + 1)) (Ici s) := by
  change Integrable (fun u => reverseFirst θ s u*(u-s+1)) (volume.restrict (Ici s))
  convert! ((laplace_Ici_integrable 2 hθ s).const_mul θ).add
    (((laplace_Ici_integrable 1 hθ s).const_mul (θ - 1)).sub
      (laplace_Ici_integrable 0 hθ s)) using 1
  funext u
  simp only [reverseFirst,Pi.add_apply,Pi.sub_apply,pow_one]
  ring

lemma reverseSecond_integrable {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (reverseSecond θ s) (Ici s) := by
  change Integrable (reverseSecond θ s) (volume.restrict (Ici s))
  convert! ((laplace_Ici_integrable 2 hθ s).const_mul θ).sub
    ((laplace_Ici_integrable 1 hθ s).const_mul 2) using 1
  funext u
  simp only [reverseSecond,Pi.sub_apply,pow_one]
  ring

lemma reverseSecond_weighted_integrable {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    IntegrableOn (fun u => reverseSecond θ s u * (u - s + 1)) (Ici s) := by
  change Integrable (fun u => reverseSecond θ s u*(u-s+1)) (volume.restrict (Ici s))
  convert! ((laplace_Ici_integrable 3 hθ s).const_mul θ).add
    (((laplace_Ici_integrable 2 hθ s).const_mul (θ - 2)).sub
      ((laplace_Ici_integrable 1 hθ s).const_mul 2)) using 1
  funext u
  simp only [reverseSecond,Pi.add_apply,Pi.sub_apply,pow_one]
  ring

lemma tailTest_reverseFirst {θ : ℝ} (hθ : 0 < θ) (s w : ℝ) :
    tailTest (reverseFirst θ s) s w = exponentialTest 1 θ s w := by
  rw [tailTest_eq, exponentialTest]
  split_ifs with hw
  · have heq : reverseFirst θ s = fun u =>
        θ * ((u - w) ^ 1 * Real.exp (-(θ * u))) +
          (θ * (w - s) - 1) * ((u - w) ^ 0 * Real.exp (-(θ * u))) := by
      funext u
      simp only [reverseFirst,pow_one,pow_zero,one_mul]
      ring
    rw [heq, integral_add ((laplace_Ici_integrable 1 hθ w).const_mul θ)
      ((laplace_Ici_integrable 0 hθ w).const_mul _),
      integral_const_mul, integral_const_mul, laplace_Ici 1 hθ w, laplace_Ici 0 hθ w]
    norm_num
    field_simp [hθ.ne']
    ring
  · rfl

lemma tailTest_reverseSecond {θ : ℝ} (hθ : 0 < θ) (s w : ℝ) :
    tailTest (reverseSecond θ s) s w = exponentialTest 2 θ s w := by
  rw [tailTest_eq, exponentialTest]
  split_ifs with hw
  · have heq : reverseSecond θ s = fun u =>
        θ * ((u - w) ^ 2 * Real.exp (-(θ * u))) +
          (2 * θ * (w - s) - 2) * ((u - w) ^ 1 * Real.exp (-(θ * u))) +
          (θ * (w - s) ^ 2 - 2 * (w - s)) *
            ((u - w) ^ 0 * Real.exp (-(θ * u))) := by
      funext u
      simp only [reverseSecond, pow_one, pow_zero, one_mul]
      ring
    rw [heq]
    have h21 : IntegrableOn (fun u =>
        θ * ((u-w)^2 * Real.exp (-(θ*u))) +
        (2*θ*(w-s)-2) * ((u-w)^1 * Real.exp (-(θ*u)))) (Ici w) := by
      change Integrable _ (volume.restrict (Ici w))
      convert! ((laplace_Ici_integrable 2 hθ w).const_mul θ).add
          ((laplace_Ici_integrable 1 hθ w).const_mul (2*θ*(w-s)-2)) using 1
    rw [integral_add h21
      ((laplace_Ici_integrable 0 hθ w).const_mul _),
      integral_add ((laplace_Ici_integrable 2 hθ w).const_mul θ)
        ((laplace_Ici_integrable 1 hθ w).const_mul _)]
    simp only [integral_const_mul, laplace_Ici _ hθ w]
    norm_num
    field_simp [hθ.ne']
    ring
  · rfl

lemma reverseFirst_weighted_integral {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    (∫ u in Ici s, reverseFirst θ s u * (u - s)) =
      Real.exp (-(θ * s)) / θ ^ 2 := by
  have heq : (fun u => reverseFirst θ s u * (u - s)) = fun u =>
      θ * ((u - s) ^ 2 * Real.exp (-(θ * u))) -
        ((u - s) ^ 1 * Real.exp (-(θ * u))) := by
    funext u
    simp only [reverseFirst, pow_one]
    ring
  rw [heq, integral_sub ((laplace_Ici_integrable 2 hθ s).const_mul θ)
    (laplace_Ici_integrable 1 hθ s), integral_const_mul,
    laplace_Ici 2 hθ s, laplace_Ici 1 hθ s]
  norm_num
  field_simp [hθ.ne']
  norm_num

lemma reverseSecond_weighted_integral {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    (∫ u in Ici s, reverseSecond θ s u * (u - s)) =
      2 * Real.exp (-(θ * s)) / θ ^ 3 := by
  have heq : (fun u => reverseSecond θ s u * (u - s)) = fun u =>
      θ * ((u - s) ^ 3 * Real.exp (-(θ * u))) -
        2 * ((u - s) ^ 2 * Real.exp (-(θ * u))) := by
    funext u
    simp only [reverseSecond]
    ring
  rw [heq, integral_sub ((laplace_Ici_integrable 3 hθ s).const_mul θ)
    ((laplace_Ici_integrable 2 hθ s).const_mul 2),
    integral_const_mul, integral_const_mul, laplace_Ici 3 hθ s, laplace_Ici 2 hθ s]
  norm_num
  field_simp [hθ.ne']
  norm_num

theorem tendsto_first_exponential_moment (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    Tendsto (fun n => (A.N n : ℝ) *
      ∫ w, exponentialTest 1 θ s w ∂A.cell c j y n) atTop
        (𝓝 (density A.vX A.vY * Real.exp (-(θ * s)) / θ ^ 2)) := by
  have h := tendsto_scaled_tailTest A hgap c j y hc he
    (g := reverseFirst θ s) (by unfold reverseFirst; fun_prop)
    (reverseFirst_integrable hθ s) (reverseFirst_weighted_integrable hθ s)
  simp_rw [tailTest_reverseFirst hθ, reverseFirst_weighted_integral hθ s] at h
  simpa only [mul_div_assoc] using h

theorem tendsto_second_exponential_moment (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) (s : ℝ) :
    Tendsto (fun n => (A.N n : ℝ) *
      ∫ w, exponentialTest 2 θ s w ∂A.cell c j y n) atTop
        (𝓝 (density A.vX A.vY * (2 * Real.exp (-(θ * s)) / θ ^ 3))) := by
  have h := tendsto_scaled_tailTest A hgap c j y hc he
    (g := reverseSecond θ s) (by unfold reverseSecond; fun_prop)
    (reverseSecond_integrable hθ s) (reverseSecond_weighted_integrable hθ s)
  simpa only [tailTest_reverseSecond hθ, reverseSecond_weighted_integral hθ s] using h

lemma reverseFirst_domination {lo hi θ u : ℝ} (hlo : 0 < lo)
    (hθlo : lo ≤ θ) (hθhi : θ ≤ hi) (hu : 0 ≤ u) :
    ‖reverseFirst θ 0 u‖ * (u - 0 + 1) ≤
      (hi * u + 1) * (u + 1) * Real.exp (-(lo * u)) := by
  have hθ0 : 0 ≤ θ := hlo.le.trans hθlo
  have hhi0 : 0 ≤ hi := hθ0.trans hθhi
  have habs : |θ * u - 1| ≤ hi * u + 1 := by
    calc
      |θ * u - 1| ≤ |θ * u| + |(1 : ℝ)| := abs_sub _ _
      _ = θ * u + 1 := by rw [abs_of_nonneg (mul_nonneg hθ0 hu)]; norm_num
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hθhi hu]
  have hexp : Real.exp (-(θ * u)) ≤ Real.exp (-(lo * u)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [reverseFirst, sub_zero, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((hi * u + 1) * Real.exp (-(lo * u))) * (u + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul habs hexp (Real.exp_pos _).le (by positivity)) (by positivity)
    _ = _ := by ring

lemma reverseSecond_domination {lo hi θ u : ℝ} (hlo : 0 < lo)
    (hθlo : lo ≤ θ) (hθhi : θ ≤ hi) (hu : 0 ≤ u) :
    ‖reverseSecond θ 0 u‖ * (u - 0 + 1) ≤
      (hi * u ^ 2 + 2 * u) * (u + 1) * Real.exp (-(lo * u)) := by
  have hθ0 : 0 ≤ θ := hlo.le.trans hθlo
  have hhi0 : 0 ≤ hi := hθ0.trans hθhi
  have habs : |θ * u ^ 2 - 2 * u| ≤ hi * u ^ 2 + 2 * u := by
    calc
      _ ≤ |θ * u ^ 2| + |2 * u| := abs_sub _ _
      _ = θ * u ^ 2 + 2 * u := by rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_right hθhi (sq_nonneg u)]
  have hexp : Real.exp (-(θ * u)) ≤ Real.exp (-(lo * u)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [reverseSecond, sub_zero, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((hi * u ^ 2 + 2 * u) * Real.exp (-(lo * u))) * (u + 1) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul habs hexp (Real.exp_pos _).le (by positivity)) (by positivity)
    _ = _ := by ring

theorem tendsto_first_moment_varying_tilt (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    (θn : ℕ → ℝ) {θ lo hi : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n, lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n : ℝ) *
      ∫ w, exponentialTest 1 (θn n) 0 w ∂A.cell c j y n) atTop
        (𝓝 (density A.vX A.vY / θ ^ 2)) := by
  let H := fun u : ℝ => (hi * u + 1) * (u + 1) * Real.exp (-(lo * u))
  have hH : IntegrableOn H (Ici 0) := by
    change Integrable H (volume.restrict (Ici 0))
    convert! ((laplace_Ici_integrable 2 hlo 0).const_mul hi).add
      (((laplace_Ici_integrable 1 hlo 0).const_mul (hi + 1)).add
        (laplace_Ici_integrable 0 hlo 0)) using 1
    funext u
    simp only [H,Pi.add_apply,sub_zero,pow_one,pow_zero,one_mul]
    ring
  have h := tendsto_scaled_tailTest_varying A hgap c j y hc he
    (fun n => reverseFirst (θn n) 0) (reverseFirst θ 0) H 0
    (fun n => by unfold reverseFirst; fun_prop)
    (fun n => reverseFirst_integrable (hlo.trans_le (hbracket n).1) 0)
    (fun u _ => (show Continuous (fun θ : ℝ => reverseFirst θ 0 u) by
      unfold reverseFirst; fun_prop).continuousAt.tendsto.comp hθn) hH
    (fun n u hu => reverseFirst_domination hlo (hbracket n).1 (hbracket n).2 hu)
  simp_rw [tailTest_reverseFirst (hlo.trans_le (hbracket _).1),
    reverseFirst_weighted_integral hθ 0] at h
  simpa [div_eq_mul_inv] using h

theorem tendsto_second_moment_varying_tilt (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    (θn : ℕ → ℝ) {θ lo hi : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n, lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n : ℝ) *
      ∫ w, exponentialTest 2 (θn n) 0 w ∂A.cell c j y n) atTop
        (𝓝 (density A.vX A.vY * (2 / θ ^ 3))) := by
  let H := fun u : ℝ => (hi * u ^ 2 + 2 * u) * (u + 1) * Real.exp (-(lo * u))
  have hH : IntegrableOn H (Ici 0) := by
    change Integrable H (volume.restrict (Ici 0))
    convert! ((laplace_Ici_integrable 3 hlo 0).const_mul hi).add
      (((laplace_Ici_integrable 2 hlo 0).const_mul (hi + 2)).add
        ((laplace_Ici_integrable 1 hlo 0).const_mul 2)) using 1
    funext u
    simp only [H,Pi.add_apply,sub_zero,pow_one]
    ring
  have h := tendsto_scaled_tailTest_varying A hgap c j y hc he
    (fun n => reverseSecond (θn n) 0) (reverseSecond θ 0) H 0
    (fun n => by unfold reverseSecond; fun_prop)
    (fun n => reverseSecond_integrable (hlo.trans_le (hbracket n).1) 0)
    (fun u _ => (show Continuous (fun θ : ℝ => reverseSecond θ 0 u) by
      unfold reverseSecond; fun_prop).continuousAt.tendsto.comp hθn) hH
    (fun n u hu => reverseSecond_domination hlo (hbracket n).1 (hbracket n).2 hu)
  simp_rw [tailTest_reverseSecond (hlo.trans_le (hbracket _).1),
    reverseSecond_weighted_integral hθ 0] at h
  simpa only [mul_zero, neg_zero, Real.exp_zero, mul_one] using h

theorem tendsto_zeroth_moment_varying_tilt (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n * c n) atTop (𝓝 0))
    (he : Tendsto (fun n => A.d n * ((j n - y n : ℤ) : ℝ)) atTop (𝓝 0))
    (θn : ℕ → ℝ) {θ lo hi : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n, lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n : ℝ) *
      ∫ w, exponentialTest 0 (θn n) 0 w ∂A.cell c j y n) atTop
        (𝓝 (density A.vX A.vY / θ)) := by
  let H := fun u : ℝ => hi * (u + 1) * Real.exp (-(lo * u))
  have hhi0 : 0 ≤ hi := hlo.le.trans ((hbracket 0).1.trans (hbracket 0).2)
  have hH : IntegrableOn H (Ici 0) := by
    change Integrable H (volume.restrict (Ici 0))
    convert! ((laplace_Ici_integrable 1 hlo 0).add
      (laplace_Ici_integrable 0 hlo 0)).const_mul hi using 1
    funext u
    simp only [H,Pi.add_apply,sub_zero,pow_one,pow_zero,one_mul]
    ring
  have hdom (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
      ‖reverseZero (θn n) u‖ * (u - 0 + 1) ≤ H u := by
    have hθ0 : 0 ≤ θn n := hlo.le.trans (hbracket n).1
    have hexp : Real.exp (-(θn n * u)) ≤ Real.exp (-(lo * u)) :=
      Real.exp_le_exp.mpr (by nlinarith [(hbracket n).1])
    rw [reverseZero, Real.norm_of_nonneg (mul_nonneg hθ0 (Real.exp_pos _).le), sub_zero]
    calc
      _ ≤ (hi * Real.exp (-(lo * u))) * (u + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hbracket n).2 hexp (Real.exp_pos _).le hhi0) (by positivity)
      _ = H u := by dsimp [H]; ring
  have h := tendsto_scaled_tailTest_varying A hgap c j y hc he
    (fun n => reverseZero (θn n)) (reverseZero θ) H 0
    (fun n => by unfold reverseZero; fun_prop)
    (fun n => reverseZero_integrable (hlo.trans_le (hbracket n).1) 0)
    (fun u _ => (show Continuous (fun θ : ℝ => reverseZero θ u) by
      unfold reverseZero; fun_prop).continuousAt.tendsto.comp hθn) hH hdom
  have htest (n : ℕ) (w : ℝ) := tailTest_reverseZero
    (hlo.trans_le (hbracket n).1) 0 w
  simp_rw [htest, reverseZero_weighted_integral hθ 0] at h
  simpa [div_eq_mul_inv] using h

end FCAppendix.Affine.Uniform06.WeightedIntervalLLT
