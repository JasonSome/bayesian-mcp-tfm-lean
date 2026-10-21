import FCAppendix.Affine.Uniform06.WeightedIntervalLLT

noncomputable section
namespace FCAppendix.Affine.Uniform06.ExponentialCellBounds

open MeasureTheory Set Filter
open scoped Topology
open IntervalRecovery WeightedIntervalLLT MixedIntervalLLT MixedCellSmoothing

lemma exponentialTest_nonneg (k : ℕ) (θ s w : ℝ) :
    0 ≤ exponentialTest k θ s w := by
  unfold exponentialTest
  split_ifs with h
  · exact mul_nonneg (pow_nonneg (sub_nonneg.mpr h) _) (Real.exp_pos _).le
  · rfl

theorem tailTest_upper_from_cell_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {g G : ℝ → ℝ} {s c : ℝ} (_hc : 0 ≤ c)
    (hg : Measurable g) (hgi : IntegrableOn g (Ici s))
    (hG : IntegrableOn (fun u => G u*(u-s+1)) (Ici s))
    (hpoint : ∀ u, s ≤ u → 0 ≤ G u ∧ g u ≤ G u)
    (hcell : ∀ u, s ≤ u → intervalMass ν s u ≤ c*(u-s+1)) :
    (∫ w,tailTest g s w ∂ν) ≤ c*(∫ u in Ici s,G u*(u-s+1)) := by
  rw [integral_tailTest ν hg hgi,← integral_const_mul]
  have hi : IntegrableOn (fun u => g u*intervalMass ν s u) (Ici s) := by
    change Integrable _ (volume.restrict (Ici s))
    convert! (integrable_tail_joint ν hg hgi).integral_prod_left using 1
    funext u
    change g u*intervalMass ν s u = ∫ y, g u*intervalIndicator s u y ∂ν
    rw [integral_const_mul]
    rfl
  apply integral_mono_ae hi (hG.const_mul c)
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
  calc
    g u*intervalMass ν s u ≤ G u*intervalMass ν s u :=
      mul_le_mul_of_nonneg_right (hpoint u hu).2 (intervalMass_nonneg _ _ _)
    _ ≤ G u*(c*(u-s+1)) := mul_le_mul_of_nonneg_left (hcell u hu) (hpoint u hu).1
    _ = _ := by ring

theorem zeroth_exponential_cell_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {θ s c : ℝ} (hθ : 0 < θ) (hc : 0 ≤ c)
    (hcell : ∀ u, s ≤ u → intervalMass ν s u ≤ c*(u-s+1)) :
    (∫ w,exponentialTest 0 θ s w ∂ν) ≤
      c*Real.exp (-(θ*s))*(1/θ+1) := by
  let G := reverseZero θ
  have hG : IntegrableOn (fun u => G u*(u-s+1)) (Ici s) := by
    change Integrable _ (volume.restrict (Ici s))
    convert! ((laplace_Ici_integrable 1 hθ s).const_mul θ).add
      ((laplace_Ici_integrable 0 hθ s).const_mul θ) using 1
    funext u
    simp only [G,reverseZero,pow_one,pow_zero,one_mul,Pi.add_apply]
    ring
  have hh := tailTest_upper_from_cell_bound ν hc
    (show Measurable (reverseZero θ) by unfold reverseZero; fun_prop)
    (reverseZero_integrable hθ s) hG
    (fun u _ => ⟨by dsimp [G,reverseZero]; positivity,le_rfl⟩) hcell
  have he : (∫ u in Ici s,G u*(u-s+1)) = Real.exp (-(θ*s))*(1/θ+1) := by
    have hf : (fun u => G u*(u-s+1)) = fun u =>
        θ*((u-s)^1*Real.exp (-(θ*u)))+θ*((u-s)^0*Real.exp (-(θ*u))) := by
      funext u
      simp only [G,reverseZero,pow_one,pow_zero,one_mul]
      ring
    rw [hf,integral_add ((laplace_Ici_integrable 1 hθ s).const_mul θ)
      ((laplace_Ici_integrable 0 hθ s).const_mul θ),integral_const_mul,integral_const_mul,
      laplace_Ici 1 hθ s,laplace_Ici 0 hθ s]
    norm_num
    field_simp [hθ.ne']
  simp_rw [tailTest_reverseZero hθ s] at hh
  rw [he] at hh
  simpa only [mul_assoc] using hh

theorem first_exponential_cell_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {θ s c : ℝ} (hθ : 0 < θ) (hc : 0 ≤ c)
    (hcell : ∀ u, s ≤ u → intervalMass ν s u ≤ c*(u-s+1)) :
    (∫ w,exponentialTest 1 θ s w ∂ν) ≤
      c*Real.exp (-(θ*s))*(3/θ^2+2/θ) := by
  let G : ℝ → ℝ := fun u => (θ*(u-s)+1)*Real.exp (-(θ*u))
  have hG : IntegrableOn (fun u => G u*(u-s+1)) (Ici s) := by
    change Integrable _ (volume.restrict (Ici s))
    convert! ((laplace_Ici_integrable 2 hθ s).const_mul θ).add
      (((laplace_Ici_integrable 1 hθ s).const_mul (θ+1)).add
        (laplace_Ici_integrable 0 hθ s)) using 1
    funext u
    simp only [G,pow_one,pow_zero,one_mul,Pi.add_apply]
    ring
  have hh := tailTest_upper_from_cell_bound ν hc
    (show Measurable (reverseFirst θ s) by unfold reverseFirst; fun_prop)
    (reverseFirst_integrable hθ s) hG (fun u hu => by
      refine ⟨?_,?_⟩
      · dsimp [G]
        have hx : 0 ≤ u-s := sub_nonneg.mpr hu
        positivity
      · dsimp [reverseFirst,G]
        exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le) hcell
  have he : (∫ u in Ici s,G u*(u-s+1)) = Real.exp (-(θ*s))*(3/θ^2+2/θ) := by
    have hf : (fun u => G u*(u-s+1)) = fun u =>
        θ*((u-s)^2*Real.exp (-(θ*u)))+
        ((θ+1)*((u-s)^1*Real.exp (-(θ*u)))+(u-s)^0*Real.exp (-(θ*u))) := by
      funext u
      simp only [G,pow_one,pow_zero,one_mul]
      ring
    have h10 : Integrable (fun u => (θ+1)*((u-s)^1*Real.exp (-(θ*u)))+
        (u-s)^0*Real.exp (-(θ*u))) (volume.restrict (Ici s)) := by
      convert! ((laplace_Ici_integrable 1 hθ s).const_mul (θ+1)).add
        (laplace_Ici_integrable 0 hθ s) using 1
    rw [hf,integral_add ((laplace_Ici_integrable 2 hθ s).const_mul θ) h10,
      integral_add ((laplace_Ici_integrable 1 hθ s).const_mul (θ+1))
        (laplace_Ici_integrable 0 hθ s),integral_const_mul,integral_const_mul,
      laplace_Ici 2 hθ s,laplace_Ici 1 hθ s,laplace_Ici 0 hθ s]
    norm_num
    field_simp [hθ.ne']
    ring
  simp_rw [tailTest_reverseFirst hθ s] at hh
  rw [he] at hh
  simpa only [mul_assoc] using hh

theorem second_exponential_cell_bound (ν : Measure ℝ) [IsFiniteMeasure ν]
    {θ s c : ℝ} (hθ : 0 < θ) (hc : 0 ≤ c)
    (hcell : ∀ u, s ≤ u → intervalMass ν s u ≤ c*(u-s+1)) :
    (∫ w,exponentialTest 2 θ s w ∂ν) ≤
      c*Real.exp (-(θ*s))*(10/θ^3+4/θ^2) := by
  let G : ℝ → ℝ := fun u => (θ*(u-s)^2+2*(u-s))*Real.exp (-(θ*u))
  have hG : IntegrableOn (fun u => G u*(u-s+1)) (Ici s) := by
    change Integrable _ (volume.restrict (Ici s))
    convert! ((laplace_Ici_integrable 3 hθ s).const_mul θ).add
      (((laplace_Ici_integrable 2 hθ s).const_mul (θ+2)).add
        ((laplace_Ici_integrable 1 hθ s).const_mul 2)) using 1
    funext u
    simp only [G,pow_one,Pi.add_apply]
    ring
  have hh := tailTest_upper_from_cell_bound ν hc
    (show Measurable (reverseSecond θ s) by unfold reverseSecond; fun_prop)
    (reverseSecond_integrable hθ s) hG (fun u hu => by
      refine ⟨?_,?_⟩
      · dsimp [G]
        have hx : 0 ≤ u-s := sub_nonneg.mpr hu
        positivity
      · dsimp [reverseSecond,G]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.exp_pos _).le) hcell
  have he : (∫ u in Ici s,G u*(u-s+1)) = Real.exp (-(θ*s))*(10/θ^3+4/θ^2) := by
    have hf : (fun u => G u*(u-s+1)) = fun u =>
        θ*((u-s)^3*Real.exp (-(θ*u)))+
        ((θ+2)*((u-s)^2*Real.exp (-(θ*u)))+2*((u-s)^1*Real.exp (-(θ*u)))) := by
      funext u
      simp only [G,pow_one]
      ring
    have h21 : Integrable (fun u => (θ+2)*((u-s)^2*Real.exp (-(θ*u)))+
        2*((u-s)^1*Real.exp (-(θ*u)))) (volume.restrict (Ici s)) := by
      convert! ((laplace_Ici_integrable 2 hθ s).const_mul (θ+2)).add
        ((laplace_Ici_integrable 1 hθ s).const_mul 2) using 1
    rw [hf,integral_add ((laplace_Ici_integrable 3 hθ s).const_mul θ) h21,
      integral_add ((laplace_Ici_integrable 2 hθ s).const_mul (θ+2))
        ((laplace_Ici_integrable 1 hθ s).const_mul 2),
      integral_const_mul,integral_const_mul,integral_const_mul,
      laplace_Ici 3 hθ s,laplace_Ici 2 hθ s,laplace_Ici 1 hθ s]
    norm_num
    field_simp [hθ.ne']
    ring
  simp_rw [tailTest_reverseSecond hθ s] at hh
  rw [he] at hh
  simpa only [mul_assoc] using hh

variable {Ω : Type*} [MeasurableSpace Ω]

theorem eventual_all_cells_exponential_bounds (A : CenteredArray Ω) (hgap : A.CompactGap) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ c : ℝ, ∀ j y : ℤ,
      ∀ θ s : ℝ, 0 < θ →
      (∫ w,exponentialTest 0 θ s w
        ∂productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) ≤
          C/(A.N n : ℝ)*Real.exp (-(θ*s))*(1/θ+1) ∧
      (∫ w,exponentialTest 1 θ s w
        ∂productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) ≤
          C/(A.N n : ℝ)*Real.exp (-(θ*s))*(3/θ^2+2/θ) ∧
      (∫ w,exponentialTest 2 θ s w
        ∂productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) ≤
          C/(A.N n : ℝ)*Real.exp (-(θ*s))*(10/θ^3+4/θ^2) := by
  obtain ⟨C,δ,hC,hδ,hbound⟩ := exists_interval_concentration A hgap
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound (2*δ) (by positivity)] with n hn
  intro c j y θ s hθ
  have hc : 0 ≤ C/(A.N n : ℝ) := div_nonneg hC.le (A.N_pos n).le
  have hcell : ∀ u, s ≤ u → intervalMass
      (productCell (A.law n) (A.X n) (A.Y n) (A.N n) c j y) s u ≤
        C/(A.N n : ℝ)*(u-s+1) := by
    intro u hu
    simpa only [div_self (show 2*δ ≠ 0 by positivity)] using hn c j y s u hu
  exact ⟨zeroth_exponential_cell_bound _ hθ hc hcell,
    first_exponential_cell_bound _ hθ hc hcell,
    second_exponential_cell_bound _ hθ hc hcell⟩

end FCAppendix.Affine.Uniform06.ExponentialCellBounds
