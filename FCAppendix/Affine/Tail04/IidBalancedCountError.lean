import FCAppendix.Affine.Tail04.IidMarkedCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators

def iidCapacity (ρ : ℝ) (N : ℕ) : ℕ := ⌊ρ*((N:ℝ)+1)⌋₊

theorem iidCapacity_error {ρ : ℝ} (hρ : ρ∈Icc (0:ℝ) 1) (N : ℕ) (hN : 0< N) :
    |(iidCapacity ρ N:ℝ)/(N:ℝ)-ρ|≤1/(N:ℝ) := by
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hlo : (iidCapacity ρ N:ℝ)≤ ρ*((N:ℝ)+1) :=
    Nat.floor_le (mul_nonneg hρ.1 (by positivity))
  have hhi : ρ*((N:ℝ)+1)<(iidCapacity ρ N:ℝ)+1 := Nat.lt_floor_add_one _
  have he : (iidCapacity ρ N:ℝ)/(N:ℝ)-ρ=((iidCapacity ρ N:ℝ)-ρ*N)/(N:ℝ) := by
    field_simp [hn.ne']
  rw [he,abs_div,abs_of_pos hn]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by nlinarith [hρ.1],by nlinarith [hρ.2]⟩) hn.le

def countNumerator (ξ share scale : ℝ) (c A M H0 H1 : ℕ) (j : Fin 2) : ℝ :=
  let Q := clampedOwner (A-M) (share*H0) (share*H1)
  if j=0 then ((M:ℝ)-ξ*((c:ℝ)-share*H0-Q))/scale
  else ((M:ℝ)-ξ*((c:ℝ)-share*H1-(A-M-Q:ℕ)))/scale

def numeratorBudget (ξ share : ℝ) (N : ℕ) : ℝ :=
  (1+2*ξ*share)/Real.sqrt N+(1+3*ξ/2)/(N:ℝ)

section NumericIntegral
variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

theorem integrable_bounded_nat (f : Ω→ℕ) (hf : Measurable f) (K : ℕ) (hK : ∀ x,f x≤ K) :
    Integrable (fun x => (f x:ℝ)) ν := by
  apply Integrable.of_bound ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hf).aestronglyMeasurable K
  exact Eventually.of_forall (fun x => by
    change ‖(f x : ℝ)‖ ≤ (K:ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast hK x)

theorem measurable_countNumerator (ξ share scale : ℝ) (c : ℕ)
    (A M H0 H1 : Ω→ℕ) (hA : Measurable A) (hM : Measurable M)
    (hH0 : Measurable H0) (hH1 : Measurable H1) (j : Fin 2) :
    Measurable (fun x => countNumerator ξ share scale c (A x) (M x) (H0 x) (H1 x) j) :=
  (measurable_of_countable (fun z : (ℕ×ℕ)×(ℕ×ℕ) =>
    countNumerator ξ share scale c z.1.1 z.1.2 z.2.1 z.2.2 j)).comp
      ((hA.prodMk hM).prodMk (hH0.prodMk hH1))

theorem integrable_countNumerator (ξ share scale : ℝ) (c K : ℕ)
    (A M H0 H1 : Ω→ℕ) (hA : Measurable A) (hM : Measurable M)
    (hH0 : Measurable H0) (hH1 : Measurable H1)
    (hAK : ∀ x,A x≤ K) (hMK : ∀ x,M x≤ K) (h0K : ∀ x,H0 x≤ K) (h1K : ∀ x,H1 x≤ K)
    (j : Fin 2) :
    Integrable (fun x => countNumerator ξ share scale c (A x) (M x) (H0 x) (H1 x) j) ν := by
  let Q := fun x => clampedOwner (A x-M x) (share*H0 x) (share*H1 x)
  have hQ : Measurable Q := (measurable_of_countable
      (fun z : (ℕ×ℕ)×(ℕ×ℕ) => clampedOwner (z.1.1-z.1.2) (share*z.2.1) (share*z.2.2))).comp
    ((hA.prodMk hM).prodMk (hH0.prodMk hH1))
  have hQK : ∀ x,Q x≤ K := fun x => (clampedOwner_le _ _ _).trans ((Nat.sub_le _ _).trans (hAK x))
  have hQ1 : Measurable (fun x => A x-M x-Q x) :=
    (measurable_of_countable (fun z : (ℕ×ℕ)×ℕ => z.1.1-z.1.2-z.2)).comp ((hA.prodMk hM).prodMk hQ)
  have hQ1K : ∀ x,A x-M x-Q x≤ K := fun x =>
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (hAK x))
  have hiM := integrable_bounded_nat ν M hM K hMK
  have hi0 := integrable_bounded_nat ν H0 hH0 K h0K
  have hi1 := integrable_bounded_nat ν H1 hH1 K h1K
  have hiQ := integrable_bounded_nat ν Q hQ K hQK
  have hiQ1 := integrable_bounded_nat ν (fun x => A x-M x-Q x) hQ1 K hQ1K
  by_cases hj : j=0
  · simpa only [countNumerator,if_pos hj,Pi.sub_apply,Pi.mul_apply,Q] using
      (hiM.sub ((((integrable_const (c:ℝ)).sub (hi0.const_mul share)).sub hiQ).const_mul ξ)).div_const scale
  · simpa only [countNumerator,if_neg hj,Pi.sub_apply,Pi.mul_apply,Q] using
      (hiM.sub ((((integrable_const (c:ℝ)).sub (hi1.const_mul share)).sub hiQ1).const_mul ξ)).div_const scale

theorem numerator_L1_of_counts (ξ share ρ : ℝ) (hξ : 0≤ ξ) (hξ1 : ξ≤1)
    (hshare : 0≤ share) (hρ : ρ∈Icc (0:ℝ) 1) (N : ℕ) (hN : 0< N)
    (A M H0 H1 : Ω→ℕ) (hA : Measurable A) (hM : Measurable M)
    (hH0 : Measurable H0) (hH1 : Measurable H1)
    (hAK : ∀ x,A x≤ N+1) (hMK : ∀ x,M x≤ N+1)
    (h0K : ∀ x,H0 x≤ N+1) (h1K : ∀ x,H1 x≤ N+1) (hMA : ∀ x,M x≤ A x)
    (abar mbar hbar : ℝ)
    (hEA : (∫ x,|(A x:ℝ)/(N:ℝ)-abar| ∂ν)≤1/Real.sqrt N+1/(N:ℝ))
    (hEM : (∫ x,|(M x:ℝ)/(N:ℝ)-mbar| ∂ν)≤1/Real.sqrt N+1/(N:ℝ))
    (hE0 : (∫ x,|(H0 x:ℝ)/(N:ℝ)-hbar| ∂ν)≤1/Real.sqrt N)
    (hE1 : (∫ x,|(H1 x:ℝ)/(N:ℝ)-hbar| ∂ν)≤1/Real.sqrt N) (j : Fin 2) :
    (∫ x,|countNumerator ξ share N (iidCapacity ρ N) (A x) (M x) (H0 x) (H1 x) j-
      ((1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar)| ∂ν)≤ numeratorBudget ξ share N := by
  let nbar := (1-ξ/2)*mbar-ξ*ρ+(ξ/2)*abar+ξ*share*hbar
  let eM := fun x => |(M x:ℝ)/(N:ℝ)-mbar|
  let eA := fun x => |(A x:ℝ)/(N:ℝ)-abar|
  let e0 := fun x => |(H0 x:ℝ)/(N:ℝ)-hbar|
  let e1 := fun x => |(H1 x:ℝ)/(N:ℝ)-hbar|
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hiA : Integrable eA ν := (((integrable_bounded_nat ν A hA (N+1) hAK).div_const N).sub (integrable_const abar)).abs
  have hiM : Integrable eM ν := (((integrable_bounded_nat ν M hM (N+1) hMK).div_const N).sub (integrable_const mbar)).abs
  have hi0 : Integrable e0 ν := (((integrable_bounded_nat ν H0 hH0 (N+1) h0K).div_const N).sub (integrable_const hbar)).abs
  have hi1 : Integrable e1 ν := (((integrable_bounded_nat ν H1 hH1 (N+1) h1K).div_const N).sub (integrable_const hbar)).abs
  have hleft := ((integrable_countNumerator ν ξ share N (iidCapacity ρ N) (N+1)
    A M H0 H1 hA hM hH0 hH1 hAK hMK h0K h1K j).sub (integrable_const nbar)).abs
  have hpoint (x : Ω) : |countNumerator ξ share N (iidCapacity ρ N) (A x) (M x) (H0 x) (H1 x) j-nbar|≤
      (1-ξ/2)*eM x+(ξ/2)*eA x+ξ*share*(e0 x+e1 x)+3*ξ/(2*N) := by
    have hb := balanced_numerator_error (A x) (M x) (H0 x) (H1 x) (iidCapacity ρ N)
      (hMA x) hξ hξ1 hshare hn ρ abar mbar hbar
    dsimp only at hb
    have hc := mul_le_mul_of_nonneg_left (iidCapacity_error hρ N hN) hξ
    have hbound : (1-ξ/2)*|(M x:ℝ)/(N:ℝ)-mbar|+
        ξ*|(iidCapacity ρ N:ℝ)/(N:ℝ)-ρ|+(ξ/2)*|(A x:ℝ)/(N:ℝ)-abar|+
        ξ*share*(|(H0 x:ℝ)/(N:ℝ)-hbar|+|(H1 x:ℝ)/(N:ℝ)-hbar|)+ξ/(2*N)≤
        (1-ξ/2)*eM x+(ξ/2)*eA x+ξ*share*(e0 x+e1 x)+3*ξ/(2*N) := by
      calc
        _ ≤ (1-ξ/2)*|(M x:ℝ)/(N:ℝ)-mbar|+ξ*(1/(N:ℝ))+
            (ξ/2)*|(A x:ℝ)/(N:ℝ)-abar|+
            ξ*share*(|(H0 x:ℝ)/(N:ℝ)-hbar|+|(H1 x:ℝ)/(N:ℝ)-hbar|)+ξ/(2*N) := by linarith
        _ = _ := by dsimp [eM,eA,e0,e1];field_simp [hn.ne'];ring
    by_cases hj : j=0
    · unfold countNumerator
      rw [if_pos hj]
      exact hb.1.trans hbound
    · unfold countNumerator
      rw [if_neg hj]
      exact hb.2.trans hbound
  have hright := (((hiM.const_mul (1-ξ/2)).add (hiA.const_mul (ξ/2))).add
    ((hi0.add hi1).const_mul (ξ*share))).add (integrable_const (3*ξ/(2*N)))
  calc
    _ ≤ ∫ x,(1-ξ/2)*eM x+(ξ/2)*eA x+ξ*share*(e0 x+e1 x)+3*ξ/(2*N) ∂ν :=
      integral_mono_ae hleft hright (Eventually.of_forall hpoint)
    _ = (1-ξ/2)*(∫ x,eM x ∂ν)+(ξ/2)*(∫ x,eA x ∂ν)+
        ξ*share*((∫ x,e0 x ∂ν)+(∫ x,e1 x ∂ν))+3*ξ/(2*N) := by
      have hma : Integrable (fun x => (1-ξ/2)*eM x + (ξ/2)*eA x) ν :=
        (hiM.const_mul _).add (hiA.const_mul _)
      have hsum : Integrable (fun x => e0 x + e1 x) ν := hi0.add hi1
      have hmass : Integrable (fun x => ξ*share*(e0 x+e1 x)) ν := hsum.const_mul _
      have hall : Integrable (fun x => (1-ξ/2)*eM x + (ξ/2)*eA x + ξ*share*(e0 x+e1 x)) ν :=
        hma.add hmass
      rw [integral_add hall (integrable_const _), integral_add hma hmass,
        integral_add (hiM.const_mul _) (hiA.const_mul _), integral_const_mul,
        integral_const_mul, integral_const_mul, integral_add hi0 hi1]
      simp
    _ ≤ (1-ξ/2)*(1/Real.sqrt N+1/(N:ℝ))+(ξ/2)*(1/Real.sqrt N+1/(N:ℝ))+
        ξ*share*(1/Real.sqrt N+1/Real.sqrt N)+3*ξ/(2*N) := by
      apply add_le_add _ (le_refl _)
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hEM (by linarith))
        (mul_le_mul_of_nonneg_left hEA (by positivity)))
        (mul_le_mul_of_nonneg_left (add_le_add hE0 hE1) (by positivity))
    _ = _ := by
      unfold numeratorBudget
      field_simp [hn.ne',(Real.sqrt_pos.mpr hn).ne']
      ring

end NumericIntegral
end FCAppendix.Affine.Tail04.MenuError
