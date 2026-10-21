import FCAppendix.Affine.Uniform06.SourceCoarseIntegral

noncomputable section
namespace FCAppendix.Affine.Uniform06.RawArrayRareBounds

open MeasureTheory Set Filter
open scoped Topology BigOperators
open MixedIntervalLLT MixedProductCharacteristic DeficitOrientation
open WeightedIntervalLLT AllImbalanceMoments

variable {Ω : Type*} [MeasurableSpace Ω]

def moment (A : CenteredArray Ω) (U : ℕ → Ω → ℝ) (cap θ : ℕ → ℝ) (a : ℝ) (k n : ℕ) : ℝ :=
  ∫ ω : Fin (A.N n) → Ω,
    exponentialTest k (θ n) (a*(integerSum (A.Y n) (A.N n) ω).natAbs)
      (cap n-continuousSum (U n) (A.N n) ω) ∂Measure.pi (fun _ => A.law n)

def window (A : CenteredArray Ω) (U : ℕ → Ω → ℝ) (cap : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin (A.N n) => A.law n)).real
    {ω | cap n-continuousSum (U n) (A.N n) ω ∈ Icc (1:ℝ) 2 ∧
      integerSum (A.Y n) (A.N n) ω=0}

theorem moment_eq_reflected (A : CenteredArray Ω) (U : ℕ → Ω → ℝ) (r cap θ : ℕ → ℝ)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n) (a : ℝ) (k n : ℕ) :
    moment A U cap θ a k n=
      ∫ ω : Fin (A.N n) → Ω,
        exponentialTest k (θ n) (a*(integerSum (A.Y n) (A.N n) ω).natAbs)
          (cap n-(A.N n:ℝ)*r n+continuousSum ((reflectX A).X n) (A.N n) ω)
            ∂Measure.pi (fun _ => A.law n) := by
  apply integral_congr_ae
  filter_upwards [reflected_sum_eq_deficit A U r cap (fun _ => 0) hcenter n] with ω hω
  simp only [sub_zero] at hω
  rw [hω]

theorem actual_moment_and_window_bounds (A : CenteredArray Ω) (hgap : A.CompactGap)
    (U : ℕ → Ω → ℝ) (r cap θ : ℕ → ℝ)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hshift : Tendsto (fun n => A.d n*(cap n-(A.N n:ℝ)*r n)) atTop (𝓝 0))
    {θ0 a : ℝ} (hθ : Tendsto θ atTop (𝓝 θ0)) (hθ0 : 0 < θ0) (ha : 0 < a) :
    ∃ K c : ℝ,0 < K ∧ 0 < c ∧ ∀ᶠ n in atTop,
      moment A U cap θ a 1 n ≤ K/(A.N n:ℝ) ∧
      moment A U cap θ a 2 n ≤ K/(A.N n:ℝ) ∧
      c/(A.N n:ℝ) ≤ window A U cap n := by
  let R := reflectX A
  have hRgap := reflectX_compactGap A hgap
  obtain ⟨C,hC,he⟩ := eventual_all_imbalance_moments R hRgap
  let F1 : ℝ → ℝ := fun t => 2*C*(3/t^2+2/t)/(1-Real.exp (-t*a))
  let F2 : ℝ → ℝ := fun t => 2*C*(10/t^3+4/t^2)/(1-Real.exp (-t*a))
  have hden : 1-Real.exp (-θ0*a) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))).ne'
  have hF1 : ContinuousAt F1 θ0 := by unfold F1; fun_prop (disch := first | exact hden | positivity)
  have hF2 : ContinuousAt F2 θ0 := by unfold F2; fun_prop (disch := first | exact hden | positivity)
  let K := |F1 θ0|+|F2 θ0|+1
  have hK : 0 < K := by dsimp [K]; positivity
  have h1K : F1 θ0 < K := by dsimp [K]; linarith [le_abs_self (F1 θ0),abs_nonneg (F2 θ0)]
  have h2K : F2 θ0 < K := by dsimp [K]; linarith [le_abs_self (F2 θ0),abs_nonneg (F1 θ0)]
  have hF1e : ∀ᶠ n in atTop,F1 (θ n) < K :=
    Tendsto.eventually_lt (hF1.tendsto.comp hθ) tendsto_const_nhds h1K
  have hF2e : ∀ᶠ n in atTop,F2 (θ n) < K :=
    Tendsto.eventually_lt (hF2.tendsto.comp hθ) tendsto_const_nhds h2K
  have hθe : ∀ᶠ n in atTop,0 < θ n := hθ.eventually_const_lt hθ0
  let c := density A.vX A.vY/2
  have hc : 0 < c := half_pos (density_pos A.vX_pos A.vY_pos)
  have hcell := relative_deficit_interval A hgap U r cap (fun _ => 0) (fun _ => 0) (fun _ => 0)
    hcenter (by simpa only [sub_zero] using hshift)
    (by simp)
    (by norm_num : (1:ℝ) < 2)
  have hwe : ∀ᶠ n in atTop,
      (1/2:ℝ) < window A U cap n/(density A.vX A.vY/(A.N n:ℝ)) := by
    simpa only [sub_zero,zero_add,sub_self,Int.cast_zero,mul_zero,
      show (2:ℝ)-1=1 by norm_num,one_mul,window] using
      hcell.eventually_const_lt (by norm_num : (1/2:ℝ) < 1)
  refine ⟨K,c,hK,hc,?_⟩
  filter_upwards [he,hF1e,hF2e,hθe,hwe] with n hn h1n h2n hθn hwn
  have hm := hn (cap n-(A.N n:ℝ)*r n) (θ n) a hθn ha
  have hM1 : moment A U cap θ a 1 n ≤ F1 (θ n)/(A.N n:ℝ) := by
    calc
      _ = _ := moment_eq_reflected A U r cap θ hcenter a 1 n
      _ ≤ 2*C/(A.N n:ℝ)*(3/(θ n)^2+2/(θ n))/(1-Real.exp (-(θ n)*a)) := by
        convert! hm.1 using 1
      _ = _ := by dsimp only [F1]; ring
  have hM2 : moment A U cap θ a 2 n ≤ F2 (θ n)/(A.N n:ℝ) := by
    calc
      _ = _ := moment_eq_reflected A U r cap θ hcenter a 2 n
      _ ≤ 2*C/(A.N n:ℝ)*(10/(θ n)^3+4/(θ n)^2)/(1-Real.exp (-(θ n)*a)) := by
        convert! hm.2 using 1
      _ = _ := by dsimp only [F2]; ring
  refine ⟨hM1.trans (div_le_div_of_nonneg_right h1n.le (A.N_pos n).le),
    hM2.trans (div_le_div_of_nonneg_right h2n.le (A.N_pos n).le),?_⟩
  have hden' := div_pos (density_pos A.vX_pos A.vY_pos) (A.N_pos n)
  have hh := (lt_div_iff₀ hden').mp hwn
  have heq : (1/2:ℝ)*(density A.vX A.vY/(A.N n:ℝ))=c/(A.N n:ℝ) := by dsimp [c]; ring
  rw [heq] at hh
  exact hh.le

end FCAppendix.Affine.Uniform06.RawArrayRareBounds
