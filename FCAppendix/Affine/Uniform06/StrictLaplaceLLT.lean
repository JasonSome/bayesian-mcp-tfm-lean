import FCAppendix.Affine.Uniform06.ArrayRecount
import FCAppendix.Affine.Uniform06.OriginalDeficitMoments

noncomputable section
namespace FCAppendix.Affine.Uniform06.StrictLaplaceLLT

open MeasureTheory Set Filter
open scoped Topology BigOperators
open MixedIntervalLLT MixedCellSmoothing MixedProductCharacteristic
open WeightedIntervalLLT ExactUntilting IntervalRecovery DeficitOrientation
open FiniteMarkedExchangeability

def strictTest (r : ℕ) (θ w : ℝ) : ℝ :=
  if 0 < w then Real.exp (-θ*w)*w^r else 0

lemma measurable_strictTest (r : ℕ) (θ : ℝ) : Measurable (strictTest r θ) := by
  unfold strictTest
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (by fun_prop) measurable_const

lemma strictTest_zero (θ w : ℝ) :
    strictTest 0 θ w=exponentialTest 0 θ 0 w-intervalIndicator 0 0 w := by
  by_cases hp : 0 < w
  · have hi : intervalIndicator 0 0 w = 0 :=
      indicator_of_notMem (show w ∉ Icc (0 : ℝ) 0 from fun h => (not_le.mpr hp) h.2) (fun _ => (1 : ℝ))
    simp [strictTest,exponentialTest,hp,hp.le,hi]
  · by_cases hz : w=0
    · subst w
      simp [strictTest,exponentialTest,intervalIndicator]
    · have hn : w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      have hi : intervalIndicator 0 0 w = 0 :=
        indicator_of_notMem (show w ∉ Icc (0 : ℝ) 0 from fun h => (not_le.mpr hn) h.1) (fun _ => (1 : ℝ))
      simp [strictTest,exponentialTest,hp,not_le.mpr hn,hi]

lemma strictTest_positive_degree {r : ℕ} (hr : 0 < r) (θ w : ℝ) :
    strictTest r θ w=exponentialTest r θ 0 w := by
  by_cases hp : 0 < w
  · simp [strictTest,exponentialTest,hp,hp.le,mul_comm]
  · by_cases hz : w=0
    · subst w
      simp [strictTest,exponentialTest,Nat.ne_of_gt hr]
    · have hn : w < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
      simp [strictTest,exponentialTest,hp,not_le.mpr hn]

lemma integrable_zeroth_test (ν : Measure ℝ) [IsFiniteMeasure ν]
    {θ : ℝ} (hθ : 0 ≤ θ) : Integrable (exponentialTest 0 θ 0) ν := by
  apply Integrable.of_bound (measurable_exponentialTest 0 θ 0).aestronglyMeasurable 1
  exact ae_of_all _ fun w => by
    by_cases hw : 0 ≤ w
    · simp only [exponentialTest,if_pos hw,pow_zero,one_mul]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hθ hw))
    · simp [exponentialTest,hw]

lemma integrable_intervalIndicator (ν : Measure ℝ) [IsFiniteMeasure ν] (a b : ℝ) :
    Integrable (intervalIndicator a b) ν := by
  apply Integrable.of_bound
    (show Measurable (intervalIndicator a b) by
      unfold intervalIndicator
      exact Measurable.ite measurableSet_Icc measurable_const measurable_const).aestronglyMeasurable 1
  exact ae_of_all _ fun w => by
    rw [Real.norm_of_nonneg (intervalIndicator_bounds a b w).1]
    exact (intervalIndicator_bounds a b w).2

theorem integral_strict_zero (ν : Measure ℝ) [IsFiniteMeasure ν]
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ w,strictTest 0 θ w ∂ν)=
      (∫ w,exponentialTest 0 θ 0 w ∂ν)-intervalMass ν 0 0 := by
  simp_rw [strictTest_zero]
  rw [integral_sub (integrable_zeroth_test ν hθ) (integrable_intervalIndicator ν 0 0)]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

theorem strict_moments (A : CenteredArray Ω) (hgap : A.CompactGap)
    (c : ℕ → ℝ) (j y : ℕ → ℤ)
    (hc : Tendsto (fun n => A.d n*c n) atTop (𝓝 0))
    (hy : Tendsto (fun n => A.d n*((j n-y n:ℤ):ℝ)) atTop (𝓝 0))
    (θn : ℕ → ℝ) {θ lo hi : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n,lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n:ℝ)*∫ w,strictTest 0 (θn n) w ∂A.cell c j y n)
      atTop (𝓝 (density A.vX A.vY/θ)) ∧
    Tendsto (fun n => (A.N n:ℝ)*∫ w,strictTest 1 (θn n) w ∂A.cell c j y n)
      atTop (𝓝 (density A.vX A.vY/θ^2)) ∧
    Tendsto (fun n => (A.N n:ℝ)*∫ w,strictTest 2 (θn n) w ∂A.cell c j y n)
      atTop (𝓝 (density A.vX A.vY*(2/θ^3))) := by
  have h₀ := tendsto_zeroth_moment_varying_tilt A hgap c j y hc hy θn hlo hbracket hθn hθ
  have h₁ := tendsto_first_moment_varying_tilt A hgap c j y hc hy θn hlo hbracket hθn hθ
  have h₂ := tendsto_second_moment_varying_tilt A hgap c j y hc hy θn hlo hbracket hθn hθ
  have hatom := tendsto_scaled_interval A hgap c j y hc hy (le_refl (0:ℝ))
  have hatom' : Tendsto (fun n => (A.N n:ℝ)*intervalMass (A.cell c j y n) 0 0)
      atTop (𝓝 0) := by
    simpa only [intervalMass_eq_measure,sub_self,zero_mul] using hatom
  refine ⟨?_,?_,?_⟩
  · have hh := h₀.sub hatom'
    simp only [sub_zero] at hh
    have he (n : ℕ) := integral_strict_zero (A.cell c j y n)
      (hlo.le.trans (hbracket n).1)
    simpa only [he,mul_sub] using hh
  · simpa only [strictTest_positive_degree (by decide : 0 < (1:ℕ))] using h₁
  · simpa only [strictTest_positive_degree (by decide : 0 < (2:ℕ))] using h₂

lemma integral_laplace_eq_reflected_cell (A : CenteredArray Ω)
    (U : ℕ → Ω → ℝ) (hU : ∀ n,Measurable (U n)) (r cap : ℕ → ℝ)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (n q : ℕ) (θ : ℝ) (y : ℤ) :
    (∫ ω : Fin (A.N n) → Ω,laplace (U n) (A.Y n) (cap n) θ y q ω
      ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))=
      ∫ w,strictTest q θ w ∂(reflectX A).cell
        (fun n => cap n-(A.N n:ℝ)*r n) (fun _ => 0) (fun _ => y) n := by
  change _ = ∫ w, strictTest q θ w ∂productCell (A.law n) ((reflectX A).X n)
    (A.Y n) (A.N n) (cap n-(A.N n:ℝ)*r n) 0 y
  rw [← OriginalDeficitMoments.integral_reflected_deficit_cell
    A U hU r cap hcenter n 0 y (measurable_strictTest q θ)]
  rw [integral_productCell (A.law n) (show Measurable (fun ω => -U n ω) from (hU n).neg)
    (A.measurable_Y n) (A.N n) (cap n) 0 y
    (measurable_strictTest q θ)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    have hs : cap n+continuousSum (fun x => -U n x) (A.N n) ω=
        cap n-sumX (U n) ω := by
      simp only [continuousSum,sumX,Finset.sum_neg_distrib,sub_eq_add_neg]
    rw [hs]
    simp only [laplace,sumY,integerSum,strictTest,zero_add]
    split_ifs <;> simp_all

theorem deleted_laplace_moments (A : CenteredArray Ω) (hgap : A.CompactGap)
    (U : ℕ → Ω → ℝ) (hU : ∀ n,Measurable (U n)) (r cap θn : ℕ → ℝ)
    (hr : ∀ n,r n ∈ Icc (0:ℝ) 1)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=U n x-r n)
    (hmatch : ∀ᶠ n in atTop,cap n=(A.N n:ℝ)*r n)
    (k : ℕ) (y : ℤ) {θ lo hi : ℝ} (hlo : 0 < lo)
    (hbracket : ∀ n,lo ≤ θn n ∧ θn n ≤ hi)
    (hθn : Tendsto θn atTop (𝓝 θ)) (hθ : 0 < θ) :
    Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (ArrayRecount.remaining A k n) → Ω,
      laplace (U n) (A.Y n) (cap n-(k:ℝ)/2) (θn n) y 0 ω
        ∂Measure.pi (fun _ : Fin (ArrayRecount.remaining A k n) => A.law n))
      atTop (𝓝 (density A.vX A.vY/θ)) ∧
    Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (ArrayRecount.remaining A k n) → Ω,
      laplace (U n) (A.Y n) (cap n-(k:ℝ)/2) (θn n) y 1 ω
        ∂Measure.pi (fun _ : Fin (ArrayRecount.remaining A k n) => A.law n))
      atTop (𝓝 (density A.vX A.vY/θ^2)) ∧
    Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (ArrayRecount.remaining A k n) → Ω,
      laplace (U n) (A.Y n) (cap n-(k:ℝ)/2) (θn n) y 2 ω
        ∂Measure.pi (fun _ : Fin (ArrayRecount.remaining A k n) => A.law n))
      atTop (𝓝 (density A.vX A.vY*(2/θ^3))) := by
  let B := ArrayRecount.deleteFixed A k
  let R := reflectX B
  let cap' := fun n => cap n-(k:ℝ)/2
  let c := fun n => cap' n-(B.N n:ℝ)*r n
  have hc : Tendsto (fun n => R.d n*c n) atTop (𝓝 0) :=
    ArrayRecount.selected_shift_zero A k cap r hr hmatch
  have hy : Tendsto (fun n => R.d n*((0-y:ℤ):ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using R.d_zero.mul_const ((0-y:ℤ):ℝ)
  have hs := strict_moments R
    (reflectX_compactGap B (ArrayRecount.deleteFixed_gap A hgap k)) c
    (fun _ => 0) (fun _ => y) hc hy θn hlo hbracket hθn hθ
  have he (n q : ℕ) := integral_laplace_eq_reflected_cell B U hU r cap' hcenter n q (θn n) y
  have hratio := ArrayRecount.full_to_remaining A k
  have hnorm (n q : ℕ) : (A.N n:ℝ)*
      (∫ ω : Fin (B.N n) → Ω,laplace (U n) (B.Y n) (cap' n) (θn n) y q ω
        ∂Measure.pi (fun _ : Fin (B.N n) => B.law n))=
      ((A.N n:ℝ)/(B.N n:ℝ))*((B.N n:ℝ)*
        ∫ w,strictTest q (θn n) w ∂(R.cell c (fun _ => 0) (fun _ => y) n)) := by
    rw [he]
    field_simp [(B.N_pos n).ne']
    rfl
  have transport (q : ℕ) (L : ℝ)
      (ht : Tendsto (fun n => (B.N n : ℝ) *
        ∫ w, strictTest q (θn n) w ∂(R.cell c (fun _ => 0) (fun _ => y) n))
          atTop (𝓝 L)) :
      Tendsto (fun n => (A.N n : ℝ) *
        ∫ ω : Fin (B.N n) → Ω, laplace (U n) (B.Y n) (cap' n) (θn n) y q ω
          ∂Measure.pi (fun _ : Fin (B.N n) => B.law n)) atTop (𝓝 L) := by
    have h := hratio.mul ht
    change Tendsto (fun n => ((A.N n : ℝ)/(B.N n : ℝ)) * ((B.N n : ℝ) *
      ∫ w, strictTest q (θn n) w ∂(R.cell c (fun _ => 0) (fun _ => y) n)))
        atTop (𝓝 (1*L)) at h
    simpa only [←hnorm,one_mul] using h
  exact ⟨transport 0 _ hs.1,transport 1 _ hs.2.1,transport 2 _ hs.2.2⟩

end FCAppendix.Affine.Uniform06.StrictLaplaceLLT
