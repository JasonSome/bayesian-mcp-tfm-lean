import FCAppendix.Affine.Uniform06.FullReciprocalMean
import FCAppendix.Affine.Uniform06.RareEmpiricalReplacement
import FCAppendix.Affine.Uniform06.FiniteSampledLaplace

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RareSourceReciprocal

open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open Uniform07 FullJointLaw FullReciprocalMean RawTiltedSource
open RareEmpiricalReplacement
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem empirical_const_mul (a : ℝ) (f : Ω → ℝ) (N : ℕ) (ω : Fin N → Ω) :
    empirical (fun x => a*f x) N ω=a*empirical f N ω := by
  unfold empirical
  rw [← Finset.mul_sum]
  ring

theorem bounded_mass_reference_replacement
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (f : ℕ → Ω → ℝ) (hf : ∀ n,Measurable (f n))
    {a : ℝ} (ha : 0< a)
    (hb : ∀ n,∀ᵐ ω ∂μ n,0≤ f n ω ∧ f n ω≤ a⁻¹)
    (N : ℕ → ℕ) (hNpos : ∀ n,0< N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → Ω) → ℝ) (hT : ∀ n,Measurable (T n))
    (k : ℕ) {B Q ν : ℝ} (hB : 0≤ B) (hQ : 0< Q)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0≤ T n ω ∧ T n ω≤ B*(N n:ℝ)^k)
    (hrare : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n)≤ Q)
    (hmean : Tendsto (fun n => ∫ ω,f n ω ∂μ n) atTop (𝓝 ν)) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*|empirical (f n) (N n) ω-ν|
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  have hunit (n : ℕ) : ∀ᵐ ω ∂μ n,a*f n ω ∈ Icc (0:ℝ) 1 := by
    filter_upwards [hb n] with ω hω
    refine ⟨mul_nonneg ha.le hω.1,?_⟩
    have hh := mul_le_mul_of_nonneg_left hω.2 ha.le
    simpa only [mul_inv_cancel₀ ha.ne'] using hh
  have hc := rare_current_mean_replacement μ (fun n ω => a*f n ω)
    (fun n => (hf n).const_mul a) hunit N hNpos hN T hT k hB hQ hTb hrare
  have hcurrent : Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      |empirical (f n) (N n) ω-∫ x,f n x ∂μ n|
        ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
    have hh := hc.div_const a
    have he (n : ℕ) : (N n:ℝ)*(∫ ω,T n ω*
        |empirical (fun x => a*f n x) (N n) ω-∫ x,a*f n x ∂μ n|
          ∂Measure.pi (fun _ : Fin (N n) => μ n))/a=
        (N n:ℝ)*∫ ω,T n ω*
          |empirical (f n) (N n) ω-∫ x,f n x ∂μ n|
            ∂Measure.pi (fun _ : Fin (N n) => μ n) := by
      simp_rw [empirical_const_mul,integral_const_mul,← mul_sub,abs_mul,abs_of_pos ha]
      rw [show (fun ω => T n ω*(a*|empirical (f n) (N n) ω-∫ x,f n x ∂μ n|))=
        fun ω => a*(T n ω*|empirical (f n) (N n) ω-∫ x,f n x ∂μ n|) by funext ω; ring,
        integral_const_mul]
      field_simp [ha.ne']
    simpa only [he,zero_div] using hh
  have hlim := hcurrent.add (((hmean.sub_const ν).abs).const_mul Q)
  simp only [sub_self,abs_zero,mul_zero,add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · exact Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) (integral_nonneg_of_ae
      ((hTb n).mono fun ω hω => mul_nonneg hω.1 (abs_nonneg _)))
  · filter_upwards [hrare] with n hn
    let P := Measure.pi (fun _ : Fin (N n) => μ n)
    let m := ∫ x,f n x ∂μ n
    have hfi : Integrable (f n) (μ n) := Integrable.of_mem_Icc 0 (a⁻¹)
      (hf n).aemeasurable (hb n)
    have hm : m ∈ Icc (0:ℝ) (a⁻¹) := by
      refine ⟨integral_nonneg_of_ae ((hb n).mono fun _ h => h.1),?_⟩
      simpa only [integral_const,probReal_univ,one_smul] using
        integral_mono_ae hfi (integrable_const (a⁻¹)) ((hb n).mono fun _ h => h.2)
    have hem : ∀ᵐ ω ∂P,empirical (f n) (N n) ω ∈ Icc (0:ℝ) (a⁻¹) := by
      have he := empirical_unit_bounds (μ n) (hunit n) (hNpos n)
      filter_upwards [he] with ω hω
      rw [empirical_const_mul] at hω
      constructor
      · nlinarith [hω.1]
      · calc
          _ ≤ 1/a := (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hω.2)
          _ = a⁻¹ := one_div a
    have hTi : Integrable (T n) P := Integrable.of_mem_Icc 0 (B*(N n:ℝ)^k)
      (hT n).aemeasurable (hTb n)
    have hint (z : ℝ) : Integrable (fun ω => T n ω*|empirical (f n) (N n) ω-z|) P := by
      apply Integrable.of_mem_Icc 0 (B*(N n:ℝ)^k*(a⁻¹+|z|))
        ((hT n).mul (((measurable_empirical (hf n) (N n)).sub_const z).abs)).aemeasurable
      filter_upwards [hem,hTb n] with ω hω ht
      refine ⟨mul_nonneg ht.1 (abs_nonneg _),?_⟩
      have hab : |empirical (f n) (N n) ω-z|≤ a⁻¹+|z| := by
        exact (abs_sub _ _).trans (by rw [abs_of_nonneg hω.1]; linarith [hω.2])
      exact mul_le_mul ht.2 hab (abs_nonneg _) (by positivity)
    have hh := integral_mono_ae (hint ν)
      ((hint m).add (hTi.const_mul |m-ν|)) (by
        filter_upwards [hTb n] with ω ht
        have ha' := mul_le_mul_of_nonneg_left (abs_sub_le (empirical (f n) (N n) ω) m ν) ht.1
        change T n ω*|empirical (f n) (N n) ω-ν| ≤
          T n ω*|empirical (f n) (N n) ω-m|+|m-ν| * T n ω
        nlinarith only [ha'])
    simp only [Pi.add_apply] at hh
    rw [integral_add (hint m) (hTi.const_mul |m-ν|),integral_const_mul] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (N n))
    have hn' := mul_le_mul_of_nonneg_right hn (abs_nonneg (m-ν))
    dsimp only [m,P] at *
    nlinarith

theorem bounded_rare_replacement
    (μ : ℕ → Measure Ω) [∀ n,IsProbabilityMeasure (μ n)]
    (f : ℕ → Ω → ℝ) (hf : ∀ n,Measurable (f n))
    {a : ℝ} (ha : 0 < a)
    (hb : ∀ n,∀ᵐ ω ∂μ n,0 ≤ f n ω ∧ f n ω ≤ a⁻¹)
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → Ω) → ℝ) (hT : ∀ n,Measurable (T n))
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) => μ n),
      0 ≤ T n ω ∧ T n ω ≤ B*(N n:ℝ)^k)
    {L ν : ℝ}
    (hrare : Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 L))
    (hmean : Tendsto (fun n => ∫ ω,f n ω ∂μ n) atTop (𝓝 ν)) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*|empirical (f n) (N n) ω-ν|
      ∂Measure.pi (fun _ : Fin (N n) => μ n)) atTop (𝓝 0) := by
  have hunit (n : ℕ) : ∀ᵐ ω ∂μ n,a*f n ω ∈ Icc (0:ℝ) 1 := by
    filter_upwards [hb n] with ω hω
    refine ⟨mul_nonneg ha.le hω.1,?_⟩
    have hh := mul_le_mul_of_nonneg_left hω.2 ha.le
    simpa only [mul_inv_cancel₀ ha.ne'] using hh
  have hmean' : Tendsto (fun n => ∫ ω,a*f n ω ∂μ n) atTop (𝓝 (a*ν)) := by
    simpa only [integral_const_mul] using hmean.const_mul a
  have ht := rare_empirical_replacement μ (fun n ω => a*f n ω)
    (fun n => (hf n).const_mul a) hunit N hNpos hN T hT k hB hTb hrare hmean'
  have he (n : ℕ) : (N n:ℝ)*∫ ω,T n ω*|empirical (fun x => a*f n x) (N n) ω-a*ν|
      ∂Measure.pi (fun _ : Fin (N n) => μ n)=
        a*((N n:ℝ)*∫ ω,T n ω*|empirical (f n) (N n) ω-ν|
          ∂Measure.pi (fun _ : Fin (N n) => μ n)) := by
    simp_rw [empirical_const_mul,← mul_sub,abs_mul,abs_of_pos ha]
    rw [show (fun ω => T n ω*(a*|empirical (f n) (N n) ω-ν|))=
      fun ω => a*(T n ω*|empirical (f n) (N n) ω-ν|) by funext ω; ring,
      integral_const_mul]
    ring
  have hh := ht.div_const a
  simpa only [he,mul_div_cancel_left₀ _ ha.ne',zero_div] using hh

theorem original_rare_reciprocal_and_window (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (law i)))
    {lo hi Θ U : ℝ} (hlo : 0 < lo) (hU : 0 ≤ U)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) U)
    (b z θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hz : ∀ n,z n ∈ Icc lo hi)
    (hθ : ∀ n,θ n ∈ Icc (-Θ) Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hzlim : Tendsto z atTop (𝓝 b0))
    (hθlim : Tendsto θ atTop (𝓝 θ0))
    (N : ℕ → ℕ) (hNpos : ∀ n,0 < N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → RowRival) → ℝ) (hT : ∀ n,Measurable (T n))
    (k : ℕ) {B L : ℝ} (hB : 0 ≤ B)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),
        0 ≤ T n ω ∧ T n ω ≤ B*(N n:ℝ)^k)
    (hrare : Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
        atTop (𝓝 L)) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      |empirical (FullReciprocalMean.reciprocal (z n)) (N n) ω-nu i b0 θ0|
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
        atTop (𝓝 0) ∧
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      empirical (FullReciprocalMean.window (z n) (b n)) (N n) ω
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
        atTop (𝓝 0) := by
  let μ := fun n => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  letI : ∀ n,IsProbabilityMeasure (μ n) :=
    fun n => tiltedSource_probability i _ (hlo.trans_le (hb n).1) (θ n)
  have hmean := original_tilted_reciprocal_and_window i G hG hlo hU hbox
    b z θ hb hz hθ hblim hzlim hθlim
  have hr := bounded_rare_replacement μ (fun n => FullReciprocalMean.reciprocal (z n))
    (fun n => FullReciprocalMean.measurable_reciprocal (z n)) hlo
    (fun n => ae_of_all _ (FullReciprocalMean.reciprocal_bounds hlo (hz n).1))
    N hNpos hN T hT k hB hTb hrare hmean.1
  have hw := rare_empirical_replacement μ (fun n => FullReciprocalMean.window (z n) (b n))
    (fun n => FullReciprocalMean.measurable_window (z n) (b n))
    (fun n => ae_of_all _ (FullReciprocalMean.window_bounds (z n) (b n)))
    N hNpos hN T hT k hB hTb hrare hmean.2
  have he (n : ℕ) : (∫ ω,T n ω*|empirical (FullReciprocalMean.window (z n) (b n)) (N n) ω-0|
      ∂Measure.pi (fun _ : Fin (N n) => μ n))=
        ∫ ω,T n ω*empirical (FullReciprocalMean.window (z n) (b n)) (N n) ω
          ∂Measure.pi (fun _ : Fin (N n) => μ n) := by
    apply integral_congr_ae
    filter_upwards [empirical_unit_bounds (μ n)
      (ae_of_all _ (FullReciprocalMean.window_bounds (z n) (b n))) (hNpos n)] with ω hω
    rw [sub_zero,abs_of_nonneg hω.1]
  exact ⟨hr,by simpa only [he] using hw⟩

theorem original_bounded_rare_reciprocal_and_window (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hG : Tendsto G atTop (𝓝 (law i)))
    {lo hi Θ U : ℝ} (hlo : 0< lo) (hU : 0≤ U)
    (hbox : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
      p ∈ EarlyJointCompactness.box (cutoff i) U)
    (b z θ : ℕ → ℝ) {b0 θ0 : ℝ}
    (hb : ∀ n,b n ∈ Icc lo hi) (hz : ∀ n,z n ∈ Icc lo hi)
    (hθ : ∀ n,θ n ∈ Icc (-Θ) Θ)
    (hblim : Tendsto b atTop (𝓝 b0)) (hzlim : Tendsto z atTop (𝓝 b0))
    (hθlim : Tendsto θ atTop (𝓝 θ0))
    (N : ℕ → ℕ) (hNpos : ∀ n,0< N n) (hN : Tendsto N atTop atTop)
    (T : (n : ℕ) → (Fin (N n) → RowRival) → ℝ) (hT : ∀ n,Measurable (T n))
    (k : ℕ) {B Q : ℝ} (hB : 0≤ B) (hQ : 0< Q)
    (hTb : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (N n) =>
      tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)),
        0≤ T n ω ∧ T n ω≤ B*(N n:ℝ)^k)
    (hrare : ∀ᶠ n in atTop,(N n:ℝ)*∫ ω,T n ω
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))≤ Q) :
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      |empirical (FullReciprocalMean.reciprocal (z n)) (N n) ω-nu i b0 θ0|
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
        atTop (𝓝 0) ∧
    Tendsto (fun n => (N n:ℝ)*∫ ω,T n ω*
      empirical (FullReciprocalMean.window (z n) (b n)) (N n) ω
      ∂Measure.pi (fun _ : Fin (N n) => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)))
        atTop (𝓝 0) := by
  let μ := fun n => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  letI : ∀ n,IsProbabilityMeasure (μ n) :=
    fun n => tiltedSource_probability i _ (hlo.trans_le (hb n).1) (θ n)
  have hm := original_tilted_reciprocal_and_window i G hG hlo hU hbox
    b z θ hb hz hθ hblim hzlim hθlim
  have hr := bounded_mass_reference_replacement μ (fun n => FullReciprocalMean.reciprocal (z n))
    (fun n => FullReciprocalMean.measurable_reciprocal (z n)) hlo
    (fun n => ae_of_all _ (FullReciprocalMean.reciprocal_bounds hlo (hz n).1))
    N hNpos hN T hT k hB hQ hTb hrare hm.1
  have hw := bounded_mass_reference_replacement μ (fun n => FullReciprocalMean.window (z n) (b n))
    (fun n => FullReciprocalMean.measurable_window (z n) (b n)) (by norm_num : (0:ℝ)<1)
    (fun (n : ℕ) => by
      simpa only [inv_one,Set.mem_Icc] using!
        (ae_of_all (μ n) (FullReciprocalMean.window_bounds (z n) (b n))))
    N hNpos hN T hT k hB hQ hTb hrare hm.2
  refine ⟨hr,?_⟩
  apply hw.congr'
  exact Eventually.of_forall fun n => congrArg ((N n:ℝ)*·) (integral_congr_ae (by
    filter_upwards [empirical_unit_bounds (μ n)
      (ae_of_all _ (FullReciprocalMean.window_bounds (z n) (b n))) (hNpos n)] with ω hω
    rw [sub_zero,abs_of_nonneg hω.1]))

end FCAppendix.Affine.Uniform06.RareSourceReciprocal
