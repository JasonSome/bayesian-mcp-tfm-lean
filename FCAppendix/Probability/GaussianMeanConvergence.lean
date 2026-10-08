import FCAppendix.Probability.CDFWeakConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
namespace FCAppendix.Probability
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BoundedContinuousFunction

private def symmetricClip (R x : ℝ) : ℝ := max (-R) (min x R)

private theorem continuous_symmetricClip (R : ℝ) : Continuous (symmetricClip R) := by
  unfold symmetricClip
  fun_prop

private theorem abs_symmetricClip_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |symmetricClip R x| ≤ R := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

private def boundedClip (R : ℝ) (hR : 0 ≤ R) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨symmetricClip R,continuous_symmetricClip R⟩ (2*R)
    (fun x y => by
      change |symmetricClip R x-symmetricClip R y| ≤ 2*R
      calc
        _ ≤ |symmetricClip R x|+|symmetricClip R y| := abs_sub _ _
        _ ≤ R+R := add_le_add (abs_symmetricClip_le hR x) (abs_symmetricClip_le hR y)
        _ = 2*R := by ring)

private theorem symmetricClip_tail {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x-symmetricClip R x| ≤ x^2/R := by
  by_cases hx : x ≤ -R
  · have hxR : x ≤ R := by linarith
    rw [symmetricClip,min_eq_left hxR,max_eq_left hx,abs_of_nonpos (by linarith)]
    apply (le_div_iff₀ hR).mpr
    nlinarith [sq_nonneg (x+R)]
  · by_cases hRx : R ≤ x
    · rw [symmetricClip,min_eq_right hRx,max_eq_right (by linarith),
        abs_of_nonneg (sub_nonneg.mpr hRx)]
      apply (le_div_iff₀ hR).mpr
      nlinarith [sq_nonneg (x-R)]
    · rw [symmetricClip,min_eq_left (le_of_not_ge hRx),max_eq_right (le_of_not_ge hx)]
      simpa using div_nonneg (sq_nonneg x) hR.le

private theorem integral_symmetricClip_tail
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) {R : ℝ} (hR : 0 < R) :
    |(∫ a, X a ∂μ) - ∫ a, symmetricClip R (X a) ∂μ| ≤ (∫ a, (X a)^2 ∂μ)/R := by
  have hi : Integrable X μ := hX.integrable (by norm_num)
  have hc : Integrable (fun a => symmetricClip R (X a)) μ :=
    Integrable.of_bound ((continuous_symmetricClip R).comp_aestronglyMeasurable hX.1)
      R (ae_of_all _ fun a => by simpa only [Real.norm_eq_abs] using abs_symmetricClip_le hR.le (X a))
  calc
    _ = |∫ a, X a-symmetricClip R (X a) ∂μ| := by rw [integral_sub hi hc]
    _ ≤ ∫ a, |X a-symmetricClip R (X a)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun a => X a-symmetricClip R (X a))
    _ ≤ ∫ a, (X a)^2/R ∂μ := integral_mono (hi.sub hc).abs
      (hX.integrable_sq.div_const R) (fun a => symmetricClip_tail hR (X a))
    _ = _ := integral_div R _

theorem probabilityMeasure_mean_tendsto_of_secondMoment_bound
    (μ : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hLp : ∀ m, MemLp (fun x : ℝ => x) 2 (μ m : Measure ℝ))
    (hν : MemLp (fun x : ℝ => x) 2 (ν : Measure ℝ))
    (K : ℝ) (hK : ∀ m, (∫ x : ℝ, x^2 ∂(μ m : Measure ℝ)) ≤ K) :
    Tendsto (fun m => ∫ x : ℝ, x ∂(μ m : Measure ℝ)) atTop
      (𝓝 (∫ x : ℝ, x ∂(ν : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let J := ∫ x : ℝ, x^2 ∂(ν : Measure ℝ)
  have ht : Tendsto (fun R : ℝ => (K+J)/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨R,hR,hsmall⟩ : ∃ R : ℝ, 0 < R ∧ (K+J)/R < ε/2 := by
    have hs := (tendsto_order.mp ht).2 (ε/2) (by linarith)
    exact ((eventually_gt_atTop 0).and hs).exists
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (boundedClip R hR.le)
  have he := (Metric.tendsto_nhds.mp hc) (ε/2) (by linarith)
  filter_upwards [he] with m hm
  change |(∫ x : ℝ, x ∂(μ m : Measure ℝ)) - ∫ x : ℝ, x ∂(ν : Measure ℝ)| < ε
  change |(∫ x, symmetricClip R x ∂(μ m : Measure ℝ)) -
    ∫ x, symmetricClip R x ∂(ν : Measure ℝ)| < ε/2 at hm
  have hmTail := integral_symmetricClip_tail (μ m : Measure ℝ) id (hLp m) hR
  have hνTail := integral_symmetricClip_tail (ν : Measure ℝ) id hν hR
  have hmK : |(∫ x : ℝ, x ∂(μ m : Measure ℝ)) - ∫ x, symmetricClip R x ∂(μ m : Measure ℝ)| ≤ K/R :=
    hmTail.trans (div_le_div_of_nonneg_right (hK m) hR.le)
  have ht1 := abs_sub_le (∫ x : ℝ, x ∂(μ m : Measure ℝ))
    (∫ x, symmetricClip R x ∂(μ m : Measure ℝ)) (∫ x : ℝ, x ∂(ν : Measure ℝ))
  have ht2 := abs_sub_le (∫ x, symmetricClip R x ∂(μ m : Measure ℝ))
    (∫ x, symmetricClip R x ∂(ν : Measure ℝ)) (∫ x : ℝ, x ∂(ν : Measure ℝ))
  rw [abs_sub_comm (∫ x, symmetricClip R x ∂(ν : Measure ℝ))] at ht2
  have hsum : K/R+J/R < ε/2 := by rw [← add_div]; exact hsmall
  change |(∫ x : ℝ, x ∂(ν : Measure ℝ))-∫ x, symmetricClip R x ∂(ν : Measure ℝ)| ≤ J/R at hνTail
  linarith

theorem gaussian_mean_tendsto_of_secondMoment_bound
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (hm : ∀ m, Measurable (X m))
    (hLp : ∀ m, MemLp (X m) 2 (μ m)) (K : ℝ)
    (hK : ∀ m, (∫ ω, (X m ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ x : ℝ, Tendsto (fun m => cdf ((μ m).map (X m)) x) atTop
      (𝓝 (cdf (gaussianReal 0 1) x))) :
    Tendsto (fun m => ∫ ω, X m ω ∂μ m) atTop (𝓝 0) := by
  let laws : ℕ → ProbabilityMeasure ℝ := fun m =>
    ⟨(μ m).map (X m),Measure.isProbabilityMeasure_map (hm m).aemeasurable⟩
  let normal : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1,inferInstance⟩
  have hw : Tendsto laws atTop (𝓝 normal) := probabilityMeasure_tendsto_of_cdf laws normal hcdf
  have hL (m : ℕ) : MemLp (fun x : ℝ => x) 2 (laws m : Measure ℝ) :=
    (memLp_map_measure_iff aestronglyMeasurable_id (hm m).aemeasurable).mpr (hLp m)
  have hLK (m : ℕ) : (∫ x : ℝ, x^2 ∂(laws m : Measure ℝ)) ≤ K := by
    change (∫ x : ℝ, x^2 ∂(μ m).map (X m)) ≤ K
    rw [integral_map (hm m).aemeasurable (by fun_prop)]
    exact hK m
  have ht := probabilityMeasure_mean_tendsto_of_secondMoment_bound laws normal hw hL
    (memLp_id_gaussianReal 2) K hLK
  have heq : (fun m => ∫ x : ℝ, x ∂(laws m : Measure ℝ)) =
      (fun m => ∫ ω, X m ω ∂μ m) := by
    funext m
    exact integral_map (hm m).aemeasurable aestronglyMeasurable_id
  rw [heq] at ht
  simpa only [normal,ProbabilityMeasure.coe_mk,integral_id_gaussianReal] using ht

theorem gaussian_mean_tendsto_of_eventually_secondMoment_bound
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    (X : (m : ℕ) → Ω m → ℝ) (K : ℝ)
    (hbound : ∀ᶠ m in atTop, Measurable (X m) ∧ MemLp (X m) 2 (μ m) ∧
      (∫ ω, (X m ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ x : ℝ, Tendsto (fun m => cdf ((μ m).map (X m)) x) atTop
      (𝓝 (cdf (gaussianReal 0 1) x))) :
    Tendsto (fun m => ∫ ω, X m ω ∂μ m) atTop (𝓝 0) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp hbound
  have ht := gaussian_mean_tendsto_of_secondMoment_bound
    (fun m => μ (m+M)) (fun m => X (m+M))
    (fun m => (hM (m+M) (Nat.le_add_left M m)).1)
    (fun m => (hM (m+M) (Nat.le_add_left M m)).2.1) K
    (fun m => (hM (m+M) (Nat.le_add_left M m)).2.2)
    (fun x => (hcdf x).comp (tendsto_add_atTop_nat M))
  exact (tendsto_add_atTop_iff_nat M).mp ht

theorem eventually_uniform_abs_lt_of_all_choices
    {B : Type*} (S : Set B) (f : ℕ → B → ℝ)
    (h : ∀ b : ℕ → B, (∀ m, b m ∈ S) → Tendsto (fun m => f m (b m)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ m in atTop, ∀ b ∈ S, |f m b| < ε := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨b₀,hb₀⟩ := hS
    let b : ℕ → B := fun m => if hh : ∃ b ∈ S, ε ≤ |f m b| then hh.choose else b₀
    have hb (m : ℕ) : b m ∈ S := by
      dsimp [b]
      split
      · exact (Exists.choose_spec ‹∃ b ∈ S, ε ≤ |f m b|›).1
      · exact hb₀
    have he := (Metric.tendsto_nhds.mp (h b hb)) ε hε
    filter_upwards [he] with m hm
    intro a ha
    by_contra hbad
    have hh : ∃ a ∈ S, ε ≤ |f m a| := ⟨a,ha,le_of_not_gt hbad⟩
    have hlarge : ε ≤ |f m (b m)| := by
      dsimp [b]
      rw [dif_pos hh]
      exact hh.choose_spec.2
    simp only [Real.dist_eq,sub_zero,not_lt.mpr hlarge] at hm
  · exact Eventually.of_forall (fun _ b hb => False.elim (hS ⟨b,hb⟩))

theorem gaussian_mean_eventually_uniform_abs_lt_of_secondMoment_bound
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    {B : Type*} (S : Set B) (X : (m : ℕ) → B → Ω m → ℝ) (K : ℝ)
    (hbound : ∀ᶠ m in atTop, ∀ b ∈ S,
      Measurable (X m b) ∧ MemLp (X m b) 2 (μ m) ∧
        (∫ ω, (X m b ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ x : ℝ, ∀ ε > 0, ∀ᶠ m in atTop, ∀ b ∈ S,
      |cdf ((μ m).map (X m b)) x-cdf (gaussianReal 0 1) x| < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ b ∈ S, |∫ ω, X m b ω ∂μ m| < ε := by
  apply eventually_uniform_abs_lt_of_all_choices S (fun m b => ∫ ω, X m b ω ∂μ m) _ hε
  intro b hb
  apply gaussian_mean_tendsto_of_eventually_secondMoment_bound μ (fun m => X m (b m)) K
  · exact hbound.mono (fun m hm => hm (b m) (hb m))
  · intro x
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    exact (hcdf x δ hδ).mono (fun m hm => by
      simpa only [Real.dist_eq] using hm (b m) (hb m))

theorem gaussian_mean_tendstoUniformlyOn_of_secondMoment_bound
    {Ω : ℕ → Type*} [∀ m, MeasurableSpace (Ω m)]
    (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    {B : Type*} (S : Set B) (X : (m : ℕ) → B → Ω m → ℝ) (K : ℝ)
    (hbound : ∀ᶠ m in atTop, ∀ b ∈ S,
      Measurable (X m b) ∧ MemLp (X m b) 2 (μ m) ∧
        (∫ ω, (X m b ω)^2 ∂μ m) ≤ K)
    (hcdf : ∀ x : ℝ, ∀ ε > 0, ∀ᶠ m in atTop, ∀ b ∈ S,
      |cdf ((μ m).map (X m b)) x-cdf (gaussianReal 0 1) x| < ε) :
    TendstoUniformlyOn (fun m b => ∫ ω, X m b ω ∂μ m) (fun _ => 0) atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact (gaussian_mean_eventually_uniform_abs_lt_of_secondMoment_bound
    μ S X K hbound hcdf hε).mono (fun m hm b hb => by
      simpa only [Real.dist_eq,zero_sub,abs_neg] using hm b hb)

end FCAppendix.Probability
