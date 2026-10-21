import FCAppendix.Affine.Uniform06.EntryCentralReplacement

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryProfileMean
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.WeightedMoments
open FCAppendix.Affine.Uniform06.EntrySamplingLaw
open FCAppendix.Affine.Uniform06.EntryCentralSampling
open FCAppendix.Affine.Uniform06.EntryEmpiricalRatio
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

def profileWeights (w0 : ℝ) (w : Ω → ℝ) (h0 : w0 ∈ Icc (0:ℝ) 1)
    (hb : ∀ ω, w ω ∈ Icc (0:ℝ) 1) {N : ℕ} (r : Fin N → Ω) : Weights (Fin (N+1)) :=
  ⟨Fin.cons w0 (fun j => w (r j)),by intro j; refine Fin.cases h0 (fun j => hb (r j)) j⟩

def profileH (h0 : ℝ) (h : Ω → ℝ) {N : ℕ} (r : Fin N → Ω) : Fin (N+1) → ℝ :=
  Fin.cons h0 (fun j => h (r j))

lemma measurable_profileWeights (w0 : ℝ) (w : Ω → ℝ) (h0 : w0 ∈ Icc (0:ℝ) 1)
    (hb : ∀ ω, w ω ∈ Icc (0:ℝ) 1) (hw : Measurable w) (N : ℕ) :
    Measurable (profileWeights w0 w h0 hb (N := N)) := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact measurable_const
  · exact hw.comp (measurable_pi_apply j)

lemma measurable_profileH (h0 : ℝ) {h : Ω → ℝ} (hh : Measurable h) (N : ℕ) :
    Measurable (profileH h0 h (N := N)) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact measurable_const
  · exact hh.comp (measurable_pi_apply j)

omit [MeasurableSpace Ω] in
lemma totalWeight_profile (w0 : ℝ) (w : Ω → ℝ) (h0 : w0 ∈ Icc (0:ℝ) 1)
    (hb : ∀ ω, w ω ∈ Icc (0:ℝ) 1) {N : ℕ} (r : Fin N → Ω) :
    totalWeight (profileWeights w0 w h0 hb r)=w0+∑ j, w (r j) := by
  simp [totalWeight,profileWeights,Fin.sum_univ_succ]

omit [MeasurableSpace Ω] in
lemma weightedMean_profile (w0 h0 : ℝ) (w h : Ω → ℝ) (hw0 : w0 ∈ Icc (0:ℝ) 1)
    (hb : ∀ ω, w ω ∈ Icc (0:ℝ) 1) {N : ℕ} (r : Fin N → Ω) :
    weightedMean (profileWeights w0 w hw0 hb r) (profileH h0 h r)=
      (w0*h0+∑ j, w (r j)*h (r j))/(w0+∑ j, w (r j)) := by
  simp [weightedMean,profileWeights,profileH,totalWeight,Fin.sum_univ_succ]

omit [MeasurableSpace Ω] in
lemma profileH_abs_le {A h0 : ℝ} {h : Ω → ℝ} (hh0 : |h0| ≤ A)
    (hb : ∀ ω, |h ω| ≤ A) {N : ℕ} (r : Fin N → Ω) (j : Fin (N+1)) :
    |profileH h0 h r j| ≤ A := by
  exact Fin.cases hh0 (fun j => hb (r j)) j

lemma shifted_ratio_error {c d a u v q r : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    |(u+q)/max c (v+r)-a/d| ≤
      |u-a| /c+|q| /c+|a| *|v-d| /(c*d)+|a| *|r| /(c*d) := by
  have hh := ratio_error_bound (u := u+q) (v := v+r) (a := a) hc hcd
  have hd : 0 < d := hc.trans_le hcd
  have hu : |u+q-a| ≤ |u-a|+|q| := by
    simpa only [sub_add_eq_add_sub] using abs_add_le (u-a) q
  have hv : |v+r-d| ≤ |v-d|+|r| := by
    simpa only [sub_add_eq_add_sub] using abs_add_le (v-d) r
  apply hh.trans
  have h1 := div_le_div_of_nonneg_right hu hc.le
  have h2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (abs_nonneg a)) (mul_pos hc hd).le
  simpa only [add_div,mul_add,add_assoc] using add_le_add h1 h2

omit [MeasurableSpace Ω] in

lemma guarded_profile_error_bound
    {N : ℕ} (hN : 0 < N) {c d a A w0 h0 : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) (hw0 : w0 ∈ Icc (0:ℝ) 1) (hh0 : |h0| ≤ A)
    (w h : Ω → ℝ) (hwb : ∀ ω, w ω ∈ Icc (0:ℝ) 1)
    (r : Fin N → Ω) :
    |guardedMean (profileWeights w0 w hw0 hwb) (profileH h0 h) (c*N) (a/d) r-a/d| ≤
      |empirical (fun ω => w ω*h ω) N r-a| /c+A/(c*N)+
      |a| *|empirical w N r-d| /(c*d)+|a| /(c*d*N) := by
  have hNr : (0:ℝ)< N := by exact_mod_cast hN
  have hd : 0 < d := hc.trans_le hcd
  have hA : 0 ≤ A := (abs_nonneg h0).trans hh0
  by_cases hg : c*(N : ℝ) ≤ totalWeight (profileWeights w0 w hw0 hwb r)
  · rw [guardedMean,if_pos hg,weightedMean_profile]
    have hv : c ≤ empirical w N r+w0/(N : ℝ) := by
      rw [totalWeight_profile] at hg
      unfold empirical
      rw [← add_div]
      apply (le_div_iff₀ hNr).mpr
      simpa only [add_comm] using hg
    have he : (w0*h0+∑ j, w (r j)*h (r j))/(w0+∑ j, w (r j))=
        (empirical (fun ω => w ω*h ω) N r+(w0*h0)/(N : ℝ))/
          max c (empirical w N r+w0/(N : ℝ)) := by
      rw [max_eq_right hv]
      unfold empirical
      rw [← add_div,← add_div]
      rw [div_div_div_cancel_right₀ hNr.ne']
      congr 1 <;> ring
    rw [he]
    apply (shifted_ratio_error hc hcd).trans
    have hq : |(w0*h0)/(N : ℝ)| ≤ A/(N : ℝ) := by
      rw [abs_div,abs_of_pos hNr,abs_mul,abs_of_nonneg hw0.1]
      apply div_le_div_of_nonneg_right _ hNr.le
      exact (mul_le_mul_of_nonneg_left hh0 hw0.1).trans
        (by nlinarith [mul_le_mul_of_nonneg_right hw0.2 hA])
    have hw : |w0/(N : ℝ)| ≤ 1/(N : ℝ) := by
      rw [abs_div,abs_of_pos hNr,abs_of_nonneg hw0.1]
      exact div_le_div_of_nonneg_right hw0.2 hNr.le
    have h1 := div_le_div_of_nonneg_right hq hc.le
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw (abs_nonneg a)) (mul_pos hc hd).le
    have ht := add_le_add (add_le_add
      (add_le_add (le_refl (|empirical (fun ω => w ω*h ω) N r-a|/c)) h1)
      (le_refl (|a| *|empirical w N r-d|/(c*d)))) h2
    simpa only [div_eq_mul_inv,mul_inv_rev,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using! ht
  · rw [guardedMean,if_neg hg,sub_self,abs_zero]
    positivity

theorem actual_guarded_profile_L1
    (μ : ℕ → Measure Ω) [∀ m, IsProbabilityMeasure (μ m)]
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (w h : ℕ → Ω → ℝ) (hw : ∀ m, Measurable (w m)) (hh : ∀ m, Measurable (h m))
    (w0 h0 : ℕ → ℝ) {A c d a : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hcd : c ≤ d)
    (hw0 : ∀ m, w0 m ∈ Icc (0:ℝ) 1) (hh0 : ∀ m, |h0 m| ≤ A)
    (hwb : ∀ m ω, w m ω ∈ Icc (0:ℝ) 1) (hhb : ∀ m ω, |h m ω| ≤ A)
    (hastar : |a/d| ≤ A)
    (hwlim : Tendsto (fun m => ∫ ω, w m ω ∂μ m) atTop (𝓝 d))
    (hglim : Tendsto (fun m => ∫ ω, w m ω*h m ω ∂μ m) atTop (𝓝 a)) :
    Tendsto (fun m => ∫ r,
      |guardedMean (profileWeights (w0 m) (w m) (hw0 m) (hwb m)) (profileH (h0 m) (h m))
        (c*N m) (a/d) r-a/d| ∂Measure.pi (fun _ : Fin (N m) => μ m)) atTop (𝓝 0) := by
  have hwB m : ∀ᵐ ω ∂μ m, |w m ω| ≤ 1 := Eventually.of_forall fun ω => by
    rw [abs_of_nonneg (hwb m ω).1]
    exact (hwb m ω).2
  have hgB m : ∀ᵐ ω ∂μ m, |w m ω*h m ω| ≤ A := Eventually.of_forall fun ω => by
    rw [abs_mul,abs_of_nonneg (hwb m ω).1]
    exact (mul_le_mul_of_nonneg_left (hhb m ω) (hwb m ω).1).trans
      (by nlinarith [mul_le_mul_of_nonneg_right (hwb m ω).2 hA])
  have hgL := empirical_L1_tendsto μ (fun m ω => w m ω*h m ω)
    (fun m => (hw m).mul (hh m)) hA hgB N hN hglim
  have hwL := empirical_L1_tendsto μ w hw (by norm_num : 0 ≤ (1:ℝ)) hwB N hN hwlim
  have hd : 0 < d := hc.trans_le hcd
  have hNr : Tendsto (fun m => (N m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hN
  have ht : Tendsto (fun m =>
      (∫ r, |empirical (fun ω => w m ω*h m ω) (N m) r-a|
        ∂Measure.pi (fun _ : Fin (N m) => μ m))/c+A/(c*N m)+
      |a| /(c*d)*(∫ r, |empirical (w m) (N m) r-d|
        ∂Measure.pi (fun _ : Fin (N m) => μ m))+|a| /(c*d*N m)) atTop (𝓝 0) := by
    simpa only [zero_div,mul_zero,zero_add,add_zero] using
      (((hgL.div_const c).add (tendsto_const_nhds.div_atTop (hNr.const_mul_atTop hc))).add
        (hwL.const_mul (|a| /(c*d)))).add
          (tendsto_const_nhds.div_atTop (hNr.const_mul_atTop (mul_pos hc hd)))
  apply squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _) ?_ ht
  intro m
  have hNr : (0:ℝ) < N m := by exact_mod_cast hNp m
  let P := Measure.pi (fun _ : Fin (N m) => μ m)
  letI : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hwi := integrable_empirical (μ m) (hw m) (by norm_num : 0 ≤ (1:ℝ)) (hwB m) (N m)
  have hgi := integrable_empirical (μ m) ((hw m).mul (hh m)) hA (hgB m) (N m)
  have hli : Integrable (fun r =>
      |guardedMean (profileWeights (w0 m) (w m) (hw0 m) (hwb m)) (profileH (h0 m) (h m))
        (c*N m) (a/d) r-a/d|) P := by
    apply Integrable.of_bound
      ((measurable_guardedMean _ _ (measurable_profileWeights _ _ _ _ (hw m) (N m))
        (measurable_profileH _ (hh m) (N m)) _ _).sub_const _).abs.aestronglyMeasurable (2*A)
    exact Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs,abs_abs]
      have hb := guardedMean_abs_le
        (profileWeights (w0 m) (w m) (hw0 m) (hwb m)) (profileH (h0 m) (h m))
        (show 0 < c*(N m : ℝ) by positivity)
        (fun r j => profileH_abs_le (hh0 m) (hhb m) r j) hastar r
      exact (abs_sub _ _).trans (by linarith)
  have hi1 : Integrable (fun r => |empirical (fun ω => w m ω*h m ω) (N m) r-a|/c) P := by
    convert! ((hgi.sub (integrable_const a)).abs).div_const c using 1
  have hi2 : Integrable (fun r => |a|/(c*d)*|empirical (w m) (N m) r-d|) P := by
    convert! ((hwi.sub (integrable_const d)).abs).const_mul (|a|/(c*d)) using 1
  have hiA : Integrable (fun _ : Fin (N m) → Ω => A/(c*N m)) P := integrable_const _
  have hiB : Integrable (fun _ : Fin (N m) → Ω => |a|/(c*d*N m)) P := integrable_const _
  have hi12 : Integrable (fun r => |empirical (fun ω => w m ω*h m ω) (N m) r-a|/c+A/(c*N m)) P := by
    convert! hi1.add hiA using 1
  have hi123 : Integrable (fun r => |empirical (fun ω => w m ω*h m ω) (N m) r-a|/c+A/(c*N m)+
      |a|/(c*d)*|empirical (w m) (N m) r-d|) P := by
    convert! hi12.add hi2 using 1
  have hiR : Integrable (fun r => |empirical (fun ω => w m ω*h m ω) (N m) r-a|/c+A/(c*N m)+
      |a|/(c*d)*|empirical (w m) (N m) r-d|+|a|/(c*d*N m)) P := by
    convert! hi123.add hiB using 1
  have hbound := integral_mono hli hiR (fun r => by
    simpa only [div_eq_mul_inv,mul_inv_rev,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using!
      guarded_profile_error_bound (hNp m) hc hcd (hw0 m) (hh0 m) (w m) (h m) (hwb m) r)
  rw [integral_add hi123 hiB,integral_add hi12 hi2,integral_add hi1 hiA] at hbound
  simpa only [integral_div,integral_const_mul,integral_const,probReal_univ,one_smul,P] using! hbound

theorem iid_guarded_replacement_L2
    (μ : ℕ → Measure Ω) [∀ m, IsProbabilityMeasure (μ m)]
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (Y w h : ℕ → Ω → ℝ)
    (hY : ∀ m, Measurable (Y m)) (hw : ∀ m, Measurable (w m)) (hh : ∀ m, Measurable (h m))
    (hYb : ∀ m, ∀ᵐ ω ∂μ m, |Y m ω| ≤ 1)
    (hYz : ∀ m, ∫ ω, Y m ω ∂μ m=0)
    (d : (m : ℕ) → (Fin (N m) → Ω) → ℕ) (hd : ∀ m, Measurable (d m))
    (hD : ∀ m r, d m r ≤ N m)
    (hcount : ∀ m r, (d m r : ℝ)=|∑ j, Y m (r j)|)
    (w0 h0 : ℕ → ℝ) {A c dbar a : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hcd : c ≤ dbar)
    (hw0 : ∀ m, w0 m ∈ Icc (0:ℝ) 1) (hh0 : ∀ m, |h0 m| ≤ A)
    (hwb : ∀ m ω, w m ω ∈ Icc (0:ℝ) 1) (hhb : ∀ m ω, |h m ω| ≤ A)
    (hastar : |a/dbar| ≤ A)
    (hwlim : Tendsto (fun m => ∫ ω, w m ω ∂μ m) atTop (𝓝 dbar))
    (hglim : Tendsto (fun m => ∫ ω, w m ω*h m ω ∂μ m) atTop (𝓝 a)) :
    Tendsto (fun m => ∫ x,
      ((guardedSample (profileWeights (w0 m) (w m) (hw0 m) (hwb m))
        (profileH (h0 m) (h m)) (d m) (c*N m) (a/dbar) x-
        (d m x.1 : ℝ)*(a/dbar))/Real.sqrt (N m : ℝ))^2
        ∂(Measure.pi (fun _ : Fin (N m) => μ m)).prod volume) atTop (𝓝 0) := by
  apply EntryCentralReplacement.actual_guarded_replacement_L2
    (fun m => Measure.pi (fun _ : Fin (N m) => μ m)) N hNp hN
    (fun m j r => Y m (r j))
    (fun m j => (hY m).comp (measurable_pi_apply j))
    (fun m j => (measurePreserving_eval (fun _ : Fin (N m) => μ m) j).quasiMeasurePreserving.ae (hYb m))
    (fun m j => by
      rw [integral_comp_eval (μ := fun _ : Fin (N m) => μ m) (hY m).aestronglyMeasurable]
      exact hYz m)
    (fun m => iIndepFun_pi fun _ : Fin (N m) => (hY m).aemeasurable)
    (fun m => profileWeights (w0 m) (w m) (hw0 m) (hwb m))
    (fun m => profileH (h0 m) (h m)) d
    (fun m => measurable_profileWeights _ _ _ _ (hw m) (N m))
    (fun m => measurable_profileH _ (hh m) (N m)) hd hA hc
    (fun m r j => profileH_abs_le (hh0 m) (hhb m) r j) hastar hD hcount
  exact actual_guarded_profile_L1 μ N hNp hN w h hw hh w0 h0 hA hc hcd hw0 hh0
    hwb hhb hastar hwlim hglim

end FCAppendix.Affine.Uniform06.EntryProfileMean
