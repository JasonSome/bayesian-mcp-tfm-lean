import FCAppendix.Probability.MeanZeroTilt
import FCAppendix.Probability.BoundedTiltBerryEsseen

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryTilts
open MeasureTheory ProbabilityTheory Set Filter Topology Real
open FCAppendix.ExponentialTilt

universe u
variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]
  (μ : (m : ℕ) → Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
  (X : (m : ℕ) → Ω m → ℝ) (r : ℕ → ℝ)

def Matches (m : ℕ) (θ : ℝ) : Prop :=
  0 < θ ∧ θ < 1 ∧
  (∫ ω, X m ω ∂(μ m).tilted (fun ω => -θ*X m ω)) = r m ∧
  ((∫ ω, X m ω ∂μ m)-r m)/(Real.exp 2*variance (X m) (μ m)) ≤ θ ∧
  θ ≤ ((∫ ω, X m ω ∂μ m)-r m)/(Real.exp (-2)*variance (X m) (μ m))

def moderateTilt (m : ℕ) : ℝ := by
  classical
  exact if h : ∃ θ, Matches μ X r m θ then Classical.choose h else 0

omit [∀ m, IsProbabilityMeasure (μ m)] in
lemma moderateTilt_spec {m : ℕ} (h : ∃ θ, Matches μ X r m θ) :
    Matches μ X r m (moderateTilt μ X r m) := by
  rw [moderateTilt,dif_pos h]
  exact Classical.choose_spec h

theorem eventually_matches
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m) (μ m)) atTop (𝓝 v))
    (hgap : Tendsto (fun m => (∫ ω, X m ω ∂μ m)-r m) atTop (𝓝 0))
    (hpos : ∀ᶠ m in atTop, 0 < (∫ ω, X m ω ∂μ m)-r m) :
    ∀ᶠ m in atTop, Matches μ X r m (moderateTilt μ X r m) := by
  have hmargin : 0 < Real.exp (-2)*v := mul_pos (Real.exp_pos _) hv
  have hlimit : Tendsto (fun m =>
      Real.exp (-2)*variance (X m) (μ m)-((∫ ω, X m ω ∂μ m)-r m))
      atTop (𝓝 (Real.exp (-2)*v)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.mul hvar).sub hgap
  filter_upwards [hvar.eventually_const_lt (show 0 < v from hv),
    hlimit.eventually_const_lt hmargin,hpos] with m hvm hgm hpm
  have hg : (∫ ω, X m ω ∂μ m)-r m <
      (1 : ℝ)*Real.exp (-2*1)*variance (X m) (μ m) := by
    norm_num only [mul_one,one_mul]
    linarith
  obtain ⟨a,ha,ham,hlo,hhi⟩ := exists_negative_tilt_of_mean_gap
    (μ m) (hX m) (hb m) (by norm_num : (0:ℝ)<1) hvm hpm hg
  have hex : ∃ θ, Matches μ X r m θ := by
    refine ⟨-a,?_,?_,?_,?_,?_⟩
    · linarith [ha.2]
    · linarith [ha.1]
    · simpa only [neg_neg] using ham
    · simpa only [mul_one,abs_of_neg ha.2] using hlo
    · simpa only [mul_one,abs_of_neg ha.2] using hhi
  exact moderateTilt_spec μ X r hex

theorem moderateTilt_tendsto_zero
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m) (μ m)) atTop (𝓝 v))
    (hgap : Tendsto (fun m => (∫ ω, X m ω ∂μ m)-r m) atTop (𝓝 0))
    (hpos : ∀ᶠ m in atTop, 0 < (∫ ω, X m ω ∂μ m)-r m) :
    Tendsto (moderateTilt μ X r) atTop (𝓝 0) := by
  have hs := eventually_matches μ X r hX hb hv hvar hgap hpos
  have hupper : Tendsto (fun m => ((∫ ω, X m ω ∂μ m)-r m)/
      (Real.exp (-2)*variance (X m) (μ m))) atTop (𝓝 0) := by
    convert! hgap.div (tendsto_const_nhds.mul hvar)
      (mul_ne_zero (Real.exp_ne_zero _) hv.ne') using 1
    simp only [zero_div]
  exact squeeze_zero' (hs.mono fun m hm => hm.1.le)
    (hs.mono fun m hm => hm.2.2.2.2) hupper

theorem moderateTilt_mul_sqrt_tendsto_atTop (N : ℕ → ℕ)
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m) (μ m)) atTop (𝓝 v))
    (hgap : Tendsto (fun m => (∫ ω, X m ω ∂μ m)-r m) atTop (𝓝 0))
    (hpos : ∀ᶠ m in atTop, 0 < (∫ ω, X m ω ∂μ m)-r m)
    (hmoderate : Tendsto (fun m => ((∫ ω, X m ω ∂μ m)-r m)*Real.sqrt (N m))
      atTop atTop) :
    Tendsto (fun m => moderateTilt μ X r m*Real.sqrt (N m)) atTop atTop := by
  have hs := eventually_matches μ X r hX hb hv hvar hgap hpos
  have hden : Tendsto (fun m => 1/(Real.exp 2*variance (X m) (μ m)))
      atTop (𝓝 (1/(Real.exp 2*v))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul hvar)
      (mul_ne_zero (Real.exp_ne_zero _) hv.ne')
  have hlow : Tendsto (fun m =>
      (((∫ ω, X m ω ∂μ m)-r m)*Real.sqrt (N m))*
        (1/(Real.exp 2*variance (X m) (μ m)))) atTop atTop :=
    hmoderate.atTop_mul_pos (by positivity) hden
  apply tendsto_atTop_mono' atTop (f₁ := fun m =>
    (((∫ ω, X m ω ∂μ m)-r m)*Real.sqrt (N m))*
      (1/(Real.exp 2*variance (X m) (μ m))))
  · filter_upwards [hs] with m hm
    have hh := mul_le_mul_of_nonneg_right hm.2.2.2.1 (Real.sqrt_nonneg (N m))
    convert! hh using 1; ring
  · exact hlow

theorem tilted_variance_tendsto
    (hX : ∀ m, Measurable (X m))
    (hb : ∀ m, ∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1)
    {v : ℝ} (hv : 0 < v)
    (hvar : Tendsto (fun m => variance (X m) (μ m)) atTop (𝓝 v))
    (hgap : Tendsto (fun m => (∫ ω, X m ω ∂μ m)-r m) atTop (𝓝 0))
    (hpos : ∀ᶠ m in atTop, 0 < (∫ ω, X m ω ∂μ m)-r m) :
    Tendsto (fun m => variance (X m)
      ((μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω))) atTop (𝓝 v) := by
  have ht := moderateTilt_tendsto_zero μ X r hX hb hv hvar hgap hpos
  have hs := eventually_matches μ X r hX hb hv hvar hgap hpos
  have hlo : Tendsto (fun m => Real.exp (-2*moderateTilt μ X r m)*
      variance (X m) (μ m)) atTop (𝓝 v) := by
    simpa only [mul_zero, Real.exp_zero, one_mul] using
      ((ht.const_mul (-2)).rexp).mul hvar
  have hhi : Tendsto (fun m => Real.exp (2*moderateTilt μ X r m)*
      variance (X m) (μ m)) atTop (𝓝 v) := by
    simpa only [mul_zero, Real.exp_zero, one_mul] using
      ((ht.const_mul 2).rexp).mul hvar
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hs] with m hm
    exact (tilted_variance_bounds (μ m) (hX m) (hb m)
      (show |-(moderateTilt μ X r m)| ≤ moderateTilt μ X r m by
        rw [abs_neg,abs_of_pos hm.1])).1
  · filter_upwards [hs] with m hm
    exact (tilted_variance_bounds (μ m) (hX m) (hb m)
      (show |-(moderateTilt μ X r m)| ≤ moderateTilt μ X r m by
        rw [abs_neg,abs_of_pos hm.1])).2

theorem exact_product_tilt (m N : ℕ) :
    Measure.pi (fun _ : Fin N =>
      (μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω)) =
    (Measure.pi (fun _ : Fin N => μ m)).tilted
      (fun z => -(moderateTilt μ X r m)*iidSum (X m) N z) :=
  pi_tilted_eq_tilted_iidSum (μ m) (X m) (-(moderateTilt μ X r m)) N

theorem actual_tilted_BerryEsseen :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m N : ℕ), Measurable (X m) →
        (∀ᵐ ω ∂μ m, X m ω ∈ Icc (0 : ℝ) 1) →
        0 < Real.sqrt ((N : ℝ)*variance (X m)
          ((μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω))) → ∀ z : ℝ,
      |cdf (((Measure.pi (fun _ : Fin N => μ m)).tilted
          (fun a => -(moderateTilt μ X r m)*iidSum (X m) N a)).map
        (fun a => (iidSum (X m) N a-(N : ℝ)*(∫ ω, X m ω ∂
          (μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω)))/
          Real.sqrt ((N : ℝ)*variance (X m)
            ((μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω))))) z -
        cdf (gaussianReal 0 1) z| ≤ C /
          Real.sqrt ((N : ℝ)*variance (X m)
            ((μ m).tilted (fun ω => -(moderateTilt μ X r m)*X m ω))) := by
  obtain ⟨C,hC,hBE⟩ := exists_tilted_iid_uniform_bound.{u}
  exact ⟨C,hC,fun m N hX hb hσ z =>
    hBE (μ m) (X m) (-(moderateTilt μ X r m)) N hX hb hσ z⟩

end FCAppendix.Affine.Uniform06.EntryTilts
