import FCAppendix.Affine.Uniform06.EntryOriginalModerate

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryGoodModerate
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.ExponentialTilt
open EntryEarlySourceLimits EntryRawSignMoments EntryRawModerate EntryOriginalModerate
open EntryUntilting EntryLaplace EntryRawGoodMoments
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

def commonFactor (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) (n : ℕ → ℕ) (m : ℕ) : ℝ :=
  Real.exp (((n m-1:ℕ):ℝ)*cgf (RawMixedSource.demand (xi i) (b m))
    (RawMixedSource.source i (joint μ V (B m))) (-theta μ i V B b n m)+
      theta μ i V B b n m*capacity (n m))

def limitConstant (i : Row) (V : Ω → ℝ) : ℝ :=
  ((gaussianPDFReal 0 1 0)/Real.sqrt (limitingVariance μ i V))*
    EntryModerateWindow.peakConstant (1-cutoff i)/eligibleHMean μ i V

omit [IsProbabilityMeasure μ] in
theorem commonFactor_positive (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (b : ℕ → ℝ) (n : ℕ → ℕ) (m : ℕ) : 0 < commonFactor μ i V B b n m := Real.exp_pos _

theorem original_good_joint_factorial_moments
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m,Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m,∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (hcap : ∀ m,∀ᵐ p ∂joint μ V (B m),p.2 ≤ ReceiptGap.cap i)
    (b : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hbt : ∀ m,b m ≤ cutoff i)
    (hb : Tendsto b atTop (𝓝 (entry i)))
    (g : ℕ → LiteralExperiment.GuardData)
    (hlo : ∀ m,0 < (g m).multiplier-(g m).radius)
    (hhi : ∀ m,0 < (g m).multiplier+(g m).radius)
    (hd : ∀ m,0 < (g m).rejectionScale)
    (hl : Tendsto (fun m => (g m).multiplier) atTop (𝓝 (entry i)))
    (hlp : ∀ m,0 < (g m).multiplier)
    (n : ℕ → ℕ) (hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    (hmoderate : Tendsto (fun m => -EntryRawCentral.center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) (A U : ℕ → ℝ) {k : ℕ} (hk : k ≤ 2) :
    Tendsto (fun m => ((n m-1:ℕ):ℝ)*(theta μ i V B b n m)^(k+2)*
      (∫ x in goodEvent i (joint μ V (B m)) (g m) (n m-1) ε (A m) (U m),
        deficitMoment k (sampleDeficit i (capacity (n m)) (b m) (g m).multiplier x)
          ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (joint μ V (B m))) (n m-1))/
            commonFactor μ i V B b n m)
      atTop (𝓝 (limitConstant μ i V*(Nat.factorial k:ℝ))) := by
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let C := fun m => capacity (n m)
  let θ := theta μ i V B b n
  let Q := commonFactor μ i V B b n
  let P := fun m => EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (N m)
  let E := fun m => goodEvent i (G m) (g m) (N m) ε (A m) (U m)
  let F := fun m => deficitMoment k ∘ sampleDeficit (N := N m) i (C m) (b m) (g m).multiplier
  have hNp : ∀ m,0 < N m := fun m => by dsimp only [N]; have := hnp m; omega
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hθ0 := (original_moderate_tilt μ i V B hV hB hvalue hadmissible hactive
    b hbp hbt hb n hnp hn hmoderate).2.1
  have hFI (m : ℕ) : Integrable (F m) (P m) :=
    Integrable.of_bound (measurable_deficitMoment
      (measurable_sampleDeficit i (C m) (b m) (g m).multiplier) k).aestronglyMeasurable _
        (ae_of_all _ fun x => by simpa only [F,Function.comp_def,Real.norm_eq_abs] using
          sampleDeficit_moment_bound i (C m) (hbp m) (g m).multiplier k x)
  have hQ : ∀ m,Real.exp (-θ m*(N m:ℝ)) ≤ Q m := fun m =>
    EntryGoodEvent.actual_untilt_factor_lower (RawMixedSource.source i (G m))
      (RawMixedSource.demand (xi i) (b m)) (RawMixedSource.measurable_demand _ _)
      (ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (hbp m))) (N m)
      (theta_bounds μ i V B b n m).1 (Nat.cast_nonneg (C m))
  have hbound (m : ℕ) : ∀ᵐ x ∂(P m).restrict (E m)ᶜ,|F m x| ≤ (N m:ℝ)^k := by
    have hCN : (C m:ℝ)+1 ≤ N m := by
      exact_mod_cast Nat.succ_le_of_lt (PhysicalRates.capacity_strictly_below_rivals (hnp m))
    exact ae_of_all _ fun x => (sampleDeficit_moment_bound i (C m) (hbp m) (g m).multiplier k x).trans
      (pow_le_pow_left₀ (by positivity) hCN k)
  have herr := EntryGoodEvent.restricted_moment_relative_error_tendsto_zero P N hN E
    (fun m => measurable_goodEvent i (G m) (g m) (N m) ε (A m) (U m)) F hFI θ Q hθ0
    (c := 2*ε^2) (C := 18) (by positivity) (by norm_num)
    (Eventually.of_forall hQ)
    (Eventually.of_forall fun m => by
      convert! goodEvent_complement_le i (G m) (g m) (N m) (hNp m) (hlo m) (hhi m) (hd m)
        hε.le (A m) (U m) using 1
      congr 2
      ring) k 1 hbound
  have hs := original_joint_factorial_moments μ i V B hV hB hvalue hadmissible hactive hcap
    b (fun m => (g m).multiplier) hbp hbt hlp hb hl n hnp hn hmoderate hk
  have herror : Tendsto (fun m =>
      |(N m:ℝ)*θ m^(k+2)*(∫ x in E m,F m x ∂P m)/Q m-
        (N m:ℝ)*θ m^(k+2)*(∫ x,F m x ∂P m)/Q m|) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => abs_nonneg _) ?_ (by simpa only [pow_one] using herr)
    intro m
    have hQp : 0 < Q m := commonFactor_positive μ i V B b n m
    have hθb := theta_bounds μ i V B b n m
    have hp : θ m^(k+2) ≤ 1 := by simpa using pow_le_pow_left₀ hθb.1 hθb.2.le (k+2)
    rw [show (N m:ℝ)*θ m^(k+2)*(∫ x in E m,F m x ∂P m)/Q m-
        (N m:ℝ)*θ m^(k+2)*(∫ x,F m x ∂P m)/Q m=
      ((N m:ℝ)*θ m^(k+2)/Q m)*((∫ x in E m,F m x ∂P m)-(∫ x,F m x ∂P m)) by ring,
      abs_mul,abs_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg (N m)) (pow_nonneg hθb.1 _)) hQp.le)]
    have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (N m))) hQp.le)
      (abs_nonneg ((∫ x in E m,F m x ∂P m)-(∫ x,F m x ∂P m)))
    simpa only [mul_one,div_mul_eq_mul_div] using hh
  exact tendsto_of_abs_sub_tendsto hs herror

lemma scaled_ratio_identity {N θ Q P A B : ℝ}
    (hN : N ≠ 0) (hθ : θ ≠ 0) (hQ : Q ≠ 0) :
    (N*θ^3*A/Q)^2/((N*θ^2*P/Q)*(N*θ^4*B/Q))=A^2/(P*B) := by
  by_cases hP : P=0
  · simp [hP]
  by_cases hB : B=0
  · simp [hB]
  field_simp [hN,hθ,hQ,hP,hB]

theorem ratio_of_factorial_moments (N : ℕ → ℕ) (hNp : ∀ m,0 < N m)
    (θ Q M0 M1 M2 : ℕ → ℝ) (hθ : ∀ᶠ m in atTop,0 < θ m)
    (hQ : ∀ m,0 < Q m) {C : ℝ} (hC : 0 < C)
    (h0 : Tendsto (fun m => (N m:ℝ)*θ m^2*M0 m/Q m) atTop (𝓝 C))
    (h1 : Tendsto (fun m => (N m:ℝ)*θ m^3*M1 m/Q m) atTop (𝓝 C))
    (h2 : Tendsto (fun m => (N m:ℝ)*θ m^4*M2 m/Q m) atTop (𝓝 (2*C))) :
    (∀ᶠ m in atTop,0 < M0 m ∧ 0 < M1 m ∧ 0 < M2 m) ∧
      Tendsto (fun m => (M1 m)^2/(M0 m*M2 m)) atTop (𝓝 (1/2:ℝ)) := by
  have hpositive : ∀ᶠ m in atTop,0 < M0 m ∧ 0 < M1 m ∧ 0 < M2 m := by
    filter_upwards [hθ,h0.eventually_const_lt hC,h1.eventually_const_lt hC,
      h2.eventually_const_lt (show 0 < 2*C by positivity)] with m hθm h0m h1m h2m
    have hNr : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
    constructor
    · exact pos_of_mul_pos_right ((div_pos_iff_of_pos_right (hQ m)).mp h0m) (by positivity)
    · constructor
      · exact pos_of_mul_pos_right ((div_pos_iff_of_pos_right (hQ m)).mp h1m) (by positivity)
      · exact pos_of_mul_pos_right ((div_pos_iff_of_pos_right (hQ m)).mp h2m) (by positivity)
  refine ⟨hpositive,?_⟩
  have hh := (h1.pow 2).div (h0.mul h2) (by positivity : C*(2*C) ≠ 0)
  have he : C^2/(C*(2*C))=(1/2:ℝ) := by field_simp [hC.ne']
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hθ] with m hθm
  exact scaled_ratio_identity (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hNp m))) hθm.ne' (hQ m).ne'

end FCAppendix.Affine.Uniform06.EntryGoodModerate
