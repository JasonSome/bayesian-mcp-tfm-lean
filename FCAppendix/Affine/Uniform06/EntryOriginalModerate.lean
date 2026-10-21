import FCAppendix.Affine.Uniform06.EntryModerateProfile

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryOriginalModerate
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.WeightedSampling FCAppendix.ExponentialTilt
open EntryEarlySourceLimits EntryRawSignMoments EntryRawFairKernel EntryRawModerate
open EntryUntilting EntryLaplace EntryModerateAveraging EntryRawTiltedFiber
open EntryModerateProfile
open scoped BigOperators

lemma theta_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ) (b : ℕ → ℝ) (n : ℕ → ℕ) (m : ℕ) :
    theta μ i V B b n m∈Ico (0:ℝ) 1 := by
  unfold theta EntryTilts.moderateTilt
  split_ifs with h
  · have hs := Classical.choose_spec h
    exact ⟨hs.1.le,hs.2.1⟩
  · norm_num

def samplingFloor (i : Row) : ℝ :=
  min (1/4) ((entry i-ReceiptGap.threshold i)/(2*xi i*ReceiptGap.cap i))

lemma samplingFloor_geometry (i : Row) :
    0 < samplingFloor i ∧ samplingFloor i ≤ 1/2 ∧
      0 ≤ 1-xi i*(1/2-samplingFloor i) ∧
      (1-xi i*(1/2-samplingFloor i))*ReceiptGap.cap i < entry i := by
  have hξ := xi_pos i
  have hU := (ReceiptGap.cap_bounds i).1
  have ht := cutoff_pos i
  have hgap := ReceiptGap.receipt_entry_margin i
  have hg : 0 < entry i-ReceiptGap.threshold i := by linarith
  have ha : 0 < samplingFloor i := lt_min (by norm_num) (div_pos hg (by positivity))
  have ha4 : samplingFloor i ≤ 1/4 := min_le_left _ _
  have ha2 : samplingFloor i ≤ 1/2 := by linarith
  have hξ1 : xi i ≤ 1 := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hfac : 0 ≤ 1-xi i*(1/2-samplingFloor i) := by
    have hm := mul_le_mul_of_nonneg_left (show 1/2-samplingFloor i ≤ (1/2:ℝ) by linarith) hξ.le
    nlinarith
  have haB := min_le_right (1/4:ℝ) ((entry i-ReceiptGap.threshold i)/(2*xi i*ReceiptGap.cap i))
  have ham : samplingFloor i*(2*xi i*ReceiptGap.cap i) ≤ entry i-ReceiptGap.threshold i :=
    (le_div_iff₀ (by positivity : 0 < 2*xi i*ReceiptGap.cap i)).mp haB
  refine ⟨ha,ha2,hfac,?_⟩
  have he : (1-xi i*(1/2-samplingFloor i))*ReceiptGap.cap i=
      ReceiptGap.threshold i+xi i*samplingFloor i*ReceiptGap.cap i := by
    unfold ReceiptGap.threshold
    ring
  rw [he]
  nlinarith

lemma weightedMonomial_cap_bound {θ W : ℝ} (hθ : 0 ≤ θ) (C k : ℕ) (hW : W ≤ C) :
    |weightedMonomial θ k W| ≤ ((C:ℝ)+1)^k := by
  by_cases hWp : 0 < W
  · rw [weightedMonomial,if_pos hWp,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (pow_nonneg hWp.le _)]
    have he : Real.exp (-θ*W) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hp : W^k ≤ ((C:ℝ)+1)^k := pow_le_pow_left₀ hWp.le (by linarith) k
    exact (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans (by nlinarith [pow_nonneg (show 0 ≤ (C:ℝ)+1 by positivity) k])
  · simp [weightedMonomial,hWp]
    positivity

lemma weighted_error_cap_bound (i : Row) {N C : ℕ} (hN : 0 < N) (hC : C ≤ N)
    {b θ c : ℝ} (hb : 0 < b) (hθ : 0 ≤ θ) (hc : 0 ≤ c)
    (l : ℝ) (k : ℕ) (r : Fin N → RowRival) :
    |Real.sqrt (N:ℝ)*weightedKernel i C b l θ k r-
      c*weightedMonomial θ (k+1) (balanced i C b r)| ≤
        ((1+c)*2^(k+1))*(N:ℝ)^(k+1) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hs : Real.sqrt (N:ℝ) ≤ N := by
    nlinarith [Real.sq_sqrt hNr.le,Real.sqrt_nonneg (N:ℝ)]
  have hCN : (C:ℝ)+1 ≤ 2*(N:ℝ) := by
    have hcN : (C:ℝ) ≤ N := by exact_mod_cast hC
    linarith
  have hkbound := weightedKernel_bound i C hb hθ l k r
  have hmbound := weightedMonomial_cap_bound hθ C (k+1) (balanced_le_capacity i C hb r)
  have ht := abs_sub (Real.sqrt (N:ℝ)*weightedKernel i C b l θ k r)
    (c*weightedMonomial θ (k+1) (balanced i C b r))
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_mul,abs_of_nonneg hc] at ht
  have hpow0 := pow_le_pow_left₀ (show 0 ≤ (C:ℝ)+1 by positivity) hCN k
  have hpow1 := pow_le_pow_left₀ (show 0 ≤ (C:ℝ)+1 by positivity) hCN (k+1)
  have ha : Real.sqrt (N:ℝ)*|weightedKernel i C b l θ k r| ≤ (N:ℝ)*(2*(N:ℝ))^k :=
    mul_le_mul hs (hkbound.trans hpow0) (abs_nonneg _) hNr.le
  have hb' := mul_le_mul_of_nonneg_left (hmbound.trans hpow1) hc
  calc
    _ ≤ (N:ℝ)*(2*(N:ℝ))^k+c*(2*(N:ℝ))^(k+1) := ht.trans (add_le_add ha hb')
    _ ≤ ((1+c)*2^(k+1))*(N:ℝ)^(k+1) := by
      rw [mul_pow,mul_pow,pow_succ,pow_succ]
      nlinarith [mul_nonneg (pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) k) (pow_nonneg hNr.le k)]

section Original
variable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem original_joint_factorial_moments
    (i : Row) (V : Ω → ℝ) (B : ℕ → Ω → ℝ)
    (hV : Measurable V) (hB : ∀ m,Measurable (B m))
    (hvalue : μ.map V=LowChernoff.conditionalValueLaw i)
    (hadmissible : ∀ m,∀ᵐ ω ∂μ,B m ω ≤ V ω)
    (hactive : ∀ᵐ ω ∂μ,entry i < V ω → Tendsto (fun m => B m ω) atTop
      (𝓝 (ActiveGraphComponent.activeBid i (V ω))))
    (hcap : ∀ m,∀ᵐ p ∂joint μ V (B m),p.2 ≤ ReceiptGap.cap i)
    (b l : ℕ → ℝ) (hbp : ∀ m,0 < b m) (hbt : ∀ m,b m ≤ cutoff i)
    (hlp : ∀ m,0 < l m)
    (hb : Tendsto b atTop (𝓝 (entry i))) (hl : Tendsto l atTop (𝓝 (entry i)))
    (n : ℕ → ℕ) (hnp : ∀ m,4 ≤ n m) (hn : Tendsto n atTop atTop)
    (hmoderate : Tendsto (fun m => -EntryRawCentral.center i (joint μ V (B m)) (n m-1)
      (capacity (n m)) (b m)) atTop atTop)
    {k : ℕ} (hk : k ≤ 2) :
    let G := fun m => joint μ V (B m)
    let θ := theta μ i V B b n
    let Q := fun m => Real.exp (((n m-1:ℕ):ℝ)*
      cgf (RawMixedSource.demand (xi i) (b m)) (RawMixedSource.source i (G m)) (-θ m)+
        θ m*capacity (n m))
    Tendsto (fun m => ((n m-1:ℕ):ℝ)*θ m^(k+2)*
      (∫ x : EntryIIDCentral.Row (Ω := RowRival) (n m-1),
        deficitMoment k (sampleDeficit i (capacity (n m)) (b m) (l m) x)
          ∂EntryIIDCentral.rowLaw (RawMixedSource.source i (G m)) (n m-1))/Q m)
      atTop (𝓝 ((((gaussianPDFReal 0 1 0)/Real.sqrt (limitingVariance μ i V))*
        EntryModerateWindow.peakConstant (1-cutoff i)/eligibleHMean μ i V)*(Nat.factorial k:ℝ))) := by
  classical
  let G := fun m => joint μ V (B m)
  letI (m : ℕ) : IsProbabilityMeasure (G m) :=
    Measure.isProbabilityMeasure_map (hV.prodMk (hB m)).aemeasurable
  let N := fun m => n m-1
  let C := fun m => capacity (n m)
  let θ := theta μ i V B b n
  let R := fun m => rawTilt i (G m) (b m) (-θ m)
  let P := fun m => Measure.pi (fun _ : Fin (N m) => R m)
  letI (m : ℕ) : IsProbabilityMeasure (R m) := rawTilt_probability i (G m) (hbp m) (-θ m)
  have hNp : ∀ m,0 < N m := fun m => by dsimp only [N]; have := hnp m; omega
  have hN : Tendsto N atTop atTop := PhysicalRates.rivals_tendsto.comp hn
  have hC : ∀ m,C m ≤ N m := fun m => (PhysicalRates.capacity_strictly_below_rivals (hnp m)).le
  have hθbounds := fun m => theta_bounds μ i V B b n m
  have htilt := original_moderate_tilt μ i V B hV hB hvalue hadmissible hactive
    b hbp hbt hb n hnp hn hmoderate
  have hθp : ∀ᶠ m in atTop,0 < θ m := htilt.1.mono (fun _ h => h.1)
  have hθ0 : Tendsto θ atTop (𝓝 0) := htilt.2.1
  have hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop := htilt.2.2.1
  have hvar : 0 < limitingVariance μ i V :=
    limitingVariance_positive μ i V B hV hB hvalue hadmissible hactive b hbp hbt hb
  let τ := 1-cutoff i
  let v := eligibleMass μ i V
  let d := eligibleHMass μ i V
  let hbar := eligibleHMean μ i V
  let a := samplingFloor i
  let S := (gaussianPDFReal 0 1 0)/Real.sqrt (limitingVariance μ i V)
  have hτ : 0 < τ := by dsimp [τ]; linarith [cutoff_lt_one i]
  have hv : 0 < v := eligibleMass_positive μ i V hV hvalue
  have hhbar : 0 < hbar := eligibleHMean_positive μ i V hV hvalue
  have ha := samplingFloor_geometry i
  have hprofile := original_tilted_profile_limits μ i V B hV hB hvalue hadmissible hactive
    b l (fun m => -θ m) hbp hlp hb hl (by simpa using hθ0.neg)
  have hupper : Tendsto (fun m => ∫ r,upper r ∂ R m) atTop (𝓝 τ) := by
    have hmean : Tendsto (fun m => ∫ r,upper r ∂ RawMixedSource.source i (G m)) atTop (𝓝 τ) := by
      simpa only [original_upper_mean] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ))
    exact small_tilt_mean_tendsto (fun m => RawMixedSource.source i (G m))
      (fun m => RawMixedSource.demand (xi i) (b m)) (fun _ => upper)
      (fun m => RawMixedSource.measurable_demand _ _) (fun _ => measurable_upper)
      (fun m => ae_of_all _ (RawMixedSource.demand_bounds (xi_pos i) (hbp m)))
      (fun _ => ae_of_all _ upper_bounds) (fun m => -θ m) (by simpa using hθ0.neg) hmean
  have hmean : ∀ j : Fin 3,Tendsto (fun m => ∫ r,EntryModerateProfile.statistics i (b m) (l m) j r ∂ R m)
      atTop (𝓝 (![τ,v,d] j)) := by
    intro j
    fin_cases j
    · exact hupper
    · exact hprofile.1
    · exact hprofile.2
  let E := fun m => EntryModerateProfile.event (R m) i (b m) (l m) (N m) a τ v d
  let e := fun m => EntryModerateProfile.meanError (R m) i (b m) (l m) (N m) τ v d
  have hE := fun m => measurable_event (R m) i (b m) (l m) (N m) a τ v d
  have he := meanError_tendsto R i b l N hN hmean
  have hrow : ∀ᶠ m in atTop,∀ᵐ r ∂P m,∀ j,hs i (b m) r j∈Icc a (1/2:ℝ) := by
    filter_upwards [hb.eventually_const_lt ha.2.2.2] with m hm
    exact actual_h_profile_ae i (G m) (hbp m) ha.1 ha.2.1 ha.2.2.1 hm.le (hcap m) (-θ m) (N m)
  have hbadpoly := event_polynomial_bad R i b l N hN hNp hbp hv hmean hrow (k+2)
  let w := fun m => weights (N := N m) i (b m) (l m)
  let h := fun m => hs (N := N m) i (b m)
  let H := fun m => upperCount (N := N m)
  let W := fun m => balanced (N := N m) i (C m) (b m)
  let c := EntryModerateWindow.peakConstant τ/(((k:ℝ)+1)*hbar)
  have hc : 0 < c := div_pos (EntryModerateWindow.peak_constant_pos hτ) (by positivity)
  have hfair (m : ℕ) (r : Fin (N m) → RowRival) :
      weightedFair w h H W N θ k m r =
        Real.sqrt (N m:ℝ)*weightedKernel i (C m) (b m) (l m) (θ m) k r := by
    dsimp only [weightedFair,w,h,H,W,weightedKernel,kernel]
    ring
  have hFI (m : ℕ) : Integrable (weightedFair w h H W N θ k m) (P m) := by
    have hm : Measurable (weightedFair w h H W N θ k m) :=
      by
        change Measurable (fun r => weightedFair w h H W N θ k m r)
        simp_rw [hfair]
        exact (measurable_weightedKernel i (C m) (b m) (l m) (θ m) k).const_mul (Real.sqrt (N m:ℝ))
    apply Integrable.of_bound hm.aestronglyMeasurable (Real.sqrt (N m:ℝ)*((C m:ℝ)+1)^k)
    exact ae_of_all _ fun r => by
      rw [Real.norm_eq_abs]
      rw [hfair]
      rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (weightedKernel_bound i (C m) (hbp m) (hθbounds m).1 (l m) k r)
        (Real.sqrt_nonneg _)
  have hscalar : ∀ q : ℝ,0 < q → ∀ j : ℕ,j ≤ 3 →
      Tendsto (scaledScalar P W N θ q j) atTop (𝓝 (S*(Nat.factorial j:ℝ))) := by
    intro q hq j hj
    have ht := original_scalar_factorial_moments μ i V B hV hB hvalue hadmissible hactive
      b hbp hbt hb n hnp hn hmoderate hq hj
    have hvroot := htilt.2.2.2.sqrt
    have hl := ht.div hvroot (Real.sqrt_pos.2 hvar).ne'
    have hl' : Tendsto (fun m =>
        (Real.sqrt ((N m:ℝ)*variance (RawMixedSource.demand (xi i) (b m)) (R m))*
          (q*θ m)^(j+1)*(∫ r : Fin (N m) → RowRival,
            weightedMonomial (q*θ m) j (W m r) ∂P m))/
          Real.sqrt (variance (RawMixedSource.demand (xi i) (b m)) (R m)))
        atTop (𝓝 (S*(Nat.factorial j:ℝ))) := by
      convert! hl using 1
      dsimp [S]
      ring
    apply hl'.congr'
    filter_upwards [htilt.2.2.2.eventually_const_lt hvar] with m hvm
    dsimp [scaledScalar,S,W]
    rw [Real.sqrt_mul (Nat.cast_nonneg _)]
    have hvn : Real.sqrt (variance (RawMixedSource.demand (xi i) (b m)) (R m)) ≠ 0 :=
      (Real.sqrt_pos.2 hvm).ne'
    field_simp [hvn]
  have hbad : Tendsto (fun m => Real.sqrt (N m:ℝ)*θ m^(k+2)*
      (∫ r,if r∈E m then 0 else |weightedFair w h H W N θ k m r-
        c*weightedMonomial (θ m) (k+1) (W m r)| ∂P m)) atTop (𝓝 0) := by
    have hlim := hbadpoly.const_mul ((1+c)*2^(k+1))
    apply squeeze_zero (fun m => by
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hθbounds m).1 _))
        (integral_nonneg (fun r => by split_ifs <;> positivity))) ?_ (by simpa using hlim)
    intro m
    have hNr : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
    have hN1 : (1:ℝ) ≤ N m := by exact_mod_cast hNp m
    have hs : Real.sqrt (N m:ℝ) ≤ N m := by
      nlinarith [Real.sq_sqrt hNr.le,Real.sqrt_nonneg (N m:ℝ)]
    have hθpow : θ m^(k+2) ≤ 1 := by
      simpa using pow_le_pow_left₀ (hθbounds m).1 (hθbounds m).2.le (k+2)
    have hn : Real.sqrt (N m:ℝ)*θ m^(k+2) ≤ N m :=
      (mul_le_mul_of_nonneg_left hθpow (Real.sqrt_nonneg _)).trans (by simpa using hs)
    have hmeas : Measurable (fun r => |weightedFair w h H W N θ k m r-
      c*weightedMonomial (θ m) (k+1) (W m r)|) := by
      simpa only [hfair,Pi.sub_apply] using (((measurable_weightedKernel i (C m) (b m) (l m) (θ m) k).const_mul _).sub
        ((EntryWeightedLaplace.measurable_weightedMonomial _ _ (measurable_balanced i (C m) (b m))).const_mul c)).abs
    have hpoint (r : Fin (N m) → RowRival) :
        |weightedFair w h H W N θ k m r-c*weightedMonomial (θ m) (k+1) (W m r)| ≤
          ((1+c)*2^(k+1))*(N m:ℝ)^(k+1) :=
      by simpa only [hfair] using weighted_error_cap_bound i (hNp m) (hC m) (hbp m) (hθbounds m).1 hc.le (l m) k r
    have hi : Integrable (fun r => |weightedFair w h H W N θ k m r-
        c*weightedMonomial (θ m) (k+1) (W m r)|) (P m) :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ fun r => by
        simpa only [Real.norm_eq_abs,abs_abs] using hpoint r)
    have hp : (∫ r,if r∈E m then 0 else |weightedFair w h H W N θ k m r-
        c*weightedMonomial (θ m) (k+1) (W m r)| ∂P m) ≤
        (((1+c)*2^(k+1))*(N m:ℝ)^(k+1))*(P m).real (E m)ᶜ := by
      have heq : (fun r => if r∈E m then 0 else |weightedFair w h H W N θ k m r-
          c*weightedMonomial (θ m) (k+1) (W m r)|)=
        (E m)ᶜ.indicator (fun r => |weightedFair w h H W N θ k m r-
          c*weightedMonomial (θ m) (k+1) (W m r)|) := by
        funext r
        by_cases hr : r∈E m <;> simp [hr]
      rw [heq,integral_indicator (hE m).compl]
      have ht := norm_integral_le_of_norm_le_const (μ := (P m).restrict (E m)ᶜ)
        (f := fun r => |weightedFair w h H W N θ k m r-c*weightedMonomial (θ m) (k+1) (W m r)|)
        (ae_of_all _ fun r => by simpa only [Real.norm_eq_abs,abs_abs] using hpoint r)
      have hn0 : 0 ≤ ∫ r : Fin (N m) → RowRival,
          |weightedFair w h H W N θ k m r-c*weightedMonomial (θ m) (k+1) (W m r)|
            ∂(P m).restrict (E m)ᶜ := integral_nonneg (fun _ => abs_nonneg _)
      simpa only [Real.norm_eq_abs,abs_of_nonneg hn0,Measure.real,Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter,mul_comm] using ht
    have hm0 : 0 ≤ (∫ r,if r∈E m then 0 else |weightedFair w h H W N θ k m r-
        c*weightedMonomial (θ m) (k+1) (W m r)| ∂P m) := by
      apply integral_nonneg
      intro r
      change (0:ℝ) ≤ if r∈E m then 0 else |weightedFair w h H W N θ k m r-
        c*weightedMonomial (θ m) (k+1) (W m r)|
      split_ifs <;> positivity
    have hh := mul_le_mul hn hp hm0 hNr.le
    convert! hh using 1
    simp only [pow_succ]
    ring
  have haverage := averaged_fair_moment P w h H W (fun m => measurable_balanced i (C m) (b m))
    N hNp hN θ e hθp hθ0 hθN he E hE ha.1 hτ hv hhbar
    (fun m r hr => event_profile (R m) i (b m) (l m) (N m) (hNp m) hv r hr)
    hk hFI hscalar hbad
  apply haverage.congr
  intro m
  rw [untilted_moment_eq_raw_kernel i (G m) (C m) (hbp m) (hθbounds m).1 (l m) k (N m)]
  dsimp [weightedKernel,kernel]
  field_simp [(Real.exp_pos _).ne']
  ring

end Original
end FCAppendix.Affine.Uniform06.EntryOriginalModerate
