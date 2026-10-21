import FCAppendix.Affine.Uniform06.EntryRawFairKernel

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryModerateProfile
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.WeightedSampling FCAppendix.ExponentialTilt
open EntryEarlySourceLimits EntryRawSignMoments EntryRawFairKernel
open EntryEmpiricalRatio EntryProfileMean EntryRawTiltedFiber WeightedMoments
open scoped BigOperators

variable {N : ℕ}

def radius (N : ℕ) : ℝ := 1/Real.sqrt (Real.sqrt (N:ℝ))

lemma radius_pos (hN : 0 < N) : 0 < radius N := by
  unfold radius
  positivity

lemma radius_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) :
    Tendsto (fun m => radius (N m)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)))

lemma radius_exponent (hN : 0 < N) : (N:ℝ)*radius N^2=Real.sqrt (N:ℝ) := by
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.2 hNr
  have hs2 : 0 < Real.sqrt (Real.sqrt (N:ℝ)) := Real.sqrt_pos.2 hs
  unfold radius
  rw [div_pow,one_pow,Real.sq_sqrt hs.le]
  calc
    _ = (N:ℝ)/Real.sqrt (N:ℝ) := by ring
    _ = _ := (div_eq_iff (ne_of_gt hs)).mpr (by nlinarith [Real.sq_sqrt hNr.le])

lemma polynomial_radius_tail (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (j : ℕ) :
    Tendsto (fun m => (N m:ℝ)^j*Real.exp (-2*Real.sqrt (N m:ℝ))) atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2*j:ℝ) 2 (by norm_num)).comp hs
  apply ht.congr
  intro m
  change (Real.sqrt (N m:ℝ))^(2*(j:ℝ))*Real.exp (-2*Real.sqrt (N m:ℝ)) = _
  rw [show (2*(j:ℝ))=((2*j:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    pow_mul,Real.sq_sqrt (Nat.cast_nonneg _)]

def statistics (i : Row) (b l : ℝ) : Fin 3 → RowRival → ℝ :=
  ![upper,rawWeight i l,fun r => rawWeight i l r*rawH i b r]

lemma statistics_measurable (i : Row) (b l : ℝ) :
    ∀ j,Measurable (statistics i b l j) := by
  intro j
  fin_cases j
  · exact measurable_upper
  · exact measurable_rawWeight i l
  · exact (measurable_rawWeight i l).mul (measurable_rawH i b)

lemma statistics_unit (i : Row) {b : ℝ} (hb : 0 < b) (l : ℝ) (j : Fin 3) (r : RowRival) :
    statistics i b l j r∈Icc (0:ℝ) 1 := by
  fin_cases j
  · exact upper_bounds r
  · exact rawWeight_bounds i l r
  · have hw := rawWeight_bounds i l r
    have hh := rawH_bounds i hb r
    change rawWeight i l r*rawH i b r∈Icc (0:ℝ) 1
    exact ⟨mul_nonneg hw.1 hh.1,
      (mul_le_mul hw.2 hh.2 hh.1 (by norm_num)).trans (by norm_num)⟩

def deviation (R : Measure RowRival) (i : Row) (b l : ℝ) (N : ℕ) (τ v d : ℝ) : ℝ :=
  radius N+(∑ j : Fin 3,|(∫ r,statistics i b l j r ∂ R)-(![τ,v,d] j)|)+1/(N:ℝ)

def meanError (R : Measure RowRival) (i : Row) (b l : ℝ) (N : ℕ) (τ v d : ℝ) : ℝ :=
  deviation R i b l N τ v d*(1+2/v+2*|d| /v^2)

def event (R : Measure RowRival) (i : Row) (b l : ℝ) (N : ℕ) (a τ v d : ℝ) : Set (Fin N → RowRival) :=
  RivalGood.good R (statistics i b l) N (radius N) ∩
    {r | (∀ j,hs i b r j∈Icc a (1/2:ℝ)) ∧ deviation R i b l N τ v d ≤ v/2}

lemma measurable_event (R : Measure RowRival) (i : Row) (b l : ℝ) (N : ℕ) (a τ v d : ℝ) :
    MeasurableSet (event R i b l N a τ v d) := by
  apply (RivalGood.measurable_good R _ (statistics_measurable i b l) N _).inter
  have he : {r : Fin N → RowRival | (∀ j,hs i b r j∈Icc a (1/2:ℝ)) ∧
      deviation R i b l N τ v d ≤ v/2}=
      (⋂ j : Fin (N+1),{r | hs i b r j∈Icc a (1/2:ℝ)}) ∩
        {r | deviation R i b l N τ v d ≤ v/2} := by
    ext r
    simp
  rw [he]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro j
    exact measurableSet_Icc.preimage ((measurable_pi_apply j).comp (measurable_hs i b))
  · exact MeasurableSet.const _

lemma deviation_nonneg (R : Measure RowRival) (i : Row) (b l : ℝ)
    (N : ℕ) (hN : 0 < N) (τ v d : ℝ) : 0 ≤ deviation R i b l N τ v d := by
  have hr := (radius_pos hN).le
  unfold deviation
  positivity

theorem event_profile (R : Measure RowRival) (i : Row) (b l : ℝ)
    (N : ℕ) (hN : 0 < N) {a τ v d : ℝ} (hv : 0 < v)
    (r : Fin N → RowRival) (hr : r∈event R i b l N a τ v d) :
    (∀ j,hs i b r j∈Icc a (1/2:ℝ)) ∧
    |(upperCount r:ℝ)/(N:ℝ)-τ| ≤ meanError R i b l N τ v d ∧
    |totalWeight (weights i b l r)/(N:ℝ)-v| ≤ meanError R i b l N τ v d ∧
    |weightedMean (weights i b l r) (hs i b r)-d/v| ≤ meanError R i b l N τ v d := by
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr hN
  let e := deviation R i b l N τ v d
  have he0 : 0 ≤ e := deviation_nonneg R i b l N hN τ v d
  have heSmall : e ≤ v/2 := hr.2.2
  have herr (j : Fin 3) : |RivalGood.empirical (statistics i b l) N r j-(![τ,v,d] j)| ≤
      radius N+|(∫ x,statistics i b l j x ∂ R)-(![τ,v,d] j)| := by
    have ht := abs_sub_le (RivalGood.empirical (statistics i b l) N r j)
      (∫ x,statistics i b l j x ∂ R) (![τ,v,d] j)
    have hg := (hr.1 j).le
    linarith
  have hsum (j : Fin 3) : |(∫ x,statistics i b l j x ∂ R)-(![τ,v,d] j)| ≤
      ∑ j : Fin 3,|(∫ x,statistics i b l j x ∂ R)-(![τ,v,d] j)| :=
    Finset.single_le_sum (f := fun j : Fin 3 =>
      |(∫ x,statistics i b l j x ∂ R)-(![τ,v,d] j)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  have h0 : |(upperCount r:ℝ)/(N:ℝ)-τ| ≤ e := by
    have hh := herr 0
    rw [upperCount_cast]
    dsimp [RivalGood.empirical,statistics] at hh
    dsimp [e,deviation]
    have := hsum 0
    change |(∫ x,EntryRawFairKernel.upper x ∂ R)-τ| ≤
      (∑ j : Fin 3,|(∫ x,statistics i b l j x ∂ R)-(![τ,v,d] j)|) at this
    linarith [one_div_nonneg.mpr hNr.le]
  have h1 : |totalWeight (weights i b l r)/(N:ℝ)-v| ≤ e := by
    have hh := herr 1
    have hw := EntryRawCentral.focalWeight_bounds i b l
    rw [weights,totalWeight_profile,add_div]
    have habs := abs_add_le ((∑ j,rawWeight i l (r j))/(N:ℝ)-v) (EntryRawCentral.focalWeight i b l/(N:ℝ))
    rw [abs_div,abs_of_nonneg hw.1,abs_of_pos hNr] at habs
    have hdiv := div_le_div_of_nonneg_right hw.2 hNr.le
    have := hsum 1
    dsimp [RivalGood.empirical,statistics] at hh
    dsimp [e,deviation]
    change |(∫ x,rawWeight i l x ∂ R)-v| ≤ _ at this
    have heq : EntryRawCentral.focalWeight i b l/(N:ℝ)+(∑ j,rawWeight i l (r j))/(N:ℝ)-v=
      ((∑ j,rawWeight i l (r j))/(N:ℝ)-v)+EntryRawCentral.focalWeight i b l/(N:ℝ) := by ring
    rw [heq]
    linarith
  let Vt := totalWeight (weights i b l r)/(N:ℝ)
  let Dt := ((EntryRawCentral.focalWeight i b l)*(1/2)+∑ j,rawWeight i l (r j)*rawH i b (r j))/(N:ℝ)
  have h2 : |Dt-d| ≤ e := by
    have hh := herr 2
    have hw := EntryRawCentral.focalWeight_bounds i b l
    have hw0 : 0 ≤ EntryRawCentral.focalWeight i b l*(1/2) :=
      mul_nonneg hw.1 (by norm_num)
    have hw1 : EntryRawCentral.focalWeight i b l*(1/2) ≤ 1 := by linarith [hw.2]
    have habs := abs_add_le ((∑ j,rawWeight i l (r j)*rawH i b (r j))/(N:ℝ)-d)
      (EntryRawCentral.focalWeight i b l*(1/2)/(N:ℝ))
    rw [abs_div,abs_of_nonneg hw0,abs_of_pos hNr] at habs
    have hdiv := div_le_div_of_nonneg_right hw1 hNr.le
    have := hsum 2
    dsimp [RivalGood.empirical,statistics] at hh
    dsimp [Dt,e,deviation]
    change |(∫ x,rawWeight i l x*rawH i b x ∂ R)-d| ≤ _ at this
    rw [add_div]
    have heq : EntryRawCentral.focalWeight i b l*(1/2)/(N:ℝ)+
      (∑ j,rawWeight i l (r j)*rawH i b (r j))/(N:ℝ)-d=
      ((∑ j,rawWeight i l (r j)*rawH i b (r j))/(N:ℝ)-d)+
        EntryRawCentral.focalWeight i b l*(1/2)/(N:ℝ) := by ring
    rw [heq]
    linarith
  have hVt : v/2 ≤ Vt := by have := (abs_le.mp h1).1; dsimp [Vt]; linarith
  have hrat := ratio_error_bound (u := Dt) (v := Vt) (a := d) (d := v)
    (show 0 < v/2 by positivity) (show v/2 ≤ v by linarith)
  rw [max_eq_right hVt] at hrat
  have hquot : Dt/Vt=weightedMean (weights i b l r) (hs i b r) := by
    rw [weights,hs,weightedMean_profile]
    dsimp [Dt,Vt]
    rw [weights,totalWeight_profile]
    by_cases hz : EntryRawCentral.focalWeight i b l+∑ j,rawWeight i l (r j)=0
    · simp [hz]
    · field_simp [hNr.ne',hz]
  rw [hquot] at hrat
  have hfac : 1 ≤ 1+2/v+2*|d| /v^2 := by
    have h2v : 0 ≤ 2/v := div_nonneg (by norm_num) hv.le
    have hdv : 0 ≤ 2*|d| /v^2 := by positivity
    linarith
  have her : e ≤ meanError R i b l N τ v d := by
    change e ≤ e*(1+2/v+2*|d| /v^2)
    nlinarith
  refine ⟨hr.2.1,h0.trans her,h1.trans her,?_⟩
  apply hrat.trans
  have hdv : 0 ≤ (v/2)*v := by positivity
  have hh1 := div_le_div_of_nonneg_right h2 (show 0 ≤ v/2 by positivity)
  have hh2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg d)) hdv
  have hbound : e/(v/2)+|d| *e/((v/2)*v) ≤ e*(1+2/v+2*|d| /v^2) := by
    have heq : e/(v/2)+|d| *e/((v/2)*v)=e*(2/v+2*|d| /v^2) := by
      field_simp [hv.ne']
    rw [heq]
    nlinarith
  exact (add_le_add hh1 hh2).trans hbound

theorem event_complement_le (R : Measure RowRival) [IsProbabilityMeasure R]
    (i : Row) {b : ℝ} (hb : 0 < b) (l : ℝ) (N : ℕ) (hN : 0 < N)
    (a τ v d : ℝ)
    (hrow : ∀ᵐ r ∂Measure.pi (fun _ : Fin N => R),∀ j,hs i b r j∈Icc a (1/2:ℝ))
    (hsmall : deviation R i b l N τ v d ≤ v/2) :
    (Measure.pi (fun _ : Fin N => R)).real (event R i b l N a τ v d)ᶜ ≤
      6*Real.exp (-2*Real.sqrt (N:ℝ)) := by
  have he : (event R i b l N a τ v d)ᶜ =ᵐ[Measure.pi (fun _ : Fin N => R)]
      (RivalGood.good R (statistics i b l) N (radius N))ᶜ := by
    filter_upwards [hrow] with r hr
    change (¬ (r∈RivalGood.good R (statistics i b l) N (radius N) ∧
      (∀ j,hs i b r j∈Icc a (1/2:ℝ)) ∧ deviation R i b l N τ v d ≤ v/2)) =
      (¬ r∈RivalGood.good R (statistics i b l) N (radius N))
    apply propext
    constructor
    · intro h hg
      exact h ⟨hg,hr,hsmall⟩
    · intro h hg
      exact h hg.1
  have hm := congrArg ENNReal.toReal (measure_congr he)
  change _ ≤ _
  rw [show (Measure.pi (fun _ : Fin N => R)).real (event R i b l N a τ v d)ᶜ=
      (Measure.pi (fun _ : Fin N => R)).real
        (RivalGood.good R (statistics i b l) N (radius N))ᶜ from hm]
  have hh := RivalGood.good_complement_le R (statistics i b l)
    (fun j => (statistics_measurable i b l j).aemeasurable)
    (fun j => ae_of_all _ (statistics_unit i hb l j)) N hN (radius_pos hN).le
  have he : -2*(N:ℝ)*radius N^2= -2*Real.sqrt (N:ℝ) := by
    rw [show -2*(N:ℝ)*radius N^2= -2*((N:ℝ)*radius N^2) by ring,radius_exponent hN]
  simpa only [Fintype.card_fin,Nat.cast_ofNat,he,show (2:ℝ)*3=6 by norm_num] using hh

theorem actual_h_profile_ae (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {b U a : ℝ} (hb : 0 < b) (_ha : 0 < a) (ha2 : a ≤ 1/2)
    (hfactor : 0 ≤ 1-xi i*(1/2-a)) (hgap : (1-xi i*(1/2-a))*U ≤ b)
    (hcap : ∀ᵐ p ∂G,p.2 ≤ U) (u : ℝ) (N : ℕ) :
    ∀ᵐ r ∂Measure.pi (fun _ : Fin N => rawTilt i G b u),∀ j,hs i b r j∈Icc a (1/2:ℝ) := by
  letI := rawTilt_probability i G hb u
  have hraw : ∀ᵐ r ∂rawTilt i G b u,r.1=0 → r.2 ≤ U :=
    (tilted_absolutelyContinuous (RawMixedSource.source i G) _).ae_le
      (EntryLiteralResponseMoments.raw_lower_cap i G hcap)
  have hcoord (j : Fin N) := (measurePreserving_eval (fun _ : Fin N => rawTilt i G b u) j).quasiMeasurePreserving.ae hraw
  filter_upwards [ae_all_iff.mpr hcoord] with r hr
  intro j
  refine Fin.cases ⟨ha2,le_rfl⟩ (fun j => ?_) j
  have hh := rawH_bounds i hb (r j)
  refine ⟨?_,hh.2⟩
  by_cases hj : (r j).1=0
  · have hp := EntryActiveMoments.exposure_upper_of_linear_guard (xi_pos i) hb
      (show 0 ≤ (1/2:ℝ)-a by linarith) hfactor (hr j hj) hgap
    change a ≤ rawH i b (r j)
    rw [rawH,if_pos hj]
    exact (show a ≤ 1/2-exposure (xi i) b (r j).2 by linarith).trans (le_max_left _ _)
  · change a ≤ rawH i b (r j)
    simp only [rawH,if_neg hj]
    exact ha2

section Limits
variable (R : ℕ → Measure RowRival) [∀ m,IsProbabilityMeasure (R m)]
    (i : Row) (b l : ℕ → ℝ) (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
include hN

omit [∀ m,IsProbabilityMeasure (R m)] in
lemma deviation_tendsto {τ v d : ℝ}
    (hmean : ∀ j : Fin 3,Tendsto (fun m => ∫ r,statistics i (b m) (l m) j r ∂ R m)
      atTop (𝓝 (![τ,v,d] j))) :
    Tendsto (fun m => deviation (R m) i (b m) (l m) (N m) τ v d) atTop (𝓝 0) := by
  have heach (j : Fin 3) := ((hmean j).sub_const (![τ,v,d] j)).abs
  have hs := tendsto_finsetSum Finset.univ (fun j _ => heach j)
  have hi : Tendsto (fun m => 1/(N m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hN)
  simpa [deviation] using ((radius_tendsto N hN).add hs).add hi

omit [∀ m,IsProbabilityMeasure (R m)] in
lemma meanError_tendsto {τ v d : ℝ}
    (hmean : ∀ j : Fin 3,Tendsto (fun m => ∫ r,statistics i (b m) (l m) j r ∂ R m)
      atTop (𝓝 (![τ,v,d] j))) :
    Tendsto (fun m => meanError (R m) i (b m) (l m) (N m) τ v d) atTop (𝓝 0) := by
  simpa [meanError] using (deviation_tendsto R i b l N hN hmean).mul_const (1+2/v+2*|d| /v^2)

theorem event_polynomial_bad
    (hNp : ∀ m,0 < N m) (hbp : ∀ m,0 < b m) {a τ v d : ℝ} (hv : 0 < v)
    (hmean : ∀ j : Fin 3,Tendsto (fun m => ∫ r,statistics i (b m) (l m) j r ∂ R m)
      atTop (𝓝 (![τ,v,d] j)))
    (hrow : ∀ᶠ m in atTop,∀ᵐ r ∂Measure.pi (fun _ : Fin (N m) => R m),
      ∀ j,hs i (b m) r j∈Icc a (1/2:ℝ)) (j : ℕ) :
    Tendsto (fun m => (N m:ℝ)^j*(Measure.pi (fun _ : Fin (N m) => R m)).real
      (event (R m) i (b m) (l m) (N m) a τ v d)ᶜ) atTop (𝓝 0) := by
  have hdev := deviation_tendsto R i b l N hN hmean
  have htail := (polynomial_radius_tail N hN j).const_mul 6
  apply squeeze_zero' (Eventually.of_forall fun m => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) measureReal_nonneg) ?_
    (by simpa using htail)
  filter_upwards [hrow,hdev.eventually (Iio_mem_nhds (show 0 < v/2 by positivity))] with m hm hem
  have hh := event_complement_le (R m) i (hbp m) (l m) (N m) (hNp m) a τ v d hm hem.le
  have ht := mul_le_mul_of_nonneg_left hh (pow_nonneg (Nat.cast_nonneg (N m)) j)
  simpa [mul_assoc,mul_left_comm,mul_comm] using ht

end Limits
end FCAppendix.Affine.Uniform06.EntryModerateProfile
