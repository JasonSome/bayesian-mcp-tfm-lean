import FCAppendix.Affine.Uniform06.EntryCentralPassage
import FCAppendix.Probability.L1WeakConvergence

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryIIDCentral
open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open FCAppendix.Affine.Uniform06
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.EntrySamplingLaw
open FCAppendix.Affine.Uniform06.EntryCentralSampling
open FCAppendix.Affine.Uniform06.EntryProfileMean
open FCAppendix.Affine.Uniform06.EntryCentralPassage
open scoped BigOperators

section Pullback
variable {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

lemma independent_pullback (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν] {g : Ξ → Ω}
    (hg : MeasurePreserving g ν μ) (F : (i : ι) → Ω → β i)
    (hF : ∀ i, Measurable (F i)) (hi : iIndepFun F μ) :
    iIndepFun (fun i x => F i (g x)) ν := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hF i).comp hg.measurable).aemeasurable)).mpr
  have hm : Measurable (fun ω i => F i ω) := measurable_pi_lambda _ hF
  have he := hi.map_fun_eq_pi_map (fun i => (hF i).aemeasurable)
  change ν.map ((fun ω i => F i ω) ∘ g)=Measure.pi (fun i => ν.map (F i ∘ g))
  rw [← Measure.map_map hm hg.measurable,hg.map_eq,he]
  congr 1
  funext i
  rw [← Measure.map_map (hF i) hg.measurable,hg.map_eq]

lemma covariance_pullback (μ : Measure Ω) (ν : Measure Ξ) {g : Ξ → Ω}
    (hg : MeasurePreserving g ν μ) {f h : Ω → ℝ} (hf : Measurable f) (hh : Measurable h) :
    covariance (fun x => f (g x)) (fun x => h (g x)) ν=covariance f h μ := by
  have he := covariance_map (μ := ν) hf.aestronglyMeasurable hh.aestronglyMeasurable hg.measurable.aemeasurable
  rw [hg.map_eq] at he
  exact he.symm

end Pullback

variable {Ω : Type*} [MeasurableSpace Ω]

abbrev Row (N : ℕ) := (Fin N → Ω) × unitInterval

def rowLaw (μ : Measure Ω) (N : ℕ) : Measure (Row (Ω := Ω) N) :=
  (Measure.pi (fun _ : Fin N => μ)).prod volume

instance probability_rowLaw (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (rowLaw μ N) := inferInstanceAs (IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin N => μ)).prod (volume : Measure unitInterval)))

def array (N : ℕ) (C : Fin 2 → Ω → ℝ) (i : Fin N) (j : Fin 2) (x : Row (Ω := Ω) N) : ℝ :=
  C j (x.1 i)

lemma measurable_array {N : ℕ} {C : Fin 2 → Ω → ℝ}
    (hC : ∀ j, Measurable (C j)) (i : Fin N) (j : Fin 2) : Measurable (array N C i j) :=
  (hC j).comp ((measurable_pi_apply i).comp measurable_fst)

lemma eval_preserving (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ) (i : Fin N) :
    MeasurePreserving (fun x : Row (Ω := Ω) N => x.1 i) (rowLaw μ N) μ :=
  (measurePreserving_eval (fun _ : Fin N => μ) i).comp measurePreserving_fst

lemma array_mean_zero (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {C : Fin 2 → Ω → ℝ} (hC : ∀ j, Measurable (C j))
    (hz : ∀ j, ∫ ω, C j ω ∂μ=0) (i : Fin N) (j : Fin 2) :
    (∫ x, array N C i j x ∂rowLaw μ N)=0 := by
  have hp := eval_preserving μ N i
  have hg : AEStronglyMeasurable (C j) ((rowLaw μ N).map (fun x : Row N => x.1 i)) := by
    rw [hp.map_eq]
    exact (hC j).aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hg
  rw [hp.map_eq] at he
  simpa only [array,hz] using! he.symm

lemma array_independent (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {C : Fin 2 → Ω → ℝ} (hC : ∀ j, Measurable (C j)) :
    iIndepFun (EntryVector.pair (array N C)) (rowLaw μ N) := by
  have hf : Measurable (fun ω => WithLp.toLp 2 (fun j => C j ω)) := by fun_prop
  have hi := iIndepFun_pi (μ := fun _ : Fin N => μ) (fun _ => hf.aemeasurable)
  exact independent_pullback (Measure.pi (fun _ : Fin N => μ)) (rowLaw μ N)
    measurePreserving_fst (fun i r => WithLp.toLp 2 (fun j => C j (r i)))
      (fun i => hf.comp (measurable_pi_apply i)) hi

lemma scalar_array_independent (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {C : Fin 2 → Ω → ℝ} (hC : ∀ j, Measurable (C j)) (j : Fin 2) :
    iIndepFun (fun i => array N C i j) (rowLaw μ N) := by
  exact independent_pullback (Measure.pi (fun _ : Fin N => μ)) (rowLaw μ N)
    measurePreserving_fst (fun i r => C j (r i))
      (fun i => (hC j).comp (measurable_pi_apply i))
        (iIndepFun_pi (μ := fun _ : Fin N => μ) (fun _ => (hC j).aemeasurable))

lemma array_covariance (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}
    {C : Fin 2 → Ω → ℝ} (hC : ∀ j, Measurable (C j))
    (v : Fin 2 → ℝ) (hv : ∀ j k, covariance (C j) (C k) μ=if j=k then v j else 0)
    (i : Fin N) (j k : Fin 2) :
    covariance (array N C i j) (array N C i k) (rowLaw μ N)=if j=k then v j else 0 := by
  change covariance (fun x : Row N => C j (x.1 i)) (fun x : Row N => C k (x.1 i)) (rowLaw μ N)=_
  rw [covariance_pullback μ (rowLaw μ N) (eval_preserving μ N i) (hC j) (hC k),hv]

omit [MeasurableSpace Ω] in
lemma folded_array_eq {N : ℕ} (hN : 0 < N) (C : Fin 2 → Ω → ℝ)
    (v : Fin 2 → ℝ) (hv : ∀ j, 0 < v j) (hstar : ℝ) (x : Row (Ω := Ω) N) :
    EntryVector.fold (Real.sqrt (v 0)) (hstar*Real.sqrt (v 1))
      (∑ i, EntryVector.standardized (array N C) v i x)=
      EntryUI.normalizedSum (fun i => array N C i 0) x+
        hstar*|(∑ i, C 1 (x.1 i))/Real.sqrt (N : ℝ)| := by
  have hR : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h0 : 0 < Real.sqrt (v 0) := Real.sqrt_pos.mpr (hv 0)
  have h1 : 0 < Real.sqrt (v 1) := Real.sqrt_pos.mpr (hv 1)
  simp only [EntryVector.fold,EntryVector.standardized,EntryVector.scale,
    WithLp.ofLp_sum,Finset.sum_apply,
    EntryUI.normalizedSum,array]
  simp only [← Finset.sum_div]
  rw [abs_div,abs_of_pos (mul_pos hR h1),abs_div,abs_of_pos hR]
  field_simp [hR.ne',h0.ne',h1.ne']

lemma selectedSum_nonneg {ι : Type*} (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i) :
    ∀ n : ℕ, ∀ p : Path ι n, 0 ≤ selectedSum h n p := by
  intro n
  induction n with
  | zero => intro p; simp [selectedSum]
  | succ n ih => intro p; exact add_nonneg (hh p.1) (ih p.2)

omit [MeasurableSpace Ω] in
lemma guardedSample_nonneg {N : ℕ} {w : (Fin N → Ω) → Weights (Fin (N+1))}
    {h : (Fin N → Ω) → Fin (N+1) → ℝ} {d : (Fin N → Ω) → ℕ}
    {c hstar : ℝ} (hh : ∀ r j, 0 ≤ h r j) (hhstar : 0 ≤ hstar) (x : Row (Ω := Ω) N) :
    0 ≤ guardedSample w h d c hstar x := by
  unfold guardedSample
  split_ifs
  · exact selectedSum_nonneg (h x.1) (hh x.1) _ _
  · exact mul_nonneg (Nat.cast_nonneg _) hhstar

def statistic {N : ℕ} (C : Fin 2 → Ω → ℝ)
    (w h : Ω → ℝ) (w0 h0 c hstar : ℝ) (hw0 : w0 ∈ Icc (0:ℝ) 1)
    (hwb : ∀ ω, w ω ∈ Icc (0:ℝ) 1) (d : (Fin N → Ω) → ℕ) (x : Row (Ω := Ω) N) : ℝ :=
  EntryUI.normalizedSum (fun i => array N C i 0) x+
    guardedSample (profileWeights w0 w hw0 hwb) (profileH h0 h) d (c*N) hstar x/Real.sqrt (N : ℝ)

theorem primitive_central_moments
    (μ : ℕ → Measure Ω) [∀ m, IsProbabilityMeasure (μ m)]
    (N : ℕ → ℕ) (hNp : ∀ m, 0 < N m) (hN : Tendsto N atTop atTop)
    (C : ℕ → Fin 2 → Ω → ℝ) (hCm : ∀ m j, Measurable (C m j))
    (hCb : ∀ m j, ∀ᵐ ω ∂μ m, |C m j ω| ≤ 1)
    (hCz : ∀ m j, ∫ ω, C m j ω ∂μ m=0)
    (v : ℕ → Fin 2 → ℝ) (v0 : Fin 2 → ℝ)
    (hvp : ∀ m j, 0 < v m j) (hv0 : ∀ j, 0 < v0 j)
    (hcv : ∀ m j k, covariance (C m j) (C m k) (μ m)=if j=k then v m j else 0)
    (hvlim : ∀ j, Tendsto (fun m => v m j) atTop (𝓝 (v0 j)))
    (w h : ℕ → Ω → ℝ) (hw : ∀ m, Measurable (w m)) (hh : ∀ m, Measurable (h m))
    (d : (m : ℕ) → (Fin (N m) → Ω) → ℕ) (hd : ∀ m, Measurable (d m))
    (hD : ∀ m r, d m r ≤ N m)
    (hcount : ∀ m r, (d m r : ℝ)=|∑ j, C m 1 (r j)|)
    (w0 h0 : ℕ → ℝ) {A c dbar a : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hcd : c ≤ dbar)
    (hw0 : ∀ m, w0 m ∈ Icc (0:ℝ) 1) (hh0 : ∀ m, h0 m ∈ Icc (0:ℝ) A)
    (hwb : ∀ m ω, w m ω ∈ Icc (0:ℝ) 1) (hhb : ∀ m ω, h m ω ∈ Icc (0:ℝ) A)
    (hastar : a/dbar ∈ Icc (0:ℝ) A)
    (hwlim : Tendsto (fun m => ∫ ω, w m ω ∂μ m) atTop (𝓝 dbar))
    (hglim : Tendsto (fun m => ∫ ω, w m ω*h m ω ∂μ m) atTop (𝓝 a))
    (z : ℕ → ℝ) {z0 : ℝ} (hz : Tendsto z atTop (𝓝 z0)) :
    let T := fun m => statistic (C m) (w m) (h m) (w0 m) (h0 m) c (a/dbar) (hw0 m) (hwb m) (d m)
    let α := Real.sqrt (v0 0)
    let β := (a/dbar)*Real.sqrt (v0 1)
    Tendsto (fun m => (rowLaw (μ m) (N m)).real {x | T m x< z m}) atTop
      (𝓝 (EntryCentralRatio.success α β z0)) ∧
    Tendsto (fun m => ∫ x, max (z m-T m x) 0 ∂rowLaw (μ m) (N m)) atTop
      (𝓝 (EntryCentralRatio.firstMoment α β z0)) ∧
    Tendsto (fun m => ∫ x, (max (z m-T m x) 0)^2 ∂rowLaw (μ m) (N m)) atTop
      (𝓝 (EntryCentralRatio.secondMoment α β z0)) := by
  dsimp only
  let P := fun m => rowLaw (μ m) (N m)
  let Arow := fun m => array (N m) (C m)
  let α := fun m => Real.sqrt (v m 0)
  let β := fun m => (a/dbar)*Real.sqrt (v m 1)
  let F := EntryCentral.foldedRow N Arow v α β
  let T := fun m => statistic (C m) (w m) (h m) (w0 m) (h0 m) c (a/dbar) (hw0 m) (hwb m) (d m)
  let S := fun m x => guardedSample (profileWeights (w0 m) (w m) (hw0 m) (hwb m))
    (profileH (h0 m) (h m)) (d m) (c*N m) (a/dbar) x/Real.sqrt (N m : ℝ)
  have hmA m i j : Measurable (Arow m i j) := measurable_array (hCm m) i j
  have hbA m i j : ∀ᵐ x ∂P m, |Arow m i j x| ≤ 1 :=
    (eval_preserving (μ m) (N m) i).quasiMeasurePreserving.ae (hCb m j)
  have hzA m i j : (∫ x, Arow m i j x ∂P m)=0 := array_mean_zero (μ m) (hCm m) (hCz m) i j
  have hiA m : iIndepFun (EntryVector.pair (Arow m)) (P m) := array_independent (μ m) (hCm m)
  have hvA m i j k : covariance (Arow m i j) (Arow m i k) (P m)=if j=k then v m j else 0 :=
    array_covariance (μ m) (hCm m) (v m) (hcv m) i j k
  let η := min (v0 0) (v0 1)/2
  have hη : 0 < η := half_pos (lt_min (hv0 0) (hv0 1))
  have hvη : ∀ᶠ m in atTop, ∀ j, η ≤ v m j := by
    have hl0 : η < v0 0 := by dsimp [η]; have := min_le_left (v0 0) (v0 1); linarith [hv0 0]
    have hl1 : η < v0 1 := by dsimp [η]; have := min_le_right (v0 0) (v0 1); linarith [hv0 1]
    filter_upwards [(hvlim 0).eventually_const_lt hl0,(hvlim 1).eventually_const_lt hl1] with m hm0 hm1 j
    fin_cases j
    · exact hm0.le
    · exact hm1.le
  have hα m : 0 < α m := Real.sqrt_pos.mpr (hvp m 0)
  have hα0 : 0 < Real.sqrt (v0 0) := Real.sqrt_pos.mpr (hv0 0)
  have hβ : ∀ᶠ m in atTop, 0 ≤ β m := Eventually.of_forall fun _ => mul_nonneg hastar.1 (Real.sqrt_nonneg _)
  have hαL := (hvlim 0).sqrt
  have hβL := (hvlim 1).sqrt.const_mul (a/dbar)
  have hFw := EntryCentral.constructed_folded_weak_limit P N Arow v hN hmA hbA hzA hiA hvA
    hη hvη α β hα hα0 hβ hαL hβL
  have hFm m : Measurable (F m) := EntryCentral.measurable_foldedRow N Arow v α β hmA m
  have hFid m x : F m x=EntryUI.normalizedSum (fun i => Arow m i 0) x+
      (a/dbar)*((d m x.1 : ℝ)/Real.sqrt (N m : ℝ)) := by
    dsimp only [F,EntryCentral.foldedRow,Arow,α,β]
    rw [folded_array_eq (hNp m) (C m) (v m) (hvp m)]
    rw [hcount,abs_div,abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hNp m))]
  have hSm m : Measurable (S m) :=
    (measurable_guardedSample _ _ _ (measurable_profileWeights _ _ _ _ (hw m) (N m))
      (measurable_profileH _ (hh m) (N m)) (hd m) _ _).div_const _
  have hTm m : Measurable (T m) :=
    (EntryUI.measurable_normalizedSum (fun i => hmA m i 0)).add (hSm m)
  have heq m x : T m x-F m x=
      (guardedSample (profileWeights (w0 m) (w m) (hw0 m) (hwb m))
        (profileH (h0 m) (h m)) (d m) (c*N m) (a/dbar) x-
          (d m x.1 : ℝ)*(a/dbar))/Real.sqrt (N m : ℝ) := by
    rw [hFid]
    dsimp [T,statistic,Arow]
    ring
  have hrep := iid_guarded_replacement_L2 μ N hNp hN (fun m => C m 1) w h
    (fun m => hCm m 1) hw hh (fun m => hCb m 1) (fun m => hCz m 1)
    d hd hD hcount w0 h0 hA hc hcd hw0
    (fun m => by rw [abs_of_nonneg (hh0 m).1]; exact (hh0 m).2)
    hwb (fun m ω => by rw [abs_of_nonneg (hhb m ω).1]; exact (hhb m ω).2)
    (by rw [abs_of_nonneg hastar.1]; exact hastar.2) hwlim hglim
  have hL2 : Tendsto (fun m => ∫ x, (T m x-F m x)^2 ∂P m) atTop (𝓝 0) := by
    simpa only [heq,P,rowLaw] using hrep
  have hLp m : MemLp (fun x => T m x-F m x) 2 (P m) := by
    apply MemLp.of_bound ((hTm m).sub (hFm m)).aestronglyMeasurable
      (2*A*N m/Real.sqrt (N m : ℝ))
    exact Eventually.of_forall fun x => by
      simp only [Real.norm_eq_abs,Pi.sub_apply]
      rw [heq,abs_div,abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast hNp m))]
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hs := EntryCentralReplacement.guardedSample_abs_le (c := c*N m)
        (profileWeights (w0 m) (w m) (hw0 m) (hwb m)) (profileH (h0 m) (h m)) (d m)
        hA (fun r j => profileH_abs_le
          (by rw [abs_of_nonneg (hh0 m).1]; exact (hh0 m).2)
          (fun ω => by rw [abs_of_nonneg (hhb m ω).1]; exact (hhb m ω).2) r j)
        (by rw [abs_of_nonneg hastar.1]; exact hastar.2) x
      have ht : |(d m x.1 : ℝ)*(a/dbar)| ≤ A*d m x.1 := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg hastar.1]
        nlinarith [mul_le_mul_of_nonneg_left hastar.2 (Nat.cast_nonneg (d m x.1))]
      exact (abs_sub _ _).trans ((add_le_add hs ht).trans (by
        have hd' : (d m x.1 : ℝ) ≤ N m := by exact_mod_cast hD m x.1
        nlinarith [mul_le_mul_of_nonneg_left hd' hA]))
  have hTw := FCAppendix.Probability.tendstoInDistribution_of_integral_abs_sub P
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) T F
      (EntryGaussianLaw.sumFold (Real.sqrt (v0 0)) ((a/dbar)*Real.sqrt (v0 1))) hTm hFw
      (fun m => ((hLp m).integrable (by norm_num)).abs) (L1_tendsto_of_L2 P _ hLp hL2)
  have hTw' : TendstoInDistribution T atTop id P
      (EntryGaussianLaw.law (Real.sqrt (v0 0)) ((a/dbar)*Real.sqrt (v0 1))) := by
    refine ⟨fun m => (hTm m).aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [EntryGaussianLaw.law,Measure.map_id] using hTw.tendsto
  have hI m : Integrable (fun x => (F m x-T m x)^2) (P m) := by
    have he : (fun x => (F m x-T m x)^2)=(fun x => (T m x-F m x)^2) := funext fun _ => by ring
    rw [he]
    exact (hLp m).integrable_sq
  have hL2' : Tendsto (fun m => ∫ x, (F m x-T m x)^2 ∂P m) atTop (𝓝 0) := by
    convert! hL2 using 1
    funext m
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by ring
  have hG : Continuous (cdf (EntryGaussianLaw.law (Real.sqrt (v0 0)) ((a/dbar)*Real.sqrt (v0 1)))) :=
    continuous_iff_continuousAt.mpr fun s =>
      (EntryConvolution.hasDerivAt_actual_cdf hα0 ((a/dbar)*Real.sqrt (v0 1)) s).continuousAt
  have hTcdf (s : ℝ) := strict_cdf_tendsto_of_L2 P F T _ hG
    (fun q => EntryCentral.constructed_folded_cdf_tendsto P N Arow v hN hmA hbA hzA hiA hvA
      hη hvη α β (fun _ => q) hα hα0 hβ hαL hβL tendsto_const_nhds)
    hI hL2' (fun _ => s) tendsto_const_nhds
  exact moments_of_actual_scalar_rows P hα0 (mul_nonneg hastar.1 (Real.sqrt_nonneg _))
    T hTm hTw' hTcdf N hNp (fun m i => Arow m i 0)
    (fun m i => hmA m i 0) (fun m i => hbA m i 0) (fun m i => hzA m i 0)
    (fun m => scalar_array_independent (μ m) (hCm m) 0) S hSm
    (fun m => Eventually.of_forall fun x => div_nonneg
      (guardedSample_nonneg (fun r j => Fin.cases (hh0 m).1 (fun j => (hhb m (r j)).1) j) hastar.1 x)
      (Real.sqrt_nonneg _)) (fun _ _ => rfl) z hz

end FCAppendix.Affine.Uniform06.EntryIIDCentral
