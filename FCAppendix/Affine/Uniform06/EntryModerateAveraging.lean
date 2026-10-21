import FCAppendix.Affine.Uniform06.EntryModerateWindow
import FCAppendix.Affine.Uniform06.EntryModerateTruncation

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryModerateAveraging
open MeasureTheory ProbabilityTheory Set Filter Topology
open FCAppendix.Affine.WeightedSampling FCAppendix.PiBinomial
open EntrySamplingLaw EntryRenewal EntryParityRenewal EntryUntilting
open EntryLaplace EntryWeightedLaplace EntryModerateTruncation EntryModerateWindow
open WeightedMoments
open scoped BigOperators Classical
universe u

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma fairMoment_le_initial (w : Weights ι) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (H k : ℕ) (W : ℝ) :
    fairMoment w h H k W ≤ deficitMoment k W := by
  let B := IndependentCounts.binomial H (1/2) (by norm_num) (by norm_num)
  have he : fairMoment w h H k W=B.expect
      (fun c : Fin (H+1) => pathMoment w h k (imbalance H c.val) ∅ W) := by
    simp only [fairMoment,FiniteLaw.expect,B,binomial_mass]
    exact (Fin.sum_univ_eq_sum_range
      (fun c => pmf H (1/2) c*pathMoment w h k (imbalance H c) ∅ W) (H+1)).symm
  rw [he]
  exact B.expect_le_const (fun c => pathMoment_le_initial w h hh k _ ∅ W)

lemma fairMoment_eq_zero_of_nonpos (w : Weights ι) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (H k : ℕ) {W : ℝ} (hW : W ≤ 0) :
    fairMoment w h H k W=0 := by
  exact le_antisymm ((fairMoment_le_initial w h hh H k W).trans_eq
    (deficitMoment_eq_zero_of_nonpos k hW)) (fairMoment_nonneg _ _ _ _ _)

lemma measurable_fairMoment {Ω : Type*} [MeasurableSpace Ω]
    (w : Ω → Weights ι) (h : Ω → ι → ℝ) (H : Ω → ℕ) (W : Ω → ℝ)
    (hw : Measurable w) (hh : Measurable h) (hH : Measurable H) (hW : Measurable W)
    (k : ℕ) : Measurable (fun x => fairMoment (w x) (h x) (H x) k (W x)) := by
  have hp (d : ℕ) : Measurable (fun x => pathMoment (w x) (h x) k d ∅ (W x)) := by
    have hm : Measurable (fun x : Ω × unitInterval =>
        deficitMoment k (W x.1-sampled w h (fun _ => d) x)) :=
      EntryRawSignMoments.measurable_deficitMoment
        ((hW.comp measurable_fst).sub
          (measurable_sampled w h (fun _ => d) hw hh measurable_const)) k
    have he : (fun x => pathMoment (w x) (h x) k d ∅ (W x))=
        (fun x => ∫ u : unitInterval, deficitMoment k (W x-sampled w h (fun _ => d) (x,u))) := by
      funext x
      exact (integral_sampler_test (w x) d
        (fun p => deficitMoment k (W x-selectedSum (h x) d p))).symm
    rw [he]
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hfixed (n : ℕ) : Measurable (fun x => fairMoment (w x) (h x) n k (W x)) := by
    unfold fairMoment
    exact Finset.measurable_sum _ (fun c _ => (hp (imbalance n c)).const_mul _)
  have hprod : Measurable (fun z : ℕ × Ω => fairMoment (w z.2) (h z.2) z.1 k (W z.2)) :=
    measurable_from_prod_countable_right hfixed
  convert! hprod.comp (hH.prodMk measurable_id) using 1

lemma exp_mul_deficitMoment (θ W : ℝ) (k : ℕ) :
    Real.exp (-θ*W)*deficitMoment k W=weightedMonomial θ k W := by
  by_cases hW : 0 < W
  · by_cases hk : k=0 <;> simp [deficitMoment,weightedMonomial,hW,hk,max_eq_left hW.le]
  · simp [weightedMonomial,hW,deficitMoment_eq_zero_of_nonpos k (le_of_not_gt hW)]

lemma normalized_coarse_bound (w : Weights ι) (h : ι → ℝ)
    {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hh : ∀ i, a ≤ h i)
    (N H k : ℕ) (hN : 0 < N) (hH : τ*(N:ℝ)/2 ≤ H) {W : ℝ} (hW : 0 ≤ W) :
    Real.sqrt (N:ℝ)*fairMoment w h H k W ≤
      (4/Real.sqrt τ)*(1/(2*a)+2)*(W+1)*deficitMoment k W := by
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr hN
  have hτs := Real.sqrt_pos.2 hτ
  have hHs : 0 < (H:ℝ)+1 := by positivity
  have hroot : Real.sqrt (N:ℝ)*Real.sqrt (2/((H:ℝ)+1)) ≤ 2/Real.sqrt τ := by
    rw [← Real.sqrt_mul hNr.le]
    apply (le_div_iff₀ hτs).2
    rw [← Real.sqrt_mul (by positivity)]
    have hfrac : (N:ℝ)*(2/((H:ℝ)+1))*τ ≤ 4 := by
      rw [show (N:ℝ)*(2/((H:ℝ)+1))*τ=(τ*(N:ℝ)*2)/((H:ℝ)+1) by ring]
      exact (div_le_iff₀ hHs).mpr (by nlinarith)
    exact (Real.sqrt_le_iff).2 ⟨by norm_num, by convert! hfrac using 1; ring⟩
  have hp : W/(2*a)+2 ≤ (1/(2*a)+2)*(W+1) := by
    have hi : 0 ≤ 1/(2*a) := by positivity
    simp only [div_eq_mul_inv,one_mul] at hi ⊢
    nlinarith only [hi,hW]
  have hmoment := deficitMoment_nonneg k W
  have hfactor : 0 ≤ W/(2*a)+2 := by positivity
  have hc := mul_le_mul_of_nonneg_left
    (actual_conditional_coarse_bound w h ha hh H k hW) (Real.sqrt_nonneg (N:ℝ))
  calc
    Real.sqrt (N:ℝ)*fairMoment w h H k W
      ≤ 2*(Real.sqrt (N:ℝ)*Real.sqrt (2/((H:ℝ)+1)))*(W/(2*a)+2)*deficitMoment k W := by
        nlinarith only [hc]
    _ ≤ 2*(2/Real.sqrt τ)*((1/(2*a)+2)*(W+1))*deficitMoment k W := by
        gcongr
    _ = _ := by ring

lemma normalized_weighted_coarse (w : Weights ι) (h : ι → ℝ)
    {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hh : ∀ i, a ≤ h i)
    (N H k : ℕ) (hN : 0 < N) (hH : τ*(N:ℝ)/2 ≤ H) (θ W : ℝ) :
    Real.sqrt (N:ℝ)*Real.exp (-θ*W)*fairMoment w h H k W ≤
      ((4/Real.sqrt τ)*(1/(2*a)+2))*
        (weightedMonomial θ (k+1) W+weightedMonomial θ k W) := by
  by_cases hW : 0 < W
  · have hh' := mul_le_mul_of_nonneg_left
      (normalized_coarse_bound w h ha hτ hh N H k hN hH hW.le) (Real.exp_pos (-θ*W)).le
    convert! hh' using 1
    · ring
    · rw [show Real.exp (-θ*W)*((4/Real.sqrt τ)*(1/(2*a)+2)*(W+1)*deficitMoment k W)=
        ((4/Real.sqrt τ)*(1/(2*a)+2))*(W+1)*(Real.exp (-θ*W)*deficitMoment k W) by ring,
        exp_mul_deficitMoment]
      simp only [weightedMonomial,if_pos hW,pow_succ]
      ring
  · simp only [fairMoment_eq_zero_of_nonpos w h (fun i => ha.le.trans (hh i)) H k
      (le_of_not_gt hW),mul_zero,weightedMonomial,if_neg hW,zero_add]
    simp

def envelope (θ ε M γ C c : ℝ) (k : ℕ) (W : ℝ) : ℝ :=
  γ*weightedMonomial θ (k+1) W+(C+c)*
    ((if θ*W ≤ ε then weightedMonomial θ (k+1) W+weightedMonomial θ k W else 0)+
      (if M ≤ θ*W then weightedMonomial θ (k+1) W+weightedMonomial θ k W else 0))

lemma envelope_nonneg {θ ε M γ C c : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (k : ℕ) (W : ℝ) : 0 ≤ envelope θ ε M γ C c k W := by
  have hg0 := weightedMonomial_nonneg θ k W
  have hg1 := weightedMonomial_nonneg θ (k+1) W
  unfold envelope
  split_ifs <;> positivity

lemma core_tail_error {F θ ε M γ C c W : ℝ} {k : ℕ}
    (hF : 0 ≤ F) (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hcoarse : F ≤ C*(weightedMonomial θ (k+1) W+weightedMonomial θ k W))
    (hcore : ε ≤ θ*W → θ*W ≤ M →
      |F-c*weightedMonomial θ (k+1) W| ≤ γ*weightedMonomial θ (k+1) W) :
    |F-c*weightedMonomial θ (k+1) W| ≤ envelope θ ε M γ C c k W := by
  have hg1 := weightedMonomial_nonneg θ (k+1) W
  have hg0 := weightedMonomial_nonneg θ k W
  have ht : |F-c*weightedMonomial θ (k+1) W| ≤
      (C+c)*(weightedMonomial θ (k+1) W+weightedMonomial θ k W) := by
    have hh := abs_sub (a := F) (b := c*weightedMonomial θ (k+1) W)
    rw [abs_of_nonneg hF,abs_of_nonneg (mul_nonneg hc hg1)] at hh
    nlinarith [mul_nonneg hc hg0]
  by_cases hlow : θ*W ≤ ε
  · unfold envelope
    rw [if_pos hlow]
    split_ifs <;> nlinarith [mul_nonneg hγ hg1]
  · by_cases hhigh : M ≤ θ*W
    · unfold envelope
      rw [if_neg hlow,if_pos hhigh]
      nlinarith [mul_nonneg hγ hg1]
    · have hh := hcore (le_of_lt (lt_of_not_ge hlow)) (le_of_lt (lt_of_not_ge hhigh))
      simpa [envelope,hlow,hhigh] using hh

end Finite

section Integrals
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {W : Ω → ℝ} (hW : Measurable W)
include hW

lemma integrable_envelope {θ ε M γ C c : ℝ} (hθ : 0 < θ) (k : ℕ) :
    Integrable (fun x => envelope θ ε M γ C c k (W x)) μ := by
  have hi := (integrable_weightedMonomial μ hW hθ (k+1)).add
    (integrable_weightedMonomial μ hW hθ k)
  exact ((integrable_weightedMonomial μ hW hθ (k+1)).const_mul γ).add
    (((hi.indicator (measurableSet_le (hW.const_mul θ) measurable_const)).add
      (hi.indicator (measurableSet_le measurable_const (hW.const_mul θ)))).const_mul (C+c))

lemma integral_envelope_bound {θ ε M γ C c : ℝ}
    (hθ : 0 < θ) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hCc : 0 ≤ C+c) (k : ℕ) :
    (∫ x, envelope θ ε M γ C c k (W x) ∂μ) ≤
      γ*(∫ x,weightedMonomial θ (k+1) (W x) ∂μ)+(C+c)*
        ((ε/θ+1)*(∫ x,weightedMonomial θ k (W x) ∂μ)+Real.exp (-M/2)*
          ((∫ x,weightedMonomial (θ/2) (k+1) (W x) ∂μ)+
            (∫ x,weightedMonomial (θ/2) k (W x) ∂μ))) := by
  have hi1 := integrable_weightedMonomial μ hW hθ (k+1)
  have hi0 := integrable_weightedMonomial μ hW hθ k
  have hs1 : Integrable (fun x => if θ*W x ≤ ε then weightedMonomial θ (k+1) (W x) else 0) μ :=
    hi1.indicator (measurableSet_le (hW.const_mul θ) measurable_const)
  have hs0 : Integrable (fun x => if θ*W x ≤ ε then weightedMonomial θ k (W x) else 0) μ :=
    hi0.indicator (measurableSet_le (hW.const_mul θ) measurable_const)
  have hl1 : Integrable (fun x => if M ≤ θ*W x then weightedMonomial θ (k+1) (W x) else 0) μ :=
    hi1.indicator (measurableSet_le measurable_const (hW.const_mul θ))
  have hl0 : Integrable (fun x => if M ≤ θ*W x then weightedMonomial θ k (W x) else 0) μ :=
    hi0.indicator (measurableSet_le measurable_const (hW.const_mul θ))
  have hsmall : Integrable (fun x =>
    (if θ*W x ≤ ε then weightedMonomial θ (k+1) (W x) else 0)+
    (if θ*W x ≤ ε then weightedMonomial θ k (W x) else 0)) μ := hs1.add hs0
  have hlarge : Integrable (fun x =>
    (if M ≤ θ*W x then weightedMonomial θ (k+1) (W x) else 0)+
    (if M ≤ θ*W x then weightedMonomial θ k (W x) else 0)) μ := hl1.add hl0
  have hsum : Integrable (fun x =>
    ((if θ*W x ≤ ε then weightedMonomial θ (k+1) (W x) else 0)+
    (if θ*W x ≤ ε then weightedMonomial θ k (W x) else 0))+
    ((if M ≤ θ*W x then weightedMonomial θ (k+1) (W x) else 0)+
    (if M ≤ θ*W x then weightedMonomial θ k (W x) else 0))) μ := hsmall.add hlarge
  have hs0le : (∫ x,if θ*W x ≤ ε then weightedMonomial θ k (W x) else 0 ∂μ) ≤
      ∫ x,weightedMonomial θ k (W x) ∂μ := by
    apply integral_mono hs0 hi0
    intro x
    dsimp only
    split_ifs <;> simp [weightedMonomial_nonneg]
  have hs1le := integral_small_window μ hW hθ hε k
  have hl1le := integral_large_window μ hW hθ hM (k+1)
  have hl0le := integral_large_window μ hW hθ hM k
  have he : (fun x => envelope θ ε M γ C c k (W x))=
      (fun x => γ*weightedMonomial θ (k+1) (W x)+(C+c)*
        (((if θ*W x ≤ ε then weightedMonomial θ (k+1) (W x) else 0)+
          (if θ*W x ≤ ε then weightedMonomial θ k (W x) else 0))+
          ((if M ≤ θ*W x then weightedMonomial θ (k+1) (W x) else 0)+
            (if M ≤ θ*W x then weightedMonomial θ k (W x) else 0)))) := by
    funext x
    simp only [envelope]
    split_ifs <;> ring
  rw [he,integral_add (hi1.const_mul γ) (hsum.const_mul (C+c)),
    integral_const_mul,integral_const_mul,integral_add hsmall hlarge,
    integral_add hs1 hs0,integral_add hl1 hl0]
  gcongr
  · nlinarith only [hs1le,hs0le]
  · nlinarith only [hl1le,hl0le]

end Integrals
section Averaging
variable {Ω κ : ℕ → Type u} [∀ m,MeasurableSpace (Ω m)]
    [∀ m,Fintype (κ m)] [∀ m,DecidableEq (κ m)] [∀ m,Nonempty (κ m)]
    (P : (m : ℕ) → Measure (Ω m)) [∀ m,IsProbabilityMeasure (P m)]

def weightedFair (w : (m : ℕ) → Ω m → Weights (κ m))
    (h : (m : ℕ) → Ω m → κ m → ℝ) (H : (m : ℕ) → Ω m → ℕ)
    (W : (m : ℕ) → Ω m → ℝ) (N : ℕ → ℕ) (θ : ℕ → ℝ) (k : ℕ)
    (m : ℕ) (x : Ω m) : ℝ :=
  Real.sqrt (N m:ℝ)*Real.exp (-θ m*W m x)*fairMoment (w m x) (h m x) (H m x) k (W m x)

def scaledScalar (W : (m : ℕ) → Ω m → ℝ) (N : ℕ → ℕ) (θ : ℕ → ℝ)
    (a : ℝ) (j m : ℕ) : ℝ :=
  Real.sqrt (N m:ℝ)*(a*θ m)^(j+1)*(∫ x,weightedMonomial (a*θ m) j (W m x) ∂P m)

theorem averaged_fair_moment
    (w : (m : ℕ) → Ω m → Weights (κ m)) (h : (m : ℕ) → Ω m → κ m → ℝ)
    (H : (m : ℕ) → Ω m → ℕ) (W : (m : ℕ) → Ω m → ℝ)
    (hW : ∀ m,Measurable (W m))
    (N : ℕ → ℕ) (hNp : ∀ m,0 < N m) (hN : Tendsto N atTop atTop)
    (θ e : ℕ → ℝ) (hθp : ∀ᶠ m in atTop,0 < θ m)
    (hθ : Tendsto θ atTop (𝓝 0))
    (hθN : Tendsto (fun m => θ m*Real.sqrt (N m:ℝ)) atTop atTop)
    (he : Tendsto e atTop (𝓝 0))
    (E : (m : ℕ) → Set (Ω m)) (hE : ∀ m,MeasurableSet (E m))
    {a A τ v μ S : ℝ} (ha : 0 < a) (hτ : 0 < τ) (hv : 0 < v) (hμ : 0 < μ)
    (hprof : ∀ m x,x∈E m → (∀ j,h m x j∈Icc a A) ∧
      |(H m x:ℝ)/(N m:ℝ)-τ| ≤ e m ∧
      |totalWeight (w m x)/(N m:ℝ)-v| ≤ e m ∧
      |weightedMean (w m x) (h m x)-μ| ≤ e m)
    {k : ℕ} (hk : k ≤ 2)
    (hFI : ∀ m,Integrable (weightedFair w h H W N θ k m) (P m))
    (hscalar : ∀ q : ℝ,0 < q → ∀ j : ℕ,j ≤ 3 →
      Tendsto (scaledScalar P W N θ q j) atTop (𝓝 (S*(Nat.factorial j:ℝ))))
    (hbad : Tendsto (fun m => Real.sqrt (N m:ℝ)*θ m^(k+2)*
      (∫ x,if x∈E m then 0 else
        |weightedFair w h H W N θ k m x-
          (peakConstant τ/(((k:ℝ)+1)*μ))*weightedMonomial (θ m) (k+1) (W m x)| ∂P m))
        atTop (𝓝 0)) :
    Tendsto (fun m => (N m:ℝ)*θ m^(k+2)*
      (∫ x,Real.exp (-θ m*W m x)*fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m))
      atTop (𝓝 ((S*peakConstant τ/μ)*(Nat.factorial k:ℝ))) := by
  classical
  let C : ℝ := (4/Real.sqrt τ)*(1/(2*a)+2)
  let c : ℝ := peakConstant τ/(((k:ℝ)+1)*μ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; exact div_pos (peak_constant_pos hτ) (by positivity)
  let F := weightedFair w h H W N θ k
  let B : ℕ → ℝ := fun m => Real.sqrt (N m:ℝ)*θ m^(k+2)*
    (∫ x,if x∈E m then 0 else |F m x-c*weightedMonomial (θ m) (k+1) (W m x)| ∂P m)
  let D : ℕ → ℝ := fun m => Real.sqrt (N m:ℝ)*θ m^(k+2)*
    |(∫ x,F m x ∂P m)-c*(∫ x,weightedMonomial (θ m) (k+1) (W m x) ∂P m)|
  let q : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  let M : ℕ → ℝ := fun j => (j:ℝ)+1
  let U : ℕ → ℕ → ℝ := fun j m =>
    q j*scaledScalar P W N θ 1 (k+1) m+(C+c)*
      ((q j+θ m)*scaledScalar P W N θ 1 k m+Real.exp (-M j/2)*
        (2^(k+2)*scaledScalar P W N θ (1/2) (k+1) m+
          θ m*2^(k+1)*scaledScalar P W N θ (1/2) k m))+B m
  let U0 : ℕ → ℝ := fun j =>
    q j*(S*(Nat.factorial (k+1):ℝ))+(C+c)*
      (q j*(S*(Nat.factorial k:ℝ))+Real.exp (-M j/2)*
        (2^(k+2)*(S*(Nat.factorial (k+1):ℝ))))
  have hU : ∀ j,Tendsto (U j) atTop (𝓝 (U0 j)) := by
    intro j
    have hs1 := hscalar 1 (by norm_num) (k+1) (by omega)
    have hs0 := hscalar 1 (by norm_num) k (by omega)
    have ht1 := hscalar (1/2) (by norm_num) (k+1) (by omega)
    have ht0 := hscalar (1/2) (by norm_num) k (by omega)
    have hh := ((hs1.const_mul (q j)).add
      ((((hθ.const_add (q j)).mul hs0).add
        (((ht1.const_mul (2^(k+2))).add
          ((hθ.mul_const (2^(k+1))).mul ht0)).const_mul (Real.exp (-M j/2)))).const_mul (C+c))).add hbad
    simpa only [U,U0,B,F,c,zero_add,add_zero,zero_mul,mul_zero] using hh
  have hb : ∀ j,∀ᶠ m in atTop,0 ≤ D m ∧ D m ≤ U j m := by
    intro j
    have hq : 0 < q j := by dsimp [q]; positivity
    have hM : 0 < M j := by dsimp [M]; positivity
    have hunif := uniform_conditional_coefficient (A := A) w h H W N hNp hN θ e hθp hθ hθN he
      ha hτ hv hμ hq hM hk (q j) hq
    have heSmall : ∀ᶠ m in atTop, e m < τ/2 :=
      he.eventually (gt_mem_nhds (show 0 < τ/2 by positivity))
    filter_upwards [hθp,heSmall,hunif] with m hθm hem hum
    have hNr : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
    have hnorm : 0 ≤ Real.sqrt (N m:ℝ)*θ m^(k+2) := by positivity
    have hi := integrable_weightedMonomial (P m) (hW m) hθm (k+1)
    have hdiff : Integrable (fun x => F m x-c*weightedMonomial (θ m) (k+1) (W m x)) (P m) :=
      (hFI m).sub (hi.const_mul c)
    have hib : Integrable (fun x => if x∈E m then 0 else
        |F m x-c*weightedMonomial (θ m) (k+1) (W m x)|) (P m) := by
      convert! hdiff.abs.indicator (hE m).compl using 1
      funext x
      simp only [Set.indicator_apply,mem_compl_iff]
      split_ifs <;> simp_all
    have hie := integrable_envelope (P m) (hW m) hθm k
      (ε := q j) (M := M j) (γ := q j) (C := C) (c := c)
    have hpoint (x : Ω m) :
        |F m x-c*weightedMonomial (θ m) (k+1) (W m x)| ≤
          envelope (θ m) (q j) (M j) (q j) C c k (W m x)+
            (if x∈E m then 0 else |F m x-c*weightedMonomial (θ m) (k+1) (W m x)|) := by
      by_cases hx : x∈E m
      · rw [if_pos hx,add_zero]
        have hp := hprof m x hx
        have hcount : τ*(N m:ℝ)/2 ≤ H m x := by
          have hlow := (abs_le.mp hp.2.1).1
          have hdiv : τ/2 ≤ (H m x:ℝ)/(N m:ℝ) := by linarith
          have hh := (le_div_iff₀ hNr).mp hdiv
          nlinarith only [hh]
        have hcoarse := normalized_weighted_coarse (w m x) (h m x) ha hτ
          (fun j => (hp.1 j).1) (N m) (H m x) k (hNp m) hcount (θ m) (W m x)
        have hF0 : 0 ≤ F m x := by
          exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
            (fairMoment_nonneg _ _ _ _ _)
        apply core_tail_error hF0 hc.le hq.le hcoarse
        intro hlo hhi
        have hu := hum x ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,hlo,hhi⟩
        have hWx : 0 < W m x := by nlinarith
        have hWp : 0 < (W m x)^(k+1) := pow_pos hWx _
        have hc0 : |Real.sqrt (N m:ℝ)*fairMoment (w m x) (h m x) (H m x) k (W m x)-
            c*(W m x)^(k+1)| ≤ q j*(W m x)^(k+1) := by
          have hu' : |(Real.sqrt (N m:ℝ)*fairMoment (w m x) (h m x) (H m x) k (W m x)-
              c*(W m x)^(k+1))/(W m x)^(k+1)| ≤ q j := by
            convert! hu.le using 1
            dsimp [c]
            field_simp
          rwa [abs_div,abs_of_pos hWp,div_le_iff₀ hWp] at hu'
        have hprod := mul_le_mul_of_nonneg_left hc0 (Real.exp_pos (-θ m*W m x)).le
        have hp' : |Real.exp (-θ m*W m x)*
            (Real.sqrt (N m:ℝ)*fairMoment (w m x) (h m x) (H m x) k (W m x)-c*(W m x)^(k+1))| ≤
            Real.exp (-θ m*W m x)*(q j*(W m x)^(k+1)) := by
          simpa only [abs_mul,abs_of_pos (Real.exp_pos (-θ m*W m x))] using hprod
        dsimp only [F,weightedFair]
        simp only [weightedMonomial,if_pos hWx]
        convert! hp' using 1
        · congr 1
          ring
        · ring
      · rw [if_neg hx]
        exact le_add_of_nonneg_left (envelope_nonneg hq.le hC.le hc.le k (W m x))
    have herr : |(∫ x,F m x ∂P m)-c*(∫ x,weightedMonomial (θ m) (k+1) (W m x) ∂P m)| ≤
        (∫ x,envelope (θ m) (q j) (M j) (q j) C c k (W m x) ∂P m)+
          (∫ x,if x∈E m then 0 else |F m x-c*weightedMonomial (θ m) (k+1) (W m x)| ∂P m) := by
      rw [← integral_const_mul,← integral_sub (hFI m) (hi.const_mul c)]
      apply (abs_integral_le_integral_abs (μ := P m)).trans
      have hsum : Integrable (fun x => envelope (θ m) (q j) (M j) (q j) C c k (W m x)+
          (if x∈E m then 0 else |F m x-c*weightedMonomial (θ m) (k+1) (W m x)|)) (P m) :=
        hie.add hib
      have hh := integral_mono hdiff.abs hsum hpoint
      simpa only [integral_add hie hib,F] using hh
    have heB := integral_envelope_bound (P m) (hW m) (γ := q j)
      hθm hq.le hM.le (add_nonneg hC.le hc.le) k
    have hfin := mul_le_mul_of_nonneg_left (herr.trans (add_le_add heB le_rfl)) hnorm
    refine ⟨by dsimp [D]; positivity,?_⟩
    convert! hfin using 1
    dsimp [U,B,scaledScalar]
    simp only [one_mul]
    field_simp [ne_of_gt hθm]
    have hcancel : (1/2:ℝ)^k*2^k=1 := by rw [← mul_pow]; norm_num
    ring_nf
    simp only [mul_assoc,hcancel,mul_one]
  have hq0 : Tendsto q atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hMtop : Tendsto M atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun j => Real.exp (-M j/2)) atTop (𝓝 0) := by
    have hd : Tendsto (fun j => M j/2) atTop atTop := by
      simpa only [div_eq_mul_inv] using
        hMtop.atTop_mul_const (show (0:ℝ)< (2:ℝ)⁻¹ by norm_num)
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp hd
    simpa only [Function.comp_def,neg_div] using hh
  have hU0 : Tendsto U0 atTop (𝓝 0) := by
    simpa only [U0,zero_mul,zero_add,mul_zero] using
      (hq0.mul_const (S*(Nat.factorial (k+1):ℝ))).add
        (((hq0.mul_const (S*(Nat.factorial k:ℝ))).add
          (hexp.mul_const (2^(k+2)*(S*(Nat.factorial (k+1):ℝ))))).const_mul (C+c))
  have hD : Tendsto D atTop (𝓝 0) :=
    tendsto_of_parameter_sandwich D (fun _ _ => 0) U (fun _ => 0) U0 0
      (fun _ => tendsto_const_nhds) hU hb tendsto_const_nhds hU0
  let T : ℕ → ℝ := fun m => (N m:ℝ)*θ m^(k+2)*
    (∫ x,Real.exp (-θ m*W m x)*fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m)
  have hdiff0 : Tendsto (fun m => T m-c*scaledScalar P W N θ 1 (k+1) m) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply hD.congr'
    filter_upwards [hθp] with m hθm
    have hNr : (0:ℝ)< N m := Nat.cast_pos.mpr (hNp m)
    have hs := Real.sq_sqrt hNr.le
    dsimp [D,T,F,weightedFair,scaledScalar]
    have hInt : (∫ x, Real.sqrt (N m:ℝ)*Real.exp (-θ m*W m x)*
        fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m) =
        Real.sqrt (N m:ℝ)*(∫ x, Real.exp (-θ m*W m x)*
        fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m) := by
      rw [←integral_const_mul]
      congr 1
      funext x
      ring
    rw [hInt]
    simp only [one_mul]
    rw [show (N m:ℝ)*θ m^(k+2)*(∫ x,Real.exp (-θ m*W m x)*
        fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m)-
        c*(Real.sqrt (N m:ℝ)*θ m^(k+1+1)*(∫ x,weightedMonomial (θ m) (k+1) (W m x) ∂P m))=
      (Real.sqrt (N m:ℝ)*θ m^(k+2))*(Real.sqrt (N m:ℝ)*
        (∫ x,Real.exp (-θ m*W m x)*fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m)-
        c*(∫ x,weightedMonomial (θ m) (k+1) (W m x) ∂P m)) by
      have hk' : k+1+1=k+2 := by omega
      rw [hk']
      nlinarith [congrArg (fun z : ℝ => z*θ m^(k+2)*(∫ x,Real.exp (-θ m*W m x)*
        fairMoment (w m x) (h m x) (H m x) k (W m x) ∂P m)) hs]]
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (N m:ℝ)*θ m^(k+2))]
  have ht := hdiff0.add ((hscalar 1 (by norm_num) (k+1) (by omega)).const_mul c)
  have hconstant : c*(S*(Nat.factorial (k+1):ℝ))=(S*peakConstant τ/μ)*(Nat.factorial k:ℝ) := by
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    dsimp [c]
    field_simp
  simpa only [sub_add_cancel,zero_add,hconstant,T] using ht

end Averaging
end FCAppendix.Affine.Uniform06.EntryModerateAveraging
