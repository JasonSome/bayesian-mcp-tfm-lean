import FCAppendix.Affine.Uniform06.EqualOnlyRareMoments
import FCAppendix.Affine.Uniform06.LiteralBadCountTransfer

noncomputable section
namespace FCAppendix.Affine.Uniform06.EqualOnlyCountTransfer

open Set MeasureTheory Filter LowBody
open scoped BigOperators Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open RawMomentPartition RawPathAdapter PreciseRootGood RareEmpiricalReplacement
open EqualOnlyRareMoments LiteralBadCountTransfer MixedIntervalLLT

theorem original_low_count_replacement (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (N c : ℕ → ℕ) [∀ n,Nonempty (Fin (N n))]
    (hN : Tendsto N atTop atTop) (hNpos : ∀ n,0< N n)
    (b θ τ : ℕ → ℝ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (N n) → Fin 4) → ℝ)
    (hb : ∀ n,0< b n) (hbL : ∀ n,b n≤(g n).multiplier)
    (hgl : ∀ n,0<(g n).multiplier-(g n).radius)
    (hbl : ∀ n,b n≤(g n).multiplier-(g n).radius)
    (hτ : ∀ n,0≤τ n) (hc : ∀ n,(c n:ℝ)≤ N n)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    {ε : ℝ} (hε : 0<ε) (s U : ℝ)
    (hfinite : ∀ᶠ n in atTop,countMargins i (G n:Measure (ℝ × ℝ))
      (N n) (c n) (b n) (θ n) ε) (q j : ℕ) :
    Tendsto (fun n => (N n:ℝ)*∫ ω : Fin (N n) → RowRival,
      ((imbalanceSum ω).natAbs:ℝ)^j*
        |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
          emptyMoment i (c n) (b n) (τ n) q ω|
        ∂Measure.pi (fun _ : Fin (N n) =>
          tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))) atTop (𝓝 0) := by
  let μ := fun n => tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  letI : ∀ n,IsProbabilityMeasure (μ n) := fun n => tiltedSource_probability i _ (hb n) _
  let P := fun n => Measure.pi (fun _ : Fin (N n) => μ n)
  let good := fun n => RivalGood.good (μ n) (TiltedGood.statistics s U) (N n) ε
  let F := fun n => fun ω : Fin (N n) → RowRival =>
    ((imbalanceSum ω).natAbs:ℝ)^j*
      |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
        emptyMoment i (c n) (b n) (τ n) q ω|
  have hF (n : ℕ) : Measurable (F n) := by
    have hk : Measurable (fun ω : Fin (N n) → RowRival => ((imbalanceSum ω).natAbs:ℝ)) :=
      (measurable_of_countable (fun z : ℤ => (z.natAbs:ℝ))).comp measurable_imbalanceSum
    exact (hk.pow_const j).mul (((measurable_literalMoment i _ _ _ _ _ _).sub
      (measurable_emptyMoment i _ _ _ _)).abs)
  have hFb (n : ℕ) : ∀ᵐ ω ∂P n,0≤ F n ω ∧ F n ω≤2*(N n:ℝ)^(q+j) := by
    apply ae_of_all
    intro ω
    have h1 := low_literal_polynomial i (c n) (g n) (cm n) (hb n) (hbL n)
      (hgl n) (hbl n) (hg n).1 (hg n).2.1 (hg n).2.2 (hτ n) (hc n) q ω
    have h2 := emptyMoment_polynomial i (c n) (hb n) (hτ n) (hc n) q ω
    have hk : ((imbalanceSum ω).natAbs:ℝ)≤(N n:ℝ) := by
      exact_mod_cast (show (imbalanceSum ω).natAbs≤ N n by
        rw [← draws_eq_natAbs]
        exact draws_le ω)
    have hj := pow_le_pow_left₀ (Nat.cast_nonneg (imbalanceSum ω).natAbs) hk j
    have hd : |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q ω-
        emptyMoment i (c n) (b n) (τ n) q ω|≤2*(N n:ℝ)^q :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]; linarith [h1.2,h2.2])
    refine ⟨by dsimp [F]; positivity,?_⟩
    have hm := mul_le_mul hj hd (abs_nonneg _) (pow_nonneg (Nat.cast_nonneg _) j)
    dsimp only [F]
    convert! hm using 1
    rw [pow_add]
    ring
  have hbad : ∀ᶠ n in atTop,(P n).real (good n)ᶜ≤8*Real.exp (-(2*ε^2)*(N n:ℝ)) := by
    apply Eventually.of_forall
    intro n
    have h := TiltedGood.source_good_complement i (G n:Measure (ℝ × ℝ))
      (hb n) (θ n) s U (hNpos n) hε.le
    convert! h using 1
    ring
  have ht := rare_bad_event_replacement μ N hN F hF (fun n => (good n)ᶜ)
    (fun n => (RivalGood.measurable_good _ _ (TiltedGood.statistics_measurable s U) _ _).compl)
    (q+j) (by norm_num : (0:ℝ)≤2) (by norm_num : (0:ℝ)≤8)
    (by positivity : 0<2*ε^2) hFb hbad
  apply ht.congr'
  filter_upwards [hfinite] with n hn
  apply congrArg ((N n:ℝ)*·)
  have hno (k : Fin (N n)) :=
    (measurePreserving_eval (fun _ : Fin (N n) => μ n) k).quasiMeasurePreserving.ae
      (TiltedGood.tilted_no_active_tag i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hno] with ω hω
  by_cases hgood : ω∈good n
  · have hv := source_valid_counts i (G n:Measure (ℝ × ℝ)) (hb n) (hNpos n)
      hn.1 hn.2.1 hn.2.2 ω hω hgood
    have he := literal_eq_empty_on_valid_counts i (c n) (g n) (cm n) (hb n) (hbL n)
      (hgl n) (hbl n) (hg n).1 (hg n).2.1 (hg n).2.2 (τ n) q ω hv
    simp only [indicator_of_notMem (show ω∉(good n)ᶜ from by simpa only [mem_compl_iff,not_not] using hgood),F,he,
      sub_self,abs_zero,mul_zero]
  · exact indicator_of_mem (show ω∈(good n)ᶜ from hgood) _

theorem original_low_literal_moments_test (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ τ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n)
    (hb : ∀ n,0< b n) (hbL : ∀ n,b n≤(g n).multiplier)
    (hgl : ∀ n,0<(g n).multiplier-(g n).radius)
    (hbl : ∀ n,b n≤(g n).multiplier-(g n).radius)
    (hc : ∀ n,(c n:ℝ)≤ A.N n)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    {τ₀ lo hi ε : ℝ} (hlo : 0< lo) (hθ : ∀ n,lo≤τ n ∧ τ n≤ hi)
    (hθlim : Tendsto τ atTop (𝓝 τ₀)) (hτ₀ : 0<τ₀) (hε : 0<ε) (s U : ℝ)
    (hfinite : ∀ᶠ n in atTop,countMargins i (G n:Measure (ℝ × ℝ))
      (A.N n) (c n) (b n) (θ n) ε) :
    ∀ q : Fin 3,Tendsto (fun n => (A.N n:ℝ)*
      ∫ ω : Fin (A.N n) → RowRival,literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))
      atTop (𝓝 (density A.vX A.vY*(q.val.factorial:ℝ)/τ₀^(q.val+1))) := by
  have he := original_empty_moments i A hgap b τ r c hY hcenter hmatch hlo hθ hθlim hτ₀
  intro q
  have hb0 := original_low_count_replacement i G A.N c A.market
    (fun n => Nat.cast_pos.mp (A.N_pos n)) b θ τ g cm hb hbL hgl hbl
    (fun n => hlo.le.trans (hθ n).1) hc hg hε s U hfinite q.val 0
  have hb1 : Tendsto (fun n => (A.N n:ℝ)*∫ ω : Fin (A.N n) → RowRival,
      |literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω-
        emptyMoment i (c n) (b n) (τ n) q.val ω|
      ∂Measure.pi (fun _ : Fin (A.N n) => A.law n)) atTop (𝓝 0) := by
    simpa only [hlaw,pow_zero,one_mul] using hb0
  have hdiff : Tendsto (fun n =>
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → RowRival,
        literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))-
      (A.N n:ℝ)*(∫ ω : Fin (A.N n) → RowRival,
        emptyMoment i (c n) (b n) (τ n) q.val ω
          ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hb1
    apply Eventually.of_forall
    intro n
    have h1 : Integrable (literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val)
        (Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
      Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val)
      (measurable_literalMoment i _ _ _ _ _ _).aemeasurable (ae_of_all _ fun ω =>
        low_literal_polynomial i _ _ _ (hb n) (hbL n) (hgl n) (hbl n)
          (hg n).1 (hg n).2.1 (hg n).2.2 (hlo.le.trans (hθ n).1) (hc n) q.val ω)
    have h2 : Integrable (emptyMoment i (c n) (b n) (τ n) q.val)
        (Measure.pi (fun _ : Fin (A.N n) => A.law n)) :=
      Integrable.of_mem_Icc 0 ((A.N n:ℝ)^q.val)
      (measurable_emptyMoment i _ _ _ _).aemeasurable (ae_of_all _ fun ω =>
        emptyMoment_polynomial i _ (hb n) (hlo.le.trans (hθ n).1) (hc n) q.val ω)
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos (A.N_pos n),← integral_sub h1 h2]
    apply mul_le_mul_of_nonneg_left _ (A.N_pos n).le
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (f:=fun ω => literalMoment i (c n) (g n) (cm n) (b n) (τ n) q.val ω-
        emptyMoment i (c n) (b n) (τ n) q.val ω)
      (μ:=Measure.pi (fun _ : Fin (A.N n) => A.law n))
  have h := hdiff.add (he q)
  convert! h using 1
  · funext n
    ring
  · simp

theorem original_low_literal_moments (i : Row)
    (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (A : CenteredArray RowRival) [∀ n,Nonempty (Fin (A.N n))] (hgap : A.CompactGap)
    (b θ r : ℕ → ℝ) (c : ℕ → ℕ) (g : ℕ → GuardData)
    (cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ)
    (hlaw : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))
    (hY : ∀ n,A.Y n=integerSign)
    (hcenter : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n)
    (hmatch : ∀ᶠ n in atTop,(c n:ℝ)=(A.N n:ℝ)*r n)
    (hb : ∀ n,0< b n) (hbL : ∀ n,b n≤(g n).multiplier)
    (hgl : ∀ n,0<(g n).multiplier-(g n).radius)
    (hbl : ∀ n,b n≤(g n).multiplier-(g n).radius)
    (hc : ∀ n,(c n:ℝ)≤ A.N n)
    (hg : ∀ n,0<(g n).margin ∧ 0<(g n).population ∧ 0<(g n).requiredDemand)
    {θ₀ lo hi ε : ℝ} (hlo : 0< lo) (hθ : ∀ n,lo≤θ n ∧ θ n≤ hi)
    (hθlim : Tendsto θ atTop (𝓝 θ₀)) (hθ₀ : 0<θ₀) (hε : 0<ε) (s U : ℝ)
    (hfinite : ∀ᶠ n in atTop,countMargins i (G n:Measure (ℝ × ℝ))
      (A.N n) (c n) (b n) (θ n) ε) :
    ∀ q : Fin 3,Tendsto (fun n => (A.N n:ℝ)*
      ∫ ω : Fin (A.N n) → RowRival,literalMoment i (c n) (g n) (cm n) (b n) (θ n) q.val ω
        ∂Measure.pi (fun _ : Fin (A.N n) => A.law n))
      atTop (𝓝 (density A.vX A.vY*(q.val.factorial:ℝ)/θ₀^(q.val+1))) := by
  exact original_low_literal_moments_test i G A hgap b θ θ r c g cm
    hlaw hY hcenter hmatch hb hbL hgl hbl hc hg hlo hθ hθlim hθ₀ hε s U hfinite

end FCAppendix.Affine.Uniform06.EqualOnlyCountTransfer
