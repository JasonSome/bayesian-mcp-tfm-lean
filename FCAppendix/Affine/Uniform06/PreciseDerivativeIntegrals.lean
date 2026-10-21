import FCAppendix.Affine.Uniform06.PreciseSourceSequence

noncomputable section
namespace FCAppendix.Affine.Uniform06.PreciseDerivativeIntegrals

open PreciseSourceSequence.Data
open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT PhysicalSourceMoments RawMomentPartition ClampedMomentBounds
open LiteralBadCountTransfer SamplingPopulation EarlyCoarseMargins
open PreciseSourceSequence SourceDerivativeBounds DerivativeMeasurableBounds
open MovingKernelLimits DerivativeScaleLimits UnguardedRareMoment

variable {i : Row} (S : Data i)

local instance data_row_probability (n : ℕ) : IsProbabilityMeasure (S.P n) := by
  dsimp only [P]
  infer_instance

def mainIntegral (q n : ℕ) : ℝ := ∫ ω,tiltedMain i (S.c n) (S.g n) (S.cm n)
  (S.b n) (S.θ n) q ω ∂S.P n
def guardIntegral (q n : ℕ) : ℝ := ∫ ω,tiltedGuard i (S.c n) (S.g n) (S.cm n)
  (S.b n) (S.θ n) q ω ∂S.P n
def mainErrorOne (n : ℕ) : ℝ := ∫ ω,
  |tiltedMain i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1 ω-
    literalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 0 ω/(xi i*S.b n)| ∂S.P n
def mainErrorTwo (n : ℕ) : ℝ := ∫ ω,
  |tiltedMain i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 2 ω-
    2*physicalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1 ω/(xi i*S.b n)| ∂S.P n

theorem zero_bound (hband : S.ReceiptBand) (n : ℕ) :
    ∀ᵐ ω ∂S.P n,literalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 0 ω∈Icc (0:ℝ) 1 := by
  simpa only [P,S.raw_law] using source_zero_moment_unit i (S.G n:Measure (ℝ × ℝ))
    (S.c n) (S.g n) (S.cm n) (S.bid_pos n) (S.bid_multiplier n) (S.guard_lower_pos n)
    (S.theta_pos n).le (S.cap_rivals n) (S.guard_positive n) (S.actual_receipt_case hband n)

theorem zero_integrable (hband : S.ReceiptBand) (n : ℕ) :
    Integrable (literalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 0) (S.P n) :=
  Integrable.of_mem_Icc 0 1 (measurable_literalMoment i _ _ _ _ _ _).aemeasurable
    (zero_bound S hband n)

theorem physical_integrable (hband : S.ReceiptBand) (q : ℕ) (hq : 0< q) (n : ℕ) :
    Integrable (physicalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) q) (S.P n) := by
  apply Integrable.of_mem_Icc 0 1 (measurable_physicalMoment i _ _ _ _ _ _).aemeasurable
  filter_upwards [zero_bound S hband n] with ω hω
  have hh := physicalMoment_le_strict_zero i (S.c n) (S.g n) (S.cm n)
    (S.bid_pos n) (S.θ n) q hq ω
  exact ⟨hh.1,hh.2.trans hω.2⟩

theorem main_integrable (hband : S.ReceiptBand) (q n : ℕ) :
    Integrable (tiltedMain i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) q) (S.P n) := by
  have hξ := xi_pos i
  have hb := S.bid_pos n
  apply Integrable.of_mem_Icc 0 ((q:ℝ)/(xi i*S.b n))
    (measurable_tiltedMain i _ _ _ _ _ _).aemeasurable
  filter_upwards [zero_bound S hband n] with ω hω
  have hh := tiltedMain_bounded_by_literal i (S.c n) (S.g n) (S.cm n)
    (S.bid_pos n) (S.bid_multiplier n) (S.guard_positive n).1
    (S.guard_positive n).2.1 (S.guard_positive n).2.2 (S.θ n) q ω
  refine ⟨hh.1,hh.2.trans ?_⟩
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hω.2
    (show 0≤(q:ℝ)/(xi i*S.b n) by positivity)

theorem guard_integrable (hband : S.ReceiptBand) (q : ℕ) (hq : 0< q) (n : ℕ) :
    Integrable (tiltedGuard i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) q) (S.P n) := by
  rcases hband with hlow | ⟨e,he,hreceipt⟩
  · have hz : tiltedGuard i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) q=
        (fun _ : Fin (S.A.N n) → RowRival => (0:ℝ)) := by
      funext ω
      exact tiltedGuard_low_zero i (S.c n) (S.g n) (S.cm n) (hlow n) (S.θ n) q ω
    rw [hz]
    exact MeasureTheory.integrable_zero (Fin (S.A.N n) → RowRival) ℝ (S.P n)
  · have hraw := RawSamplingBounds.original_receipt_h_bounds i (S.G n:Measure (ℝ × ℝ))
      (ReceiptGap.cap_bounds i).1 (S.bid_pos n) (S.bid_cap n) he (S.law_cap n)
      (hreceipt n) (S.θ n) (S.g n)
    have hh : ∀ᵐ x ∂S.A.law n,0≤ rawH (xi i) (S.b n) x := by
      rw [S.raw_law]
      exact hraw.mono fun _ h => h.1
    have hcoord : ∀ᵐ ω ∂S.P n,∀ j,0≤ rawH (xi i) (S.b n) (ω j) :=
      ae_all_iff.mpr fun j =>
        (measurePreserving_eval (fun _ : Fin (S.A.N n) => S.A.law n) j).quasiMeasurePreserving.ae hh
    apply Integrable.of_mem_Icc 0
      (1/(xi i*((S.g n).multiplier-(S.g n).radius)*(S.g n).margin*(S.g n).population))
      (measurable_tiltedGuard i _ _ _ _ _ _).aemeasurable
    filter_upwards [hcoord] with ω hω
    exact tiltedGuard_high_bound i (S.c n) (S.g n) (S.cm n) (S.bid_pos n)
      (S.bid_multiplier n) (S.bid_rejection n) (S.high_seed_below he hreceipt n)
      (S.guard_lower_pos n) (S.radius_nonneg n)
      (S.guard_positive n).1 (S.guard_positive n).2.1 (S.guard_positive n).2.2
      (S.theta_pos n).le q hq ω hω

theorem velocity_integral_partition (hband : S.ReceiptBand) (q : ℕ) (hq : 0< q) (n : ℕ) :
    S.V q n=mainIntegral S q n+guardIntegral S q n := by
  dsimp only [V,mainIntegral,guardIntegral]
  rw [← integral_add (main_integrable S hband q n) (guard_integrable S hband q hq n)]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => tiltedVelocity_eq_main_add_guard i (S.c n) (S.g n) (S.cm n)
    (S.bid_pos n) (S.bid_multiplier n) (S.guard_lower_pos n) (S.radius_nonneg n)
    (S.guard_positive n).1 (S.guard_positive n).2.1 (S.guard_positive n).2.2 (S.θ n) q ω

theorem actual_normalized_main_errors (hband : S.ReceiptBand) :
    Tendsto (fun n => (S.A.N n:ℝ)*mainErrorOne S n) atTop (𝓝 0) ∧
    Tendsto (fun n => (S.A.N n:ℝ)^2*mainErrorTwo S n) atTop (𝓝 0) := by
  have hξ := xi_pos i
  obtain ⟨Γ,B,hB,hΓ,hm,hC,hR⟩ := S.constructed_first_second hband
  obtain ⟨BC,hBC,hBCe⟩ := shared_eventually_bounded hΓ hC
  obtain ⟨BR,hBR,hBRe⟩ := shared_eventually_bounded hΓ hR
  obtain ⟨BZ,hBZ,hBZe⟩ := shared_eventually_bounded hΓ (hm (0:Fin 3))
  let BB := BC+BR+BZ
  have hBB : 0≤ BB := by dsimp [BB]; linarith
  have hc : ∀ᶠ n in atTop,|(S.A.N n:ℝ)^2*S.C n|≤ BB :=
    hBCe.mono fun n hn => hn.trans (by dsimp [BB]; linarith)
  have hr : ∀ᶠ n in atTop,|(S.A.N n:ℝ)^3*S.R n|≤ BB :=
    hBRe.mono fun n hn => hn.trans (by dsimp [BB]; linarith)
  have hz : ∀ᶠ n in atTop,|(S.A.N n:ℝ)*S.Z 0 n|≤ BB :=
    hBZe.mono fun n hn => hn.trans (by dsimp [BB]; linarith)
  obtain ⟨εc,hεc,Q,hQ,hfin⟩ := S.finite_margins
  let U := ReceiptGap.cap i
  let lo := floorPrice i
  let γ := Q/(4*U)
  have hU : 0< U := (ReceiptGap.cap_bounds i).1
  have hlo : 0< lo := (floorPrice_bounds i).1
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hloU : U/2≤ lo := by
    have hξ : xi i≤1/2 := by cases i <;> norm_num [xi,xiQ,etaQ]
    dsimp [lo,floorPrice]
    nlinarith
  have hlb (n : ℕ) : lo< S.b n := (floorPrice_bounds i).2.trans_le (S.bid_band n).1
  have hbs (n : ℕ) : S.b n< entry i := (S.bid_band n).2.trans_lt S.subentry
  have herror : ∀ᶠ n in atTop,
      0≤ mainErrorOne S n ∧ 0≤ mainErrorTwo S n ∧
      mainErrorOne S n≤ S.C n/(S.b n-lo)+S.Z 0 n/(xi i*(S.b n)^2*γ*(S.A.N n:ℝ))+
        16/(xi i*S.b n)*Real.exp (-(2*εc^2)*(S.A.N n:ℝ)) ∧
      mainErrorTwo S n≤2*S.R n/(S.b n-lo)+2*S.C n/(xi i*(S.b n)^2*γ*(S.A.N n:ℝ))+
        32/(xi i*S.b n)*Real.exp (-(2*εc^2)*(S.A.N n:ℝ)) := by
    filter_upwards [hfin] with n hn
    have hh := original_main_integral_errors i (S.G n:Measure (ℝ × ℝ)) (S.c n)
      (S.g n) (S.cm n) hlo (hlb n) (hbs n) hU (S.bid_cap n) hloU (le_refl lo)
      (Nat.cast_pos.mp (S.A.N_pos n)) (S.theta_pos n).le (S.cap_rivals n)
      (S.bid_multiplier n) (S.guard_lower_pos n) (S.guard_positive n)
      (S.actual_receipt_case hband n) (S.law_cap n) hεc hQ hn.2.2
      hn.1.1 hn.1.2.1 hn.1.2.2 hn.2.1
    refine ⟨integral_nonneg (fun _ => abs_nonneg _),integral_nonneg (fun _ => abs_nonneg _),?_⟩
    simpa only [← S.raw_law,mainErrorOne,mainErrorTwo,C,R,Z,P,tiltedPhysical,γ,U] using hh
  exact main_errors S.A.N S.A.market (fun n => Nat.cast_pos.mp (S.A.N_pos n))
    S.b S.C S.R (S.Z 0) (mainErrorOne S) (mainErrorTwo S) S.bid_limit hlo
    ((floorPrice_bounds i).2.trans_le S.limit_bid_band.1) (xi_pos i) hγ
    (by positivity : 0<2*εc^2) hBB hc hr hz herror

theorem actual_main_replacement (hband : S.ReceiptBand) :
    Tendsto (fun n => (S.A.N n:ℝ)*mainIntegral S 1 n-
      (S.A.N n:ℝ)*S.Z 0 n/(xi i*S.b n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (S.A.N n:ℝ)^2*mainIntegral S 2 n-
      2*(S.A.N n:ℝ)^2*S.C n/(xi i*S.b n)) atTop (𝓝 0) := by
  have he := actual_normalized_main_errors S hband
  constructor
  · apply squeeze_zero_norm' _ he.1
    apply Eventually.of_forall
    intro n
    have hi := main_integrable S hband 1 n
    have hz := (zero_integrable S hband n).div_const (xi i*S.b n)
    have hh := norm_integral_le_integral_norm (f:=fun ω =>
      tiltedMain i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1 ω-
        literalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 0 ω/(xi i*S.b n)) (μ:=S.P n)
    rw [integral_sub hi hz,integral_div] at hh
    rw [Real.norm_eq_abs,mul_div_assoc,← mul_sub,abs_mul,abs_of_pos (S.A.N_pos n)]
    simpa only [Real.norm_eq_abs,mainIntegral,mainErrorOne,Z] using
      mul_le_mul_of_nonneg_left hh (S.A.N_pos n).le
  · apply squeeze_zero_norm' _ he.2
    apply Eventually.of_forall
    intro n
    have hi := main_integrable S hband 2 n
    have hc := ((physical_integrable S hband 1 (by omega) n).const_mul 2).div_const (xi i*S.b n)
    have hh := norm_integral_le_integral_norm (f:=fun ω =>
      tiltedMain i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 2 ω-
        2*physicalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1 ω/(xi i*S.b n)) (μ:=S.P n)
    rw [integral_sub hi hc,integral_div,integral_const_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (S.A.N n:ℝ))
    rw [Real.norm_eq_abs]
    have hC : (∫ ω,physicalMoment i (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1 ω ∂S.P n)=S.C n := by
      simp only [C,tiltedPhysical,P,S.raw_law]
    rw [hC] at hm
    have heq : (S.A.N n:ℝ)^2*mainIntegral S 2 n-
        2*(S.A.N n:ℝ)^2*S.C n/(xi i*S.b n)=
        (S.A.N n:ℝ)^2*(mainIntegral S 2 n-2*S.C n/(xi i*S.b n)) := by ring
    rw [heq,abs_mul,abs_of_nonneg (sq_nonneg (S.A.N n:ℝ))]
    simpa only [Real.norm_eq_abs,mainIntegral,mainErrorTwo] using hm

theorem actual_guard_replacement (hband : S.ReceiptBand) (q : Fin 2) :
    Tendsto (fun n => (S.A.N n:ℝ)^(q.val+1)*guardIntegral S (q.val+1) n) atTop (𝓝 0) := by
  have hξ := xi_pos i
  rcases hband with hlow | ⟨e,he,hreceipt⟩
  · have hz (n : ℕ) : guardIntegral S (q.val+1) n=0 := by
      dsimp only [guardIntegral]
      have h := integral_congr_ae (μ:=S.P n) (ae_of_all _ fun ω =>
        tiltedGuard_low_zero i (S.c n) (S.g n) (S.cm n) (hlow n) (S.θ n) (q.val+1) ω)
      simpa only [integral_zero] using h
    simpa only [hz,mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
  · let U := ReceiptGap.cap i
    let lo := floorPrice i
    let η := e/(xi i*U)
    have hU : 0< U := (ReceiptGap.cap_bounds i).1
    have hlo : 0< lo := (floorPrice_bounds i).1
    have hη : 0<η := by dsimp [η]; positivity
    have hraw (n : ℕ) : ∀ᵐ x ∂S.A.law n,0≤ rawH (xi i) (S.b n) x ∧
        (0< rawWeight (xi i) (S.g n) x → η≤ rawH (xi i) (S.b n) x) := by
      rw [S.raw_law]
      exact RawSamplingBounds.original_receipt_h_bounds i (S.G n:Measure (ℝ × ℝ))
        hU (S.bid_pos n) (S.bid_cap n) he (S.law_cap n) (hreceipt n) (S.θ n) (S.g n)
    obtain ⟨B,hB,hBe⟩ := eventual_unguarded_bound i S.A S.gap S.b S.θ S.r S.c S.g
      S.bid_pos S.raw_sign S.raw_center S.cap_rivals S.theta_lower_pos S.theta_band hη hraw
    obtain ⟨εc,hεc,Q,hQ,hfin⟩ := S.finite_margins
    let γ := Q/(4*U)
    let a0 := cutoff i/4
    let K0 := 1/(xi i*a0*S.ε)
    let J0 := xi i/((cutoff i/2-lo)*γ)
    let K := fun n => 1/(xi i*((S.g n).multiplier-(S.g n).radius)*
      (S.g n).margin*(S.g n).population)
    let J := fun n => xi i/((S.b n-lo)*γ)
    let T := fun n => ∫ ω,unguardedRow i (S.c n) (S.g n) (S.b n) (S.θ n) (q.val+1) ω ∂S.P n
    have hγ : 0<γ := by dsimp [γ]; positivity
    have ha0 : 0< a0 := div_pos (cutoff_pos i) (by norm_num)
    have hgap : 0< cutoff i/2-lo := sub_pos.mpr (floorPrice_bounds i).2
    have hε := S.margin_pos
    have hK0 : 0< K0 := by dsimp [K0]; positivity
    have hJ0 : 0< J0 := by dsimp [J0]; positivity
    have hlb (n : ℕ) : lo< S.b n := (floorPrice_bounds i).2.trans_le (S.bid_band n).1
    have hbs (n : ℕ) : S.b n< entry i := (S.bid_band n).2.trans_lt S.subentry
    have hloU : U/2≤ lo := by
      have hξ : xi i≤1/2 := by cases i <;> norm_num [xi,xiQ,etaQ]
      dsimp [lo,floorPrice]
      nlinarith
    have hseed (n : ℕ) : (S.g n).seedCutoff< S.b n := by
      rw [(S.literal_fields n).seed_eq]
      have hthreshold : cutoff i/2<(1-xi i/2)*U := by
        dsimp only [U]
        rw [ReceiptGap.cap_scaled]
        have hcoef : (1/2:ℝ)<(1-xi i/2)*ReceiptGap.capFactor i := by
          cases i <;> norm_num [ReceiptGap.capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
        nlinarith [mul_lt_mul_of_pos_right hcoef (cutoff_pos i)]
      linarith [hreceipt n]
    have hK : ∀ᶠ n in atTop,0≤ K n ∧ K n≤ K0/(S.A.N n:ℝ) := by
      apply Eventually.of_forall
      intro n
      have hNpos := S.A.N_pos n
      have hεn := (S.guard_positive n).1
      have hMn := (S.guard_positive n).2.1
      have hgln := S.guard_lower_pos n
      have hglo : a0≤(S.g n).multiplier-(S.g n).radius := by
        rw [(S.literal_fields n).radius_eq]
        dsimp only [a0,SourcePrefixConstructor.radius]
        nlinarith [cutoff_pos i,(S.bid_band n).1,S.bid_multiplier n]
      have hd0 : 0< xi i*a0*S.ε*(S.A.N n:ℝ) := by positivity
      have hd : xi i*a0*S.ε*(S.A.N n:ℝ)≤
          xi i*((S.g n).multiplier-(S.g n).radius)*(S.g n).margin*(S.g n).population := by
        apply mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left hglo (xi_pos i).le)
            (S.margin_lower n) S.margin_pos.le (by positivity))
          (S.population_rivals n) (S.A.N_pos n).le (by positivity)
      refine ⟨by dsimp only [K]; positivity,?_⟩
      have hh := one_div_le_one_div_of_le hd0 hd
      convert! hh using 1
      dsimp only [K,K0]
      field_simp [hd0.ne',(xi_pos i).ne',ha0.ne',S.margin_pos.ne',(S.A.N_pos n).ne']
    have hJ : ∀ᶠ n in atTop,0≤ J n ∧ J n≤ J0 := by
      apply Eventually.of_forall
      intro n
      have hd : 0<(S.b n-lo)*γ := mul_pos (sub_pos.mpr (hlb n)) hγ
      refine ⟨by dsimp [J]; positivity,?_⟩
      apply (div_le_div_iff₀ hd (mul_pos hgap hγ)).mpr
      nlinarith [mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (S.bid_band n).1 hγ.le) (xi_pos i).le]
    have hT : ∀ᶠ n in atTop,0≤ T n ∧ (S.A.N n:ℝ)*T n≤ B := by
      filter_upwards [hBe] with n hn
      exact ⟨integral_nonneg (unguardedRow_nonneg i _ _ _ _ _),hn ⟨q.val+1,by omega⟩⟩
    have hF : ∀ᶠ n in atTop,0≤ guardIntegral S (q.val+1) n ∧
        guardIntegral S (q.val+1) n≤ K n*(J n/(S.A.N n:ℝ))^(q.val+1)*T n+
          8*K n*Real.exp (-(2*εc^2)*(S.A.N n:ℝ)) := by
      filter_upwards [hfin] with n hn
      have hh := original_guard_integral_bound i (S.G n:Measure (ℝ × ℝ)) (S.c n)
        (S.g n) (S.cm n) hlo (hlb n) (hbs n) hU (S.bid_cap n) hloU (le_refl lo)
        (Nat.cast_pos.mp (S.A.N_pos n)) (S.theta_pos n).le (S.cap_rivals n)
        (S.bid_multiplier n) (S.bid_rejection n) (hseed n) (S.guard_lower_pos n)
        (S.radius_nonneg n) (S.guard_positive n)
        (by rw [← S.raw_law]; exact (hraw n).mono fun _ h => h.1)
        (S.law_cap n) hεc hQ hn.2.2 hn.1.1 hn.1.2.1 hn.1.2.2 hn.2.1 (q.val+1) (by omega)
      have heq : xi i/((S.b n-lo)*γ*(S.A.N n:ℝ))=J n/(S.A.N n:ℝ) := by
        dsimp only [J]
        rw [div_div]
      simpa only [← S.raw_law,guardIntegral,P,γ,U,K,T,heq] using hh
    exact guard_error S.A.N S.A.market (fun n => Nat.cast_pos.mp (S.A.N_pos n))
      (guardIntegral S (q.val+1)) T K J (q.val+1) hK0.le hJ0.le hB.le
      (by positivity : 0<2*εc^2) hT hK hJ hF

theorem actual_velocity_replacement (hband : S.ReceiptBand) :
    Tendsto (fun n => (S.A.N n:ℝ)*S.V 1 n-
      (S.A.N n:ℝ)*S.Z 0 n/(xi i*S.b n)) atTop (𝓝 0) ∧
    Tendsto (fun n => (S.A.N n:ℝ)^2*S.V 2 n-
      2*(S.A.N n:ℝ)^2*S.C n/(xi i*S.b n)) atTop (𝓝 0) := by
  have hm := actual_main_replacement S hband
  have hg1 := actual_guard_replacement S hband (0:Fin 2)
  have hg2 := actual_guard_replacement S hband (1:Fin 2)
  constructor
  · have hh := hm.1.add hg1
    convert! hh using 1
    · funext n
      rw [velocity_integral_partition S hband 1 (by omega) n]
      norm_num only [Fin.val_zero,Nat.reduceAdd,pow_one]
      ring
    · simp
  · have hh := hm.2.add hg2
    convert! hh using 1
    · funext n
      rw [velocity_integral_partition S hband 2 (by omega) n]
      norm_num only [Fin.val_one,Nat.reduceAdd]
      ring
    · simp

end FCAppendix.Affine.Uniform06.PreciseDerivativeIntegrals
