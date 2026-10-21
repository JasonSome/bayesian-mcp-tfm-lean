import FCAppendix.Affine.Uniform06.LiteralGammaMoments
import FCAppendix.Affine.Uniform06.SourcePhysicalRootTransfer
import FCAppendix.Affine.Uniform06.SourceLowPhysicalRootTransfer
import FCAppendix.Affine.Uniform06.SourceDerivativeBounds
import FCAppendix.Affine.Uniform06.DerivativeScaleLimits
import FCAppendix.Affine.Uniform06.SourcePrefixConstructor

noncomputable section
namespace FCAppendix.Affine.Uniform06.PreciseSourceSequence

open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT PhysicalSourceMoments RawMomentPartition ClampedMomentBounds
open LiteralBadCountTransfer SamplingPopulation EarlyCoarseMargins
open LiteralGuardRare SourcePrefixConstructor MovingKernelLimits

structure Data (i : Row) where
  G : ℕ → ProbabilityMeasure (ℝ × ℝ)
  joint_limit : Tendsto G atTop (𝓝 (FullJointLaw.law i))
  A : CenteredArray RowRival
  gap : A.CompactGap
  m : ℕ → ℕ
  market : Tendsto m atTop atTop
  rivals : ∀ n,A.N n=m n-1
  b : ℕ → ℝ
  θ : ℕ → ℝ
  r : ℕ → ℝ
  g : ℕ → GuardData
  cm : ∀ n,(Fin (A.N n) → Fin 4) → ℝ
  cmbar : ℕ → ℝ
  raw_law : ∀ n,A.law n=tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n)
  raw_sign : ∀ n,A.Y n=integerSign
  raw_center : ∀ n,∀ᵐ x ∂A.law n,A.X n x=demand (xi i) (b n) x-r n
  hi : ℝ
  Θ : ℝ
  t0 : ℝ
  b0 : ℝ
  θ0 : ℝ
  subentry : hi< entry i
  theta_lower_pos : 0< t0
  bid_band : ∀ n,b n∈Icc (cutoff i/2) hi
  theta_band : ∀ n,t0≤θ n ∧ θ n≤Θ
  bid_limit : Tendsto b atTop (𝓝 b0)
  theta_limit : Tendsto θ atTop (𝓝 θ0)
  value_marginal : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=LowChernoff.conditionalValueLaw i
  below_value : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),p.2≤ p.1
  box : ∀ n,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
    p∈EarlyJointCompactness.box (cutoff i) (ReceiptGap.cap i)
  early_active : ∀ᶠ n in atTop,∀ᵐ p ∂(G n:Measure (ℝ × ℝ)),
    p.1∈Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
      |p.2-ActiveGraphComponent.activeBid i p.1|≤ cutoff i/10000
  matching : ∀ᶠ n in atTop,(∫ x,demand (xi i) (b n) x
    ∂tiltedSource i (G n:Measure (ℝ × ℝ)) (b n) (θ n))=
      (capacity (m n):ℝ)/(A.N n:ℝ)
  multiplier_limit : Tendsto (fun n => (g n).multiplier) atTop (𝓝 (entry i))
  literal_fields : ∀ n,LiteralFields i (g n)
  population_eq : ∀ n,(g n).population=(m n:ℝ)
  bid_multiplier : ∀ n,b n≤(g n).multiplier
  guard_lower_pos : ∀ n,0<(g n).multiplier-(g n).radius
  bid_rejection : ∀ n,b n≤(g n).rejectionRoot
  ε : ℝ
  Kcount : ℝ
  margin_pos : 0<ε
  margin_lower : ∀ n,ε≤(g n).margin
  count_constant_nonneg : 0≤ Kcount
  count_receipt : ∀ n,∀ᵐ ω ∂Measure.pi (fun _ : Fin (A.N n) => A.law n),
    |cm n (fun j => (ω j).1)/(g n).population-cmbar n|≤
      Kcount*(deviationSum (A.law n) (xi i) (g n) ω+(g n).population⁻¹)

namespace Data

variable {i : Row} (S : Data i)

instance source_nonempty (n : ℕ) : Nonempty (Fin (S.A.N n)) :=
  ⟨⟨0,Nat.cast_pos.mp (S.A.N_pos n)⟩⟩

def c : ℕ → ℕ := fun n => capacity (S.m n)
def P (n : ℕ) : Measure (Fin (S.A.N n) → RowRival) := Measure.pi (fun _ => S.A.law n)
def g0 : GuardData := {S.g 0 with multiplier:=entry i}
def C (n : ℕ) : ℝ := tiltedPhysical i (S.G n:Measure (ℝ × ℝ))
  (S.A.N n) (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 1
def R (n : ℕ) : ℝ := tiltedPhysical i (S.G n:Measure (ℝ × ℝ))
  (S.A.N n) (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) 2
def Z (q n : ℕ) : ℝ := ∫ ω,literalMoment i (S.c n) (S.g n) (S.cm n)
  (S.b n) (S.θ n) q ω ∂S.P n
def V (q n : ℕ) : ℝ := ∫ ω,DerivativeMeasurableBounds.tiltedVelocity i (S.c n)
  (S.g n) (S.cm n) (S.b n) (S.θ n) q ω ∂S.P n
def ν : ℝ := FullReciprocalMean.nu i S.b0 S.θ0
def d : ℝ := density S.A.vX S.A.vY

def ReceiptBand : Prop :=
  (∀ n,S.b n≤(S.g n).multiplier-(S.g n).radius) ∨
  ∃ e>0,∀ n,(1-xi i/2)*ReceiptGap.cap i+e≤ S.b n

theorem bid_pos (n : ℕ) : 0< S.b n :=
  (half_pos (cutoff_pos i)).trans_le (S.bid_band n).1
theorem limit_bid_band : S.b0∈Icc (cutoff i/2) S.hi :=
  isClosed_Icc.mem_of_tendsto S.bid_limit (Eventually.of_forall S.bid_band)
theorem limit_bid_pos : 0< S.b0 := (half_pos (cutoff_pos i)).trans_le S.limit_bid_band.1
theorem limit_bid_subentry : S.b0< entry i := S.limit_bid_band.2.trans_lt S.subentry
theorem theta_pos (n : ℕ) : 0< S.θ n := S.theta_lower_pos.trans_le (S.theta_band n).1
theorem limit_theta_pos : 0< S.θ0 := S.theta_lower_pos.trans_le
  (isClosed_Icc.mem_of_tendsto S.theta_limit (Eventually.of_forall S.theta_band)).1
theorem theta_upper_pos : 0< S.Θ := (S.theta_pos 0).trans_le (S.theta_band 0).2
theorem nu_pos : 0< S.ν := FullReciprocalMean.nu_pos i S.limit_bid_pos S.limit_bid_subentry S.θ0
theorem density_pos : 0< S.d := MixedIntervalLLT.density_pos S.A.vX_pos S.A.vY_pos
theorem bid_cap (n : ℕ) : S.b n≤ ReceiptGap.cap i :=
  (S.bid_band n).2.trans (S.subentry.le.trans (ReceiptGap.entry_below_cap i).le)
theorem law_cap (n : ℕ) : ∀ᵐ p ∂(S.G n:Measure (ℝ × ℝ)),p.2≤ ReceiptGap.cap i :=
  (S.box n).mono fun _ hp => hp.2.2
theorem market_two (n : ℕ) : 2≤ S.m n := by
  have hn := Nat.cast_pos.mp (S.A.N_pos n)
  rw [S.rivals] at hn
  omega
theorem cap_rivals (n : ℕ) : (S.c n:ℝ)≤ S.A.N n := by
  rw [S.rivals]
  have hc : capacity (S.m n)≤ S.m n-1 := by
    unfold capacity
    have hm := S.market_two n
    omega
  exact_mod_cast hc
theorem floor_error (n : ℕ) : |(S.c n:ℝ)-(S.A.N n:ℝ)*rho|≤1 := by
  rw [S.rivals]
  exact SourceCoarseIntegral.capacity_centered_error (S.market_two n)
theorem guard_positive (n : ℕ) :
    0<(S.g n).margin ∧ 0<(S.g n).population ∧ 0<(S.g n).requiredDemand := by
  refine ⟨(S.literal_fields n).margin_pos,(S.literal_fields n).population_pos,?_⟩
  rw [(S.literal_fields n).demand_eq]
  exact (EntryEarlySourceLimits.requiredDemand_bounds i).1
theorem radius_nonneg (n : ℕ) : 0≤(S.g n).radius := by
  rw [(S.literal_fields n).radius_eq]
  exact (div_pos (cutoff_pos i) (by norm_num : (0:ℝ)<10000)).le
theorem radius_small (n : ℕ) : (S.g n).radius≤ cutoff i/100 := by
  rw [(S.literal_fields n).radius_eq]
  unfold radius
  nlinarith [cutoff_pos i]
theorem population_rivals (n : ℕ) : (S.A.N n:ℝ)≤(S.g n).population := by
  rw [S.population_eq,S.rivals]
  exact_mod_cast Nat.sub_le (S.m n) 1

theorem center_mean (n : ℕ) : S.r n=∫ x,demand (xi i) (S.b n) x ∂S.A.law n := by
  have hi : Integrable (demand (xi i) (S.b n)) (S.A.law n) :=
    Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
      (ae_of_all _ (demand_bounds (xi_pos i) (S.bid_pos n)))
  have hh := integral_congr_ae (S.raw_center n)
  rw [S.A.mean_X,integral_sub hi (integrable_const (S.r n)),integral_const] at hh
  simp only [probReal_univ,one_smul] at hh
  linarith

theorem center_bounds (n : ℕ) : S.r n∈Icc (0:ℝ) 1 := by
  rw [S.center_mean n]
  have hi : Integrable (demand (xi i) (S.b n)) (S.A.law n) :=
    Integrable.of_mem_Icc 0 1 (measurable_demand _ _).aemeasurable
      (ae_of_all _ (demand_bounds (xi_pos i) (S.bid_pos n)))
  refine ⟨integral_nonneg (fun x => (demand_bounds (xi_pos i) (S.bid_pos n) x).1),?_⟩
  have h := integral_mono_ae hi (integrable_const (1:ℝ))
    (ae_of_all _ fun x => (demand_bounds (xi_pos i) (S.bid_pos n) x).2)
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem centered_capacity : ∀ᶠ n in atTop,(S.c n:ℝ)=(S.A.N n:ℝ)*S.r n := by
  filter_upwards [S.matching] with n hn
  rw [← S.raw_law,← S.center_mean] at hn
  have hh := (eq_div_iff (S.A.N_pos n).ne').mp hn
  change (capacity (S.m n):ℝ)=(S.A.N n:ℝ)*S.r n
  nlinarith

theorem high_seed_below {e : ℝ} (he : 0< e)
    (hreceipt : ∀ n,(1-xi i/2)*ReceiptGap.cap i+e≤ S.b n) (n : ℕ) :
    (S.g n).seedCutoff< S.b n := by
  rw [(S.literal_fields n).seed_eq]
  have hthreshold : cutoff i/2<(1-xi i/2)*ReceiptGap.cap i := by
    rw [ReceiptGap.cap_scaled]
    have hcoef : (1/2:ℝ)<(1-xi i/2)*ReceiptGap.capFactor i := by
      cases i <;> norm_num [ReceiptGap.capFactor,x,xQ,kappa,kappaQ,xi,xiQ,etaQ]
    nlinarith [mul_lt_mul_of_pos_right hcoef (cutoff_pos i)]
  linarith [hreceipt n]

theorem finite_margins : ∃ εc>0,∃ Q>0,∀ᶠ n in atTop,
    countMargins i (S.G n:Measure (ℝ × ℝ)) (S.A.N n) (S.c n) (S.b n) (S.θ n) εc ∧
    Q≤(TiltedGood.law i (S.G n:Measure (ℝ × ℝ)) (S.b n) (S.θ n)).real
      (CostAmplification.activeStrip (entry i) (ReceiptGap.cap i)) ∧ 12*εc≤ Q := by
  obtain ⟨lo,εc,Q,a,d,hlo,hεc,hQ,ha,hd,hfin⟩ :=
    eventual_source_margins i S.G S.m S.b S.θ S.g S.market S.subentry S.theta_upper_pos
      S.bid_band S.value_marginal (Eventually.of_forall S.law_cap) S.early_active
      (Eventually.of_forall fun n => ⟨S.theta_pos n,(S.theta_band n).2⟩)
      (by simpa only [← S.rivals] using S.matching) S.multiplier_limit
      (Eventually.of_forall S.radius_small) (Eventually.of_forall S.guard_positive)
  refine ⟨εc,hεc,Q,hQ,?_⟩
  filter_upwards [hfin] with n hn
  rcases hn with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hp,hrm,hs,hεQ,_,_,_,_⟩
  rw [← S.rivals] at hp hrm
  exact ⟨⟨S.floor_error n,hp,hrm⟩,hs,hεQ⟩

theorem actual_receipt_case (hband : S.ReceiptBand) (n : ℕ) :
    SourceDerivativeBounds.ReceiptCase i (S.G n:Measure (ℝ × ℝ)) (S.g n) (S.b n) (S.θ n) := by
  rcases hband with hlow | ⟨e,he,hreceipt⟩
  · exact Or.inl (hlow n)
  · exact Or.inr ((RawSamplingBounds.original_receipt_h_bounds i
      (S.G n:Measure (ℝ × ℝ)) (ReceiptGap.cap_bounds i).1 (S.bid_pos n)
      (S.bid_cap n) he (S.law_cap n) (hreceipt n) (S.θ n) (S.g n)).mono fun _ h => h.1)

theorem constructed_literal_moments (hband : S.ReceiptBand) :
    ∃ Γ : ℕ → ℝ,∃ B>0,(∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B) ∧
      ∀ q : Fin 3,Tendsto (fun n => (S.A.N n:ℝ)*S.Z q.val n-
        (S.d*(q.val.factorial:ℝ)/S.θ0^(q.val+1))*Γ n) atTop (𝓝 0) := by
  obtain ⟨εc,hεc,Q,hQ,hfin⟩ := S.finite_margins
  rcases hband with hlow | ⟨e,he,hreceipt⟩
  · refine ⟨fun _ => 1,1,by norm_num,Eventually.of_forall (fun _ => ⟨le_rfl,le_rfl⟩),?_⟩
    have hh := EqualOnlyCountTransfer.original_low_literal_moments i S.G S.A S.gap
      S.b S.θ S.r S.c S.g S.cm S.raw_law S.raw_sign S.raw_center S.centered_capacity
      S.bid_pos S.bid_multiplier S.guard_lower_pos hlow S.cap_rivals S.guard_positive
      S.theta_lower_pos S.theta_band S.theta_limit S.limit_theta_pos hεc (entry i)
      (ReceiptGap.cap i) (hfin.mono fun _ h => h.1)
    intro q
    have h := (hh q).sub_const (S.d*(q.val.factorial:ℝ)/S.θ0^(q.val+1))
    simpa only [Z,P,d,mul_one,sub_self] using h
  · have hg0 : S.g0.multiplier=entry i := rfl
    have hgreq0 : S.g0.requiredDemand=PrefixRoot.requiredDemand i :=
      (S.literal_fields 0).demand_eq
    have hh := LiteralGammaMoments.original_current_gamma_literal_moments i S.G
      S.joint_limit S.value_marginal S.below_value S.A S.gap S.b S.θ S.r S.c S.g S.g0
      S.cm S.cmbar S.raw_law S.raw_sign S.raw_center S.center_bounds S.centered_capacity
      S.cap_rivals S.bid_pos S.limit_bid_pos S.bid_limit S.theta_limit S.limit_theta_pos
      S.theta_lower_pos S.theta_band (ReceiptGap.cap_bounds i).1 S.law_cap S.bid_cap he hreceipt
      S.multiplier_limit hg0 hgreq0 (fun n => (S.literal_fields n).demand_eq.trans hgreq0.symm)
      (fun n => (S.guard_positive n).2.1) S.population_rivals S.margin_pos S.margin_lower
      S.count_constant_nonneg S.guard_lower_pos
      (fun n => by linarith [S.guard_lower_pos n,S.radius_nonneg n])
      (fun n => by rw [(S.literal_fields n).scale_eq]; exact div_pos (cutoff_pos i) (by norm_num))
      (half_pos (cutoff_pos i)) (by linarith [cutoff_pos i])
      (fun n => (S.literal_fields n).seed_eq) S.count_receipt S.bid_multiplier hεc
      (hfin.mono fun _ h => h.1)
    obtain ⟨B,hB,hΓ⟩ := hh.1
    refine ⟨fun n => GuardedSampledMoments.sourceGamma i (S.G n:Measure (ℝ × ℝ))
      (S.A.N n) (S.c n) (S.b n) (S.θ n) (S.g n) (S.cmbar n),B,hB,hΓ,?_⟩
    simpa only [Z,P,d] using hh.2

theorem constructed_response_replacement (hband : S.ReceiptBand) (q : Fin 2) :
    Tendsto (fun n => (S.A.N n:ℝ)^(q.val+2)*tiltedPhysical i (S.G n:Measure (ℝ × ℝ))
        (S.A.N n) (S.c n) (S.g n) (S.cm n) (S.b n) (S.θ n) (q.val+1)-
      (1/(S.b0*S.ν))^(q.val+1)*(S.A.N n:ℝ)*S.Z (q.val+1) n) atTop (𝓝 0) := by
  rcases hband with hlow | ⟨e,he,hreceipt⟩
  · exact SourceLowPhysicalRootTransfer.original_summed_response_replacement i S.G S.joint_limit
      S.A S.gap S.m S.market S.rivals S.b S.θ S.r S.g S.cm S.raw_law S.raw_sign S.raw_center
      S.subentry S.theta_lower_pos S.bid_band S.theta_band S.bid_limit S.theta_limit
      S.value_marginal S.box S.early_active S.matching S.multiplier_limit S.radius_small
      S.guard_positive (fun n => (S.literal_fields n).demand_eq) S.bid_multiplier
      S.guard_lower_pos hlow q
  · exact SourcePhysicalRootTransfer.original_summed_response_replacement i S.G S.joint_limit
      S.A S.gap S.m S.market S.rivals S.b S.θ S.r S.g S.cm S.raw_law S.raw_sign S.raw_center
      S.subentry S.theta_lower_pos he S.bid_band S.theta_band S.bid_limit S.theta_limit
      S.value_marginal S.box S.early_active S.matching S.multiplier_limit S.radius_small
      S.guard_positive (fun n => (S.literal_fields n).demand_eq) S.bid_multiplier hreceipt q

theorem constructed_first_second (hband : S.ReceiptBand) :
    ∃ Γ : ℕ → ℝ,∃ B>0,(∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B) ∧
      (∀ q : Fin 3,Tendsto (fun n => (S.A.N n:ℝ)*S.Z q.val n-
        (S.d*(q.val.factorial:ℝ)/S.θ0^(q.val+1))*Γ n) atTop (𝓝 0)) ∧
      Tendsto (fun n => (S.A.N n:ℝ)^2*S.C n-
        (S.d/(S.b0*S.ν*S.θ0^2))*Γ n) atTop (𝓝 0) ∧
      Tendsto (fun n => (S.A.N n:ℝ)^3*S.R n-
        (2*S.d/(S.b0^2*S.ν^2*S.θ0^3))*Γ n) atTop (𝓝 0) := by
  obtain ⟨Γ,B,hB,hΓ,hm⟩ := S.constructed_literal_moments hband
  have h1 := (S.constructed_response_replacement hband (0:Fin 2)).add
    ((hm (1:Fin 3)).const_mul (1/(S.b0*S.ν)))
  have h2 := (S.constructed_response_replacement hband (1:Fin 2)).add
    ((hm (2:Fin 3)).const_mul ((1/(S.b0*S.ν))^2))
  norm_num at h1 h2
  refine ⟨Γ,B,hB,hΓ,hm,?_,?_⟩
  · convert! h1 using 1
    · funext n
      dsimp only [C]
      field_simp [S.limit_bid_pos.ne',S.nu_pos.ne',S.limit_theta_pos.ne']
      ring
  · convert! h2 using 1
    · funext n
      dsimp only [R]
      field_simp [S.limit_bid_pos.ne',S.nu_pos.ne',S.limit_theta_pos.ne']
      ring

end Data
end FCAppendix.Affine.Uniform06.PreciseSourceSequence
