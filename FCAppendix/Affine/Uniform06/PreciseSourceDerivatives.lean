import FCAppendix.Affine.Uniform06.PreciseDerivativeIntegrals
import FCAppendix.Affine.Uniform06.DerivativeUntilting

noncomputable section
namespace FCAppendix.Affine.Uniform06.PreciseSourceDerivatives

open PreciseSourceSequence.Data
open MeasureTheory Set Filter LowBody
open scoped Topology BigOperators
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open MixedIntervalLLT PhysicalSourceMoments RawMomentPartition LiteralCoarsePath
open PreciseSourceSequence PreciseDerivativeIntegrals MovingKernelLimits
open DerivativeMeasurableBounds ExactUntilting FixedPriceCanonicalRows FixedPriceCanonicalIntegral

variable {i : Row} (S : Data i)

theorem constructed_four (hband : S.ReceiptBand) :
    ∃ Γ : ℕ → ℝ,∃ B>0,(∀ᶠ n in atTop,Γ n∈Icc (1:ℝ) B) ∧
      Tendsto (fun n => (S.A.N n:ℝ)^2*S.C n-
        (S.d/(S.b0*S.ν*S.θ0^2))*Γ n) atTop (𝓝 0) ∧
      Tendsto (fun n => (S.A.N n:ℝ)^3*S.R n-
        (2*S.d/(S.b0^2*S.ν^2*S.θ0^3))*Γ n) atTop (𝓝 0) ∧
      Tendsto (fun n => (S.A.N n:ℝ)*S.V 1 n-
        (S.d/(xi i*S.b0*S.θ0))*Γ n) atTop (𝓝 0) ∧
      Tendsto (fun n => (S.A.N n:ℝ)^2*S.V 2 n-
        (2*S.d/(xi i*S.b0^2*S.ν*S.θ0^2))*Γ n) atTop (𝓝 0) := by
  obtain ⟨Γ,B,hB,hΓ,hm,hC,hR⟩ := S.constructed_first_second hband
  have hv := actual_velocity_replacement S hband
  have hx0 : xi i*S.b0≠0 := (mul_pos (xi_pos i) S.limit_bid_pos).ne'
  have ha1 : Tendsto (fun n => 1/(xi i*S.b n)) atTop (𝓝 (1/(xi i*S.b0))) :=
    tendsto_const_nhds.div (S.bid_limit.const_mul (xi i)) hx0
  have ha2 : Tendsto (fun n => 2/(xi i*S.b n)) atTop (𝓝 (2/(xi i*S.b0))) :=
    tendsto_const_nhds.div (S.bid_limit.const_mul (xi i)) hx0
  have hm0 : Tendsto (fun n => (S.A.N n:ℝ)*S.Z 0 n-(S.d/S.θ0)*Γ n) atTop (𝓝 0) := by
    simpa only [Fin.val_zero,Nat.factorial_zero,Nat.cast_one,mul_one,Nat.zero_add,pow_one] using hm 0
  have h1 := hv.1.add (varying_multiplier hΓ hm0 ha1)
  have h2 := hv.2.add (varying_multiplier hΓ hC ha2)
  refine ⟨Γ,B,hB,hΓ,hC,hR,?_,?_⟩
  · convert h1 using 1
    · funext n
      field_simp [(xi_pos i).ne',S.limit_bid_pos.ne',S.limit_theta_pos.ne',(S.bid_pos n).ne']
      ring
    · simp
  · convert h2 using 1
    · funext n
      field_simp [(xi_pos i).ne',S.limit_bid_pos.ne',S.limit_theta_pos.ne',
        S.nu_pos.ne',(S.bid_pos n).ne']
      ring
    · simp

def castMargin {N M : ℕ} (h : N=M) (cm : (Fin N → Fin 4) → ℝ) :
    (Fin M → Fin 4) → ℝ := fun kind => cm (fun j => kind (Fin.cast h j))

theorem integral_cast {N M : ℕ} (h : N=M) (μ : Measure RowRival)
    (cm : (Fin N → Fin 4) → ℝ)
    (F : ∀ n,((Fin n → Fin 4) → ℝ) → (Fin n → RowRival) → ℝ) :
    (∫ ω : Fin N → RowRival,F N cm ω ∂Measure.pi (fun _ => μ))=
      ∫ ω : Fin M → RowRival,F M (castMargin h cm) ω ∂Measure.pi (fun _ => μ) := by
  subst M
  rfl

def sourceMargin (n : ℕ) : (Fin (S.m n-1) → Fin 4) → ℝ :=
  castMargin (S.rivals n) (S.cm n)

def sourceC (n : ℕ) : ℝ := sourceCanonicalMarginal i (S.m n)
  (S.G n:Measure (ℝ × ℝ)) (S.g n) (sourceMargin S n) (S.b n)
def sourceR (n : ℕ) : ℝ := sourceCanonicalDuplicate i (S.m n)
  (S.G n:Measure (ℝ × ℝ)) (S.g n) (sourceMargin S n) (S.b n)
def sourceCp (n : ℕ) : ℝ := Cprime i (S.m n)
  (S.G n:Measure (ℝ × ℝ)) (S.g n) (sourceMargin S n) (S.b n)
def sourceRp (n : ℕ) : ℝ := Rprime i (S.m n)
  (S.G n:Measure (ℝ × ℝ)) (S.g n) (sourceMargin S n) (S.b n)
def finiteLikelihood (n : ℕ) : ℝ := Real.exp (-cost (source i (S.G n:Measure (ℝ × ℝ)))
  (demand (xi i) (S.b n)) (S.θ n) (S.c n) (S.A.N n))

theorem finiteLikelihood_pos (n : ℕ) : 0< finiteLikelihood S n := Real.exp_pos _

theorem original_integral_identities (n : ℕ) :
    sourceC S n=(∫ ω : Fin (S.A.N n) → RowRival,
      originalRowMarginal (xi i) (S.c n) (S.g n) (S.cm n) (S.b n) ω
        ∂Measure.pi (fun _ => source i (S.G n:Measure (ℝ × ℝ)))) ∧
    sourceR S n=(∫ ω : Fin (S.A.N n) → RowRival,
      originalRowDuplicate (xi i) (S.c n) (S.g n) (S.cm n) (S.b n) ω
        ∂Measure.pi (fun _ => source i (S.G n:Measure (ℝ × ℝ)))) ∧
    sourceCp S n=(∫ ω : Fin (S.A.N n) → RowRival,
      rowVelocity (xi i) (S.c n) (S.g n) (S.cm n) 1 (S.b n) ω
        ∂Measure.pi (fun _ => source i (S.G n:Measure (ℝ × ℝ)))) ∧
    sourceRp S n=(∫ ω : Fin (S.A.N n) → RowRival,
      rowVelocity (xi i) (S.c n) (S.g n) (S.cm n) 2 (S.b n) ω
        ∂Measure.pi (fun _ => source i (S.G n:Measure (ℝ × ℝ)))) := by
  have hc := integral_cast (S.rivals n) (source i (S.G n:Measure (ℝ × ℝ))) (S.cm n)
    (fun N cm => originalRowMarginal (N:=N) (xi i) (S.c n) (S.g n) cm (S.b n))
  have hr := integral_cast (S.rivals n) (source i (S.G n:Measure (ℝ × ℝ))) (S.cm n)
    (fun N cm => originalRowDuplicate (N:=N) (xi i) (S.c n) (S.g n) cm (S.b n))
  have hv (q : ℕ) := integral_cast (S.rivals n) (source i (S.G n:Measure (ℝ × ℝ))) (S.cm n)
    (fun N cm => rowVelocity (N:=N) (xi i) (S.c n) (S.g n) cm q (S.b n))
  exact ⟨hc.symm,hr.symm,(hv 1).symm,(hv 2).symm⟩

theorem same_finite_factor (n : ℕ) :
    sourceC S n=finiteLikelihood S n*S.C n ∧
    sourceR S n=finiteLikelihood S n*S.R n ∧
    sourceCp S n=finiteLikelihood S n*S.V 1 n ∧
    sourceRp S n=finiteLikelihood S n*S.V 2 n := by
  have hid := original_integral_identities S n
  have ht (F : (Fin (S.A.N n) → RowRival) → ℝ) :=
    iid_reverse_tilt (source i (S.G n:Measure (ℝ × ℝ)))
      (measurable_demand (xi i) (S.b n))
      (ae_of_all _ (demand_bounds (xi_pos i) (S.bid_pos n)))
      (S.θ n) (S.c n) (S.A.N n) F
  have heC : S.C n=(∫ ω : Fin (S.A.N n) → RowRival,
      Real.exp (-S.θ n*deficit i (S.b n) (S.c n) ω)*
        originalRowMarginal (xi i) (S.c n) (S.g n) (S.cm n) (S.b n) ω ∂S.P n) := by
    dsimp only [C,tiltedPhysical,P]
    rw [S.raw_law]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => (physicalMoment_one_two i (S.c n) (S.g n) (S.cm n)
      (S.bid_multiplier n) (S.θ n) (S.guard_positive n).1 (S.guard_positive n).2.1
      (S.guard_positive n).2.2 ω).1
  have heR : S.R n=(∫ ω : Fin (S.A.N n) → RowRival,
      Real.exp (-S.θ n*deficit i (S.b n) (S.c n) ω)*
        originalRowDuplicate (xi i) (S.c n) (S.g n) (S.cm n) (S.b n) ω ∂S.P n) := by
    dsimp only [R,tiltedPhysical,P]
    rw [S.raw_law]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => (physicalMoment_one_two i (S.c n) (S.g n) (S.cm n)
      (S.bid_multiplier n) (S.θ n) (S.guard_positive n).1 (S.guard_positive n).2.1
      (S.guard_positive n).2.2 ω).2
  refine ⟨?_,?_,?_,?_⟩
  · rw [hid.1,heC]
    simpa only [finiteLikelihood,P,S.raw_law,tiltedSource,deficit] using
      ht (originalRowMarginal (xi i) (S.c n) (S.g n) (S.cm n) (S.b n))
  · rw [hid.2.1,heR]
    simpa only [finiteLikelihood,P,S.raw_law,tiltedSource,deficit] using
      ht (originalRowDuplicate (xi i) (S.c n) (S.g n) (S.cm n) (S.b n))
  · rw [hid.2.2.1]
    simpa only [finiteLikelihood,V,P,S.raw_law,tiltedVelocity,tiltedSource,deficit] using
      ht (rowVelocity (xi i) (S.c n) (S.g n) (S.cm n) 1 (S.b n))
  · rw [hid.2.2.2]
    simpa only [finiteLikelihood,V,P,S.raw_law,tiltedVelocity,tiltedSource,deficit] using
      ht (rowVelocity (xi i) (S.c n) (S.g n) (S.cm n) 2 (S.b n))

theorem ratio_identities (n : ℕ) :
    sourceCp S n/sourceC S n=S.V 1 n/S.C n ∧
    sourceR S n/sourceC S n=S.R n/S.C n ∧
    sourceRp S n/sourceC S n=S.V 2 n/S.C n := by
  have h := same_finite_factor S n
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
  by_cases hc : S.C n=0
  · simp only [hc,mul_zero,div_zero,and_self]
  · constructor
    · field_simp [hc,(finiteLikelihood_pos S n).ne']
    · constructor <;> field_simp [hc,(finiteLikelihood_pos S n).ne']

theorem relative_ratios (hband : S.ReceiptBand) :
    (∀ᶠ n in atTop,0< sourceC S n) ∧
    Tendsto (fun n => (sourceCp S n/sourceC S n)/(S.A.N n:ℝ))
      atTop (𝓝 (S.θ0*S.ν/xi i)) ∧
    Tendsto (fun n => (S.A.N n:ℝ)*(sourceR S n/sourceC S n))
      atTop (𝓝 (2/(S.b0*S.ν*S.θ0))) ∧
    Tendsto (fun n => sourceRp S n/sourceC S n) atTop (𝓝 (2/(xi i*S.b0))) ∧
    Tendsto (fun n => (sourceR S n/sourceC S n)*
      (xi i*S.b n*(sourceCp S n/sourceC S n))/2) atTop (𝓝 1) := by
  obtain ⟨Γ,B,hB,hΓ,hC,hR,hV1,hV2⟩ := constructed_four S hband
  have hh := four_kernel_ratios S.density_pos S.nu_pos S.limit_theta_pos (xi_pos i)
    S.limit_bid_pos S.A.N_pos S.bid_limit hΓ hC hR hV1 hV2
  refine ⟨?_,?_,?_,?_,?_⟩
  · filter_upwards [hh.1] with n hn
    rw [(same_finite_factor S n).1]
    exact mul_pos (finiteLikelihood_pos S n) hn
  · simpa only [(ratio_identities S _).1] using hh.2.1
  · simpa only [(ratio_identities S _).2.1] using hh.2.2.1
  · simpa only [(ratio_identities S _).2.2] using hh.2.2.2.1
  · simpa only [(ratio_identities S _).1,(ratio_identities S _).2.1] using hh.2.2.2.2

theorem classical_derivatives
    (hnull : ∀ n a,((S.G n:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (H : ℕ → ℝ)
    (hprefix : ∀ n,LiteralPrefixStieltjes.PrefixConditions (xi i) (S.g n) (H n))
    (hεM : ∀ n,1<(S.g n).margin*(S.g n).population)
    (hbH : ∀ n,S.b n< H n)
    (hbL : ∀ n,S.b n<(S.g n).multiplier)
    (hbz : ∀ n,S.b n<(S.g n).rejectionRoot)
    (hclip : ∀ n,(1-xi i)*ReceiptGap.cap i≤(S.g n).multiplier-(S.g n).radius) :
    ∀ n,
      HasDerivAt (sourceCanonicalMarginal i (S.m n) (S.G n:Measure (ℝ × ℝ))
        (S.g n) (sourceMargin S n)) (sourceCp S n) (S.b n) ∧
      HasDerivAt (sourceCanonicalDuplicate i (S.m n) (S.G n:Measure (ℝ × ℝ))
        (S.g n) (sourceMargin S n)) (sourceRp S n) (S.b n) := by
  intro n
  have hnon : ∀ᵐ p ∂(S.G n:Measure (ℝ × ℝ)),0≤ p.2 := (S.box n).mono fun _ hp => hp.2.1
  have ha : 0<(S.g n).radius := by
    rw [(S.literal_fields n).radius_eq]
    exact div_pos (cutoff_pos i) (by norm_num : (0:ℝ)<10000)
  have hbU : S.b n< ReceiptGap.cap i :=
    ((S.bid_band n).2.trans_lt S.subentry).trans (ReceiptGap.entry_below_cap i)
  exact source_canonical_derivatives i (S.m n) (S.G n:Measure (ℝ × ℝ)) (hnull n)
    hnon (S.law_cap n) (S.g n) (sourceMargin S n) (hprefix n) ha (hεM n)
    (S.bid_pos n) (hbH n) (hbL n) (hbz n) hbU (hclip n)

end FCAppendix.Affine.Uniform06.PreciseSourceDerivatives
