import FCAppendix.Affine.Uniform06.PreciseFamilyBridge
import FCAppendix.Affine.Uniform06.PreciseSourceDerivatives
import FCAppendix.Affine.Uniform06.OptimizedPhysicalRate

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePreciseFamily

open PreciseSourceSequence.Data
open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open PreciseSourceSequence PreciseSourceDerivatives RawTiltedSource RawMixedSource

section Data
variable {i : Row} (S : Data i)

theorem data_limit_in_rate_band : S.b0∈OptimizedPhysicalRate.band i :=
  ⟨S.limit_bid_band.1,S.limit_bid_subentry⟩

theorem data_mixed_matching : ∀ᶠ n in atTop,
    SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (S.b n)
      (S.G n:Measure (ℝ × ℝ)))) Prod.fst (S.θ n)=
        (capacity (S.m n):ℝ)/((S.m n-1:ℕ):ℝ) := by
  filter_upwards [S.matching] with n hn
  have hp : (∫ x,demand (xi i) (S.b n) x
      ∂tiltedSource i (S.G n:Measure (ℝ × ℝ)) (S.b n) (S.θ n))=
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (S.b n)
        (S.G n:Measure (ℝ × ℝ)))) Prod.fst (S.θ n) := by
    have hpres := tilted_point_preserving i (S.G n:Measure (ℝ × ℝ))
      (S.bid_pos n) (S.θ n)
    change (∫ x,Prod.fst (point (xi i) (S.b n) x) ∂_)=∫ y,Prod.fst y ∂_
    have hmap := hpres.map_eq
    dsimp only [MixedLaw.tiltedLaw] at hmap
    rw [← hmap]
    exact (integral_map hpres.measurable.aemeasurable measurable_fst.aestronglyMeasurable).symm
  rw [← hp,hn,S.rivals]

theorem data_theta_eq_constructed : S.θ0=OptimizedPhysicalRate.theta i S.b0 := by
  have hb0 := data_limit_in_rate_band S
  have hz := OptimizedPhysicalRate.normalized_mem_band i hb0
  obtain ⟨s,hs,hslim,hscore,_hrate,_hcost⟩ :=
    FullRateLimit.original_triangular_cost_limit i S.G S.joint_limit S.b S.θ
      S.bid_pos hz (by simpa only [OptimizedPhysicalRate.physical_scale] using S.bid_limit)
      S.m S.market (data_mixed_matching S)
  have he : S.θ0=s := tendsto_nhds_unique S.theta_limit hslim
  rw [← he] at hscore
  exact OptimizedPhysicalRate.theta_unique i hb0 hscore

theorem data_rate_coefficient : OptimizedPhysicalRate.A i S.b0=S.θ0*S.ν/xi i := by
  rw [OptimizedPhysicalRate.A_eq_theta_nu_div_xi,← data_theta_eq_constructed S]
  rfl

theorem data_A_tendsto :
    Tendsto (fun n => OptimizedPhysicalRate.A i (S.b n)) atTop
      (𝓝 (OptimizedPhysicalRate.A i S.b0)) := by
  apply ((OptimizedPhysicalRate.continuousOn_A i) S.b0 (data_limit_in_rate_band S)).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨S.bid_limit,Eventually.of_forall fun n =>
    ⟨(S.bid_band n).1,(S.bid_band n).2.trans_lt S.subentry⟩⟩

theorem data_market_pos (n : ℕ) : (0:ℝ)< S.m n := by
  exact_mod_cast (show 0< S.m n by have h:=S.market_two n; omega)

theorem data_rival_market_ratio :
    Tendsto (fun n => (S.A.N n:ℝ)/(S.m n:ℝ)) atTop (𝓝 1) := by
  have hi : Tendsto (fun n => (S.m n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp S.market)
  have hh : Tendsto (fun n => 1-(S.m n:ℝ)⁻¹) atTop (𝓝 (1:ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  apply hh.congr'
  exact Eventually.of_forall fun n => by
    change 1-(S.m n:ℝ)⁻¹=(S.A.N n:ℝ)/(S.m n:ℝ)
    rw [S.rivals,Nat.cast_sub (by have h:=S.market_two n; omega),Nat.cast_one]
    field_simp [(data_market_pos S n).ne']

theorem data_market_rival_ratio :
    Tendsto (fun n => (S.m n:ℝ)/(S.A.N n:ℝ)) atTop (𝓝 1) := by
  have hh := (data_rival_market_ratio S).inv₀ (by norm_num : (1:ℝ)≠0)
  simpa only [inv_one,inv_div] using hh

theorem data_relative_limits (hband : S.ReceiptBand) :
    (∀ᶠ n in atTop,0< sourceC S n) ∧
    Tendsto (fun n => sourceCp S n/
      ((S.m n:ℝ)*sourceC S n*OptimizedPhysicalRate.A i (S.b n))) atTop (𝓝 1) ∧
    Tendsto (fun n => (S.m n:ℝ)*xi i*S.b n*OptimizedPhysicalRate.A i (S.b n)*
      sourceR S n/(2*sourceC S n)) atTop (𝓝 1) ∧
    Tendsto (fun n => (xi i*S.b n/2)*(sourceRp S n/sourceC S n)) atTop (𝓝 1) ∧
    Tendsto (fun n => (xi i*S.b n/2)*(sourceCp S n/sourceC S n)*
      (sourceR S n/sourceC S n)) atTop (𝓝 1) ∧
    Tendsto (fun n => sourceR S n/sourceC S n) atTop (𝓝 0) := by
  have hh := relative_ratios S hband
  have hA := data_A_tendsto S
  have hA0 := OptimizedPhysicalRate.A_pos i (data_limit_in_rate_band S)
  have hAn (n : ℕ) : 0< OptimizedPhysicalRate.A i (S.b n) :=
    OptimizedPhysicalRate.A_pos i ⟨(S.bid_band n).1,(S.bid_band n).2.trans_lt S.subentry⟩
  have hcoef := data_rate_coefficient S
  have hslope : Tendsto (fun n => (sourceCp S n/sourceC S n)/(S.A.N n:ℝ))
      atTop (𝓝 (OptimizedPhysicalRate.A i S.b0)) := by
    rw [hcoef]
    exact hh.2.1
  have hraw1 := (hslope.div hA hA0.ne').mul (data_rival_market_ratio S)
  have hraw2 := (hh.2.2.1.mul (data_market_rival_ratio S)).mul
    (((S.bid_limit.const_mul (xi i)).mul hA).div_const 2)
  have hraw3 := hh.2.2.2.1.mul ((S.bid_limit.const_mul (xi i)).div_const 2)
  have hinv : Tendsto (fun n => (S.A.N n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp S.A.market)
  have hraw0 := hh.2.2.1.mul hinv
  refine ⟨hh.1,?_,?_,?_,?_,?_⟩
  · have hlim : Tendsto
        (fun n => (((sourceCp S n/sourceC S n)/(S.A.N n:ℝ))/
          OptimizedPhysicalRate.A i (S.b n))*((S.A.N n:ℝ)/(S.m n:ℝ)))
        atTop (𝓝 (1:ℝ)) := by
      simpa only [Pi.div_apply,div_self hA0.ne',one_mul] using! hraw1
    apply hlim.congr'
    filter_upwards [hh.1] with n hn
    field_simp [hn.ne',(S.A.N_pos n).ne',(data_market_pos S n).ne',(hAn n).ne']
  · have he : (2/(S.b0*S.ν*S.θ0)*1)*(xi i*S.b0*OptimizedPhysicalRate.A i S.b0/2)=1 := by
      rw [hcoef]
      field_simp [S.limit_bid_pos.ne',S.nu_pos.ne',S.limit_theta_pos.ne',(xi_pos i).ne']
    rw [he] at hraw2
    apply hraw2.congr'
    filter_upwards [hh.1] with n hn
    field_simp [hn.ne',(S.A.N_pos n).ne',(data_market_pos S n).ne']
  · have he : (2/(xi i*S.b0))*(xi i*S.b0/2)=1 := by
      field_simp [(xi_pos i).ne',S.limit_bid_pos.ne']
    rw [he] at hraw3
    apply hraw3.congr'
    exact Eventually.of_forall fun n => by ring
  · apply hh.2.2.2.2.congr'
    exact Eventually.of_forall fun n => by ring
  · have hlim : Tendsto (fun n => ((S.A.N n:ℝ)*(sourceR S n/sourceC S n))*
        (S.A.N n:ℝ)⁻¹) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hraw0
    apply hlim.congr'
    exact Eventually.of_forall fun n => by
      field_simp [(S.A.N_pos n).ne']

end Data

structure RelativeBounds (i : Row) (m : ℕ) (G : ProbabilityMeasure (ℝ × ℝ))
    (g : GuardData) (cm : (Fin (m-1) → Fin 4) → ℝ) (b ε : ℝ) : Prop where
  canonical_pos : 0< sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b
  hasDeriv_C : HasDerivAt (sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm)
    (FixedPriceCanonicalIntegral.Cprime i m (G:Measure (ℝ × ℝ)) g cm b) b
  hasDeriv_R : HasDerivAt (sourceCanonicalDuplicate i m (G:Measure (ℝ × ℝ)) g cm)
    (FixedPriceCanonicalIntegral.Rprime i m (G:Measure (ℝ × ℝ)) g cm b) b
  slope : |FixedPriceCanonicalIntegral.Cprime i m (G:Measure (ℝ × ℝ)) g cm b/
    ((m:ℝ)*sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b*
      OptimizedPhysicalRate.A i b)-1|<ε
  duplicate : |(m:ℝ)*xi i*b*OptimizedPhysicalRate.A i b*
    sourceCanonicalDuplicate i m (G:Measure (ℝ × ℝ)) g cm b/
      (2*sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b)-1|<ε
  duplicate_derivative : |(xi i*b/2)*
    (FixedPriceCanonicalIntegral.Rprime i m (G:Measure (ℝ × ℝ)) g cm b/
      sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b)-1|<ε
  factor : |(xi i*b/2)*
    (FixedPriceCanonicalIntegral.Cprime i m (G:Measure (ℝ × ℝ)) g cm b/
      sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b)*
    (sourceCanonicalDuplicate i m (G:Measure (ℝ × ℝ)) g cm b/
      sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b)-1|<ε
  small_duplicate : |sourceCanonicalDuplicate i m (G:Measure (ℝ × ℝ)) g cm b/
    sourceCanonicalMarginal i m (G:Measure (ℝ × ℝ)) g cm b|<ε

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

theorem uniform_u19 (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) a,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i) {d : ℝ} (hd : 0< d) (hdmax : d≤ x i-1/2) :
    ∀ ε>0,∀ᶠ m in atTop,∀ E : C m,∀ b∈Icc (cutoff i/2) ((x i-d)*cutoff i),
      RelativeBounds i m (G m E) (g m E) (cm m E) b ε := by
  intro ε hε
  apply eventually_test_of_derived_data G g cm i h05 hatom hfields hpsi hK hd hdmax
    (fun m J h count b => RelativeBounds i m J h count b ε)
  intro S hband hnull hgeom
  have hr := data_relative_limits S hband
  have hd := classical_derivatives S hnull (fun _ => sortEnd i)
    (fun n => (hgeom n).prefix) (fun n => (hgeom n).margin_population)
    (fun n => (hgeom n).bid_prefix) (fun n => (hgeom n).bid_multiplier)
    (fun n => (hgeom n).bid_rejection) (fun n => (hgeom n).cap_guard)
  have h1 := (Metric.tendsto_nhds.mp hr.2.1) ε hε
  have h2 := (Metric.tendsto_nhds.mp hr.2.2.1) ε hε
  have h3 := (Metric.tendsto_nhds.mp hr.2.2.2.1) ε hε
  have h4 := (Metric.tendsto_nhds.mp hr.2.2.2.2.1) ε hε
  have h0 := (Metric.tendsto_nhds.mp hr.2.2.2.2.2) ε hε
  filter_upwards [hr.1,h1,h2,h3,h4,h0] with n hn h1n h2n h3n h4n h0n
  simp only [Real.dist_eq,sub_zero] at h1n h2n h3n h4n h0n
  exact ⟨hn,(hd n).1,(hd n).2,h1n,h2n,h3n,h4n,h0n⟩

theorem exists_threshold_u19 (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) a,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i) {d ε : ℝ}
    (hd : 0< d) (hdmax : d≤ x i-1/2) (hε : 0<ε) :
    ∃ M : ℕ,∀ m≥ M,∀ E : C m,∀ b∈Icc (cutoff i/2) ((x i-d)*cutoff i),
      RelativeBounds i m (G m E) (g m E) (cm m E) b ε := by
  exact eventually_atTop.mp (uniform_u19 G g cm i h05 hatom hfields hpsi hK hd hdmax ε hε)

end Family
end FCAppendix.Affine.Uniform06.SourcePreciseFamily
