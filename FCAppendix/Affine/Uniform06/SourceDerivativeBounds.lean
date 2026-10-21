import FCAppendix.Affine.Uniform06.DerivativeMeasurableBounds
import FCAppendix.Affine.Uniform06.PreciseRootGood

noncomputable section
namespace FCAppendix.Affine.Uniform06.SourceDerivativeBounds

open Set MeasureTheory Filter LowBody
open scoped BigOperators Topology
open Uniform07 LiteralExperiment RawMixedSource RawTiltedSource RawMarkedLaplace
open PhysicalSourceMoments RawMomentPartition LiteralDerivativeMoments
open DerivativeMeasurableBounds PreciseRootGood RawPathAdapter
open LiteralCoarsePath ClampedMomentBounds EqualOnlyRareMoments RareEmpiricalReplacement
open GuardVelocityRareBound UnguardedRareMoment LiteralGuardVelocity

section Integration
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_good_domination (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) {F J : Ω → ℝ} {B : ℝ}
    (hFi : Integrable F μ) (hJi : Integrable J μ)
    (hJ0 : ∀ᵐ ω ∂μ,0≤ J ω) (hFb : ∀ᵐ ω ∂μ,F ω≤ B)
    (hgood : ∀ᵐ ω ∂μ,ω∈E → F ω≤ J ω) :
    (∫ ω,F ω ∂μ)≤(∫ ω,J ω ∂μ)+B*μ.real Eᶜ := by
  have hi : Integrable (Eᶜ.indicator (fun _ : Ω => B)) μ :=
    (integrable_const B).indicator hE.compl
  have hp : ∀ᵐ ω ∂μ,F ω≤ J ω+Eᶜ.indicator (fun _ : Ω => B) ω := by
    filter_upwards [hJ0,hFb,hgood] with ω hj hf hg
    by_cases he : ω∈E
    · rw [indicator_of_notMem (show ω∉Eᶜ from by simpa only [mem_compl_iff,not_not] using he),add_zero]
      exact hg he
    · rw [indicator_of_mem (show ω∈Eᶜ from he)]
      linarith
  have hh := integral_mono_ae hFi (hJi.add hi) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add hJi hi,integral_indicator hE.compl,setIntegral_const] at hh
  simpa only [smul_eq_mul,mul_comm B] using hh

end Integration

variable {N : ℕ} [Nonempty (Fin N)]

def ReceiptCase (i : Row) (G : Measure (ℝ × ℝ)) (g : GuardData) (b θ : ℝ) : Prop :=
  b≤ g.multiplier-g.radius ∨ ∀ᵐ x ∂tiltedSource i G b θ,0≤ rawH (xi i) b x

omit [Nonempty (Fin N)] in
theorem source_zero_moment_unit (i : Row) (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    (c : ℕ) (g : GuardData) (cm : (Fin N → Fin 4) → ℝ) {b θ : ℝ}
    (hb : 0< b) (hbL : b≤ g.multiplier) (hgl : 0< g.multiplier-g.radius)
    (hθ : 0≤θ) (hc : (c:ℝ)≤ N)
    (hg : 0< g.margin ∧ 0< g.population ∧ 0< g.requiredDemand)
    (hcase : ReceiptCase i G g b θ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => tiltedSource i G b θ),
      literalMoment i c g cm b θ 0 ω∈Icc (0:ℝ) 1 := by
  letI := tiltedSource_probability i G hb θ
  rcases hcase with hlow | hhigh
  · exact ae_of_all _ fun ω => by
      simpa only [pow_zero] using low_literal_polynomial i c g cm hb hbL hgl hlow
        hg.1 hg.2.1 hg.2.2 hθ hc 0 ω
  · have hh (j : Fin N) :=
      (measurePreserving_eval (fun _ : Fin N => tiltedSource i G b θ) j).quasiMeasurePreserving.ae hhigh
    filter_upwards [ae_all_iff.mpr hh] with ω hω
    simpa only [pow_zero] using literalMoment_polynomial i c g cm hb hbL hθ 0 hc
      hg.1 hg.2.1 hg.2.2 ω hω

omit [Nonempty (Fin N)] in

theorem original_main_integral_errors (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo b θ s U ε Q : ℝ}
    (hlo : 0< lo) (hlb : lo< b) (hbs : b< s) (hU : 0< U) (hbU : b≤ U)
    (hloU : U/2≤ lo) (hclip : (1-xi i)*U≤ lo)
    (hN : 0< N) (hθ : 0≤θ) (hc : (c:ℝ)≤ N) (hbL : b≤ g.multiplier)
    (hgl : 0< g.multiplier-g.radius)
    (hg : 0< g.margin ∧ 0< g.population ∧ 0< g.requiredDemand)
    (hcase : ReceiptCase i G g b θ)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) (hε : 0<ε) (hQ : 0< Q) (hεQ : 12*ε≤ Q)
    (hfloor : |(c:ℝ)-(N:ℝ)*rho|≤1)
    (hpos : ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hstrip : Q≤(TiltedGood.law i G b θ).real (CostAmplification.activeStrip s U)) :
    let P := Measure.pi (fun _ : Fin N => tiltedSource i G b θ)
    let γ := Q/(4*U)
    (∫ ω,|tiltedMain i c g cm b θ 1 ω-literalMoment i c g cm b θ 0 ω/(xi i*b)| ∂P)≤
      (∫ ω,physicalMoment i c g cm b θ 1 ω ∂P)/(b-lo)+
      (∫ ω,literalMoment i c g cm b θ 0 ω ∂P)/(xi i*b^2*γ*(N:ℝ))+
      16/(xi i*b)*Real.exp (-(2*ε^2)*(N:ℝ)) ∧
    (∫ ω,|tiltedMain i c g cm b θ 2 ω-2*physicalMoment i c g cm b θ 1 ω/(xi i*b)| ∂P)≤
      2*(∫ ω,physicalMoment i c g cm b θ 2 ω ∂P)/(b-lo)+
      2*(∫ ω,physicalMoment i c g cm b θ 1 ω ∂P)/(xi i*b^2*γ*(N:ℝ))+
      32/(xi i*b)*Real.exp (-(2*ε^2)*(N:ℝ)) := by
  let μ := tiltedSource i G b θ
  let P := Measure.pi (fun _ : Fin N => μ)
  letI : IsProbabilityMeasure μ := tiltedSource_probability i G (hlo.trans hlb) θ
  let E := RivalGood.good μ (TiltedGood.statistics s U) N ε
  let γ := Q/(4*U)
  let Z := literalMoment i c g cm b θ 0
  let C := physicalMoment i c g cm b θ 1
  let R := physicalMoment i c g cm b θ 2
  let F1 := fun ω => |tiltedMain i c g cm b θ 1 ω-Z ω/(xi i*b)|
  let F2 := fun ω => |tiltedMain i c g cm b θ 2 ω-2*C ω/(xi i*b)|
  let J1 := fun ω => C ω/(b-lo)+Z ω/(xi i*b^2*γ*(N:ℝ))
  let J2 := fun ω => 2*R ω/(b-lo)+2*C ω/(xi i*b^2*γ*(N:ℝ))
  have hb : 0< b := hlo.trans hlb
  have hξ := xi_pos i
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hden : 0< xi i*b := mul_pos (xi_pos i) hb
  have hden2 : 0< xi i*b^2*γ*(N:ℝ) := by positivity
  have hgap : 0< b-lo := sub_pos.mpr hlb
  have hE : MeasurableSet E := RivalGood.measurable_good _ _
    (TiltedGood.statistics_measurable s U) N ε
  have hZ := source_zero_moment_unit i G c g cm hb hbL hgl hθ hc hg hcase
  have hCR : ∀ᵐ ω ∂P,C ω∈Icc (0:ℝ) 1 ∧ R ω∈Icc (0:ℝ) 1 := by
    filter_upwards [hZ] with ω hz
    have h1 := physicalMoment_le_strict_zero i c g cm hb θ 1 (by omega) ω
    have h2 := physicalMoment_le_strict_zero i c g cm hb θ 2 (by omega) ω
    exact ⟨⟨h1.1,h1.2.trans hz.2⟩,⟨h2.1,h2.2.trans hz.2⟩⟩
  have hZi : Integrable Z P := Integrable.of_mem_Icc 0 1
    (measurable_literalMoment i c g cm b θ 0).aemeasurable hZ
  have hCi : Integrable C P := Integrable.of_mem_Icc 0 1
    (measurable_physicalMoment i c g cm b θ 1).aemeasurable ((hCR).mono fun _ h => h.1)
  have hRi : Integrable R P := Integrable.of_mem_Icc 0 1
    (measurable_physicalMoment i c g cm b θ 2).aemeasurable ((hCR).mono fun _ h => h.2)
  have hJ1i : Integrable J1 P := (hCi.div_const _).add (hZi.div_const _)
  have hJ2i : Integrable J2 P := ((hRi.const_mul 2).div_const _).add ((hCi.const_mul 2).div_const _)
  have hJ0 : ∀ᵐ ω ∂P,0≤ J1 ω ∧ 0≤ J2 ω := by
    filter_upwards [hZ,hCR] with ω hz hcω
    have hC0 := hcω.1.1
    have hR0 := hcω.2.1
    have hZ0 := hz.1
    constructor <;> dsimp only [J1,J2] <;> positivity
  have hFbound : ∀ᵐ ω ∂P,F1 ω≤2/(xi i*b) ∧ F2 ω≤4/(xi i*b) := by
    filter_upwards [hZ] with ω hz
    have hh := tilted_main_error_envelopes i c g cm hb hbL hg.1 hg.2.1 hg.2.2 θ ω
    constructor
    · apply hh.1.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2
        (show 0≤2/(xi i*b) by positivity)
    · apply hh.2.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2
        (show 0≤4/(xi i*b) by positivity)
  have hF1i : Integrable F1 P := Integrable.of_mem_Icc 0 (2/(xi i*b))
    (((measurable_tiltedMain i c g cm b θ 1).sub
      ((measurable_literalMoment i c g cm b θ 0).div_const _)).abs).aemeasurable
    (hFbound.mono fun ω h => ⟨abs_nonneg _,h.1⟩)
  have hF2i : Integrable F2 P := Integrable.of_mem_Icc 0 (4/(xi i*b))
    (((measurable_tiltedMain i c g cm b θ 2).sub
      (((measurable_physicalMoment i c g cm b θ 1).const_mul 2).div_const _)).abs).aemeasurable
    (hFbound.mono fun ω h => ⟨abs_nonneg _,h.2⟩)
  have hrows := SourceCoarseIntegral.tilted_raw_row_support i G hb hU.le hbU θ N hcap
  have hgood : ∀ᵐ ω ∂P,ω∈E → F1 ω≤ J1 ω ∧ F2 ω≤ J2 ω := by
    filter_upwards [hrows] with ω hω heω
    have hcω := source_good_counts_and_reciprocal i G hb hbs hU hlo hloU hN
      hfloor hpos hroom hQ hεQ hstrip ω hω.2 heω
    have hcapω : ∀ j,(ω j).1=0 → (ω j).2≤ U := by
      intro j hj
      simpa only [rowBids,Fin.cons_succ,if_pos hj] using hω.1 j.succ
    have hemp : γ+(LiteralExperiment.imbalance (patternTemplate c (fun j => (ω j).1)):ℝ)/
        (lo*(N:ℝ))≤ empirical (FullReciprocalMean.reciprocal b) N ω := by
      rw [literal_imbalance_eq c ω hcω.1]
      exact hcω.2.2
    exact tilted_main_row_errors i c g cm hlo hlb hU.le hbU hbL hγ hN hclip
      hg.1 hg.2.1 hg.2.2 θ ω hcapω hemp
  have hprob : P.real Eᶜ≤8*Real.exp (-(2*ε^2)*(N:ℝ)) := by
    have h := TiltedGood.source_good_complement i G hb θ s U hN hε.le
    convert! h using 1
    ring
  have h1 := integral_good_domination P E hE hF1i hJ1i
    (hJ0.mono fun _ h => h.1) (hFbound.mono fun _ h => h.1)
    (hgood.mono fun _ h he => (h he).1)
  have h2 := integral_good_domination P E hE hF2i hJ2i
    (hJ0.mono fun _ h => h.2) (hFbound.mono fun _ h => h.2)
    (hgood.mono fun _ h he => (h he).2)
  have hJ1 : (∫ ω,J1 ω ∂P)=(∫ ω,C ω ∂P)/(b-lo)+(∫ ω,Z ω ∂P)/(xi i*b^2*γ*(N:ℝ)) := by
    rw [integral_add (hCi.div_const _) (hZi.div_const _),integral_div,integral_div]
  have hJ2 : (∫ ω,J2 ω ∂P)=2*(∫ ω,R ω ∂P)/(b-lo)+2*(∫ ω,C ω ∂P)/(xi i*b^2*γ*(N:ℝ)) := by
    rw [integral_add ((hRi.const_mul 2).div_const _) ((hCi.const_mul 2).div_const _),
      integral_div,integral_div,integral_const_mul,integral_const_mul]
  rw [hJ1] at h1
  rw [hJ2] at h2
  have he1 := mul_le_mul_of_nonneg_left hprob (show 0≤2/(xi i*b) by positivity)
  have he2 := mul_le_mul_of_nonneg_left hprob (show 0≤4/(xi i*b) by positivity)
  have he1' : 2/(xi i*b)*P.real Eᶜ≤16/(xi i*b)*Real.exp (-(2*ε^2)*(N:ℝ)) := by
    convert! he1 using 1
    ring
  have he2' : 4/(xi i*b)*P.real Eᶜ≤32/(xi i*b)*Real.exp (-(2*ε^2)*(N:ℝ)) := by
    convert! he2 using 1
    ring
  constructor
  · simpa only [F1,C,Z,P,γ,μ] using h1.trans (add_le_add le_rfl he1')
  · simpa only [F2,C,R,Z,P,γ,μ] using h2.trans (add_le_add le_rfl he2')

theorem original_guard_integral_bound (i : Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G] (c : ℕ) (g : GuardData)
    (cm : (Fin N → Fin 4) → ℝ) {lo b θ s U ε Q : ℝ}
    (hlo : 0< lo) (hlb : lo< b) (hbs : b< s) (hU : 0< U) (hbU : b≤ U)
    (hloU : U/2≤ lo) (hclip : (1-xi i)*U≤ lo)
    (hN : 0< N) (hθ : 0≤θ) (hc : (c:ℝ)≤ N) (hbL : b≤ g.multiplier)
    (hbz : b≤ g.rejectionRoot) (hseed : g.seedCutoff< b)
    (hgl : 0< g.multiplier-g.radius) (ha : 0≤ g.radius)
    (hg : 0< g.margin ∧ 0< g.population ∧ 0< g.requiredDemand)
    (hh : ∀ᵐ x ∂tiltedSource i G b θ,0≤ rawH (xi i) b x)
    (hcap : ∀ᵐ p ∂G,p.2≤ U) (hε : 0<ε) (hQ : 0< Q) (hεQ : 12*ε≤ Q)
    (hfloor : |(c:ℝ)-(N:ℝ)*rho|≤1)
    (hpos : ε*(N:ℝ)+2<(N:ℝ)*(rho-TiltedGood.upperProbability i G b θ))
    (hroom : 2*ε*(N:ℝ)+3≤(N:ℝ)*(TiltedGood.lowerProbability i G b θ-
      (rho-TiltedGood.upperProbability i G b θ)))
    (hstrip : Q≤(TiltedGood.law i G b θ).real (CostAmplification.activeStrip s U))
    (q : ℕ) (hq : 0< q) :
    let P := Measure.pi (fun _ : Fin N => tiltedSource i G b θ)
    let γ := Q/(4*U)
    let K := 1/(xi i*(g.multiplier-g.radius)*g.margin*g.population)
    0≤(∫ ω,tiltedGuard i c g cm b θ q ω ∂P) ∧
    (∫ ω,tiltedGuard i c g cm b θ q ω ∂P)≤
      K*(xi i/((b-lo)*γ*(N:ℝ)))^q*
        (∫ ω,unguardedRow i c g b θ q ω ∂P)+
      8*K*Real.exp (-(2*ε^2)*(N:ℝ)) := by
  let μ := tiltedSource i G b θ
  let P := Measure.pi (fun _ : Fin N => μ)
  let E := RivalGood.good μ (TiltedGood.statistics s U) N ε
  let γ := Q/(4*U)
  let K := 1/(xi i*(g.multiplier-g.radius)*g.margin*g.population)
  let a := K*(xi i/((b-lo)*γ*(N:ℝ)))^q
  let T : (Fin N → RowRival) → ℝ := unguardedRow i c g b θ q
  let V := tiltedGuard i c g cm b θ q
  have hb : 0< b := hlo.trans hlb
  have hξ := xi_pos i
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  letI : IsProbabilityMeasure μ := tiltedSource_probability i G hb θ
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hmargin := hg.1
  have hpopulation := hg.2.1
  have hgap := sub_pos.mpr hlb
  have hK : 0< K := by dsimp [K]; positivity
  have ha0 : 0≤ a := by dsimp [a]; positivity
  have hE : MeasurableSet E := RivalGood.measurable_good _ _
    (TiltedGood.statistics_measurable s U) N ε
  have hcoords : ∀ᵐ ω ∂P,∀ j,0≤ rawH (xi i) b (ω j) :=
    ae_all_iff.mpr fun j => (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hh
  have hVb : ∀ᵐ ω ∂P,V ω∈Icc (0:ℝ) K := by
    filter_upwards [hcoords] with ω hω
    exact tiltedGuard_high_bound i c g cm hb hbL hbz hseed hgl ha hg.1 hg.2.1 hg.2.2
      hθ q hq ω hω
  have hVi : Integrable V P := Integrable.of_mem_Icc 0 K
    (measurable_tiltedGuard i c g cm b θ q).aemeasurable hVb
  have hTb := unguardedRow_polynomial (N := N) i μ c g hb hθ q hN hc hh
  have hTi : Integrable T P := Integrable.of_mem_Icc 0 ((N:ℝ)^q)
    (measurable_unguardedRow i c g b θ q).aemeasurable hTb
  have hrows := SourceCoarseIntegral.tilted_raw_row_support i G hb hU.le hbU θ N hcap
  have hgood : ∀ᵐ ω ∂P,ω∈E → V ω≤ a*T ω := by
    filter_upwards [hrows] with ω hω heω
    have hcω := source_good_counts_and_reciprocal i G hb hbs hU hlo hloU hN
      hfloor hpos hroom hQ hεQ hstrip ω hω.2 heω
    have hcapω : ∀ j,(ω j).1=0 → (ω j).2≤ U := by
      intro j hj
      simpa only [rowBids,Fin.cons_succ,if_pos hj] using hω.1 j.succ
    exact (actual_guard_velocity_majorant i c g cm hlo hU.le hlb hbU hclip hγ hN
      hbL hbz hseed hgl ha hg.1 hg.2.1 hg.2.2 q hq ω hcω.1 hcapω hcω.2.2).2
  have hprob : P.real Eᶜ≤8*Real.exp (-(2*ε^2)*(N:ℝ)) := by
    have h := TiltedGood.source_good_complement i G hb θ s U hN hε.le
    convert! h using 1
    ring
  have hi := integral_good_domination P E hE hVi (hTi.const_mul a)
    (hTb.mono fun ω hω => mul_nonneg ha0 hω.1) (hVb.mono fun _ h => h.2) hgood
  rw [integral_const_mul] at hi
  have hbnd := mul_le_mul_of_nonneg_left hprob hK.le
  refine ⟨integral_nonneg_of_ae (hVb.mono fun _ h => h.1),?_⟩
  dsimp only [a,K,γ,V,T,P,μ] at *
  nlinarith

end FCAppendix.Affine.Uniform06.SourceDerivativeBounds
