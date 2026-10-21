import FCAppendix.Affine.Uniform06.EarlyJointCompactness
import FCAppendix.Affine.Uniform06.UniformFromSubsequences
import FCAppendix.Affine.Uniform06.EarlyCoarseTiltConstructor

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EarlyCoarseUniform

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment RawMixedSource EarlyJointCompactness

def finiteCost (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (z θ : ℝ) : ℝ :=
  ExactUntilting.cost (source i G) (demand (xi i) (z*cutoff i)) θ (capacity m) (m-1)

def normalizedC (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) (z θ : ℝ) : ℝ :=
  sourceCanonicalMarginal i m G g cm (z*cutoff i)*
    Real.exp (finiteCost i m G z θ)*((m-1:ℕ):ℝ)^2

def normalizedR (i : Row) (m : ℕ) (G : Measure (ℝ × ℝ)) (g : GuardData)
    (cm : (Fin (m-1) → Fin 4) → ℝ) (z θ : ℝ) : ℝ :=
  sourceCanonicalDuplicate i m G g cm (z*cutoff i)*
    Real.exp (finiteCost i m G z θ)*((m-1:ℕ):ℝ)^3

theorem normalize_bounds {C R I N c U V : ℝ} (hN : 0 < N)
    (hl : c*Real.exp (-I)/N^2 ≤ C) (hu : C ≤ U*Real.exp (-I)/N^2)
    (hr : R ≤ V*Real.exp (-I)/N^3) (hC : 0 < C) (hRC : 0 ≤ R/C) :
    c ≤ C*Real.exp I*N^2 ∧ C*Real.exp I*N^2 ≤ U ∧
    R*Real.exp I*N^3 ≤ V ∧ 0 ≤ R*Real.exp I*N^3 := by
  have he : Real.exp (-I)*Real.exp I=1 := by rw [← Real.exp_add]; simp
  have hn2 : 0 < N^2 := pow_pos hN 2
  have hn3 : 0 < N^3 := pow_pos hN 3
  have hl' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hn2).mp hl) (Real.exp_pos I).le
  have hu' := mul_le_mul_of_nonneg_right ((le_div_iff₀ hn2).mp hu) (Real.exp_pos I).le
  have hr' := mul_le_mul_of_nonneg_right ((le_div_iff₀ hn3).mp hr) (Real.exp_pos I).le
  have hc : (c*Real.exp (-I))*Real.exp I=c := by rw [mul_assoc,he,mul_one]
  have hU : (U*Real.exp (-I))*Real.exp I=U := by rw [mul_assoc,he,mul_one]
  have hV : (V*Real.exp (-I))*Real.exp I=V := by rw [mul_assoc,he,mul_one]
  rw [hc] at hl'
  rw [hU] at hu'
  rw [hV] at hr'
  have hR : 0 ≤ R := by
    have hh := mul_nonneg hRC hC.le
    rwa [div_mul_cancel₀ R hC.ne'] at hh
  exact ⟨by nlinarith [hl'],by nlinarith [hu'],by nlinarith [hr'],by positivity⟩

section Family
variable (C : ℕ → Type*)
variable (G : (m : ℕ) → C m → ProbabilityMeasure (ℝ × ℝ))
variable (g : (m : ℕ) → C m → GuardData)
variable (cm : (m : ℕ) → C m → (Fin (m-1) → Fin 4) → ℝ)

theorem good_subsequence (i : Row) {d : ℝ} (hd : 0 < d)
    (θ : (m : ℕ) → C m → ℝ → ℝ)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hbox : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ box (cutoff i) (ReceiptGap.cap i))
    (hbid : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hmatch : ∀ᶠ m in atTop,∀ E : C m,∀ z ∈ Icc (1/2:ℝ) (x i-d),
      SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i)
        (G m E:Measure (ℝ × ℝ)))) Prod.fst (θ m E z)=
          (capacity m:ℝ)/((m-1:ℕ):ℝ))
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hguard : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      0 < (g m E).margin ∧ 0 < (g m E).population ∧ 0 < (g m E).requiredDemand)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (E : (n : ℕ) → C (m n)) (z : ℕ → ℝ) (hz : ∀ n,z n ∈ Icc (1/2:ℝ) (x i-d)) :
    ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∃ c U V : ℝ,
      0 < c ∧ 0 < U ∧ 0 < V ∧ ∀ᶠ n in atTop,
        c ≤ normalizedC i (m (φ n)) (G (m (φ n)) (E (φ n)):Measure (ℝ × ℝ))
          (g (m (φ n)) (E (φ n))) (cm (m (φ n)) (E (φ n))) (z (φ n))
          (θ (m (φ n)) (E (φ n)) (z (φ n))) ∧
        normalizedC i (m (φ n)) (G (m (φ n)) (E (φ n)):Measure (ℝ × ℝ))
          (g (m (φ n)) (E (φ n))) (cm (m (φ n)) (E (φ n))) (z (φ n))
          (θ (m (φ n)) (E (φ n)) (z (φ n))) ≤ U ∧
        normalizedR i (m (φ n)) (G (m (φ n)) (E (φ n)):Measure (ℝ × ℝ))
          (g (m (φ n)) (E (φ n))) (cm (m (φ n)) (E (φ n))) (z (φ n))
          (θ (m (φ n)) (E (φ n)) (z (φ n))) ≤ V ∧
        0 ≤ normalizedR i (m (φ n)) (G (m (φ n)) (E (φ n)):Measure (ℝ × ℝ))
          (g (m (φ n)) (E (φ n))) (cm (m (φ n)) (E (φ n))) (z (φ n))
          (θ (m (φ n)) (E (φ n)) (z (φ n))) := by
  let GG := fun n => G (m n) (E n)
  have ha : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ n in atTop,
      ∀ᵐ p ∂(GG n:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e := by
    intro a ha e he
    filter_upwards [hm.eventually (hactive a ha e he)] with n hn
    exact hn (E n)
  obtain ⟨G0,φ0,hφ0,hG0,hv0,hb0,hact0⟩ := exists_early_joint_limit i GG
    (fun n => hvalue _ _) (fun n => hbox _ _) (fun n => hbid _ _) ha
  obtain ⟨z0,hz0,ψ,hψ,hzlim⟩ := isCompact_Icc.isSeqCompact (fun n => hz (φ0 n))
  let φ := φ0 ∘ ψ
  have hφ : StrictMono φ := hφ0.comp hψ
  have hmφ : Tendsto (m ∘ φ) atTop atTop := hm.comp hφ.tendsto_atTop
  have hGφ : Tendsto (GG ∘ φ) atTop (𝓝 G0) := hG0.comp hψ.tendsto_atTop
  have hhi : (x i-d)*cutoff i < entry i := by
    unfold entry
    nlinarith [mul_pos hd (cutoff_pos i)]
  have hband : ∀ n,z (φ n)*cutoff i ∈ Icc (cutoff i/2) ((x i-d)*cutoff i) := by
    intro n
    constructor
    · nlinarith [(hz (φ n)).1,cutoff_pos i]
    · exact mul_le_mul_of_nonneg_right (hz (φ n)).2 (cutoff_pos i).le
  have hactiveStrip : ∀ᶠ n in atTop,∀ᵐ p ∂(GG (φ n):Measure (ℝ × ℝ)),
      p.1 ∈ Ioc (EarlyRankCeiling.ceilingValue i) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ cutoff i/10000 := by
    have ha0 : 0 < EarlyRankCeiling.ceilingValue i-entry i :=
      sub_pos.mpr (EarlyRankCeiling.ceilingValue_bounds i).1.1
    have hh := hφ.tendsto_atTop.eventually (ha (EarlyRankCeiling.ceilingValue i-entry i) ha0
      (cutoff i/10000) (div_pos (cutoff_pos i) (by norm_num)))
    have he : entry i+(EarlyRankCeiling.ceilingValue i-entry i)=EarlyRankCeiling.ceilingValue i := by ring
    simpa only [he] using hh
  have hmat : ∀ᶠ n in atTop,SubentryTilt.mean (MixedLaw.law i
      (MixedLaw.physicalLowerLaw i (z (φ n)*cutoff i)
        (GG (φ n):Measure (ℝ × ℝ)))) Prod.fst
      (θ (m (φ n)) (E (φ n)) (z (φ n)))=
        (capacity (m (φ n)):ℝ)/((m (φ n)-1:ℕ):ℝ) := by
    filter_upwards [hmφ.eventually hmatch] with n hn
    exact hn (E (φ n)) (z (φ n)) (hz (φ n))
  have hL : Tendsto (fun n => (g (m (φ n)) (E (φ n))).multiplier) atTop (𝓝 (entry i)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hmφ.eventually (hroot ε hε)] with n hn
    simpa only [Real.dist_eq, Function.comp_def] using! hn (E (φ n))
  have hg : ∀ᶠ n in atTop,(g (m (φ n)) (E (φ n))).radius ≤ cutoff i/100 ∧
      0 < (g (m (φ n)) (E (φ n))).margin ∧ 0 < (g (m (φ n)) (E (φ n))).population ∧
      0 < (g (m (φ n)) (E (φ n))).requiredDemand := by
    filter_upwards [hmφ.eventually hguard] with n hn
    exact hn (E (φ n))
  obtain ⟨c,U,V,hc,hU,hV,hout⟩ :=
    EarlyCoarseKernels.source_coarse_from_early_joint_limit i (GG ∘ φ) G0 hGφ
      (fun n => hvalue _ _) hv0 hb0 hact0 (m ∘ φ) hmφ
      (fun n => z (φ n)*cutoff i) (fun n => θ (m (φ n)) (E (φ n)) (z (φ n)))
      (fun n => g (m (φ n)) (E (φ n))) (fun n => cm (m (φ n)) (E (φ n)))
      hhi ⟨hz0.1,by linarith [hz0.2]⟩ hband (hzlim.mul_const (cutoff i))
      (Eventually.of_forall fun n => (hbox _ _).mono fun p hp => hp.2.2)
      hactiveStrip hmat hL (hg.mono fun n hn => hn.1) (hg.mono fun n hn => hn.2)
  refine ⟨φ,hφ,c,U,V,hc,hU,hV,?_⟩
  filter_upwards [hout,hmφ.eventually (eventually_ge_atTop 2)] with n hn hm2
  have hsize : 2 ≤ m (φ n) := hm2
  exact normalize_bounds (N := ((m (φ n)-1 : ℕ) : ℝ)) (Nat.cast_pos.mpr (by omega)) hn.1 hn.2.1 hn.2.2.1
    hn.2.2.2.1 hn.2.2.2.2.1

theorem source_uniform_coarse (i : Row) {d : ℝ} (hd : 0 < d) (hdmax : d ≤ x i-1/2)
    (hvalue : ∀ m (E : C m),(G m E:Measure (ℝ × ℝ)).map Prod.fst=
      LowChernoff.conditionalValueLaw i)
    (hbox : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),
      p ∈ box (cutoff i) (ReceiptGap.cap i))
    (hbid : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2 ≤ p.1)
    (hactive : ∀ a > (0:ℝ),∀ e > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.1 ∈ Ioc (entry i+a) (cutoff i) →
        |p.2-ActiveGraphComponent.activeBid i p.1| ≤ e)
    (hroot : ∀ ε > (0:ℝ),∀ᶠ m in atTop,∀ E : C m,
      |(g m E).multiplier-entry i| < ε)
    (hguard : ∀ᶠ m in atTop,∀ E : C m,(g m E).radius ≤ cutoff i/100 ∧
      0 < (g m E).margin ∧ 0 < (g m E).population ∧ 0 < (g m E).requiredDemand) :
    ∃ θ : (m : ℕ) → C m → ℝ → ℝ,∃ θlo θhi : ℝ,∃ A : ℕ,
      0 < θlo ∧ 0 < θhi ∧ ∀ᶠ m in atTop,∀ E : C m,∀ z ∈ Icc (1/2:ℝ) (x i-d),
        θ m E z ∈ Icc θlo θhi ∧
        SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i)
          (G m E:Measure (ℝ × ℝ)))) Prod.fst (θ m E z)=
            (capacity m:ℝ)/((m-1:ℕ):ℝ) ∧
        1/((A:ℝ)+1) ≤ normalizedC i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ∧
        normalizedC i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ≤ (A:ℝ)+1 ∧
        normalizedR i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) ≤ (A:ℝ)+1 ∧
        0 ≤ normalizedR i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z) := by
  classical
  obtain ⟨θlo,θhi,vlo,vhi,hlo,hhi,hvlo,hvhi,hex⟩ :=
    FiniteMean.eventual_uniform_source_tilts C (fun m E => (G m E:Measure (ℝ × ℝ))) i
      hd hdmax (fun _ _ => inferInstance) hvalue hbid hactive
  let P := fun m (E : C m) z t => t ∈ Icc θlo θhi ∧
    SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i (z*cutoff i)
      (G m E:Measure (ℝ × ℝ)))) Prod.fst t=(capacity m:ℝ)/((m-1:ℕ):ℝ)
  let θ := fun m (E : C m) z => if h : ∃ t,P m E z t then Classical.choose h else 0
  have ht : ∀ᶠ m in atTop,∀ E : C m,∀ z ∈ Icc (1/2:ℝ) (x i-d),P m E z (θ m E z) := by
    filter_upwards [hex] with m hm E z hz
    obtain ⟨t,ht,hmean,_⟩ := hm E z hz
    have he : ∃ t,P m E z t := ⟨t,ht,hmean⟩
    dsimp only [θ]
    rw [dif_pos he]
    exact Classical.choose_spec he
  have hm := ht.mono fun m hm E z hz => (hm E z hz).2
  obtain ⟨A,hA⟩ := UniformFromSubsequences.positive_bounds
    (Icc (1/2:ℝ) (x i-d))
    (fun m E z => normalizedC i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z))
    (fun m E z => normalizedR i m (G m E:Measure (ℝ × ℝ)) (g m E) (cm m E) z (θ m E z))
    (good_subsequence C G g cm i hd θ hvalue hbox hbid hactive hm hroot hguard)
  refine ⟨θ,θlo,θhi,A,hlo,hhi,?_⟩
  filter_upwards [ht,hA] with m hm hAm E z hz
  exact ⟨(hm E z hz).1,(hm E z hz).2,hAm E z hz⟩

end Family
end FCAppendix.Affine.Uniform06.EarlyCoarseUniform
