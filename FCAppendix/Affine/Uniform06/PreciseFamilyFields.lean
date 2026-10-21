import FCAppendix.Affine.Uniform06.SourceEarlyFamily
import FCAppendix.Affine.Uniform06.FiniteMean
import FCAppendix.Affine.Uniform06.LiteralGuardRare
import FCAppendix.Affine.Uniform06.RawTiltedSource
import FCAppendix.Affine.Uniform06.FixedPriceCanonicalIntegral

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.SourcePreciseFamily

open MeasureTheory Set Filter Topology LowBody
open Uniform07 LiteralExperiment SourceEarlyFamily SourcePrefixConstructor
open LiteralGuardRare RawTiltedSource

section Family
variable {C : ℕ → Type*}
    (G : ∀ m,C m → ProbabilityMeasure (ℝ × ℝ))
    (g : ∀ m,C m → GuardData)
    (cm : ∀ m,C m → (Fin (m-1) → Fin 4) → ℝ)

structure KernelFields (i : Row) where
  population_eq : ∀ m (E : C m),(g m E).population=(m:ℝ)
  ε : ℝ
  margin_pos : 0<ε
  margin_lower : ∀ m (E : C m),ε≤(g m E).margin
  Kcount : ℝ
  count_constant_nonneg : 0≤ Kcount
  cmbar : ∀ m,C m → ℝ → ℝ → ℝ
  count_receipt : ∀ m (E : C m) (b θ : ℝ),0< b → b≤(g m E).multiplier →
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (m-1) =>
      tiltedSource i (G m E:Measure (ℝ × ℝ)) b θ),
      |cm m E (fun j => (ω j).1)/(g m E).population-cmbar m E b θ|≤
        Kcount*(deviationSum (tiltedSource i (G m E:Measure (ℝ × ℝ)) b θ)
          (xi i) (g m E) ω+(g m E).population⁻¹)

theorem exists_uniform_matching_parameters (i : Row)
    (h05 : EarlyMenuFields G g cm i) {d : ℝ}
    (hd : 0< d) (hdmax : d≤ x i-1/2) :
    ∃ θ : ∀ m,C m → ℝ → ℝ,∃ t0 Θ : ℝ,0< t0 ∧ 0<Θ ∧
      ∀ᶠ m in atTop,∀ E : C m,∀ b ∈ Icc (cutoff i/2) ((x i-d)*cutoff i),
        θ m E b∈Icc t0 Θ ∧
        SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
          (G m E:Measure (ℝ × ℝ)))) Prod.fst (θ m E b)=
            (capacity m:ℝ)/((m-1:ℕ):ℝ) := by
  classical
  have hbelow : ∀ m (E : C m),∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2≤ p.1 :=
    fun m E => (h05.permitted m E).mono fun _ hp => hp.2.trans (min_le_left _ _)
  obtain ⟨t0,Θ,vlo,vhi,ht0,hΘ,hvlo,hvhi,hex⟩ :=
    FiniteMean.eventual_uniform_source_tilts C (fun m E => (G m E:Measure (ℝ × ℝ))) i
      hd hdmax (fun _ _ => inferInstance) h05.value_marginal hbelow
      (source_early_active G g cm i h05)
  let P := fun m (E : C m) b s => s∈Icc t0 Θ ∧
    SubentryTilt.mean (MixedLaw.law i (MixedLaw.physicalLowerLaw i b
      (G m E:Measure (ℝ × ℝ)))) Prod.fst s=(capacity m:ℝ)/((m-1:ℕ):ℝ)
  let θ := fun m (E : C m) b => if h : ∃ s,P m E b s then Classical.choose h else 0
  refine ⟨θ,t0,Θ,ht0,hΘ,?_⟩
  filter_upwards [hex] with m hm
  intro E b hb
  have hz : b/cutoff i∈Icc (1/2:ℝ) (x i-d) := by
    constructor
    · exact (le_div_iff₀ (cutoff_pos i)).mpr (by nlinarith [hb.1])
    · exact (div_le_iff₀ (cutoff_pos i)).mpr hb.2
  obtain ⟨s,hs,hmean,_hvar⟩ := hm E (b/cutoff i) hz
  have he : ∃ s,P m E b s := by
    refine ⟨s,hs,?_⟩
    simpa only [div_mul_cancel₀ b (cutoff_pos i).ne'] using hmean
  dsimp only [θ]
  rw [dif_pos he]
  exact Classical.choose_spec he

structure PointGeometry (i : Row) (g : GuardData) (b : ℝ) : Prop where
  «prefix» : LiteralPrefixStieltjes.PrefixConditions (xi i) g (sortEnd i)
  radius_pos : 0< g.radius
  margin_population : 1< g.margin*g.population
  bid_pos : 0< b
  bid_prefix : b< sortEnd i
  bid_multiplier : b< g.multiplier
  bid_rejection : b< g.rejectionRoot
  bid_cap : b< ReceiptGap.cap i
  cap_guard : (1-xi i)*ReceiptGap.cap i≤ g.multiplier-g.radius

theorem eventually_point_geometry (i : Row) (h05 : EarlyMenuFields G g cm i)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i) {hi : ℝ} (hhi : hi< entry i) :
    ∀ᶠ m in atTop,∀ E : C m,∀ b∈Icc (cutoff i/2) hi,
      PointGeometry i (g m E) b := by
  have hgap : 0<(entry i-hi)/2 := half_pos (sub_pos.mpr hhi)
  have hroot := h05.root_limit ((entry i-hi)/2) hgap
  have hrootclip := h05.root_limit (cutoff i/200) (by have ht:=cutoff_pos i; positivity)
  have hlarge : Tendsto (fun m : ℕ => hK.ε*(m:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop).const_mul_atTop hK.margin_pos
  have hpop : ∀ᶠ m : ℕ in atTop,1< hK.ε*(m:ℝ) := hlarge.eventually_gt_atTop 1
  filter_upwards [eventually_source_prefix G g cm i h05 hfields hpsi,
    hroot,hrootclip,hpop] with m hp hr hrc hpm
  intro E b hb
  have hbp : 0< b := (half_pos (cutoff_pos i)).trans_le hb.1
  have hbH : b< sortEnd i := by
    unfold sortEnd
    have ht := cutoff_pos i
    linarith [hb.2]
  have hbL : b<(g m E).multiplier := by
    have h := (abs_lt.mp (hr E)).1
    linarith [hb.2]
  have hεM : 1<(g m E).margin*(g m E).population := by
    rw [hK.population_eq]
    exact hpm.trans_le (mul_le_mul_of_nonneg_right (hK.margin_lower m E) (Nat.cast_nonneg m))
  have hclip : (1-xi i)*ReceiptGap.cap i≤(g m E).multiplier-(g m E).radius := by
    have hn : (1-xi i)*ReceiptGap.cap i < entry i-cutoff i/100 := by
      have hκ : 0 < kappa i := by cases i <;> norm_num [kappa,kappaQ,xiQ,etaQ]
      have hleft : kappa i < x i-1/100 := by
        cases i <;> norm_num [x,xQ,kappa,kappaQ,xiQ,etaQ]
      have hcap := mul_lt_mul_of_pos_left (ReceiptGap.cap_bounds i).2 hκ
      have hl := mul_lt_mul_of_pos_right hleft (cutoff_pos i)
      rw [ReceiptGap.kappa_eq_one_sub] at hcap hl
      unfold entry
      nlinarith
    have h := (abs_lt.mp (hrc E)).1
    rw [(hfields m E).radius_eq]
    unfold radius
    have ht := cutoff_pos i
    linarith
  refine ⟨(hp E).2.1,?_,hεM,hbp,hbH,hbL,
    hbH.trans_le (hp E).2.1.rejection,hb.2.trans_lt (hhi.trans (ReceiptGap.entry_below_cap i)),hclip⟩
  rw [(hfields m E).radius_eq]
  unfold radius
  exact div_pos (cutoff_pos i) (by norm_num)

theorem eventually_every_fixed_derivatives (i : Row)
    (h05 : EarlyMenuFields G g cm i)
    (hatom : ∀ m (E : C m) a,((G m E:Measure (ℝ × ℝ)).map Prod.snd) {a}=0)
    (hfields : ∀ m (E : C m),LiteralFields i (g m E))
    (hpsi : ∀ m (E : C m),
      (∫ p,PrefixRoot.sourcePsi i (g m E).rejectionRoot p.2
        ∂(G m E:Measure (ℝ × ℝ)))=3*PrefixRoot.requiredDemand i)
    (hK : KernelFields G g cm i) {hi : ℝ} (hhi : hi< entry i) :
    ∀ᶠ m in atTop,∀ E : C m,∀ b∈Icc (cutoff i/2) hi,
      HasDerivAt (sourceCanonicalMarginal i m (G m E) (g m E) (cm m E))
        (FixedPriceCanonicalIntegral.Cprime i m (G m E) (g m E) (cm m E) b) b ∧
      HasDerivAt (sourceCanonicalDuplicate i m (G m E) (g m E) (cm m E))
        (FixedPriceCanonicalIntegral.Rprime i m (G m E) (g m E) (cm m E) b) b := by
  have hused := source_common_used G g cm i h05 hatom
  filter_upwards [eventually_point_geometry G g cm i h05 hfields hpsi hK hhi]
    with m hm
  intro E b hb
  have hnon : ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),0≤ p.2 :=
    (hused m E).mono fun _ hp => hp.2.1.le
  have hcap : ∀ᵐ p ∂(G m E:Measure (ℝ × ℝ)),p.2≤ ReceiptGap.cap i :=
    (h05.permitted m E).mono fun _ hp => hp.2.trans (min_le_right _ _)
  have hd := hm E b hb
  exact FixedPriceCanonicalIntegral.source_canonical_derivatives i m (G m E:Measure (ℝ × ℝ))
    (hatom m E) hnon hcap (g m E) (cm m E) hd.prefix hd.radius_pos hd.margin_population
    hd.bid_pos hd.bid_prefix hd.bid_multiplier hd.bid_rejection hd.bid_cap hd.cap_guard

end Family
end FCAppendix.Affine.Uniform06.SourcePreciseFamily
