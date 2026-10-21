import FCAppendix.Affine.Hybrid.Tail03.LowerCoefficient
import FCAppendix.Affine.Hybrid.Tail03.RateCertificates
import FCAppendix.Affine.Hybrid.Tail03.SourceMomentRefinement
import FCAppendix.Affine.Hybrid.Tail03.Taylor
import FCAppendix.Affine.Hybrid.Tail03.Law

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03
open Set Filter Topology MeasureTheory

structure ExplicitTwoTripleLogCertificates (p : Center) where
  privateTolerance : ℝ
  tolerance_pos : 0 < privateTolerance
  tolerance_small : privateTolerance ≤ 1/1000
  delta_small : delta p < privateTolerance
  lower : 2*FCAppendix.Ample.binaryKL (99/200) (1-activeMass p/2)+1397/10000 <
    FCAppendix.Affine.LowBody.jointRate (lowMass p) (partialMass p) (activeMass p) (99/200)
  upper : ∀z : ℝ,0≤ z → z< privateTolerance →
    2*FCAppendix.Ample.binaryKL (99/200) (1-(partialMass p+z)/2)+1101/10000 <
      FCAppendix.Affine.LowBody.jointRate (lowMass p) (activeMass p-z) (partialMass p+z) (99/200)

structure Parameters (eta1 eta2 : ℝ) where
  center : Center
  eta1_eq : center.eta1=eta1
  eta2_eq : center.eta2=eta2
  theta_small : center.theta < 1/100
  theta_source_small : center.theta ≤ xi center/100
  theta_lower_floor : center.theta ≤ 11*xi center*(lowerRelativeMargin (xiOne center))^2/(128*xiOne center)
  rect : Rectangle center
  analytic : RectangleAnalyticCertificate center rect
  d0 : ℝ
  valueWidth : ℝ
  tailMass : ℝ
  tailFloor : ℝ
  bulkBidWidth : ℝ
  d0_pos : 0 < d0
  valueWidth_pos : 0 < valueWidth
  valueWidth_small : valueWidth < 1
  valueWidth_source_small : valueWidth ≤ xi center/1000
  low_separation : d0 < 2-valueWidth
  bulk_separation : 2+valueWidth < bulkValue center-valueWidth
  tail_separation : bulkValue center+valueWidth < tailFloor
  menus : UniformActiveAndPartialMenuInequalities center rect valueWidth
  moments : ExplicitMomentRectangleInequalities center rect bulkBidWidth tailMass
  relativeMoments : SourceRelativeMomentParameters center rect.lo rect.hi
  relative_u : relativeMoments.u=bulkBidWidth
  relative_zeta : relativeMoments.zeta=tailMass
  rates : ExplicitTwoTripleLogCertificates center
  lowerGuards : ExplicitCoefficientOneGuards center valueWidth
  low_receipt_one : d0 < (1-xiOne center)*lowerGuards.L
  low_receipt_two : d0 < min (R center/4) (kappa center/4)
  boundary : BoundaryTaylorData center rect
  tail_above_boundary : boundary.V0 < tailFloor
  bulk_derivative : ∀lam∈rect.box,∀v∈Icc (bulkValue center-valueWidth) (bulkValue center+valueWidth),
    ∀b∈Icc (1:ℝ) (B center),deriv (utility center lam v) b≤-(1/25:ℝ)
  bulk_floor : ∀lam∈rect.box,∀v∈Icc (bulkValue center-valueWidth) (bulkValue center+valueWidth),
    ∀b∈Icc (1:ℝ) (B center),utility center lam v b ≤ utility center lam v 1

namespace Parameters

def lawInput {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) : LawInput where
  s := lowMass p.center
  h := partialMass p.center
  a := activeMass p.center
  d0 := p.d0
  w := p.valueWidth
  vA := bulkValue p.center
  zeta := p.tailMass
  M := p.tailFloor
  s_large := by unfold lowMass; linarith [delta_pos p.center]
  h_pos := by norm_num [partialMass]
  a_pos := activeMass_pos p.center
  masses := masses_sum p.center
  d0_pos := p.d0_pos
  w_pos := p.valueWidth_pos
  zeta_pos := p.moments.zeta_pos
  zeta_lt_one := lt_trans p.moments.zeta_small (by norm_num)
  low_partial := p.low_separation
  partial_bulk := p.bulk_separation
  bulk_tail := p.tail_separation

def Amin {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) : ℝ := p.boundary.Amin
def Amax {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) : ℝ := p.boundary.Amax
def capK {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) : ℝ := p.boundary.capK

lemma aggregate_margin {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) :
    0 < partialMass p.center*(p.center.theta-oneMixedMass p.center) := by
  have ht := p.center.theta_pos
  have hs := p.theta_small
  norm_num [partialMass,oneMixedMass,delta]
  nlinarith

lemma aggregate_margin_identity {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) :
    partialMass p.center*(p.center.theta-oneMixedMass p.center)=
      (8/25)*p.center.theta-5*p.center.theta^2 := by
  norm_num [partialMass,oneMixedMass,delta]
  ring

end Parameters

def commonLaw {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) : ProbabilityMeasure ℝ :=
  mixFourComponents p.lawInput

theorem commonLaw_properties {eta1 eta2 : ℝ} (p : Parameters eta1 eta2) :
    AtomlessUnboundedPositiveDensity (commonLaw p) p.tailFloor :=
  uniform_pareto_mixture_properties p.lawInput

theorem exists_parameters (eta1 eta2 : ℝ) (h1 : 0 < eta1)
    (h12 : eta1 < eta2) (h2 : eta2 < 1) : Nonempty (Parameters eta1 eta2) := by
  obtain ⟨eps,heps,hepssmall,hrates⟩ := perturbable_source_rate_guards
  have ha := small_theta_analytic eta1 eta2 h1 h12 h2
  have hl := small_theta_lower_guards eta1 eta2 h1 h12 h2
  have ht2 : Tendsto (fun t : ℝ=> t^2) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) := by
    have hh : Tendsto (fun t : ℝ=>t^2) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ)^2)):=
      (hasDerivAt_pow 2 (0:ℝ)).continuousAt.tendsto
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0)] using hh.mono_left nhdsWithin_le_nhds
  have hpositive : ∀ᶠt : ℝ in 𝓝[>] (0:ℝ),0< t := self_mem_nhdsWithin
  have hsmall : ∀ᶠt : ℝ in 𝓝[>] (0:ℝ),t<1/100 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/100)).filter_mono nhdsWithin_le_nhds
  have hxi : 0<(1-eta2)/2 := by linarith only [h2]
  have hsource : ∀ᶠt : ℝ in 𝓝[>] (0:ℝ),t<((1-eta2)/2)/100 :=
    (eventually_lt_nhds (div_pos hxi (by norm_num))).filter_mono nhdsWithin_le_nhds
  have hx1 : 0 < (1-eta1)/2 := by linarith only [h12,h2]
  have hx1half : (1-eta1)/2 < 1/2 := by linarith only [h1]
  have htau := lowerRelativeMargin_pos hx1 hx1half
  have hbudget : 0 < 11*((1-eta2)/2)*(lowerRelativeMargin ((1-eta1)/2))^2/(128*((1-eta1)/2)) := by
    positivity
  have hfloor : ∀ᶠt : ℝ in 𝓝[>] (0:ℝ),
      t < 11*((1-eta2)/2)*(lowerRelativeMargin ((1-eta1)/2))^2/(128*((1-eta1)/2)) :=
    (eventually_lt_nhds hbudget).filter_mono nhdsWithin_le_nhds
  have hall := ha.and (hl.and (hpositive.and (hsmall.and (hsource.and (hfloor.and
    (ht2.eventually (Iio_mem_nhds heps)))))))
  obtain ⟨theta,hat,hlow,hpos,hsm,hsource,hfloor,hsq⟩ := hall.exists
  let c : Center := ⟨eta1,eta2,theta,h1,h12,h2,hpos,by linarith⟩
  obtain ⟨hcentral⟩ := hat c rfl rfl rfl
  obtain ⟨wL,hwL,hL⟩ := hlow c rfl rfl rfl
  obtain ⟨rect,hrect⟩ := closed_rectangle_by_strict_continuity c hcentral
  obtain ⟨wA,hwA,hwA1,hA⟩ := narrow_value_widths c rect hrect
  obtain ⟨wB,hwB,hB⟩ := bulk_floor_widths c rect hrect
  obtain ⟨relative,hmom⟩ := exists_common_source_moment_parameters c rect
  let u := relative.u
  let zeta := relative.zeta
  obtain ⟨bd⟩ := uniform_boundary_Taylor c rect hrect
  let wRaw := min wL (min wA wB)
  let w := min wRaw (min (1/2) (xi c/1000))/2
  have hwRaw : 0<wRaw := lt_min hwL (lt_min hwA hwB)
  have hxi := xi_pos c
  have hw : 0<w := by dsimp [w];positivity
  have hwRaw' : w≤wRaw := by
    have hh := min_le_left wRaw (min (1/2) (xi c/1000))
    dsimp [w]
    linarith only [hh,hwRaw]
  have hwL' : w≤wL := hwRaw'.trans (min_le_left _ _)
  have hwA' : w≤wA := (hwRaw'.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hwB' : w≤wB := (hwRaw'.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hwother : w < min (1/2) (xi c/1000) := by
    have hh := min_le_right wRaw (min (1/2) (xi c/1000))
    have hp : 0< min (1/2:ℝ) (xi c/1000) := lt_min (by norm_num) (by positivity)
    dsimp [w]
    linarith only [hh,hp]
  have hwhalf : w<1/2 := hwother.trans_le (min_le_left _ _)
  have hwsource : w≤xi c/1000 := hwother.le.trans (min_le_right _ _)
  obtain ⟨lower⟩ := hL w hw hwL'
  have hmenus := hA w hw hwA'
  let d0 := min ((1-xiOne c)*lower.L) (min (R c/4) (kappa c/4))/4
  have hd : 0 < d0 := by
    have hx := xiOne_lt_half c
    have hk1 : 0 < 1-xiOne c := by linarith
    have hLp := lower.L_pos
    have hR := R_pos c
    have hk := kappa_pos c
    dsimp [d0]
    positivity
  have hd1 : d0 < (1-xiOne c)*lower.L := by
    have hh := min_le_left ((1-xiOne c)*lower.L) (min (R c/4) (kappa c/4))
    dsimp [d0] at hd ⊢
    linarith
  have hd2 : d0 < min (R c/4) (kappa c/4) := by
    have hh := min_le_right ((1-xiOne c)*lower.L) (min (R c/4) (kappa c/4))
    dsimp [d0] at hd ⊢
    linarith
  have hdw : d0 < 2-w := by
    have hh := hd2.trans_le (min_le_right _ _)
    have hx := xi_pos c
    unfold kappa at hh
    linarith
  let M := max (bulkValue c+2) (bd.V0+1)
  have hM : bulkValue c+w< M := by
    have hh := le_max_left (bulkValue c+2) (bd.V0+1)
    dsimp [M]
    linarith
  have hMb : bd.V0< M := by
    have hh := le_max_right (bulkValue c+2) (bd.V0+1)
    dsimp [M]
    linarith
  have hsourceRate := hrates (delta c) 0 (delta_pos c).le hsq (by norm_num) heps
  refine ⟨{
    center := c
    eta1_eq := rfl
    eta2_eq := rfl
    theta_small := hsm
    theta_source_small := hsource.le
    theta_lower_floor := hfloor.le
    rect := rect
    analytic := hrect
    d0 := d0
    valueWidth := w
    tailMass := zeta
    tailFloor := M
    bulkBidWidth := u
    d0_pos := hd
    valueWidth_pos := hw
    valueWidth_small := by linarith only [hwhalf]
    valueWidth_source_small := hwsource
    low_separation := hdw
    bulk_separation := hmenus.high_values
    tail_separation := hM
    menus := hmenus
    moments := hmom
    relativeMoments := relative
    relative_u := rfl
    relative_zeta := rfl
    rates := {
      privateTolerance := eps
      tolerance_pos := heps
      tolerance_small := hepssmall
      delta_small := hsq
      lower := by simpa only [lowMass,activeMass,partialMass] using hsourceRate.1
      upper := fun z hz0 hz=> by
        simpa only [lowMass,activeMass,partialMass] using
          (hrates (delta c) z (delta_pos c).le hsq hz0 hz).2 }
    lowerGuards := lower
    low_receipt_one := hd1
    low_receipt_two := hd2
    boundary := bd
    tail_above_boundary := hMb
    bulk_derivative := fun lam hlam v hv b hb => (hB w hw hwB' lam hlam v hv).2.2 b hb
    bulk_floor := fun lam hlam v hv b hb=>(hB w hw hwB' lam hlam v hv).1 b hb }⟩

end FCAppendix.Affine.Hybrid.Tail03
