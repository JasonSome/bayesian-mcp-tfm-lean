import FCAppendix.Affine.Hybrid.Native02.SourceOriginalPayoff
import FCAppendix.Affine.Hybrid.Native02.PrimitiveMenuMargins
import FCAppendix.Affine.LowBody.ActualLowBidEquilibrium

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.Distributional

structure PrimitiveInput where
  eta : ℝ
  s : ℝ
  a : ℝ
  h : ℝ
  rho : ℝ
  d : ℝ
  vlo : ℝ
  vhi : ℝ
  L : ℝ
  U : ℝ
  R : ℝ
  lam : ℝ
  eta_pos : 0< eta
  eta_lt_one : eta<1
  s_pos : 0< s
  a_pos : 0< a
  h_pos : 0< h
  mass : s+a+h=1
  d_nonneg : 0≤ d
  L_pos : 0< L
  L_lt_U : L< U
  value_order : vlo≤ vhi
  z : ℝ
  z_nonneg : 0≤ z
  z_lt_one : z<1
  rho_lower : h/2< rho
  rho_upper : rho< a+h/2
  qbar_pos : 0< sourceExposure a h rho z
  qbar_lt_one : sourceExposure a h rho z<1
  box_lower : (1-(1-eta)/2)*U<(1-(1-eta)/2*sourceExposure a h rho z)*L
  box_upper : (1-(1-eta)/2*sourceExposure a h rho z)*U< L
  low_receipt : d<(1-(1-eta)/2)*L
  value_surplus : U< vlo
  inward_lower : L< inwardScale ((1-eta)/2) z (sourceExposure a h rho z)*vlo
  inward_upper : inwardScale ((1-eta)/2) z (sourceExposure a h rho z)*vhi< U
  upper_floor : U< R
  low_rate_gap : 2*Ample.binaryKL rho (1-h/2)< LowBody.jointRate s a h rho
  capacity : ℕ→ℕ
  capacity_limit : Tendsto (fun m=>(capacity m:ℝ)/(m:ℝ)) atTop (𝓝 rho)
  lowValues : ProbabilityMeasure (LowBody.LowValue d)
  activeValues : ProbabilityMeasure (ActiveValue vlo vhi)
  upperValues : ProbabilityMeasure ℝ
  lowValues_atomless : NullSingletonClass (lowValues : Measure (LowBody.LowValue d))
  activeValues_atomless : NullSingletonClass (activeValues : Measure (ActiveValue vlo vhi))
  upperValues_atomless : NullSingletonClass (upperValues : Measure ℝ)
  low_positive : ∀ᵐv ∂(lowValues : Measure (LowBody.LowValue d)),0< v.1
  activeSupport : Set ℝ
  upperSupport : Set ℝ
  active_compact : IsCompact activeSupport
  upper_compact : IsCompact upperSupport
  active_supported : ∀ᵐv ∂(activeValues : Measure (ActiveValue vlo vhi)),v.1∈ activeSupport
  upper_supported : ∀ᵐv ∂(upperValues : Measure ℝ),v∈ upperSupport
  active_band : activeSupport⊆Icc vlo vhi
  upper_separated : ∀ v∈ upperSupport,vhi< v
  lam_pos : 0< lam
  maximizing_interior : ∀ v : ActiveValue vlo vhi,
    v.1∈ activeSupport→
    unitArgmax (two ((1-eta)/2) z v.1 lam)
      (continuousOn_two_unit (by linarith) (by linarith) z v.1 lam)∈ Ioo (0:ℝ) 1
  clearing : (∫v : ActiveValue vlo vhi,
    unitArgmax (two ((1-eta)/2) z v.1 lam)
      (continuousOn_two_unit (by linarith) (by linarith) z v.1 lam)
      ∂(activeValues : Measure (ActiveValue vlo vhi)))=sourceExposure a h rho z
  active_menu_one : ∀ v∈ activeSupport,
    Menus.U1 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) z lam v<
      Menus.U2 (by linarith : 0 < (1-eta)/2) (by linarith : (1-eta)/2 < 1) z lam v
  active_menu_M1 : ∀ v∈ activeSupport,
    Menus.M1 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) lam v<
      Menus.U2 (by linarith : 0 < (1-eta)/2) (by linarith : (1-eta)/2 < 1) z lam v
  active_menu_upper : ∀ v∈ activeSupport,v-R<
    Menus.U2 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) z lam v
  active_menu_M2 : 0< z→∀ v∈ activeSupport,outsideTwo v lam<
    Menus.U2 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) z lam v
  upper_menu_two : ∀ v∈ upperSupport,
    Menus.U2 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) z lam v< v-R
  upper_menu_one : ∀ v∈ upperSupport,
    Menus.U1 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) z lam v< v-R
  upper_menu_M1 : ∀ v∈ upperSupport,
    Menus.M1 (by linarith : 0<(1-eta)/2) (by linarith : (1-eta)/2<1) lam v< v-R
  upper_menu_M2 : ∀ v∈ upperSupport,outsideTwo v lam< v-R

namespace PrimitiveInput
variable (p : PrimitiveInput)
def xi : ℝ := (1-p.eta)/2
def kappa : ℝ := 1-p.xi
def qbar : ℝ := sourceExposure p.a p.h p.rho p.z
def h0 : ℝ := 1-p.xi*p.qbar
theorem xi_pos : 0< p.xi := by dsimp [xi];linarith [p.eta_lt_one]
theorem xi_half : p.xi<1/2 := by dsimp [xi];linarith [p.eta_pos]
theorem xi_lt_one : p.xi<1 := p.xi_half.trans (by norm_num)
theorem kappa_pos : 0< p.kappa := sub_pos.mpr p.xi_lt_one
theorem kappa_le_one : p.kappa≤1 := by dsimp [kappa];linarith [p.xi_pos]
theorem rho_pos : 0< p.rho := (half_pos p.h_pos).trans p.rho_lower
theorem rho_lt_one : p.rho<1 := by linarith [p.rho_upper,p.s_pos,p.h_pos,p.mass]
theorem h_le_one : p.h≤1 := by linarith [p.s_pos,p.a_pos,p.mass]
theorem d_pos : 0< p.d := low_bound_pos p.lowValues p.low_positive
theorem d_lt_L : p.d< p.L :=
  p.low_receipt.trans (by nlinarith [p.L_pos, p.eta_lt_one])
theorem U_pos : 0< p.U := p.L_pos.trans p.L_lt_U
theorem R_pos : 0< p.R := p.U_pos.trans p.upper_floor
theorem vlo_pos : 0< p.vlo := p.U_pos.trans p.value_surplus
theorem active_nonempty : p.activeSupport.Nonempty := by
  obtain ⟨v,hv⟩:=p.active_supported.exists
  exact ⟨v,hv⟩
theorem upper_nonempty : p.upperSupport.Nonempty := p.upper_supported.exists

abbrev Value := ActiveValue p.vlo p.vhi
abbrev Bid := ActiveBaseBid p.L p.U
abbrev Low := LowBody.LowValue p.d

def q (v : p.Value) : ℝ := unitArgmax (two p.xi p.z v.1 p.lam)
  (continuousOn_two_unit p.xi_pos p.xi_lt_one p.z v.1 p.lam)
def beta (v : p.Value) : ℝ := p.lam/(1-p.xi*p.q v)

theorem q_mem (v : p.Value) : p.q v∈ Icc (0:ℝ) 1 :=
  (unitArgmax_spec _ _).1
theorem q_interior_on_support (v : p.Value) (hv : v.1∈ p.activeSupport) :
    p.q v∈ Ioo (0:ℝ) 1 := p.maximizing_interior v hv
theorem q_max (v : p.Value) (r : ℝ) (hr : r∈ Icc (0:ℝ) 1) :
    two p.xi p.z v.1 p.lam r≤ two p.xi p.z v.1 p.lam (p.q v) :=
  (unitArgmax_spec _ _).2 r hr
theorem target_value (v : p.Value) :
    two p.xi p.z v.1 p.lam (p.q v)=Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam v.1 := rfl

def categories : FiniteLaw (Fin 4) := LowBody.categoryLaw p.s p.a p.h
  p.s_pos.le p.a_pos.le p.h_pos.le p.mass (Measure.dirac (0:ℝ))

def lowReal (low : ProbabilityMeasure p.Low) : Measure ℝ :=
  (low : Measure p.Low).map Subtype.val
instance lowReal_isProbability (low : ProbabilityMeasure p.Low) :
    IsProbabilityMeasure (p.lowReal low) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
def bidReal (pi : Law (A:=p.Bid) (p.activeValues : Measure p.Value)) : Measure ℝ :=
  ((pi.1 : Measure (p.Value×p.Bid)).map Prod.snd).map Subtype.val
instance bidReal_isProbability (pi : Law (A:=p.Bid) (p.activeValues : Measure p.Value)) :
    IsProbabilityMeasure (p.bidReal pi) := by
  letI : IsProbabilityMeasure ((pi.1 : Measure (p.Value×p.Bid)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

def originalValues : Measure ℝ := originalValueLaw p.s p.a p.h
  ((p.lowValues : Measure p.Low).map Subtype.val)
  ((p.activeValues : Measure p.Value).map Subtype.val) p.upperValues

end PrimitiveInput

structure FrozenActiveFamily (p : PrimitiveInput) where
  start : ℕ
  low : ℕ→ ProbabilityMeasure p.Low
  joint : ℕ→ Law (A:=p.Bid) (p.activeValues : Measure p.Value)
  low_witness : ∀ m≥ start,∃W : LowBody.ActualAtomlessLowLimit (m-1) p.d p.xi
    (p.capacity m) p.categories (p.lowValues : Measure p.Low),
      low m=W.joint.1.map measurable_snd.aemeasurable
  atomless : ∀ m≥ start,NullSingletonClass
    ((joint m).1.map measurable_snd.aemeasurable : Measure p.Bid)
  numeric_IC : ∀ m≥ start,∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),∀ b : p.Bid,
    FullContext.physicalSourceUtility (m-1) (p.capacity m) p.xi p.z p.L p.U
      p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
      (p.lowReal (low m)) (p.bidReal (joint m)) x.1.1 b.1≤
    FullContext.physicalSourceUtility (m-1) (p.capacity m) p.xi p.z p.L p.U
      p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
      (p.lowReal (low m)) (p.bidReal (joint m)) x.1.1 x.2.1
  price_limit : Tendsto (fun m=> p.h0/reciprocalMean (p.bidReal (joint m)))
    atTop (𝓝 p.lam)
  supported_graph : ∀ eps>0,∀ᶠm in atTop,
    ∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),|x.2.1-p.beta x.1|< eps
  response_measurable : Measurable p.q
  response_boxed : ∀ v : p.Value,p.beta v∈ Icc p.L p.U

def ActiveProducer : Prop := ∀ p : PrimitiveInput,Nonempty (FrozenActiveFamily p)

end FCAppendix.Affine.Hybrid.Native02
