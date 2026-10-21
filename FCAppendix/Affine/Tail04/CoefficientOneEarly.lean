import FCAppendix.Affine.Tail04.OriginalCompactLaws
import FCAppendix.Affine.Hybrid.Menu
import FCAppendix.Affine.LowBody.SourcePrimitiveGuards
import FCAppendix.Probability.PiBinomial
import FCAppendix.Probability.IndependentCounts

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open OriginalValues

structure ScalarInput (P : ValueParameters) where
  eta : ℝ
  U : ℝ
  R : ℝ
  lambdaLo : ℝ
  eta_pos : 0< eta
  eta_lt_one : eta<1
  U_pos : 0< U
  cap_below_floor : U< R
  floor_below_upper : R< P.vA-P.w
  multiplier_pos : 0< lambdaLo
  multiplier_below_floor : lambdaLo< R
  canonical_gap : (1-(1-eta)/2)*R< lambdaLo
  upper_gap : R<(P.vA-P.w)*(5*P.theta^2/partialMass)*
    (1-(1-lambdaLo/R)/((1-eta)/2))^2

namespace ScalarInput
variable {P : ValueParameters} (p : ScalarInput P)
def xi : ℝ := (1-p.eta)/2
def mixedMass (_p : ScalarInput P) : ℝ := 5*P.theta^2/partialMass
def qR : ℝ := (1-p.lambdaLo/p.R)/p.xi
def rho : ℝ := p.mixedMass*(1-p.qR)^2
theorem floor_pos : 0< p.R := p.U_pos.trans p.cap_below_floor
theorem xi_pos : 0< p.xi := by unfold xi;linarith [p.eta_lt_one]
theorem qR_lt_one : p.qR<1 := by
  have hratio : 1-p.xi< p.lambdaLo/p.R := (lt_div_iff₀ p.floor_pos).mpr p.canonical_gap
  exact (div_lt_one p.xi_pos).mpr (by linarith)
theorem mixedMass_pos : 0< p.mixedMass := by
  unfold mixedMass
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos P.theta_pos))
    (by norm_num [partialMass])
theorem rho_pos : 0< p.rho :=
  mul_pos p.mixedMass_pos (sq_pos_of_pos (sub_pos.mpr p.qR_lt_one))
theorem upper_gap_rho : p.R<(P.vA-P.w)*p.rho := by
  simpa only [rho,mixedMass,qR,xi,mul_assoc] using p.upper_gap
end ScalarInput

def lowerValues (P : ValueParameters) : Set ℝ := Icc 0 P.d0∪P.partialValues

theorem lowerValues_below {P : ValueParameters} (v : ℝ) (hv : v∈lowerValues P) :
    v< P.vA-P.w := by
  rcases hv with hlow | hpartial
  · linarith [hlow.2,P.low_partial_gap,P.partial_active_gap,P.w_pos]
  · exact hpartial.2.trans_lt P.partial_active_gap

namespace ScalarInput
variable {P : ValueParameters} (p : ScalarInput P)

def ownerMass : ℝ := 1-p.mixedMass

theorem mixedMass_lt_one : p.mixedMass<1 := by
  have ht := P.theta_small
  have ht0 := P.theta_pos
  have hsq : P.theta^2<1/100 := by nlinarith
  change 5*P.theta^2/partialMass<1
  norm_num [partialMass]
  nlinarith

theorem ownerMass_bounds : p.ownerMass∈Ico (0:ℝ) 1 := by
  unfold ownerMass
  exact ⟨by linarith [p.mixedMass_lt_one],by linarith [p.mixedMass_pos]⟩

theorem source_qbar :
    (((99/200:ℝ)-activeMass P.theta/2)/partialMass-p.ownerMass/2)/
      (1-p.ownerMass)=3/5 := by
  have he : 1-p.ownerMass=p.mixedMass := by unfold ownerMass;ring
  rw [he]
  apply (div_eq_iff p.mixedMass_pos.ne').mpr
  unfold ownerMass mixedMass activeMass delta partialMass
  ring

theorem source_rank_interior (_p : ScalarInput P) :
    activeMass P.theta/2<99/200 ∧ 99/200< partialMass+activeMass P.theta/2 := by
  have ht := P.theta_pos
  have ht1 := P.theta_small
  unfold activeMass partialMass delta
  constructor <;> nlinarith [sq_nonneg P.theta]

end ScalarInput

structure BoundedSource (P : ValueParameters) where
  scalar : ScalarInput P
  L : ℝ
  lam : ℝ
  upperMax : ℝ
  FH0 : ProbabilityMeasure ℝ
  q : ℝ → ℝ
  q_measurable : Measurable q
  upper_value_atomless : NullSingletonClass (FH0 : Measure ℝ)
  upper_value_support : ∀ᵐ v ∂(FH0 : Measure ℝ),v∈Icc (P.vA-P.w) upperMax

namespace BoundedSource
variable {P : ValueParameters} (s : BoundedSource P)

def h0 : ℝ := 1-s.scalar.xi*(3/5)
def T0 : ℝ := Hybrid.inwardScale s.scalar.xi s.scalar.ownerMass (3/5)

def valueMeasure : Measure ℝ :=
  ENNReal.ofReal (lowMass P.theta) • (P.originalLowLaw.map Subtype.val) +
  ENNReal.ofReal partialMass • (P.originalPartialLaw.map Subtype.val) +
  ENNReal.ofReal (activeMass P.theta) • (s.FH0 : Measure ℝ)

end BoundedSource

structure BoundedSourceGuards {P : ValueParameters} (s : BoundedSource P) : Prop where
  low_rate_gap :
    2*Ample.binaryKL (99/200) (1-activeMass P.theta/2)<
      LowBody.jointRate (lowMass P.theta) partialMass (activeMass P.theta) (99/200)
  L_pos : 0< s.L
  lam_pos : 0< s.lam
  q_interior : ∀ v∈P.partialValues,s.q v∈Ioo (0:ℝ) 1
  q_maximizes : ∀ v∈P.partialValues,∀ q∈Icc (0:ℝ) 1,
    Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam q≤
      Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v)
  q_mean : (∫ v, s.q v ∂(P.originalPartialLaw.map Subtype.val))=3/5
  receipt_order :
    (1-s.scalar.xi)*s.scalar.U< s.h0*s.L ∧ s.h0*s.L< s.h0*s.scalar.U ∧
      s.h0*s.scalar.U< s.L
  low_receipt_gap : P.d0<(1-s.scalar.xi)*s.L
  inward : s.L< s.T0*(2-P.w) ∧ s.T0*(2-P.w)< s.T0*(2+P.w) ∧
    s.T0*(2+P.w)< s.scalar.U ∧ s.scalar.U<2-P.w
  lower_multiplier : s.scalar.lambdaLo=s.h0*s.L
  active_gap : ∀ v∈P.partialValues,
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.one s.scalar.xi s.scalar.ownerMass v s.lam q<
        Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v)) ∧
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.one s.scalar.xi 0 v s.lam q<
        Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v)) ∧
    v-s.scalar.R< Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v) ∧
    (0< s.scalar.ownerMass → Hybrid.outsideTwo v s.lam<
      Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v))
  upper_gap : ∀ v∈Icc (P.vA-P.w) s.upperMax,
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.two s.scalar.xi s.scalar.ownerMass v s.lam q< v-s.scalar.R) ∧
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.one s.scalar.xi s.scalar.ownerMass v s.lam q< v-s.scalar.R) ∧
    (∀ q∈Icc (0:ℝ) 1,
      Hybrid.one s.scalar.xi 0 v s.lam q< v-s.scalar.R) ∧
    Hybrid.outsideTwo v s.lam< v-s.scalar.R

namespace BoundedSource
variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

def partialLimit (v : ℝ) (hv : v∈P.partialValues) : CountLaw 2 :=
  FiniteLaw.mixture (FiniteLaw.dirac 1)
    (IndependentCounts.binomial 2 (s.q v) (hs.q_interior v hv).1.le (hs.q_interior v hv).2.le)
    s.scalar.ownerMass s.scalar.ownerMass_bounds.1 s.scalar.ownerMass_bounds.2.le

def lowerLimit (v : ℝ) : CountLaw 2 :=
  if hv : v∈P.partialValues then s.partialLimit hs v hv else FiniteLaw.dirac 0

theorem lowerLimit_low (v : ℝ) (hv : v∈Icc 0 P.d0) :
    s.lowerLimit hs v=FiniteLaw.dirac 0 := by
  have hn : v∉P.partialValues := by
    intro hp
    exact (not_le.mpr (hv.2.trans_lt P.low_partial_gap)) hp.1
  simp only [lowerLimit,dif_neg hn]

theorem lowerLimit_partial (v : ℝ) (hv : v∈P.partialValues) :
    s.lowerLimit hs v=s.partialLimit hs v hv := by
  simp only [lowerLimit,dif_pos hv]

theorem partialLimit_expect (v : ℝ) (hv : v∈P.partialValues) (f : Fin 3→ℝ) :
    (s.partialLimit hs v hv).expect f=
      s.scalar.ownerMass*f 1+s.scalar.mixedMass*
        (IndependentCounts.binomial 2 (s.q v)
          (hs.q_interior v hv).1.le (hs.q_interior v hv).2.le).expect f := by
  rw [partialLimit,FiniteLaw.expect_mixture,FiniteLaw.expect_dirac]
  congr 1
  unfold ScalarInput.ownerMass
  ring

end BoundedSource

end FCAppendix.Affine.Tail04.CoefficientOne
