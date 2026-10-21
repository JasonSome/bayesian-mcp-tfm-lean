import FCAppendix.Affine.Tail04.OriginalValueLaw
import FCAppendix.Affine.LowBody.CategoricalRateGuards

noncomputable section
namespace FCAppendix.Affine.Tail04.SourceAnalyticContract
open MeasureTheory Set Real

def endpoint (ξ : ℝ) : ℝ := 1+ξ/50
def partialFloor (ξ : ℝ) : ℝ := 1-37*ξ/40
def flagBase (P : ValueParameters) (reg : Bool) : ℝ :=
  if reg then 5*(partialMass+P.theta^2)/(4*activeMass P.theta)
  else 10*P.theta^2/(9*activeMass P.theta)
def flag (P : ValueParameters) (ξ : ℝ) (reg : Bool) (b : ℝ) : ℝ :=
  flagBase P reg*((endpoint ξ-b)/(endpoint ξ-1))^2
def exposure (ξ lam b : ℝ) : ℝ := (1-lam/b)/ξ
def success (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) : ℝ :=
  1-((1-P.theta)*flag P ξ false b*(1-exposure ξ lam.1 b)^2+
    P.theta*flag P ξ true b*(1-exposure ξ lam.2 b)^2)
def duplicates (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) : ℝ :=
  (1-P.theta)*flag P ξ false b*(exposure ξ lam.1 b)^2+
    P.theta*flag P ξ true b*(exposure ξ lam.2 b)^2
def payment (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (b : ℝ) : ℝ :=
  b*(success P ξ lam b+(1-2*ξ)*duplicates P ξ lam b)
def utility (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) (v b : ℝ) : ℝ :=
  v*success P ξ lam b-payment P ξ lam b
def leading (P : ValueParameters) (ξ : ℝ) (lam : ℝ×ℝ) : ℝ :=
  ((1-P.theta)*flagBase P false*(1-exposure ξ lam.1 (endpoint ξ))^2+
    P.theta*flagBase P true*(1-exposure ξ lam.2 (endpoint ξ))^2)/(endpoint ξ-1)^2
def centerMoment (P : ValueParameters) (reg : Bool) : ℝ :=
  if reg then 5*(partialMass+P.theta^2)/4 else 10*P.theta^2/9
def numerator (P : ValueParameters) (ξ M : ℝ) (reg : Bool) : ℝ :=
  if reg then (1-ξ/2)*M-ξ*(partialMass+P.theta^2)/2
  else (1-ξ/2)*M-ξ*(P.theta^2)/2
def relativeError (P : ValueParameters) (ξ u : ℝ) : ℝ :=
  P.zeta+u*(1+2/(endpoint ξ-1))

structure Parameters where
  P : ValueParameters
  ξ : ℝ
  Up : ℝ
  u : ℝ
  k : ℝ
  width : ℝ
  ρ : ℝ
  κ : ℝ
  Amin : ℝ
  Amax : ℝ
  ξ_pos : 0< ξ
  ξ_half : ξ<1/2
  u_pos : 0< u
  partial_floor_lt : partialFloor ξ< Up
  partial_cap_lt_one : Up<1
  width_pos : 0< width
  low_gap : P.d0<1-ξ
  width_small : width≤ ξ/1000
  partial_value_gap : Up<2-P.w
  bulk_box_lt : 1+u< endpoint ξ
  partial_width_small : Up< partialFloor ξ+ξ/1000
  moment_small : relativeError P ξ u< ξ/1000
  κ_pos : 0< κ
  Amin_pos : 0< Amin
  cap_lower : 1/(4*Amin)< k
  cap_upper : k<1/(2*Amax)
  low_entropy_gap :
    2*Ample.binaryKL (99/200) (1-partialMass/2)<
      LowBody.jointRate (lowMass P.theta) (activeMass P.theta) partialMass (99/200)
  Λ : Set (ℝ×ℝ)
  compact_rectangle : IsCompact Λ
  moment_tolerance : relativeError P ξ u< ρ
  moment_invariant : ∀M W : Bool→ℝ,
    (∀reg,|M reg-centerMoment P reg|≤ centerMoment P reg*ρ)→
    (∀reg,|W reg-centerMoment P reg|≤ centerMoment P reg*ρ)→
    (numerator P ξ (M false) false/W false,numerator P ξ (M true) true/W true)∈Λ
  bulk_derivative : ∀lam∈Λ,∀v∈Icc (P.vA-P.w) (P.vA+P.w),∀b∈Icc (1:ℝ) (endpoint ξ),
    deriv (utility P ξ lam v) b≤-κ
  tail_derivatives : ∀lam∈Λ,
    (∀b∈Ico (1:ℝ) (endpoint ξ),0< deriv (success P ξ lam) b) ∧
    (∀b∈Ioo (1:ℝ) (endpoint ξ),
      0< deriv (deriv (payment P ξ lam)) b*deriv (success P ξ lam) b-
        deriv (payment P ξ lam) b*deriv (deriv (success P ξ lam)) b) ∧
    deriv (payment P ξ lam) 1< P.M*deriv (success P ξ lam) 1
  leading_bounds : ∀lam∈Λ,Amin≤ leading P ξ lam ∧ leading P ξ lam≤ Amax
  exposure_rectangle : ∀lam∈Λ,
    (1-ξ)*endpoint ξ< lam.1 ∧ lam.1<1-ξ/2 ∧
      (1-ξ)*endpoint ξ< lam.2 ∧ lam.2<1-ξ/2
  theta_small : P.theta≤ ξ/100
  value_width_small : P.w≤ ξ/1000
  bulk_center : P.vA=11*ξ/(10*P.theta)

namespace Parameters

variable (S : Parameters)

lemma k_pos : 0< S.k :=
  (by have hh:=S.Amin_pos;positivity : 0<1/(4*S.Amin)).trans S.cap_lower

lemma Amax_pos : 0< S.Amax := by
  have hh:=one_div_pos.mp (S.k_pos.trans S.cap_upper)
  linarith

lemma coefficient_pos : 0<1-2*S.ξ := by linarith [S.ξ_half]
lemma coefficient_lt_one : 1-2*S.ξ<1 := by linarith [S.ξ_pos]

end Parameters
end FCAppendix.Affine.Tail04.SourceAnalyticContract
