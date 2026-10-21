import FCAppendix.Affine.Hybrid.Tail03.LowerEarlyScalar
import FCAppendix.Affine.Tail04.OriginalCompactAtomless
import FCAppendix.Affine.Hybrid.Finishing01ClearingScalar

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03.LowerEarlyResponse
open MeasureTheory ProbabilityTheory Set Filter Topology
open EarlySourceAdapter

variable {eta1 eta2 : ℝ} (p : Parameters eta1 eta2)

lemma exposure_eq : sourceExposure (partialMass p.center) (activeMass p.center) (99/200)
    (oneOwnerMass p.center) = 3/5 := by
  change (((99/200:ℝ)-activeMass p.center/2)/(partialMass p.center)-oneOwnerMass p.center/2)/
    (1-oneOwnerMass p.center) = 3/5
  convert! (LowerEarlyScalar.scalar p).source_qbar

lemma owner_bounds : oneOwnerMass p.center ∈ Ico (0:ℝ) 1 := by
  convert! (LowerEarlyScalar.scalar p).ownerMass_bounds

def primitives : Finish01.Primitives where
  s := lowMass p.center
  a := partialMass p.center
  h := activeMass p.center
  rho := 99/200
  d := p.d0
  vlo := 2-p.valueWidth
  vhi := 2+p.valueWidth
  L := p.lowerGuards.L
  U := p.lowerGuards.U
  xi := xiOne p.center
  z := oneOwnerMass p.center
  s_pos := by dsimp [lowMass,delta];positivity
  a_pos := by norm_num [partialMass]
  h_pos := activeMass_pos p.center
  mass := masses_sum p.center
  xi_pos := xiOne_pos p.center
  xi_half := xiOne_lt_half p.center
  z_nonneg := (owner_bounds p).1
  z_lt_one := (owner_bounds p).2
  d_nonneg := p.d0_pos.le
  L_pos := p.lowerGuards.L_pos
  value_order := by linarith [p.valueWidth_pos]
  rho_lower := by
    convert! (LowerEarlyScalar.scalar p).source_rank_interior.1
  rho_upper := by
    convert! (LowerEarlyScalar.scalar p).source_rank_interior.2
  qbar_pos := by rw [exposure_eq p];norm_num
  qbar_lt_one := by rw [exposure_eq p];norm_num
  box_lower := by simpa only [exposure_eq p,lowerH] using p.lowerGuards.receipt_lo
  box_upper := by simpa only [exposure_eq p,lowerH] using p.lowerGuards.receipt_hi
  low_receipt := p.low_receipt_one
  value_surplus := p.lowerGuards.upper_value
  inward_lower := by simpa only [exposure_eq p] using p.lowerGuards.inward_lo
  inward_upper := by simpa only [exposure_eq p] using p.lowerGuards.inward_hi
  low_rate_gap := by linarith only [p.rates.lower]

def partialLaw : Measure (primitives p).Value := (values p).originalPartialLaw

instance partialLaw_probability : IsProbabilityMeasure (partialLaw p) := by
  convert! FCAppendix.Affine.Tail04.ValueParameters.originalPartialLaw_probability (values p)

def clearing : (primitives p).Price :=
  ((primitives p).exists_unique_clearing (partialLaw p)).choose

lemma clearing_mean :
    (∫ v : (primitives p).Value,(primitives p).qResponse v (clearing p)
      ∂partialLaw p) = 3/5 := by
  have h := ((primitives p).exists_unique_clearing (partialLaw p)).choose_spec.1
  exact h.trans (exposure_eq p)

def response (v : ℝ) : ℝ :=
  (primitives p).qResponse
    (FCAppendix.Affine.Tail04.OriginalValues.clipToBand (2-p.valueWidth) (2+p.valueWidth)
      (by linarith [p.valueWidth_pos]) v) (clearing p)

lemma response_measurable : Measurable (response p) := by
  exact (primitives p).continuous_response.measurable.comp
    ((FCAppendix.Affine.Tail04.OriginalValues.measurable_clipToBand (2-p.valueWidth) (2+p.valueWidth)
      (by linarith [p.valueWidth_pos])).prodMk measurable_const)

lemma response_on_band (v : ℝ) (hv : v ∈ Icc (2-p.valueWidth) (2+p.valueWidth)) :
    response p v = (primitives p).qResponse v (clearing p) := by
  unfold response
  rw [FCAppendix.Affine.Tail04.OriginalValues.clipToBand_eq _ _ _ hv]

lemma response_interior (v : ℝ) (hv : v ∈ Icc (2-p.valueWidth) (2+p.valueWidth)) :
    response p v ∈ Ioo (0:ℝ) 1 := by
  rw [response_on_band p v hv]
  exact ((primitives p).qResponse_spec ⟨v,hv⟩ (clearing p)).1

lemma response_maximizes (v : ℝ) (hv : v ∈ Icc (2-p.valueWidth) (2+p.valueWidth))
    (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    two (xiOne p.center) (oneOwnerMass p.center) v (clearing p) r ≤
      two (xiOne p.center) (oneOwnerMass p.center) v (clearing p) (response p v) := by
  rw [response_on_band p v hv]
  have hg := (primitives p).response_quadratic_gap ⟨v,hv⟩ (clearing p) hr
  have hp : 0 ≤ (1-(primitives p).z)*(primitives p).vlo*
      (r-(primitives p).qResponse v (clearing p))^2 := by
    have hz := (primitives p).z_lt_one
    have hval := (primitives p).vlo_pos
    positivity
  change 0 ≤ (1-oneOwnerMass p.center)*(2-p.valueWidth)*
    (r-(primitives p).qResponse v (clearing p))^2 at hp
  change (1-oneOwnerMass p.center)*(2-p.valueWidth)*
    (r-(primitives p).qResponse v (clearing p))^2 ≤
      two (xiOne p.center) (oneOwnerMass p.center) v (clearing p)
        ((primitives p).qResponse v (clearing p))-
      two (xiOne p.center) (oneOwnerMass p.center) v (clearing p) r at hg
  linarith only [hp,hg]

lemma response_mean :
    (∫ v,response p v ∂((values p).originalPartialLaw.map Subtype.val)) = 3/5 := by
  rw [integral_map measurable_subtype_coe.aemeasurable (response_measurable p).aestronglyMeasurable]
  calc
    _ = ∫ v : (primitives p).Value,(primitives p).qResponse v (clearing p)
        ∂(values p).originalPartialLaw := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => response_on_band p v.1 v.2)
    _ = _ := by convert! clearing_mean p

end FCAppendix.Affine.Hybrid.Tail03.LowerEarlyResponse
