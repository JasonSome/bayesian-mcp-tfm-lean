import FCAppendix.Affine.Hybrid.Tail03.LowerEarlyResponse
import FCAppendix.Affine.Tail04.SourcePairContract

noncomputable section
namespace FCAppendix.Affine.Hybrid.Tail03.LowerEarlySource
open MeasureTheory ProbabilityTheory Set Filter Topology
open EarlySourceAdapter LowerEarlyResponse
open FCAppendix.Affine.Tail04.CoefficientOne

variable {eta1 eta2 : ℝ} (p : Parameters eta1 eta2)

def source : BoundedSource (values p) where
  scalar := LowerEarlyScalar.scalar p
  L := p.lowerGuards.L
  lam := clearing p
  upperMax := bulkValue p.center+p.valueWidth
  FH0 := ⟨bandMeasure (bulkValue p.center-p.valueWidth) (bulkValue p.center+p.valueWidth),
    bandMeasure_probability (by linarith [p.valueWidth_pos])⟩
  q := response p
  q_measurable := response_measurable p
  upper_value_atomless := bandMeasure_atomless _ _
  upper_value_support := bandMeasure_supported _ _

lemma multiplier_box : (clearing p : ℝ) ∈
    Icc (lowerH (xiOne p.center)*p.lowerGuards.L)
      (lowerH (xiOne p.center)*p.lowerGuards.U) := by
  have h := (clearing p).2
  simpa only [Finish01.Primitives.h0,Finish01.Primitives.qbar,primitives,exposure_eq,lowerH] using h

lemma guards : BoundedSourceGuards (source p) where
  low_rate_gap := by convert! (primitives p).low_rate_gap
  L_pos := p.lowerGuards.L_pos
  lam_pos := (primitives p).price_pos (clearing p)
  q_interior := response_interior p
  q_maximizes := response_maximizes p
  q_mean := response_mean p
  receipt_order := by
    have hH : 0 < lowerH (xiOne p.center) := by
      linarith [(lowerH_bounds (xiOne_pos p.center) (xiOne_lt_half p.center)).1]
    refine ⟨?_,?_,?_⟩
    · convert! p.lowerGuards.receipt_lo
    · convert! mul_lt_mul_of_pos_left p.lowerGuards.box_strict hH
    · convert! p.lowerGuards.receipt_hi
  low_receipt_gap := p.low_receipt_one
  inward := by
    have hT := (primitives p).scale_pos
    have hmid := mul_lt_mul_of_pos_left
      (by linarith [p.valueWidth_pos] : 2-p.valueWidth < 2+p.valueWidth) hT
    refine ⟨?_,?_,?_,?_⟩
    · convert! p.lowerGuards.inward_lo
    · change inwardScale (xiOne p.center) (oneOwnerMass p.center) (3/5)*(2-p.valueWidth) <
        inwardScale (xiOne p.center) (oneOwnerMass p.center) (3/5)*(2+p.valueWidth)
      simpa only [primitives,Finish01.Primitives.qbar,exposure_eq] using hmid
    · convert! p.lowerGuards.inward_hi
    · exact p.lowerGuards.upper_value
  lower_multiplier := rfl
  active_gap := by
    intro v hv
    have hg := active_all_menu_guards (p.lowerGuards.active v hv (clearing p) (multiplier_box p))
    have hmax := response_maximizes p v hv (3/5) (by norm_num)
    refine ⟨?_,?_,?_,?_⟩
    · intro q hq
      convert! ((hg.2.2 q hq).1).trans_le hmax
    · intro q hq
      have h := ((hg.2.2 q hq).2).trans_le hmax
      convert! h using 1
      simp only [Hybrid.one,zero_div,zero_add,sub_zero,one_mul]
      rfl
    · convert! hg.1.trans_le hmax
    · intro _hz
      convert! hg.2.1.trans_le hmax
  upper_gap := by
    intro v hv
    have hg := upper_all_menu_guards (p.lowerGuards.upper (clearing p) (multiplier_box p)) v hv.1
    refine ⟨?_,?_,?_,?_⟩
    · intro q hq
      convert! (hg.2 q hq).1
    · intro q hq
      convert! (hg.2 q hq).2.1
    · intro q hq
      have h := (hg.2 q hq).2.2
      convert! h using 1
      simp only [Hybrid.one,zero_div,zero_add,sub_zero,one_mul]
      rfl
    · convert! hg.1

def pair : FCAppendix.Affine.Tail04.SourcePairContract.Parameters eta1 eta2 where
  two := analyticParameters p
  one := source p
  one_guards := guards p
  first_coefficient := p.eta1_eq
  second_coefficient := by
    change 1-2*xi p.center = eta2
    unfold xi
    linarith only [p.eta2_eq]
  coefficient_order := by linarith only [p.eta1_eq,p.eta2_eq,p.center.eta12]

theorem exists_pair (eta1 eta2 : ℝ) (h1 : 0 < eta1) (h12 : eta1 < eta2) (h2 : eta2 < 1) :
    Nonempty (FCAppendix.Affine.Tail04.SourcePairContract.Parameters eta1 eta2) := by
  obtain ⟨p⟩ := exists_parameters eta1 eta2 h1 h12 h2
  exact ⟨pair p⟩

end FCAppendix.Affine.Hybrid.Tail03.LowerEarlySource
