import FCAppendix.Affine.Uniform05RestrictedLaw

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

def guardRadius (i : Row) : ℝ := t i/10000

lemma guardRadius_pos (i : Row) : 0 < guardRadius i :=
  div_pos (t_pos i) (by norm_num)

def lawWeight (i : Row) (G : RestrictedLaw i) (b : ℝ) : ℝ :=
  guardWeight (requiredDemand i) (exposure (xi i) G.multiplier b)

lemma lawWeight_range (i : Row) (G : RestrictedLaw i) (b : ℝ) :
    0 ≤ lawWeight i G b ∧ lawWeight i G b ≤ 1 :=
  ⟨guardWeight_nonneg _ _,guardWeight_le_one _ _⟩

lemma continuous_lawWeight_bid (i : Row) (G : RestrictedLaw i) :
    Continuous (lawWeight i G) := by
  have hz : 0 < G.multiplier := (demandLo_pos i).trans G.multiplier_guards.1
  unfold lawWeight guardWeight
  exact continuous_clip01.comp
    (((continuous_const.mul (continuous_exposure (xi_range i).1 hz)).sub
      continuous_const).div_const _)

lemma continuous_lawWeight (i : Row) :
    Continuous (fun p : RestrictedLaw i × ℝ => lawWeight i p.1 p.2) := by
  have hroot : Continuous (fun p : RestrictedLaw i × ℝ => p.1.multiplier) :=
    RestrictedLaw.continuous_multiplier.comp continuous_fst
  have he : Continuous (fun p : RestrictedLaw i × ℝ =>
      exposure (xi i) p.1.multiplier p.2) := by
    unfold ClippedResidual.exposure
    apply continuous_const.min
    exact (continuous_const.max (continuous_snd.sub hroot)).div
      (continuous_const.mul (continuous_snd.max hroot)) (fun p => by
        have hz : 0 < p.1.multiplier :=
          (demandLo_pos i).trans p.1.multiplier_guards.1
        exact ne_of_gt (mul_pos (xi_range i).1 (hz.trans_le (le_max_right _ _))))
  unfold lawWeight guardWeight
  exact continuous_clip01.comp
    (((continuous_const.mul he).sub continuous_const).div_const _)

lemma continuous_rejection_statistic (i : Row) :
    Continuous (fun p : RestrictedLaw i × ℝ =>
      rejectionExposure (rejectionScale i) p.1.rejectionRoot p.2) :=
  (continuous_rejectionExposure (rejectionScale_pos i)).comp
    ((RestrictedLaw.continuous_rejectionRoot.comp continuous_fst).prodMk continuous_snd)

lemma shifted_multiplier_guards (i : Row) (G : RestrictedLaw i) :
    max (kappa i*cap i) ((52 : ℝ)/100*t i) < G.multiplier-guardRadius i := by
  have hg := G.multiplier_guards.1
  have hreceipt := numerical_root_receipt_gap i
  have ht := t_pos i
  apply max_lt
  · unfold guardRadius
    nlinarith
  · unfold guardRadius
    nlinarith

theorem positive_weight_eligibility (i : Row) (G : RestrictedLaw i)
    {b : ℝ} (hb : b ≤ cap i) (hw : 0 < lawWeight i G b) :
    G.multiplier+3*guardRadius i < b := by
  have hr := (requiredDemand_range i).1
  have hΛ := G.multiplier_guards.1
  have hΛ0 := (demandLo_pos i).trans hΛ
  have ht := t_pos i
  have hp := guardWeight_positive_imp hr hw
  have hΛb : G.multiplier < b := by
    by_contra h
    have he : exposure (xi i) G.multiplier b = 0 := exposure_zero (le_of_not_gt h)
    rw [he] at hp
    linarith
  have hb0 := hΛ0.trans hΛb
  have hreceipt : (1-xi i)*b ≤ G.multiplier := by
    have hκ := (kappa_range i).1.le
    have := (mul_le_mul_of_nonneg_left hb hκ).trans G.multiplier_guards.2.2.2.le
    simpa [kappa] using this
  rw [exposure_of_between (xi_range i).1 hΛ0 hΛb hreceipt] at hp
  have hdiv := (lt_div_iff₀ (xi_range i).1).mp hp
  have hmul := (div_lt_iff₀ hb0).mp
    (show G.multiplier/b < 1-(requiredDemand i/4)*xi i by linarith)
  have hcoeff : (1 : ℝ)/600 ≤ requiredDemand i*xi i/4 := by
    have hrr := requiredDemand_ge_one_sixtieth i
    cases i <;> norm_num [xi,eta] at hrr ⊢ <;> linarith
  have hcb := mul_le_mul_of_nonneg_right hcoeff hb0.le
  have hlower : (54 : ℝ)/100*t i < b := hΛ.trans hΛb
  unfold guardRadius
  nlinarith

lemma integrable_lawWeight (i : Row) (G : RestrictedLaw i) :
    Integrable (fun b : Bid i => lawWeight i G b) (G.bidLaw : Measure (Bid i)) := by
  exact integrable_of_unit_bounds _
    ((continuous_lawWeight_bid i G).comp continuous_subtype_val).measurable
    (fun b => (lawWeight_range i G b).1) (fun b => (lawWeight_range i G b).2)

theorem mean_lawWeight_lower (i : Row) (G : RestrictedLaw i) :
    requiredDemand i/(2-requiredDemand i) ≤
      ∫ b : Bid i, lawWeight i G b ∂(G.bidLaw : Measure (Bid i)) := by
  have hr := (requiredDemand_range i).1
  have hr1 : requiredDemand i < 1 := by linarith [(requiredDemand_range i).2]
  apply weight_mean_lower hr hr1
  have hΛ0 := (demandLo_pos i).trans G.multiplier_guards.1
  have hp := integrable_lawDemand i G.bidLaw hΛ0
  have hw := integrable_lawWeight i G
  have hpoint : ∀ b : Bid i,
      exposure (xi i) G.multiplier b ≤ requiredDemand i/2+
        (1-requiredDemand i/2)*lawWeight i G b := by
    intro b
    exact demand_le_weight_chord hr hr1
      (exposure_nonneg (xi_range i).1 hΛ0) (exposure_le_one _ _ _)
  have h := integral_mono hp ((integrable_const _).add (hw.const_mul _)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const _) (hw.const_mul _), integral_const_mul] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  change lawDemand i G.bidLaw G.multiplier ≤ _ at h
  rwa [G.multiplier_equation] at h

def lawDemandSlack (i : Row) : ℝ :=
  requiredDemand i*guardRadius i/(xi i*cap i+guardRadius i)

lemma lawDemandSlack_pos (i : Row) : 0 < lawDemandSlack i := by
  have hr := (requiredDemand_range i).1
  have ha := guardRadius_pos i
  have hξ := (xi_range i).1
  have hU := cap_pos i
  unfold lawDemandSlack
  positivity

theorem shifted_lawDemand_slack (i : Row) (G : RestrictedLaw i) :
    requiredDemand i+lawDemandSlack i ≤
      lawDemand i G.bidLaw (G.multiplier-guardRadius i) ∧
    lawDemand i G.bidLaw (G.multiplier+guardRadius i) ≤
      requiredDemand i-lawDemandSlack i := by
  have ha := guardRadius_pos i
  have hξ := (xi_range i).1
  have hU := cap_pos i
  have hr := (requiredDemand_range i).1
  have hleft := shifted_multiplier_guards i G
  have hlpos : 0 < G.multiplier-guardRadius i :=
    (rejectionLo_pos i).trans ((le_max_right _ _).trans_lt hleft)
  have hlreceipt : kappa i*cap i ≤ G.multiplier-guardRadius i :=
    ((le_max_left _ _).trans_lt hleft).le
  have hden : 0 < xi i*cap i+guardRadius i := by positivity
  have hbase : 0 < xi i*cap i := mul_pos hξ hU
  have hminus := lawDemand_drop i G.bidLaw hlpos hlreceipt
    (a := G.multiplier-guardRadius i) (b := G.multiplier) le_rfl (by linarith)
  have hplus := lawDemand_drop i G.bidLaw
    ((demandLo_pos i).trans G.multiplier_guards.1)
    G.multiplier_guards.2.2.2.le (a := G.multiplier)
    (b := G.multiplier+guardRadius i) le_rfl (by linarith)
  rw [G.multiplier_equation] at hminus hplus
  have hgap : lawDemandSlack i ≤ guardRadius i/(xi i*cap i)*requiredDemand i := by
    unfold lawDemandSlack
    calc
      requiredDemand i*guardRadius i/(xi i*cap i+guardRadius i)
        ≤ requiredDemand i*guardRadius i/(xi i*cap i) :=
          div_le_div_of_nonneg_left (mul_nonneg hr.le ha.le) hbase (by linarith)
      _ = _ := by ring
  constructor
  · have he : (G.multiplier-(G.multiplier-guardRadius i))/(xi i*cap i) =
        guardRadius i/(xi i*cap i) := by ring
    rw [he] at hminus
    linarith
  · have he : ((G.multiplier+guardRadius i)-G.multiplier)/(xi i*cap i) =
        guardRadius i/(xi i*cap i) := by ring
    rw [he] at hplus
    have hh := (div_le_iff₀ hbase).mp
      (show guardRadius i*lawDemand i G.bidLaw (G.multiplier+guardRadius i)/(xi i*cap i) ≤
        requiredDemand i-lawDemand i G.bidLaw (G.multiplier+guardRadius i) by
        convert! hplus using 1; ring)
    have hgap' : lawDemandSlack i ≤ requiredDemand i-
        lawDemand i G.bidLaw (G.multiplier+guardRadius i) := by
      unfold lawDemandSlack
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith

def restrictedWidth (i : Row) (v : ℝ) : ℝ := min v (cap i)-floorBid i v

lemma restrictedWidth_nonneg (i : Row) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (t i)) :
    0 ≤ restrictedWidth i v :=
  sub_nonneg.mpr (floor_le_min_value_cap i hv.1 hv.2)

lemma restrictedWidth_pos (i : Row) {v : ℝ} (hv0 : 0 < v) (hvt : v ≤ t i) :
    0 < restrictedWidth i v := by
  unfold restrictedWidth
  apply sub_pos.mpr
  apply lt_min
  · have h := floor_le_chi_mul i hv0.le (t_pos i).le
    have hc : chi < 1 := by norm_num [chi]
    nlinarith
  · have h := floor_le_chi_mul i hv0.le (t_pos i).le
    have hc : 0 ≤ chi := by norm_num [chi]
    exact h.trans_lt ((mul_le_mul_of_nonneg_left hvt hc).trans_lt (chi_t_lt_cap i))

def noisyBid (i : Row) (ε v q z : ℝ) : ℝ :=
  floorBid i v+restrictedWidth i v*((1-ε)*q+ε*z)

lemma noisyBid_mem_box (i : Row) {ε v q z : ℝ}
    (hε : ε ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) (t i))
    (hq : q ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    noisyBid i ε v q z ∈ Icc (floorBid i v) (min v (cap i)) := by
  have hmix0 : 0 ≤ (1-ε)*q+ε*z :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hε.2) hq.1) (mul_nonneg hε.1 hz.1)
  have hmix1 : (1-ε)*q+ε*z ≤ 1 := by
    have h₁ := mul_le_mul_of_nonneg_left hq.2 (sub_nonneg.mpr hε.2)
    have h₂ := mul_le_mul_of_nonneg_left hz.2 hε.1
    nlinarith
  have hwidth := restrictedWidth_nonneg i hv
  unfold noisyBid
  constructor
  · nlinarith
  · have h := mul_le_mul_of_nonneg_left hmix1 hwidth
    unfold restrictedWidth at *
    nlinarith

lemma noisyBid_noise_strictMono (i : Row) {ε v q : ℝ}
    (hε : 0 < ε) (hv : 0 < v) (hvt : v ≤ t i) :
    StrictMono (noisyBid i ε v q) := by
  intro z z' hzz'
  have hw := restrictedWidth_pos i hv hvt
  unfold noisyBid
  nlinarith [mul_pos (mul_pos hw hε) (sub_pos.mpr hzz')]

lemma continuous_noisyBid (i : Row) :
    Continuous (fun p : ℝ × ℝ × ℝ × ℝ => noisyBid i p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hf := continuous_floor i
  unfold noisyBid restrictedWidth
  fun_prop

end FCAppendix.Affine.Uniform05
