import FCAppendix.Affine.Uniform06.EntryGoodModerate
import FCAppendix.Affine.Uniform06.EntryLiteralAbove

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace FCAppendix.Affine.Uniform06.EntryModerateRootFinite
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.WeightedSampling
open EntryRawSignMoments EntryUntilting EntryLiteralResponseGeometry
open EntryLiteralResponseMoments EntryReciprocalLimit EntryRandomReciprocal
open EntryResponseTransfer EntryEmpiricalRatio ReciprocalSecantBounds
open scoped BigOperators

variable {N C : ℕ}

def goodMoment (ν : Measure RowRival) (i : Row) (C : ℕ) (g : LiteralExperiment.GuardData)
    (b A U ε : ℝ) (k : ℕ) (x : EntryIIDCentral.Row (Ω := RowRival) N) : ℝ :=
  if x∈usable ν i g b A U ε then deficitMoment k (sampleDeficit i C b g.multiplier x) else 0

lemma measurable_goodMoment (ν : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε : ℝ) (k : ℕ) :
    Measurable (goodMoment (N := N) ν i C g b A U ε k) :=
  Measurable.ite (measurable_usable ν i g b A U ε)
    (measurable_deficitMoment (measurable_sampleDeficit i C b g.multiplier) k) measurable_const

lemma goodMoment_nonneg (ν : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε : ℝ) (k : ℕ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) : 0 ≤ goodMoment ν i C g b A U ε k x := by
  unfold goodMoment
  split_ifs
  · exact deficitMoment_nonneg _ _
  · exact le_rfl

lemma goodMoment_le (ν : Measure RowRival) (i : Row) (C : ℕ)
    (g : LiteralExperiment.GuardData) (b A U ε : ℝ) (k : ℕ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    goodMoment ν i C g b A U ε k x ≤ deficitMoment k (sampleDeficit i C b g.multiplier x) := by
  unfold goodMoment
  split_ifs <;> simp [deficitMoment_nonneg]

lemma good_deficit_identity (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (hstar : ℝ) (x : EntryIIDCentral.Row (Ω := RowRival) N)
    (hx : x∈usable ν i g b A U ε) :
    EntryRawCentral.deficit i C b g.multiplier c hstar x=sampleDeficit i C b g.multiplier x := by
  have hW := finite_weight ν i g h x.1 hx.1
  change c * (N : ℝ) ≤ totalWeight (weights i b g.multiplier x.1) at hW
  unfold EntryRawCentral.deficit EntryRawCentral.selected EntryCentralSampling.guardedSample
  change (C : ℝ) - (∑ j, RawMixedSource.demand (xi i) b (x.1 j)) -
    (if c * (N : ℝ) ≤ totalWeight (weights i b g.multiplier x.1) then
      EntrySamplingLaw.sampled (weights i b g.multiplier) (hs i b) RawMixedSource.draws x
    else (RawMixedSource.draws x.1 : ℝ) * hstar) = _
  rw [if_pos hW]
  rfl

lemma response_strict_indicator (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    deficitMoment 0 (response ν i C g b A U ε x)=goodMoment ν i C g b A U ε 0 x := by
  have hp := (total_finite_geometry ν i g h 0 x).2.2.2.2.2.2
  unfold goodMoment
  by_cases hx : x∈usable ν i g b A U ε
  · rw [if_pos hx]
    simp only [deficitMoment_zero]
    congr 1
    rw [hp,good_deficit_identity ν i g h 0 x hx]
    simp [hx]
  · have hz : response ν i C g b A U ε x=0 := by simp [response,hx]
    simp [hz,hx]

theorem rescaled_response_moment (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s d : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (hd : 0 < d) (hdq : d ≤ q/(2*U)) (k : ℕ)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) :
    (N:ℝ)^k*deficitMoment k (response ν i C g b A U ε x)=
      (coefficient N b d (slope ν i C g b A U ε x/(N:ℝ)))^k*
        goodMoment ν i C g b A U ε k x := by
  by_cases hk : k=0
  · subst k
    simp only [pow_zero,one_mul,response_strict_indicator ν i g h x]
  have hN : (0:ℝ)< N := Nat.cast_pos.mpr h.rivals_pos
  have hp0 : 0 ≤ response ν i C g b A U ε x := by
    unfold response
    split_ifs
    · exact (complement_bounds i C g b x).1
    · rfl
  have he := EntryLiteralAbove.response_coefficient_scale ν i g h hd hdq
    (show (0:ℝ)<1 by norm_num) 0 x
  simp only [div_one] at he
  unfold goodMoment
  by_cases hx : x∈usable ν i g b A U ε
  · rw [if_pos hx]
    rw [if_pos hx,good_deficit_identity ν i g h 0 x hx] at he
    have hh := congrArg (fun z : ℝ => z^k) he
    simpa only [deficitMoment,if_neg hk,max_eq_left hp0,mul_pow] using hh
  · have hz : response ν i C g b A U ε x=0 := by simp [response,hx]
    simp [hx,hz,deficitMoment,hk]

lemma successful_draw_bound (i : Row) (C : ℕ) (b l : ℝ)
    {a : ℝ} (ha : 0 < a) (x : EntryIIDCentral.Row (Ω := RowRival) N)
    (hh : ∀ j,a ≤ hs i b x.1 j) (hD : 0 < sampleDeficit i C b l x) :
    (RawMixedSource.draws x.1:ℝ) ≤ balanced i C b x.1/a := by
  have hsum := EntryRenewal.selectedSum_lower (hs i b x.1) hh (RawMixedSource.draws x.1)
    (EntrySamplingLaw.sampler (RawMixedSource.draws x.1) (weights i b l x.1) x.2)
  have hb : a*(RawMixedSource.draws x.1:ℝ) < balanced i C b x.1 := by
    change a*(RawMixedSource.draws x.1:ℝ) ≤
      EntrySamplingLaw.sampled (weights i b l) (hs i b) RawMixedSource.draws x at hsum
    dsimp only [sampleDeficit] at hD
    linarith
  exact (le_div_iff₀ ha).mpr (by nlinarith)

theorem successful_reciprocal_error
    (ν : Measure RowRival) (i : Row) (g : LiteralExperiment.GuardData)
    {b A U ε c q lo γ w s a r κ : ℝ} (h : Inputs ν i g N C b A U ε c q lo γ w s)
    (ha : 0 < a) (_hr : 0 ≤ r)
    (x : EntryIIDCentral.Row (Ω := RowRival) N) (hx : x∈usable ν i g b A U ε)
    (hh : ∀ j,a ≤ hs i b x.1 j) (hD : 0 < sampleDeficit i C b g.multiplier x)
    (hW : balanced i C b x.1 ≤ r*(N:ℝ)) :
    let D := xi i/(q/(2*U))
    let z := max lo (b-D*r)
    |slope ν i C g b A U ε x/(N:ℝ)-κ| ≤
      |empirical (rawReciprocal b) N x.1-κ|+
      |empirical (rawReciprocal z) N x.1-κ|+
        (2/lo)*(r/a+1/(N:ℝ)) := by
  let D := xi i/(q/(2*U))
  let z := max lo (b-D*r)
  have hNr : (0:ℝ)< N := Nat.cast_pos.mpr h.rivals_pos
  have hq : 0 < q/(2*U) := div_pos h.strip_pos (by have := h.cap_pos; positivity)
  have hDP : 0 < D := div_pos (xi_pos i) hq
  have hb : 0 < b := h.lo_pos.trans_le (h.lower_price.trans h.bid_window.1)
  have hf := total_finite_geometry ν i g h 0 x
  have hDg := good_deficit_identity ν i g h 0 x hx
  have hdisp := (finite_displacement ν i g h 0 x).2
  rw [hDg,max_eq_left hD.le] at hdisp
  have hDle : sampleDeficit i C b g.multiplier x ≤ balanced i C b x.1 := by
    have hn := sample_nonneg i hb g.multiplier x
    dsimp only [sampleDeficit]
    linarith
  have hclose : b-price ν i C g b A U ε x ≤ D*r := by
    have hdn := (div_le_iff₀ hNr).mpr (hDle.trans hW)
    have hp := mul_le_mul_of_nonneg_left hdn hDP.le
    have hdisp' : b-price ν i C g b A U ε x ≤
        D * (sampleDeficit i C b g.multiplier x / (N : ℝ)) := by
      simpa only [D, mul_div_assoc] using hdisp
    exact hdisp'.trans hp
  have hz : z ≤ price ν i C g b A U ε x := max_le hf.1 (by dsimp[z] at *; linarith)
  have hlo : reciprocalAt i g b b x/(N:ℝ) ≤ slope ν i C g b A U ε x/(N:ℝ) :=
    div_le_div_of_nonneg_right hf.2.2.1 hNr.le
  have hhi : slope ν i C g b A U ε x/(N:ℝ) ≤ reciprocalAt i g b z x/(N:ℝ) := by
    exact div_le_div_of_nonneg_right
      (hf.2.2.2.1.trans (reciprocalSum_antitone _ _ (h.lo_pos.trans_le (le_max_left _ _)) hz)) hNr.le
  have he0 := focal_deletion_empirical_bound h.rivals_pos x.1 0 b lo κ h.lo_pos
    (h.lower_price.trans h.bid_window.1) (sampleSet i g b x)
    (EntryReciprocalLimit.removed_card_le (profile i g b) RawMixedSource.draws x)
  have he1 := focal_deletion_empirical_bound h.rivals_pos x.1 0 z lo κ h.lo_pos
    (le_max_left _ _) (sampleSet i g b x)
    (EntryReciprocalLimit.removed_card_le (profile i g b) RawMixedSource.draws x)
  have hd := successful_draw_bound i C b g.multiplier ha x hh hD
  have hdr : (RawMixedSource.draws x.1:ℝ)/(N:ℝ) ≤ r/a := by
    have hd' := (div_le_div_of_nonneg_right hd hNr.le).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hW ha.le) hNr.le)
    convert! hd' using 1; field_simp [ha.ne',hNr.ne']
  have herr := absolute_interval_bound hlo hhi (κ := κ)
  have hB := (add_le_add he0 he1)
  apply herr.trans (hB.trans ?_)
  have hR : 2*((RawMixedSource.draws x.1:ℝ)+1)/(lo*(N:ℝ)) ≤
      (2/lo)*(r/a+1/(N:ℝ)) := by
    have hadd : (RawMixedSource.draws x.1:ℝ)/(N:ℝ)+1/(N:ℝ) ≤ r/a+1/(N:ℝ) := by
      linarith
    have hh' := mul_le_mul_of_nonneg_left hadd
      (show 0 ≤ 2/lo by have := h.lo_pos; positivity)
    convert! hh' using 1; field_simp [h.lo_pos.ne',hNr.ne']
  change _ ≤ |empirical (rawReciprocal b) N x.1-κ|+
    |empirical (rawReciprocal z) N x.1-κ|+(2/lo)*(r/a+1/(N:ℝ))
  rw [mul_div_assoc] at hR
  linarith

lemma small_power_error {a b L : ℝ} (ha : |a| ≤ L) (hb : |b| ≤ L) (k : ℕ) (hk : k ≤ 2) :
    |a^k-b^k| ≤ (1+2*L)*|a-b| := by
  have hL : 0 ≤ L := (abs_nonneg a).trans ha
  interval_cases k
  · simp
    positivity
  · simp only [pow_one]
    nlinarith [abs_nonneg (a-b)]
  · rw [show a^2-b^2=(a-b)*(a+b) by ring,abs_mul]
    have hh := (abs_add_le a b).trans (add_le_add ha hb)
    have hp := mul_le_mul_of_nonneg_left hh (abs_nonneg (a-b))
    nlinarith [abs_nonneg (a-b)]

end FCAppendix.Affine.Uniform06.EntryModerateRootFinite
