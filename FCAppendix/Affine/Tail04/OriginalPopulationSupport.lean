import FCAppendix.Affine.Tail04.OriginalPopulation
import FCAppendix.Affine.Tail04.SourceRoleMasses

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPopulation
open MeasureTheory ProbabilityTheory Set Filter Game Bayes
open Existence.Distributional OriginalValues Hybrid

def sourceBands (P : ValueParameters) (E : Observable.Regions) (t : ℝ)
    (x : ℝ × JointAction 2) : Prop :=
  (x.1 ∈ Icc (0:ℝ) P.d0 ∧ x.2.bid ≤ E.d ∧ x.2.routeCount=2) ∨
  (x.1 ∈ P.partialValues ∧ x.2.bid ∈ Icc E.R E.Rp ∧ x.2.routeCount=1) ∨
  (x.1 ∈ P.movingActiveValues t ∧ x.2.bid ∈ Icc (1:ℝ) E.U ∧ x.2.routeCount=2) ∨
  (t < x.1 ∧ E.H ≤ x.2.bid ∧ x.2.routeCount=1)

theorem measurableSet_sourceBands (P : ValueParameters) (E : Observable.Regions) (t : ℝ) :
    MeasurableSet {x | sourceBands P E t x} := by
  let vb : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  let vk : Measurable (fun x : ℝ × JointAction 2 => x.2.routeCount) :=
    (measurable_routeCount 2).comp measurable_snd
  simp only [sourceBands, setOf_or, setOf_and]
  exact ((measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_le vb measurable_const).inter (measurableSet_eq_fun vk measurable_const))).union
    (((measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage vb).inter (measurableSet_eq_fun vk measurable_const))).union
    (((measurableSet_Icc.preimage measurable_fst).inter
      ((measurableSet_Icc.preimage vb).inter (measurableSet_eq_fun vk measurable_const))).union
    ((measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_le measurable_const vb).inter (measurableSet_eq_fun vk measurable_const)))))

theorem fourJoint_ae (s h a z : ℝ)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (Q : ℝ × JointAction 2 → Prop)
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), Q x)
    (hP : ∀ᵐ x ∂(PP : Measure (ℝ × JointAction 2)), Q x)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), Q x)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), Q x) :
    ∀ᵐ x ∂fourJoint s h a z PL PP PA PH, Q x :=
  ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hL _, Measure.ae_smul_measure hP _⟩,
      Measure.ae_smul_measure hA _⟩, Measure.ae_smul_measure hH _⟩

variable (P : ValueParameters) (E : Observable.Regions) (hd : E.d=P.d0)
  (t : ℝ) (ht : P.M ≤ t)

local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v, t < v → E.H ≤ upperBid v)

local notation "hR" => E.d_nonneg.trans E.d_lt_R.le
local notation "J" => originalJoint P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid

include hd hfloor in
theorem originalJoint_sourceBands :
    ∀ᵐ x ∂(J : Measure (ℝ × JointAction 2)), sourceBands P E t x := by
  apply fourJoint_ae
  · apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurableSet_sourceBands P E t)).mpr
    exact Eventually.of_forall (fun x => Or.inl
      ⟨x.1.2, by change (x.2:ℝ) ≤ E.d;rw [hd];exact x.2.2.2, rfl⟩)
  · exact (bandJoint_support hR 1 (by norm_num) P.originalPartialLaw πP).mono
      (fun _ hx => Or.inr (Or.inl hx))
  · exact (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
      (P.originalMovingActiveLaw t ht) πA).mono
      (fun _ hx => Or.inr (Or.inr (Or.inl hx)))
  · apply (ae_map_iff (measurable_id.prodMk
      (measurable_upperAction upperBid hupperBid)).aemeasurable
      (measurableSet_sourceBands P E t)).mpr
    filter_upwards [P.originalMovingUpperLaw_support t] with v hv
    exact Or.inr (Or.inr (Or.inr
      ⟨hv, (hfloor v hv).trans (le_max_left _ _), rfl⟩))

include ht in

theorem sourceBands_correspondence (x : ℝ × JointAction 2)
    (hx : sourceBands P E t x) :
    (x.2.bid ≤ E.d ↔ x.1 ≤ P.d0) ∧
      (x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t) ∧
      (E.H ≤ x.2.bid ↔ t < x.1) := by
  have hda : P.d0 < P.vA-P.w := by
    linarith [P.low_partial_gap, P.partial_active_gap, P.w_pos]
  have hdt : P.d0 < t := by linarith [P.active_tail_gap, P.w_pos]
  have hpt : 2+P.w < t := by
    linarith [P.partial_active_gap, P.active_tail_gap, P.w_pos]
  rcases hx with hx | hx | hx | hx
  · have hnB : x.2.bid ∉ E.privateBids :=
      fun hh => (not_lt.mpr hx.2.1) (E.private_above_low hh)
    have hnP : x.1 ∉ P.partialValues := by intro hh; linarith [hx.1.2, hh.1, P.low_partial_gap]
    have hnT : ¬t < x.1 := by linarith [hx.1.2]
    have hnH : ¬E.H ≤ x.2.bid := by linarith [hx.2.1, E.d_lt_H]
    exact ⟨iff_of_true hx.2.1 hx.1.2,
      iff_of_false hnB (by simpa only [privateValues, movingUpperValues, mem_union,
        mem_Ioi, hnP, hnT, or_self] using (not_false : ¬False)),
      iff_of_false hnH hnT⟩
  · have hB : x.2.bid ∈ E.privateBids := Or.inl hx.2.1
    have hP : x.1 ∈ P.privateValues t := Or.inl hx.1
    have hnD : ¬x.2.bid ≤ E.d := not_le.mpr (E.private_above_low hB)
    have hnV : ¬x.1 ≤ P.d0 := by linarith [hx.1.1, P.low_partial_gap]
    have hnH : ¬E.H ≤ x.2.bid := by linarith [hx.2.1.2, E.Rp_lt_H]
    have hnT : ¬t < x.1 := by linarith [hx.1.2]
    exact ⟨iff_of_false hnD hnV, iff_of_true hB hP, iff_of_false hnH hnT⟩
  · have hnD : ¬x.2.bid ≤ E.d := by linarith [hx.2.1.1, E.d_lt_one]
    have hnV : ¬x.1 ≤ P.d0 := by linarith [hx.1.1]
    have hnB : x.2.bid ∉ E.privateBids := by
      rintro (hh | hh)
      · linarith [hh.2, hx.2.1.1, E.Rp_lt_one]
      · change E.H ≤ x.2.bid at hh
        linarith [hx.2.1.2, E.U_lt_H]
    have hnP : x.1 ∉ P.partialValues := by intro hh; linarith [hx.1.1, hh.2, P.partial_active_gap]
    have hnT : ¬t < x.1 := not_lt.mpr hx.1.2
    have hnH : ¬E.H ≤ x.2.bid := by linarith [hx.2.1.2, E.U_lt_H]
    exact ⟨iff_of_false hnD hnV,
      iff_of_false hnB (by simpa only [privateValues, movingUpperValues, mem_union,
        mem_Ioi, hnP, hnT, or_self] using (not_false : ¬False)),
      iff_of_false hnH hnT⟩
  · have hB : x.2.bid ∈ E.privateBids := Or.inr hx.2.1
    have hP : x.1 ∈ P.privateValues t := Or.inr hx.1
    have hnD : ¬x.2.bid ≤ E.d := not_le.mpr (E.private_above_low hB)
    have hnV : ¬x.1 ≤ P.d0 := by linarith [hx.1]
    exact ⟨iff_of_false hnD hnV, iff_of_true hB hP, iff_of_true hx.2.1 hx.1⟩

include hd hfloor in
theorem originalJoint_role_correspondence :
    ∀ᵐ x ∂(J : Measure (ℝ × JointAction 2)),
      (x.2.bid ≤ E.d ↔ x.1 ≤ P.d0) ∧
      (x.2.bid ∈ E.privateBids ↔ x.1 ∈ P.privateValues t) ∧
      (E.H ≤ x.2.bid ↔ t < x.1) :=
  (originalJoint_sourceBands P E hd t ht πL πP πA upperBid hupperBid hfloor).mono
    (fun x hx => sourceBands_correspondence P E t ht x hx)

end FCAppendix.Affine.Tail04.OriginalPopulation
