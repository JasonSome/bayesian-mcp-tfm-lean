import FCAppendix.Affine.Tail04.CoefficientOneEarly
import FCAppendix.Affine.Tail04.OriginalCompactAtomless
import FCAppendix.Affine.Hybrid.Native02.ScalarOptimizerUnique
import FCAppendix.Affine.Hybrid.Native02.PrimitiveImplementation

noncomputable section
namespace FCAppendix.Affine.Tail04.CoefficientOne.NativeSource
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 OriginalValues

variable {P : ValueParameters} (s : BoundedSource P) (hs : BoundedSourceGuards s)

lemma xi_half : s.scalar.xi < 1/2 := by
  dsimp [ScalarInput.xi]
  linarith [s.scalar.eta_pos]

lemma xi_lt_one : s.scalar.xi < 1 := (xi_half s).trans (by norm_num)

lemma exposure_eq : sourceExposure partialMass (activeMass P.theta) (99/200)
    s.scalar.ownerMass = 3/5 := s.scalar.source_qbar

lemma partial_pos (v : ℝ) (hv : v ∈ P.partialValues) : 0 < v := by
  exact (P.d0_pos.trans P.low_partial_gap).trans_le hv.1

include hs in
lemma argmax_eq (v : ℝ) (hv : v ∈ P.partialValues) :
    unitArgmax (two s.scalar.xi s.scalar.ownerMass v s.lam)
      (continuousOn_two_unit s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass v s.lam)
      = s.q v :=
  unitArgmax_two_eq_of_interior_maximizer s.scalar.xi_pos (xi_lt_one s)
    s.scalar.ownerMass_bounds.1 s.scalar.ownerMass_bounds.2
    (partial_pos v hv) hs.lam_pos (hs.q_interior v hv) (hs.q_maximizes v hv)

include hs in
lemma target_eq (v : ℝ) (hv : v ∈ P.partialValues) :
    Menus.U2 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v =
      two s.scalar.xi s.scalar.ownerMass v s.lam (s.q v) := by
  exact unitMaximum_eq_of_maximizer _ _ _
    ⟨(hs.q_interior v hv).1.le,(hs.q_interior v hv).2.le⟩ (hs.q_maximizes v hv)

include hs in
lemma active_one (v : ℝ) (hv : v ∈ P.partialValues) :
    Menus.U1 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v <
      Menus.U2 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v := by
  rw [target_eq s hs v hv]
  exact (hs.active_gap v hv).1 _ (unitArgmax_spec _ _).1

include hs in
lemma active_M1 (v : ℝ) (hv : v ∈ P.partialValues) :
    Menus.M1 s.scalar.xi_pos (xi_lt_one s) s.lam v <
      Menus.U2 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v := by
  rw [target_eq s hs v hv]
  have h := (hs.active_gap v hv).2.1
    (unitArgmax (outsideOneAt s.scalar.xi v s.lam)
      (continuousOn_M1_unit s.scalar.xi_pos (xi_lt_one s) v s.lam))
    (unitArgmax_spec _ _).1
  simpa only [Menus.M1,unitMaximum,one,outsideOneAt,zero_div,zero_add,sub_zero,one_mul]
    using h

include hs in
lemma upper_two (v : ℝ) (hv : v ∈ Icc (P.vA-P.w) s.upperMax) :
    Menus.U2 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v < v-s.scalar.R :=
  (hs.upper_gap v hv).1 _ (unitArgmax_spec _ _).1

include hs in
lemma upper_one (v : ℝ) (hv : v ∈ Icc (P.vA-P.w) s.upperMax) :
    Menus.U1 s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass s.lam v < v-s.scalar.R :=
  (hs.upper_gap v hv).2.1 _ (unitArgmax_spec _ _).1

include hs in
lemma upper_M1 (v : ℝ) (hv : v ∈ Icc (P.vA-P.w) s.upperMax) :
    Menus.M1 s.scalar.xi_pos (xi_lt_one s) s.lam v < v-s.scalar.R := by
  have h := (hs.upper_gap v hv).2.2.1
    (unitArgmax (outsideOneAt s.scalar.xi v s.lam)
      (continuousOn_M1_unit s.scalar.xi_pos (xi_lt_one s) v s.lam))
    (unitArgmax_spec _ _).1
  simpa only [Menus.M1,unitMaximum,one,outsideOneAt,zero_div,zero_add,sub_zero,one_mul]
    using h

lemma capacity_density :
    Tendsto (fun m : ℕ => (marketCapacity m : ℝ)/(m : ℝ)) atTop (nhds (99/200:ℝ)) := by
  exact (tendsto_nat_floor_mul_div_atTop (by norm_num : (0:ℝ) ≤ 99/200)).comp
    tendsto_natCast_atTop_atTop

def input : PrimitiveInput where
  eta := s.scalar.eta
  s := lowMass P.theta
  a := partialMass
  h := activeMass P.theta
  rho := 99/200
  d := P.d0
  vlo := 2-P.w
  vhi := 2+P.w
  L := s.L
  U := s.scalar.U
  R := s.scalar.R
  lam := s.lam
  eta_pos := s.scalar.eta_pos
  eta_lt_one := s.scalar.eta_lt_one
  s_pos := P.low_mass_pos
  a_pos := by norm_num [partialMass]
  h_pos := P.active_mass_pos
  mass := mass_sum P.theta
  d_nonneg := P.d0_pos.le
  L_pos := hs.L_pos
  L_lt_U := by
    have hH : 0 < s.h0 := by
      dsimp only [BoundedSource.h0]
      linarith [s.scalar.xi_pos,xi_half s]
    have hh := hs.receipt_order.2.1
    nlinarith
  value_order := by linarith [P.w_pos]
  z := s.scalar.ownerMass
  z_nonneg := s.scalar.ownerMass_bounds.1
  z_lt_one := s.scalar.ownerMass_bounds.2
  rho_lower := s.scalar.source_rank_interior.1
  rho_upper := s.scalar.source_rank_interior.2
  qbar_pos := by rw [exposure_eq s];norm_num
  qbar_lt_one := by rw [exposure_eq s];norm_num
  box_lower := by simpa only [exposure_eq s,ScalarInput.xi,BoundedSource.h0,BoundedSource.T0] using hs.receipt_order.1
  box_upper := by simpa only [exposure_eq s,ScalarInput.xi,BoundedSource.h0,BoundedSource.T0] using hs.receipt_order.2.2
  low_receipt := hs.low_receipt_gap
  value_surplus := hs.inward.2.2.2
  inward_lower := by simpa only [exposure_eq s,ScalarInput.xi,BoundedSource.h0,BoundedSource.T0] using hs.inward.1
  inward_upper := by simpa only [exposure_eq s,ScalarInput.xi,BoundedSource.h0,BoundedSource.T0] using hs.inward.2.2.1
  upper_floor := s.scalar.cap_below_floor
  low_rate_gap := hs.low_rate_gap
  capacity := marketCapacity
  capacity_limit := capacity_density
  lowValues := ⟨P.originalLowLaw,inferInstance⟩
  activeValues := ⟨P.originalPartialLaw,inferInstance⟩
  upperValues := s.FH0
  lowValues_atomless := by
    change NullSingletonClass P.originalLowLaw
    infer_instance
  activeValues_atomless := by
    change NullSingletonClass P.originalPartialLaw
    infer_instance
  upperValues_atomless := s.upper_value_atomless
  low_positive := P.originalLowLaw_positive
  activeSupport := P.partialValues
  upperSupport := Icc (P.vA-P.w) s.upperMax
  active_compact := isCompact_Icc
  upper_compact := isCompact_Icc
  active_supported := Eventually.of_forall (fun v => v.2)
  upper_supported := s.upper_value_support
  active_band := Subset.rfl
  upper_separated := fun v hv => P.partial_active_gap.trans_le hv.1
  lam_pos := hs.lam_pos
  maximizing_interior := by
    intro v hv
    convert! (argmax_eq s hs v hv).symm ▸ hs.q_interior v hv
  clearing := by
    have hq : (∫ v : ActiveValue (2-P.w) (2+P.w),
        unitArgmax (two s.scalar.xi s.scalar.ownerMass v.1 s.lam)
          (continuousOn_two_unit s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass v.1 s.lam)
        ∂P.originalPartialLaw) = ∫ v : ActiveValue (2-P.w) (2+P.w),s.q v.1
          ∂P.originalPartialLaw := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => argmax_eq s hs v v.2)
    change (∫ v : ActiveValue (2-P.w) (2+P.w),
      unitArgmax (two s.scalar.xi s.scalar.ownerMass v.1 s.lam)
        (continuousOn_two_unit s.scalar.xi_pos (xi_lt_one s) s.scalar.ownerMass v.1 s.lam)
      ∂P.originalPartialLaw) = sourceExposure partialMass (activeMass P.theta) (99/200) s.scalar.ownerMass
    rw [hq]
    rw [← integral_map measurable_subtype_coe.aemeasurable s.q_measurable.aestronglyMeasurable]
    exact hs.q_mean.trans (exposure_eq s).symm
  active_menu_one := active_one s hs
  active_menu_M1 := active_M1 s hs
  active_menu_upper := by
    intro v hv
    convert! ((hs.active_gap v hv).2.2.1).trans_eq (target_eq s hs v hv).symm
  active_menu_M2 := by
    intro hz v hv
    convert! ((hs.active_gap v hv).2.2.2 hz).trans_eq (target_eq s hs v hv).symm
  upper_menu_two := upper_two s hs
  upper_menu_one := upper_one s hs
  upper_menu_M1 := upper_M1 s hs
  upper_menu_M2 := fun v hv => (hs.upper_gap v hv).2.2.2

lemma input_q (v : (input s hs).Value) : (input s hs).q v = s.q v.1 := by
  convert! argmax_eq s hs v.1 v.2

lemma input_original_values : (input s hs).originalValues = s.valueMeasure := rfl

lemma input_active_count (v : (input s hs).Value) :
    (input s hs).activeCount v = s.partialLimit hs v.1 v.2 := by
  unfold PrimitiveInput.activeCount activeLimitLaw BoundedSource.partialLimit
  congr 2
  exact input_q s hs v

theorem exists_native_implementation : Nonempty (NativeImplementation (input s hs)) :=
  native_affine_implementation_from_primitives (input s hs)

end FCAppendix.Affine.Tail04.CoefficientOne.NativeSource
