import FCAppendix.Affine.Hybrid.Native02.NullTypes
import FCAppendix.Affine.Hybrid.UpperLaw

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Game Bayes

def lowNullAction (v : ℝ) : JointAction 2 :=
  ⟨max v 0/2,div_nonneg (le_max_right _ _) (by norm_num),2,le_rfl⟩

theorem measurable_lowNullAction : Measurable lowNullAction := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (((measurable_id.max measurable_const).div_const 2).prodMk measurable_const).comap_le

def extendActiveAction {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (beta : ActiveValue vlo vhi→ ActiveBaseBid L U) (v : ℝ) : JointAction 2 :=
  activeBroadcast hL (beta (Set.projIcc vlo vhi hvv v))

theorem measurable_extendActiveAction {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (beta : ActiveValue vlo vhi→ ActiveBaseBid L U) (hb : Measurable beta) :
    Measurable (extendActiveAction hvv hL beta) :=
  (measurable_activeBroadcast hL).comp
    (hb.comp (continuous_projIcc (h:=hvv)).measurable)

theorem extendActiveAction_at_value {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (beta : ActiveValue vlo vhi→ ActiveBaseBid L U) (v : ActiveValue vlo vhi) :
    extendActiveAction hvv hL beta v.1=activeBroadcast hL (beta v) := by
  unfold extendActiveAction
  rw [Set.projIcc_val]

def sourceNullAction {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (beta : ActiveValue vlo vhi→ ActiveBaseBid L U)
    (upperBid : ℝ→ℝ) (v : ℝ) : JointAction 2 :=
  if v≤ d then lowNullAction v
  else if v≤ vhi then extendActiveAction hvv hL beta v
  else upperAction upperBid (max v t)

theorem measurable_sourceNullAction {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (beta : ActiveValue vlo vhi→ ActiveBaseBid L U) (hb : Measurable beta)
    (upperBid : ℝ→ℝ) (hu : Measurable upperBid) :
    Measurable (sourceNullAction hvv hL d t beta upperBid) := by
  exact Measurable.ite measurableSet_Iic measurable_lowNullAction
    (Measurable.ite measurableSet_Iic (measurable_extendActiveAction hvv hL beta hb)
      ((measurable_upperAction upperBid hu).comp (measurable_id.max measurable_const)))

theorem sourceNullAction_low {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (beta : ActiveValue vlo vhi→ ActiveBaseBid L U)
    (upperBid : ℝ→ℝ) (v : ℝ) (hv : 0< v) (hvd : v≤ d) :
    (sourceNullAction hvv hL d t beta upperBid v).bid=v/2 ∧
    (sourceNullAction hvv hL d t beta upperBid v).bid≤ d ∧
    (sourceNullAction hvv hL d t beta upperBid v).routeCount=2 := by
  simp only [sourceNullAction,if_pos hvd,lowNullAction,max_eq_left hv.le]
  exact ⟨trivial,by linarith,trivial⟩

theorem sourceNullAction_active {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (hdl : d< vlo) (_hht : vhi< t)
    (beta : ActiveValue vlo vhi→ ActiveBaseBid L U) (upperBid : ℝ→ℝ)
    (v : ActiveValue vlo vhi) :
    sourceNullAction hvv hL d t beta upperBid v.1=activeBroadcast hL (beta v) := by
  have hvd : ¬v.1≤ d := not_le.mpr (hdl.trans_le v.property.1)
  rw [sourceNullAction,if_neg hvd,if_pos v.property.2,extendActiveAction_at_value]

theorem sourceNullAction_above_active {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (hdv : d< vlo) (beta : ActiveValue vlo vhi→ ActiveBaseBid L U)
    (upperBid : ℝ→ℝ) (v : ℝ) (hv : vhi< v) :
    sourceNullAction hvv hL d t beta upperBid v=upperAction upperBid (max v t) := by
  simp only [sourceNullAction,if_neg (not_le.mpr ((hdv.trans_le hvv).trans hv)),
    if_neg (not_le.mpr hv)]

theorem sourceNullAction_upper {vlo vhi L U : ℝ} (hvv : vlo≤ vhi) (hL : 0≤ L)
    (d t : ℝ) (hdt : d< t) (hvt : vhi< t) (beta : ActiveValue vlo vhi→ ActiveBaseBid L U)
    (upperBid : ℝ→ℝ) (v : ℝ) (hv : t≤ v) :
    sourceNullAction hvv hL d t beta upperBid v=upperAction upperBid v := by
  simp only [sourceNullAction,if_neg (not_le.mpr (hdt.trans_le hv)),
    if_neg (not_le.mpr (hvt.trans_le hv)),max_eq_left hv]

end FCAppendix.Affine.Hybrid.Native02
