import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import FCAppendix.Affine.Multiple07.SourceCertificate

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Set Filter Topology
open Hybrid.Native02

theorem native02_xi_literal : (1-eta)/2=xi := by norm_num [eta,xi]

theorem native02_unitMaximum_eq_sup (f : ℝ→ℝ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    Hybrid.Native02.unitMaximum f hf = sSup (f '' Icc (0:ℝ) 1) := by
  have hb : BddAbove (f '' Icc (0:ℝ) 1) :=
    ⟨Hybrid.Native02.unitMaximum f hf,by
      rintro y ⟨q,hq,rfl⟩
      exact Hybrid.Native02.le_unitMaximum f hf q hq⟩
  apply le_antisymm
  · exact le_csSup hb ⟨Hybrid.Native02.unitArgmax f hf,
      (Hybrid.Native02.unitArgmax_spec f hf).1,rfl⟩
  · refine csSup_le (s:=f '' Icc (0:ℝ) 1) ⟨f 0,⟨0,⟨le_rfl,zero_le_one⟩,rfl⟩⟩ ?_
    rintro y ⟨q,hq,rfl⟩
    exact Hybrid.Native02.le_unitMaximum f hf q hq

theorem native02_U1_source (r : Partition) (v : ℝ) :
    Hybrid.Native02.Menus.U1 (by norm_num [xi] : 0< xi)
      (by norm_num [xi] : xi<1) 0 (multiplier r) v = sourceOneMaximum r v := by
  rw [Hybrid.Native02.Menus.U1,native02_unitMaximum_eq_sup]
  rfl

theorem native02_U2_source (r : Partition) (v : ℝ) :
    Hybrid.Native02.Menus.U2 (by norm_num [xi] : 0< xi)
      (by norm_num [xi] : xi<1) 0 (multiplier r) v = sourceTwoMaximum r v := by
  rw [Hybrid.Native02.Menus.U2,native02_unitMaximum_eq_sup]
  rfl

theorem native02_M1_source (r : Partition) (v : ℝ) :
    Hybrid.Native02.Menus.M1 (by norm_num [xi] : 0< xi)
      (by norm_num [xi] : xi<1) (multiplier r) v = sourceOneMaximum r v := by
  rw [Hybrid.Native02.Menus.M1,native02_unitMaximum_eq_sup]
  have he : Hybrid.Native02.outsideOneAt xi v (multiplier r) =
      Hybrid.one xi 0 v (multiplier r) := by
    funext q
    simp only [Hybrid.one,Hybrid.Native02.outsideOneAt,
      zero_div,zero_add,sub_zero,one_mul]
  rw [he]
  rfl

theorem native02_source_argmax (r : Partition) (v : ℝ) (hv : activeLower r≤ v) :
    Hybrid.Native02.unitArgmax (Hybrid.two xi 0 v (multiplier r))
      (Hybrid.Native02.continuousOn_two_unit (by norm_num [xi])
        (by norm_num [xi]) 0 v (multiplier r)) = exposure r v :=
  (source_two_zero_argmax_iff r hv).mp
    (Hybrid.Native02.unitArgmax_spec _ _).2

theorem source_compact_exposure_integral (r : Partition) :
    (∫v : Hybrid.ActiveValue (activeLower r) (activeUpper r), exposure r v.1
      ∂sourceActiveValueLaw r) = activeFraction r := by
  have hm : Measurable (exposure r) := by unfold exposure; fun_prop
  have h := active_exposure_integral r
  rw [←sourceActiveValueLaw_map_val r,
    integral_map measurable_subtype_coe.aemeasurable hm.aestronglyMeasurable] at h
  exact h

def sourceNative02Input (r : Partition) : Hybrid.Native02.PrimitiveInput := by
  have hguards := literal_receipt_inward_guards r
  have hL := hguards.1
  have hLU := hguards.2.1
  have hκU := hguards.2.2.1
  have hh0U := hguards.2.2.2.2.1
  have hd := hguards.2.2.2.2.2.1
  have hLi := hguards.2.2.2.2.2.2.1
  have hUi := hguards.2.2.2.2.2.2.2.2.1
  have hUv := hguards.2.2.2.2.2.2.2.2.2.1
  have hUR := hguards.2.2.2.2.2.2.2.2.2.2.1
  refine
    { eta := eta
      s := 3/200
      a := activeMass r
      h := upperMass r
      rho := rho
      d := lowCeiling
      vlo := activeLower r
      vhi := activeUpper r
      L := bidLower r
      U := bidUpper r
      R := upperFloor r
      lam := multiplier r
      eta_pos := by norm_num [eta]
      eta_lt_one := by norm_num [eta]
      s_pos := by norm_num
      a_pos := by cases r <;> norm_num [activeMass]
      h_pos := by cases r <;> norm_num [upperMass]
      mass := by cases r <;> norm_num [activeMass,upperMass]
      d_nonneg := by norm_num [lowCeiling]
      L_pos := hL
      L_lt_U := hLU
      value_order := by cases r <;> norm_num [activeLower,activeUpper]
      z := 0
      z_nonneg := le_rfl
      z_lt_one := zero_lt_one
      rho_lower := by cases r <;> norm_num [upperMass,rho]
      rho_upper := by cases r <;> norm_num [activeMass,upperMass,rho]
      qbar_pos := by simpa only [sourceExposure_zero] using (activeFraction_mem r).1
      qbar_lt_one := by simpa only [sourceExposure_zero] using (activeFraction_mem r).2
      box_lower := by simpa only [native02_xi_literal,sourceExposure_zero,kappa,meanReceipt] using hκU
      box_upper := by simpa only [native02_xi_literal,sourceExposure_zero,meanReceipt] using hh0U
      low_receipt := by simpa only [native02_xi_literal,kappa] using hd
      value_surplus := hUv
      inward_lower := by
        simpa only [native02_xi_literal,sourceExposure_zero,sourceInwardScale_zero] using hLi
      inward_upper := by
        simpa only [native02_xi_literal,sourceExposure_zero,sourceInwardScale_zero] using hUi
      upper_floor := hUR
      low_rate_gap := source_joint_rate_gap r
      capacity := marketCapacity
      capacity_limit := marketCapacity_density
      lowValues := ⟨sourceLowValueLaw,inferInstance⟩
      activeValues := ⟨sourceActiveValueLaw r,inferInstance⟩
      upperValues := ⟨upperValueLaw r,inferInstance⟩
      lowValues_atomless := by change NullSingletonClass sourceLowValueLaw; infer_instance
      activeValues_atomless := by change NullSingletonClass (sourceActiveValueLaw r); infer_instance
      upperValues_atomless := by change NullSingletonClass (upperValueLaw r); infer_instance
      low_positive := sourceLowValueLaw_positive
      activeSupport := Icc (activeLower r) (activeUpper r)
      upperSupport := Icc (upperLower r) (2301/2000)
      active_compact := isCompact_Icc
      upper_compact := isCompact_Icc
      active_supported := ae_of_all _ (fun v => v.property)
      upper_supported := upperValueLaw_support r
      active_band := Subset.rfl
      upper_separated := by
        intro v hv
        exact (show activeUpper r< upperLower r by cases r <;>
          norm_num [activeUpper,upperLower]).trans_le hv.1
      lam_pos := (multiplier_bounds r).1
      maximizing_interior := ?_
      clearing := ?_
      active_menu_one := ?_
      active_menu_M1 := ?_
      active_menu_upper := ?_
      active_menu_M2 := by intro hz; exact False.elim ((lt_irrefl 0) hz)
      upper_menu_two := ?_
      upper_menu_one := ?_
      upper_menu_M1 := ?_
      upper_menu_M2 := fun _ hv => (literal_upper_maximum_guards r hv.1).2.2 }
  · intro v hv
    simpa only [native02_xi_literal,native02_source_argmax r v.1 hv.1] using
      exposure_bounds_of_lower r hv.1
  · simp only [native02_xi_literal,sourceExposure_zero]
    have he (v : Hybrid.ActiveValue (activeLower r) (activeUpper r)) :=
      native02_source_argmax r v.1 v.property.1
    simp_rw [he]
    exact source_compact_exposure_integral r
  · intro v hv
    simp only [native02_xi_literal,native02_U1_source]
    exact (literal_active_maximum_guards r hv).1.trans_eq (native02_U2_source r v).symm
  · intro v hv
    simp only [native02_xi_literal,native02_M1_source]
    exact (literal_active_maximum_guards r hv).1.trans_eq (native02_U2_source r v).symm
  · intro v hv
    simpa only [native02_xi_literal,native02_U2_source] using
      (literal_active_maximum_guards r hv).2.1
  · intro v hv
    simpa only [native02_xi_literal,native02_U2_source] using
      (literal_upper_maximum_guards r hv.1).1
  · intro v hv
    simpa only [native02_xi_literal,native02_U1_source] using
      (literal_upper_maximum_guards r hv.1).2.1
  · intro v hv
    simpa only [native02_xi_literal,native02_M1_source] using
      (literal_upper_maximum_guards r hv.1).2.1

@[simp] theorem sourceNative02Input_xi (r : Partition) : (sourceNative02Input r).xi=xi :=
  native02_xi_literal
@[simp] theorem sourceNative02Input_qbar (r : Partition) :
    (sourceNative02Input r).qbar=activeFraction r := sourceExposure_zero r
@[simp] theorem sourceNative02Input_capacity (r : Partition) (m : ℕ) :
    (sourceNative02Input r).capacity m=marketCapacity m := rfl
@[simp] theorem sourceNative02Input_eta (r : Partition) : (sourceNative02Input r).eta=eta := rfl
@[simp] theorem sourceNative02Input_d (r : Partition) : (sourceNative02Input r).d=lowCeiling := rfl
@[simp] theorem sourceNative02Input_vlo (r : Partition) : (sourceNative02Input r).vlo=activeLower r := rfl
@[simp] theorem sourceNative02Input_vhi (r : Partition) : (sourceNative02Input r).vhi=activeUpper r := rfl
@[simp] theorem sourceNative02Input_z (r : Partition) : (sourceNative02Input r).z=0 := rfl
@[simp] theorem sourceNative02Input_upperSupport (r : Partition) :
    (sourceNative02Input r).upperSupport=upperSet r := rfl

@[simp] theorem sourceNative02Input_originalValues (r : Partition) :
    (sourceNative02Input r).originalValues=sourceValueLaw := by
  change ENNReal.ofReal (3/200:ℝ) • sourceLowValueLaw.map Subtype.val +
    ENNReal.ofReal (activeMass r) • (sourceActiveValueLaw r).map Subtype.val +
    ENNReal.ofReal (upperMass r) • upperValueLaw r = sourceValueLaw
  rw [sourceLowValueLaw_map_val,sourceActiveValueLaw_map_val]
  exact (sourceValueLaw_decomposition r).symm

@[simp] theorem sourceNative02Input_q (r : Partition)
    (v : Hybrid.ActiveValue (activeLower r) (activeUpper r)) :
    (sourceNative02Input r).q v=exposure r v.1 := by
  change Hybrid.Native02.unitArgmax (Hybrid.two ((1-eta)/2) 0 v.1 (multiplier r)) _ = _
  simpa only [native02_xi_literal] using native02_source_argmax r v.1 v.property.1

end FCAppendix.Affine.Multiple07
