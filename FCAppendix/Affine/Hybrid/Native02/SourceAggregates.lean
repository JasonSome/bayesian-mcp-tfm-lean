import FCAppendix.Affine.Hybrid.Native02.SourceCountVersions

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes

namespace PrimitiveInput
variable (p : PrimitiveInput)

instance originalValues_isProbability : IsProbabilityMeasure p.originalValues := by
  constructor
  change (originalValueLaw p.s p.a p.h
    ((p.lowValues : Measure p.Low).map Subtype.val)
    ((p.activeValues : Measure p.Value).map Subtype.val) p.upperValues) univ=1
  simp only [originalValueLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul,
    Measure.map_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ,
    measure_univ,mul_one]
  rw [←ENNReal.ofReal_add p.s_pos.le p.a_pos.le,
    ←ENNReal.ofReal_add (add_nonneg p.s_pos.le p.a_pos.le) p.h_pos.le,p.mass]
  norm_num

def activeCount (v : p.Value) : CountLaw 2 := activeLimitLaw p.z (p.q v)
  p.z_nonneg p.z_lt_one.le (p.q_mem v).1 (p.q_mem v).2

def limitCount (v : ℝ) : CountLaw 2 :=
  if v≤ p.d then FiniteLaw.dirac (0:Fin 3)
  else if v∈ Icc p.vlo p.vhi then
    p.activeCount (Set.projIcc p.vlo p.vhi p.value_order v)
  else FiniteLaw.dirac (1:Fin 3)

theorem limitCount_low (v : ℝ) (hv : v∈ Icc (0:ℝ) p.d) :
    p.limitCount v=FiniteLaw.dirac (0:Fin 3) := by
  simp only [limitCount,if_pos hv.2]

theorem limitCount_active (v : p.Value) : p.limitCount v.1=p.activeCount v := by
  have hdl : p.d< p.vlo := (p.d_lt_L.trans p.L_lt_U).trans p.value_surplus
  simp only [limitCount,if_neg (not_le.mpr (hdl.trans_le v.property.1)),
    if_pos v.property,Set.projIcc_val]

theorem limitCount_upper (v : ℝ) (hv : v∈ p.upperSupport) :
    p.limitCount v=FiniteLaw.dirac (1:Fin 3) := by
  have hdl : p.d< p.vlo := (p.d_lt_L.trans p.L_lt_U).trans p.value_surplus
  have hu:=p.upper_separated v hv
  have hdv : p.d< v := (hdl.trans_le p.value_order).trans hu
  have hb : v∉Icc p.vlo p.vhi := fun h=>(not_lt.mpr h.2) hu
  simp only [limitCount,if_neg (not_le.mpr hdv),if_neg hb]

theorem measurable_limitCount_mass (A : FrozenActiveFamily p) (r : Fin 3) :
    Measurable (fun v=>(p.limitCount v).mass r) := by
  have hq : Measurable (fun v : ℝ=> p.q (Set.projIcc p.vlo p.vhi p.value_order v)) :=
    A.response_measurable.comp (continuous_projIcc (h:=p.value_order)).measurable
  have hact : Measurable (fun v : ℝ=>
      (p.activeCount (Set.projIcc p.vlo p.vhi p.value_order v)).mass r) := by
    simp only [activeCount,activeLimitLaw_mass]
    exact (continuous_activeMass p.z r).measurable.comp hq
  classical
  have hm : Measurable (fun v : ℝ => if v ≤ p.d then (FiniteLaw.dirac (0:Fin 3)).mass r
      else if v ∈ Icc p.vlo p.vhi then
        (p.activeCount (Set.projIcc p.vlo p.vhi p.value_order v)).mass r
      else (FiniteLaw.dirac (1:Fin 3)).mass r) :=
    Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Icc hact measurable_const)
  unfold limitCount
  convert! hm using 1
  funext v
  by_cases hd : v ≤ p.d
  · simp only [if_pos hd]
  · by_cases hv : v ∈ Icc p.vlo p.vhi
    · simp only [if_neg hd, if_pos hv]
    · simp only [if_neg hd, if_neg hv]

theorem original_values_band_support : ∀ᵐv ∂p.originalValues,
    v∈ Icc (0:ℝ) p.d ∨ v∈ Icc p.vlo p.vhi ∨ v∈ p.upperSupport := by
  change ∀ᵐv ∂originalValueLaw p.s p.a p.h
    ((p.lowValues : Measure p.Low).map Subtype.val)
    ((p.activeValues : Measure p.Value).map Subtype.val) p.upperValues, _
  rw [originalValueLaw,ae_add_measure_iff,ae_add_measure_iff]
  constructor
  · constructor
    · apply Measure.ae_smul_measure
      have hl : ∀ᵐv ∂(p.lowValues : Measure p.Low).map Subtype.val,v∈ Icc (0:ℝ) p.d :=
        (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
          (ae_of_all _ (fun v=> v.property))
      exact hl.mono (fun _ hv=> Or.inl hv)
    · apply Measure.ae_smul_measure
      have ha : ∀ᵐv ∂(p.activeValues : Measure p.Value).map Subtype.val,v∈ Icc p.vlo p.vhi :=
        (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
          (ae_of_all _ (fun v=> v.property))
      exact ha.mono (fun _ hv=> Or.inr (Or.inl hv))
  · exact Measure.ae_smul_measure (p.upper_supported.mono (fun _ hv=> Or.inr (Or.inr hv))) _

theorem original_integral_limitCount (A : FrozenActiveFamily p) (f : Fin 3→ℝ) :
    (∫v,(p.limitCount v).expect f ∂p.originalValues)=
      p.s*f 0+p.a*(∫v : p.Value,(p.activeCount v).expect f ∂(p.activeValues : Measure p.Value))+
        p.h*f 1 := by
  let FL:=(p.lowValues : Measure p.Low).map Subtype.val
  let FA:=(p.activeValues : Measure p.Value).map Subtype.val
  let FH:=(p.upperValues : Measure ℝ)
  letI : IsProbabilityMeasure FL := Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  letI : IsProbabilityMeasure FA := Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  let g:=fun v=>(p.limitCount v).expect f
  have hg : Measurable g := FiniteLaw.measurable_expect p.limitCount (p.measurable_limitCount_mass A) f
  have hi (mu : Measure ℝ) [IsFiniteMeasure mu] : Integrable g mu :=
    FiniteLaw.integrable_expect mu p.limitCount (p.measurable_limitCount_mass A) f
  have hL : (∫v,g v ∂FL)=f 0 := by
    rw [show FL=(p.lowValues : Measure p.Low).map Subtype.val from rfl,
      integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
    have he : (fun v : p.Low=> g v.1)=fun _=> f 0 := by
      funext v
      change (p.limitCount v.1).expect f=f 0
      rw [p.limitCount_low v.1 v.property,FiniteLaw.expect_dirac]
    rw [he,integral_const,probReal_univ,one_smul]
  have hA : (∫v,g v ∂FA)=∫v : p.Value,(p.activeCount v).expect f ∂(p.activeValues : Measure p.Value) := by
    rw [show FA=(p.activeValues : Measure p.Value).map Subtype.val from rfl,
      integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
    apply integral_congr_ae
    exact ae_of_all _ (fun v=> by dsimp only [g];rw [p.limitCount_active])
  have hH : (∫v,g v ∂FH)=f 1 := by
    have he : g=ᵐ[FH]fun _=> f 1 := p.upper_supported.mono
      (fun v hv=> by dsimp only [g];rw [p.limitCount_upper v hv,FiniteLaw.expect_dirac])
    rw [integral_congr_ae he,integral_const,probReal_univ,one_smul]
  change (∫v,g v ∂(ENNReal.ofReal p.s • FL+ENNReal.ofReal p.a • FA+
    ENNReal.ofReal p.h • FH))=_
  rw [integral_add_measure
    ((hi FL).smul_measure ENNReal.ofReal_ne_top |>.add_measure
      ((hi FA).smul_measure ENNReal.ofReal_ne_top))
    ((hi FH).smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure ((hi FL).smul_measure ENNReal.ofReal_ne_top)
      ((hi FA).smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,integral_smul_measure,
    ENNReal.toReal_ofReal p.s_pos.le,ENNReal.toReal_ofReal p.a_pos.le,
    ENNReal.toReal_ofReal p.h_pos.le,hL,hA,hH]
  rfl

def coverage : ℝ := p.h+p.a*(∫v : p.Value,(p.activeCount v).success ∂(p.activeValues : Measure p.Value))
def duplicates : ℝ := p.a*(∫v : p.Value,(p.activeCount v).duplicates ∂(p.activeValues : Measure p.Value))

theorem coverage_positive : 0< p.coverage := by
  have hnon : 0≤∫v : p.Value,(p.activeCount v).success ∂(p.activeValues : Measure p.Value) :=
    integral_nonneg (fun v=>(p.activeCount v).success_nonneg)
  unfold coverage
  exact add_pos_of_pos_of_nonneg p.h_pos (mul_nonneg p.a_pos.le hnon)

theorem integral_limit_success (A : FrozenActiveFamily p) :
    (∫v,(p.limitCount v).success ∂p.originalValues)=p.coverage := by
  simpa only [CountLaw.success,successIndicator,Nat.cast_zero,Nat.cast_one,
    Fin.val_zero,Fin.val_one,ite_true,one_ne_zero,ite_false,mul_zero,mul_one,zero_add,
    coverage,add_comm] using p.original_integral_limitCount A (fun r=> successIndicator r.val)

theorem integral_limit_duplicates (A : FrozenActiveFamily p) :
    (∫v,(p.limitCount v).duplicates ∂p.originalValues)=p.duplicates := by
  have h:=p.original_integral_limitCount A (fun r=>(r.val:ℝ)-successIndicator r.val)
  unfold duplicates
  simp_rw [CountLaw.duplicates_eq_expect]
  simpa only [successIndicator,Fin.val_zero,Fin.val_one,
    Nat.cast_zero,Nat.cast_one,ite_true,one_ne_zero,ite_false,sub_zero,sub_self,mul_zero,
    zero_add,add_zero] using h

theorem integrable_q (A : FrozenActiveFamily p) : Integrable p.q (p.activeValues : Measure p.Value) :=
  Integrable.of_bound A.response_measurable.aestronglyMeasurable 1
    (ae_of_all _ (fun v=> by rw [Real.norm_eq_abs,abs_of_nonneg (p.q_mem v).1];exact (p.q_mem v).2))

theorem active_load_integral (A : FrozenActiveFamily p) :
    (∫v : p.Value,(p.activeCount v).load ∂(p.activeValues : Measure p.Value))=
      p.z+2*(1-p.z)*p.qbar := by
  have hclear : (∫ v : p.Value, p.q v ∂(p.activeValues : Measure p.Value)) = p.qbar := p.clearing
  simp only [activeCount,activeLimitLaw_load]
  rw [integral_add (integrable_const _) ((p.integrable_q A).const_mul _),
    integral_const,probReal_univ,one_smul,integral_const_mul,hclear]

theorem source_load_identity : p.h+p.a*(p.z+2*(1-p.z)*p.qbar)=2*p.rho := by
  unfold qbar sourceExposure
  field_simp [p.a_pos.ne',(sub_pos.mpr p.z_lt_one).ne']
  ring

theorem integral_limit_load (A : FrozenActiveFamily p) :
    (∫v,(p.limitCount v).load ∂p.originalValues)=2*p.rho := by
  have h:=p.original_integral_limitCount A (fun r=>(r.val:ℝ))
  simp only [Fin.val_zero,Fin.val_one,Nat.cast_zero,Nat.cast_one,
    mul_zero,mul_one,zero_add] at h
  change (∫ v, (p.limitCount v).load ∂p.originalValues) =
    p.a*(∫ v : p.Value, (p.activeCount v).load ∂(p.activeValues : Measure p.Value))+p.h at h
  rw [p.active_load_integral A] at h
  rw [h,add_comm]
  exact p.source_load_identity

theorem duplicates_formula (_A : FrozenActiveFamily p) :
    p.duplicates=p.a*(1-p.z)*(∫v : p.Value,(p.q v)^2 ∂(p.activeValues : Measure p.Value)) := by
  unfold duplicates
  simp only [activeCount,activeLimitLaw_duplicates,integral_const_mul]
  ring

theorem coverage_formula (A : FrozenActiveFamily p) :
    p.coverage=p.h+p.a*(p.z+(1-p.z)*(2*p.qbar-
      ∫v : p.Value,(p.q v)^2 ∂(p.activeValues : Measure p.Value))) := by
  have hclear : (∫ v : p.Value, p.q v ∂(p.activeValues : Measure p.Value)) = p.qbar := p.clearing
  have hq2 : Integrable (fun v : p.Value => (p.q v)^2) (p.activeValues : Measure p.Value) :=
    Integrable.of_bound (A.response_measurable.pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ (fun v => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        nlinarith [(p.q_mem v).1,(p.q_mem v).2,
          mul_nonneg (p.q_mem v).1 (sub_nonneg.mpr (p.q_mem v).2)]))
  have hi : Integrable (fun v : p.Value => 2*p.q v-(p.q v)^2) (p.activeValues : Measure p.Value) :=
    ((p.integrable_q A).const_mul 2).sub hq2
  unfold coverage
  simp only [activeCount,activeLimitLaw_success]
  have hint := integral_add (integrable_const p.z) (hi.const_mul (1-p.z))
  rw [hint, integral_const, probReal_univ, one_smul, integral_const_mul]
  have hsub := integral_sub ((p.integrable_q A).const_mul 2) hq2
  rw [hsub, integral_const_mul, hclear]

end PrimitiveInput

theorem actual_source_aggregate_limits (p : PrimitiveInput) (A : FrozenActiveFamily p)
    {M C : ℕ→ℕ} (G : ∀ k,FiniteGame (M k) 2 (C k) unitInterval)
    (hM : ∀ k,0< M k) (hF : ∀ k,(G k).F=p.originalValues)
    (t : ℝ) (hupperSupport : ∀ v∈ p.upperSupport,t≤ v)
    (hlow : ∀ v∈ Icc (0:ℝ) p.d,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (0:Fin 3)).mass r)))
    (hactive : ∀ v : p.Value,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v.1).mass r) atTop (𝓝 ((p.activeCount v).mass r)))
    (hupper : ∀ v,t≤ v→∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r)
        atTop (𝓝 ((FiniteLaw.dirac (1:Fin 3)).mass r))) :
    Tendsto (fun k=> finiteCoverage (G k)) atTop (𝓝 p.coverage) ∧
    Tendsto (fun k=> finiteLoad (G k)) atTop (𝓝 (2*p.rho)) ∧
    Tendsto (fun k=> finiteLoad (G k)-finiteCoverage (G k)) atTop (𝓝 p.duplicates) ∧
    Tendsto (fun k=> finiteLoad (G k)/finiteCoverage (G k)) atTop (𝓝 (2*p.rho/p.coverage)) := by
  have hc : ∀ᵐv ∂p.originalValues,∀ i : ∀ k,Fin (M k),∀ r,
      Tendsto (fun k=>(typeOutcome (G k) (i k) v).mass r) atTop (𝓝 ((p.limitCount v).mass r)) := by
    filter_upwards [p.original_values_band_support] with v hv
    rcases hv with hlo|ha|hhi
    · simpa only [p.limitCount_low v hlo] using hlow v hlo
    · simpa only [p.limitCount_active (⟨v,ha⟩ : p.Value)] using hactive ⟨v,ha⟩
    · simpa only [p.limitCount_upper v hhi] using hupper v (hupperSupport v hhi)
  obtain ⟨hQ,hload,hD⟩:=actual_aggregate_limits G hM p.originalValues hF p.limitCount hc
  rw [p.integral_limit_success A] at hQ
  rw [p.integral_limit_load A] at hload
  rw [p.integral_limit_duplicates A] at hD
  exact ⟨hQ,hload,hD,actual_multiplicity_limit G p.coverage_positive hload hQ⟩

end FCAppendix.Affine.Hybrid.Native02
