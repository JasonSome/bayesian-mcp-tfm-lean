import FCAppendix.Affine.Tail04.FavoredLocalCountGain

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set Filter Topology
open scoped BigOperators
variable {ι Ω X : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
  [MeasurableSpace X]

theorem measurable_independentFlagLaw_mass_of (p : X → ι → ℝ)
    (hp0 : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x i, p x i ≤ 1)
    (hp : ∀ i, Measurable (fun x => p x i)) (flags : ι → Bool) :
    Measurable (fun x => (independentFlagLaw (p x) (hp0 x) (hp1 x)).mass flags) := by
  change Measurable (fun x => ∏ i, if flags i then p x i else 1-p x i)
  apply Finset.measurable_prod
  intro i _
  cases h : flags i
  · simp only [Bool.false_eq_true,ite_false]
    exact measurable_const.sub (hp i)
  · simpa only [h,ite_true] using hp i

theorem measurable_selectionPromotionGap
    (left right : X → FiniteLaw (Finset ι))
    (hl : ∀ S, Measurable (fun x => (left x).mass S))
    (hr : ∀ S, Measurable (fun x => (right x).mass S))
    (i : ι) (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Measurable (fun x => selectionPromotionGap (left x) (right x) i
      v bi eta heta0 heta1) := by
  classical
  have hp : Measurable (fun x => (left x).prob (fun S => i ∈ S)) := by
    simp only [FiniteLaw.prob_eq_expect,FiniteLaw.expect]
    exact Finset.measurable_sum _ fun S _ => (hl S).mul_const _
  have hq : Measurable (fun x => (right x).prob (fun S => i ∈ S)) := by
    simp only [FiniteLaw.prob_eq_expect,FiniteLaw.expect]
    exact Finset.measurable_sum _ fun S _ => (hr S).mul_const _
  simp only [selectionPromotionGap_eq,twoMixedFavoredGain]
  exact ((measurable_const.mul (measurable_const.sub hp)).mul
    (measurable_const.sub hq)).add ((measurable_const.mul hp).mul hq)

theorem measurable_localPromotionGain
    (mu : X → FiniteLaw Ω) (hmu : ∀ omega, Measurable (fun x => (mu x).mass omega))
    (left right : X → Ω → FiniteLaw (Finset ι))
    (hl : ∀ omega S, Measurable (fun x => (left x omega).mass S))
    (hr : ∀ omega S, Measurable (fun x => (right x omega).mass S))
    (chi : X → Ω → ℝ) (hchi : ∀ omega, Measurable (fun x => chi x omega))
    (i : ι) (v bi eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Measurable (fun x => localPromotionGain (mu x) (left x) (right x) i (chi x)
      v bi eta heta0 heta1) := by
  unfold localPromotionGain FiniteLaw.expect
  exact Finset.measurable_sum _ fun omega _ =>
    (hmu omega).mul ((hchi omega).mul (measurable_selectionPromotionGap
      (fun x => left x omega) (fun x => right x omega) (hl omega) (hr omega)
      i v bi eta heta0 heta1))

theorem integrable_localPromotionGain (mu0 : Measure X) [IsFiniteMeasure mu0]
    (mu : X → FiniteLaw Ω) (hmu : ∀ omega, Measurable (fun x => (mu x).mass omega))
    (left right : X → Ω → FiniteLaw (Finset ι))
    (hl : ∀ omega S, Measurable (fun x => (left x omega).mass S))
    (hr : ∀ omega S, Measurable (fun x => (right x omega).mass S))
    (chi : X → Ω → ℝ) (hchi : ∀ omega, Measurable (fun x => chi x omega))
    (hchi0 : ∀ x omega, 0 ≤ chi x omega) (hchi1 : ∀ x omega, chi x omega ≤ 1)
    (i : ι) {v bi eta : ℝ} (hvb : bi ≤ v) (hb : 0 ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    Integrable (fun x => localPromotionGain (mu x) (left x) (right x) i (chi x)
      v bi eta heta0 heta1) mu0 :=
  Integrable.of_mem_Icc 0 ((v-bi)+eta*bi)
    (measurable_localPromotionGain mu hmu left right hl hr chi hchi i
      v bi eta heta0 heta1).aemeasurable
    (ae_of_all _ fun x => localPromotionGain_bounds (mu x) (left x) (right x) i
      (chi x) (hchi0 x) (hchi1 x) hvb hb heta0 heta1)

theorem ordinary_carrier_promotion_gain (mu0 : Measure X) [IsFiniteMeasure mu0]
    (E : Set X) (hE : MeasurableSet E)
    (p : X → ι → ℝ) (hp0 : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x i, p x i ≤ 1)
    (hp : ∀ i, Measurable (fun x => p x i)) (i j : ι) (hij : i ≠ j)
    (left right : X → (ι → Bool) → FiniteLaw (Finset ι))
    (hl : ∀ flags S, Measurable (fun x => (left x flags).mass S))
    (hr : ∀ flags S, Measurable (fun x => (right x flags).mass S))
    (chi : X → (ι → Bool) → ℝ)
    (hchi : ∀ flags, Measurable (fun x => chi x flags))
    (hchi0 : ∀ x flags, 0 ≤ chi x flags) (hchi1 : ∀ x flags, chi x flags ≤ 1)
    (good : X → (ι → Bool) → Prop)
    (hg : ∀ flags, MeasurableSet {x | good x flags})
    (hgood : ∀ x flags, good x flags → chi x flags=1)
    {v bi eta L qmin pb : ℝ} (hvb : bi ≤ v) (hL : 0 ≤ L) (hb : L ≤ bi)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hqmin : 0 ≤ qmin)
    (hpair : ∀ x ∈ E, p x i=pb ∧ p x j=pb)
    (hleft : ∀ x ∈ E, ∀ flags, flags i=true → flags j=true → good x flags →
      qmin ≤ (left x flags).prob (fun S => i ∈ S))
    (hright : ∀ x ∈ E, ∀ flags, flags i=true → flags j=true → good x flags →
      qmin ≤ (right x flags).prob (fun S => i ∈ S)) :
    (eta*L*qmin^2)*pb^2*mu0.real E-
        (eta*L*qmin^2)*(∫ x in E,
          (independentFlagLaw (p x) (hp0 x) (hp1 x)).prob (fun flags => ¬good x flags) ∂mu0) ≤
      ∫ x in E, localPromotionGain (independentFlagLaw (p x) (hp0 x) (hp1 x))
        (left x) (right x) i (chi x) v bi eta heta0 heta1 ∂mu0 := by
  classical
  let g := eta*L*qmin^2
  let C : X → FiniteLaw (ι → Bool) := fun x => independentFlagLaw (p x) (hp0 x) (hp1 x)
  let bad : X → ℝ := fun x => (C x).prob (fun flags => ¬good x flags)
  let gain : X → ℝ := fun x => localPromotionGain (C x) (left x) (right x) i
    (chi x) v bi eta heta0 heta1
  have hC : ∀ flags, Measurable (fun x => (C x).mass flags) :=
    measurable_independentFlagLaw_mass_of p hp0 hp1 hp
  have hbmeas : Measurable bad := by
    unfold bad FiniteLaw.prob FiniteLaw.expect
    apply Finset.measurable_sum
    intro flags _
    exact (hC flags).mul (Measurable.ite (hg flags).compl measurable_const measurable_const)
  have hbad : Integrable bad mu0 :=
    Integrable.of_mem_Icc 0 1 hbmeas.aemeasurable
      (ae_of_all _ fun x => ⟨(C x).prob_nonneg _,(C x).prob_le_one _⟩)
  have hgain : Integrable gain mu0 := integrable_localPromotionGain mu0 C hC
    left right hl hr chi hchi hchi0 hchi1 i hvb (hL.trans hb) heta0 heta1
  have hpoint : ∀ᵐ x ∂mu0.restrict E, g*(pb^2-bad x) ≤ gain x := by
    filter_upwards [ae_restrict_mem hE] with x hx
    have hh := flagged_localPromotionGain_lower (p x) (hp0 x) (hp1 x) i j hij
      (left x) (right x) (chi x) (hchi0 x) (good x) (hgood x)
      hvb hL hb heta0 heta1 hqmin (hleft x hx) (hright x hx)
    change g * (p x i * p x j - bad x) ≤ gain x at hh
    rw [(hpair x hx).1, (hpair x hx).2] at hh
    simpa only [pow_two] using hh
  have hh := integral_mono_ae
    (((integrable_const (pb^2)).sub hbad.integrableOn).const_mul g)
    hgain.integrableOn hpoint
  change (∫ x in E, g * (pb^2 - bad x) ∂mu0) ≤ ∫ x in E, gain x ∂mu0 at hh
  rw [integral_const_mul]
    at hh
  change g * (∫ x in E, pb^2 - bad x ∂mu0) ≤ ∫ x in E, gain x ∂mu0 at hh
  rw [integral_sub (integrable_const (pb^2)) hbad.integrableOn,
    integral_const] at hh
  have hmass : (mu0.restrict E).real univ=mu0.real E := by
    simp only [measureReal_def,Measure.restrict_apply_univ]
  simp only [smul_eq_mul,hmass] at hh
  change g*pb^2*mu0.real E-g*(∫ x in E, bad x ∂mu0) ≤ ∫ x in E, gain x ∂mu0
  nlinarith only [hh]

theorem carrier_error_rate {mu0 : Measure X} [IsFiniteMeasure mu0]
    (E : Set X) {g pb delta gain badIntegral : ℝ} (hg : 0 ≤ g)
    (hactual : g*pb^2*mu0.real E-g*badIntegral ≤ gain)
    (hconditional : badIntegral ≤ delta*mu0.real E) :
    g*(pb^2-delta)*mu0.real E ≤ gain := by
  have h := mul_le_mul_of_nonneg_left hconditional hg
  nlinarith

omit [DecidableEq ι] in

theorem iid_coordinate_event_real {Y : Type*} [MeasurableSpace Y]
    (nu : Measure Y) [IsProbabilityMeasure nu]
    (E : Set Y) (hE : MeasurableSet E) (j : ι) :
    (Measure.pi (fun _ : ι => nu)).real {x | x j ∈ E}=nu.real E := by
  have hmap := (measurePreserving_eval (μ:=fun _ : ι => nu) j).map_eq
  have h := congrArg (fun mu : Measure Y => mu E) hmap
  rw [Measure.map_apply (measurable_pi_apply j) hE] at h
  exact congrArg ENNReal.toReal h

omit [DecidableEq ι] in

theorem rank_coefficient_population_lower [Nonempty ι] {m : ℕ}
    (hcard : Fintype.card ι ≤ m) :
    1/((m:ℝ)*((m:ℝ)+1)) ≤ 1/(2*Hybrid.rankDenominator ι) := by
  have hN : 0 < (Fintype.card ι:ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hm : (Fintype.card ι:ℝ) ≤ (m:ℝ) := by exact_mod_cast hcard
  have hd : 0 < 2*Hybrid.rankDenominator ι :=
    mul_pos (by norm_num) Hybrid.rankDenominator_pos
  apply one_div_le_one_div_of_le hd
  unfold Hybrid.rankDenominator
  nlinarith

end FCAppendix.Affine.Tail04
