import FCAppendix.Exclusive.NarrowGlobalGuardsTails
import FCAppendix.Exclusive.NarrowGlobalGuardsFiniteFull

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Global
open Set MeasureTheory ProbabilityTheory Filter

theorem integral_lower_route_tail_negative {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E)
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k < n)
    (a : UserTariff) (ha : a.Allowed) (G : Schedule n)
    (g v b lower upper delta V : ℝ) (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V)
    (hV : 0 ≤ V) (hlower : 0 < lower) (hd0 : 0 < delta) (hdhalf : delta ≤ 1/2)
    (hsmall : delta*(V+1) ≤ lower/2) (hb : 0 < b) (hlarge : upper ≤ b*delta^(n-1))
    (lam : Ω → ℝ) (hlam : Measurable lam) (hlam0 : ∀ w, 0 ≤ lam w)
    (hgood : ∀ w ∈ E, lam w ∈ Icc lower upper)
    (hbad : mu.real Eᶜ < 1/(V+1)) :
    (∫ w, LowType.binomialPayoff a G k g v b (demand n b (lam w)) ∂mu) < 0 := by
  have hp : Measurable (fun w => demand n b (lam w)) :=
    (continuous_demand n hn b).measurable.comp hlam
  have hprange : ∀ w, demand n b (lam w) ∈ Icc (0:ℝ) 1 :=
    fun w => ⟨demand_nonneg _ _ _,demand_le_one n hb (hlam0 w)⟩
  apply LowType.integral_negative_of_good_event mu E hE _
    (LowType.integrable_binomialPayoff mu a G k g v b _ hp hprange) hV (by norm_num : (0:ℝ)<1)
  · exact Eventually.of_forall fun w => LowType.payoff_le_low_upper a ha G hkn.le hg hb.le
      (hprange w).1 (hprange w).2 hV (by linarith)
  · exact Eventually.of_forall fun w hw => large_bid_lower_route_negative n k hn hk hkn a ha G
      g v b (lam w) lower upper delta V 1 hg hv0 hvV (by norm_num) hlower (hgood w hw)
      hd0 hdhalf hsmall hb hlarge
  · exact hbad

theorem integral_affine_tail_negative {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E)
    (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n)
    (eta : ℝ) (heta : eta ∈ Icc (0:ℝ) 1) (G : Schedule n)
    (g v b lower upper delta V : ℝ) (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hvV : v ≤ V)
    (hV : 0 ≤ V) (hlower : 0 < lower) (hd0 : 0 < delta) (hdhalf : delta ≤ 1/2)
    (hsmall : delta*(V+1) ≤ lower/2) (hb : 0 < b) (hlarge : upper ≤ b*delta^(n-1))
    (lam : Ω → ℝ) (hlam : Measurable lam) (hlam0 : ∀ w, 0 ≤ lam w)
    (hgood : ∀ w ∈ E, lam w ∈ Icc lower upper)
    (hbad : mu.real Eᶜ < 1/(V+1)) :
    (∫ w, LowType.binomialPayoff (.affine eta) G k g v b (demand n b (lam w)) ∂mu) < 0 := by
  have hp : Measurable (fun w => demand n b (lam w)) :=
    (continuous_demand n hn b).measurable.comp hlam
  have hprange : ∀ w, demand n b (lam w) ∈ Icc (0:ℝ) 1 :=
    fun w => ⟨demand_nonneg _ _ _,demand_le_one n hb (hlam0 w)⟩
  apply LowType.integral_negative_of_good_event mu E hE _
    (LowType.integrable_binomialPayoff mu (.affine eta) G k g v b _ hp hprange) hV (by norm_num : (0:ℝ)<1)
  · exact Eventually.of_forall fun w => LowType.payoff_le_low_upper (.affine eta) heta G hkn hg hb.le
      (hprange w).1 (hprange w).2 hV (by linarith)
  · exact Eventually.of_forall fun w hw => large_bid_affine_negative n k hn hk hkn eta heta.1 G
      g v b (lam w) lower upper delta V 1 hg hv0 hvV (by norm_num) hlower (hgood w hw)
      hd0 hdhalf hsmall hb hlarge
  · exact hbad

theorem integral_unique_tail_reference_gap {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (E : Set Ω) (hE : MeasurableSet E)
    (d : ℕ) (hd : 1 ≤ d) (G : Schedule (d+1))
    (g v b lower upper delta refPrice p0 error : ℝ)
    (hg : 0 ≤ g) (hv0 : 0 ≤ v) (hv2 : v ≤ 2) (hv : v ≤ 1+error)
    (hlower : 0 < lower) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hb : 0 < b) (hlarge : upper ≤ b*delta^d)
    (href : 0 < refPrice) (hp0 : 0 < p0) (hp1 : p0 < 1) (hFOC : (1-p0)^d=refPrice)
    (hlo : refPrice-error ≤ lower)
    (hbudget : ((d+1:ℕ)+1:ℝ)*error+(d+1:ℕ)*upper*delta ≤
      ((d:ℝ)*refPrice*(1-p0))/2)
    (lam : Ω → ℝ) (hlam : Measurable lam) (hlam0 : ∀ w, 0 ≤ lam w)
    (hgood : ∀ w ∈ E, lam w ∈ Icc lower upper)
    (hbad : mu.real Eᶜ ≤ ((d:ℝ)*refPrice*(1-p0))/(4*(2+((d:ℝ)*refPrice*(1-p0))/2))) :
    (∫ w, LowType.binomialPayoff .unique G (d+1) g v b (demand (d+1) b (lam w)) ∂mu)+
      ((d:ℝ)*refPrice*(1-p0))/4 ≤ referenceUtility d .unique refPrice 1 p0 := by
  let margin : ℝ := (d:ℝ)*refPrice*(1-p0)
  let U := referenceUtility d .unique refPrice 1 p0
  have hm : 0 < margin := mul_pos (mul_pos (Nat.cast_pos.mpr (by omega)) href) (sub_pos.mpr hp1)
  have hU : 0 < U := by
    apply referenceUtility_pos d hd .unique trivial refPrice 1 p0 href hp0 hp1
    dsimp [fTariff,fUnique]
    rw [← hFOC]
    field_simp [(pow_pos (sub_pos.mpr hp1) d).ne']
  have hp : Measurable (fun w => demand (d+1) b (lam w)) :=
    (continuous_demand (d+1) (by omega) b).measurable.comp hlam
  have hprange : ∀ w, demand (d+1) b (lam w) ∈ Icc (0:ℝ) 1 :=
    fun w => ⟨demand_nonneg _ _ _,demand_le_one (d+1) hb (hlam0 w)⟩
  have hu := LowType.integrable_binomialPayoff mu .unique G (d+1) g v b _ hp hprange
  have hbound := LowType.integral_upper_of_good_event mu E hE _ hu 2 (margin/2-U)
    (Eventually.of_forall fun w => LowType.payoff_le_low_upper .unique trivial G le_rfl hg hb.le
      (hprange w).1 (hprange w).2 (by norm_num) (by linarith))
    (Eventually.of_forall fun w hw => by
      have h := large_bid_unique_reference_gap d hd G g v b (lam w) lower upper delta (1+error)
        1 refPrice p0 error hg hv0 hv hlower (hgood w hw) hd0 hd1 hb hlarge href hp1
        (by simpa only [one_mul] using hFOC) (le_refl _) hlo hbudget
      change LowType.binomialPayoff .unique G (d+1) g v b (demand (d+1) b (lam w)) ≤ -(margin/2-U)
      change LowType.binomialPayoff .unique G (d+1) g v b (demand (d+1) b (lam w))+margin/2 ≤ U at h
      linarith only [h])
  have hprob := (le_div_iff₀ (show (0:ℝ)<4*(2+margin/2) by positivity)).mp hbad
  have he : mu.real E=1-mu.real Eᶜ := by rw [probReal_compl_eq_one_sub hE]; ring
  rw [he] at hbound
  have hbad0 : 0 ≤ mu.real Eᶜ := measureReal_nonneg
  have hcost : (2+margin/2-U)*mu.real Eᶜ ≤ (2+margin/2)*mu.real Eᶜ :=
    mul_le_mul_of_nonneg_right (by linarith only [hU.le]) hbad0
  change _+margin/4 ≤ U
  nlinarith only [hbound,hprob,hcost]

end FCAppendix.Exclusive.Narrow.Global
