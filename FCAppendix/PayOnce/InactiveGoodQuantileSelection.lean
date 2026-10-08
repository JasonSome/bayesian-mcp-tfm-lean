import FCAppendix.PayOnce.GoodQuantileSelection
import FCAppendix.PayOnce.EffectiveVanishingBid

namespace FCAppendix.PayOnce.GoodQuantileSelection
open MeasureTheory ProbabilityTheory Set Filter Topology

theorem exists_four_positive_good_quantiles (F : Measure ℝ) [IsProbabilityMeasure F]
    {g q : ℝ} (hatom : ∀ v : ℝ, g < v → F {v} = 0)
    (hq0 : 0 ≤ q) (hq : q < F.real (Ioi g))
    (Good : ℝ → Prop) (hgood : ∀ᵐ v ∂F, g < v → Good v) :
    ∃ a x y b : ℝ, Good a ∧ Good x ∧ Good y ∧ Good b ∧
      g < a ∧ a < x ∧ x < y ∧ y < b ∧
      0 < F (Icc a x) ∧ 0 < F (Ioc x y) ∧ 0 < F (Icc y b) ∧
      0 < F (Iic y) ∧ q < F.real (Ioi b) := by
  let H := ProbabilityTheory.cond F (Ioi g)
  have hπ : 0 < F.real (Ioi g) := hq0.trans_lt hq
  have hπne : F (Ioi g) ≠ 0 := by
    intro hz
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hπ
  haveI : IsProbabilityMeasure H := ProbabilityTheory.cond_isProbabilityMeasure hπne
  haveI : NullSingletonClass H := VanishingBidIC.nullSingleton_cond_positive F g hatom
  have hactive : ∀ᵐ v ∂H, g < v := ProbabilityTheory.ae_cond_mem measurableSet_Ioi
  have hgoodH : ∀ᵐ v ∂H, Good v := by
    filter_upwards [ProbabilityTheory.cond_absolutelyContinuous.ae_le hgood, hactive] with v hv ha
    exact hv ha
  obtain ⟨a,x,y,b,ha,hx,hy,hb,hga,hax,hxy,hyb,haxM,hxyM,hybM,hleft,hqb⟩ :=
    exists_four_good_quantiles H hactive (div_nonneg hq0 hπ.le)
      ((div_lt_one hπ).mpr hq) Good hgoodH
  have hpos {E : Set ℝ} (he : 0 < H E) : 0 < F E := by
    apply pos_iff_ne_zero.mpr
    intro hz
    exact he.ne' (ProbabilityTheory.cond_absolutelyContinuous hz)
  refine ⟨a,x,y,b,ha,hx,hy,hb,hga,hax,hxy,hyb,hpos haxM,hpos hxyM,hpos hybM,hpos hleft,?_⟩
  have hgb : g < b := hga.trans (hax.trans (hxy.trans hyb))
  have hmul : H.real (Ioi b) * F.real (Ioi g) = F.real (Ioi b) := by
    have hh := congrArg ENNReal.toReal (ProbabilityTheory.cond_mul_eq_inter
      (s := Ioi g) measurableSet_Ioi (Ioi b) F)
    simpa only [ENNReal.toReal_mul, inter_eq_right.mpr (Ioi_subset_Ioi hgb.le), measureReal_def] using hh
  have hh := (div_lt_iff₀ hπ).mp hqb
  rwa [hmul] at hh

end FCAppendix.PayOnce.GoodQuantileSelection
