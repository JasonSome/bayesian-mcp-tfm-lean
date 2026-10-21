import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapMenu
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05Capped

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators

def exactNativeGame {row : Uniform07.Row} {M : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row M) (hc : 1≤ Uniform07.capacity M) (R : ℝ) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  letI : NeZero M:=E.marketNeZero
  nativeGame E hc R

theorem auxiliary_guard (row : Uniform07.Row) (G : Uniform05.RestrictedLaw row) :
    Uniform07.kappa row*sourceLowerPriceCeiling row< G.multiplier-Early.nativeRadius row := by
  have hg:=(Crossover.Physical.source_auxiliary_floor_guards row).2.2.2
  have hΛ:=G.multiplier_guards.1
  simp only [Uniform05.t_eq_canonical] at hΛ
  linarith

theorem eventual_exact_receipt (row : Uniform07.Row) :
    ∀ᶠ M : ℕ in atTop,∀E : UniformFinite.ExactRestrictedLaw row M,
      Uniform05.kappa row*Uniform05.t row≤ UniformFinite.Source.rootLo row E.law := by
  obtain ⟨K,hK⟩:=eventually_atTop.1 (UniformFinite.Late.Exceptional.eventual_receipt row)
  filter_upwards [eventually_ge_atTop (K+1)] with M hM
  intro E
  exact hK (M-1) (by omega) E.pi E.IC

theorem eventual_native_above_cap_source_menu (row : Uniform07.Row)
    {tol : ℝ} (htol : 0< tol) :
    ∀ᶠ M : ℕ in atTop,∀E : UniformFinite.ExactRestrictedLaw row M,
      ∀hc : 1≤ Uniform07.capacity M,∀i : Fin M,∀v : ℝ,∀A : JointAction 2,
      v∈Icc (0:ℝ) (Uniform07.cutoff row) → A.routeCount=2 →
      Early.bidCap row< A.bid → A.bid< sourceLowerPriceCeiling row →
      |(problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v A-
        UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) A.bid|< tol := by
  let C:=UniformFinite.Late.Exceptional.errorConstant row
  let δ:=min (UniformFinite.Source.commonGuardMargin row) (tol/(4*C))
  have hC : 0< C:=UniformFinite.Late.Exceptional.errorConstant_pos row
  have hδ : 0<δ:=lt_min (UniformFinite.Source.common_guard_margin row)
    (div_pos htol (by positivity))
  have hδle : δ≤ UniformFinite.Source.commonGuardMargin row:=min_le_left _ _
  have hCδ : C*δ≤ tol/4 := by
    have hh:=(le_div_iff₀ (show 0<4*C by positivity)).mp
      (min_le_right (UniformFinite.Source.commonGuardMargin row) (tol/(4*C)))
    change δ*(4*C)≤ tol at hh
    nlinarith
  have hNat : Tendsto (fun M : ℕ=>(M:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have hsize : ∀ᶠ M : ℕ in atTop,4/(M:ℝ)≤δ := by
    exact (tendsto_const_div_atTop_nhds_zero_nat (4:ℝ)).eventually
      (Iic_mem_nhds hδ)
  have hexp : Tendsto (fun M : ℕ=>Real.exp (-(M:ℝ)*δ^2/2)) atTop (𝓝 0) := by
    have hh:=Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hNat.const_mul_atTop (show 0<δ^2/2 by positivity))
    convert hh using 1
    funext M
    congr 1
    ring
  have htail : ∀ᶠ M : ℕ in atTop,
      540*Uniform07.cutoff row*Real.exp (-(M:ℝ)*δ^2/2)< tol/4 := by
    have hh:=hexp.const_mul (540*Uniform07.cutoff row)
    simp only [mul_zero] at hh
    exact hh.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨radius,hr,hmod⟩:=UniformFinite.Late.Exceptional.full_product_modulus row
    (half_pos htol)
  obtain ⟨N₀,ε₀,hε₀,hroot⟩:=UniformFinite.noisy_multiplier_localization row hr
  filter_upwards [hsize,htail,eventual_exact_receipt row,eventually_ge_atTop (N₀+1)]
    with M hS hT hReceipt hN
  intro E hc i v A hv hA hU hR
  letI : NeZero M:=E.marketNeZero
  have hΛ:=hroot (M-1) (by omega) 0 hε₀.le E.pi E.IC
  have hV : v∈Icc (0:ℝ) (Uniform05.t row) := by
    simpa only [Uniform05.t_eq_canonical] using hv
  have hB : A.bid∈Icc (0:ℝ) (Uniform05.t row) := by
    refine ⟨A.bid_nonneg,?_⟩
    simpa only [Uniform05.t_eq_canonical] using
      hR.le.trans (Crossover.Physical.source_auxiliary_floor_guards row).2.2.1.le
  have hP:=hmod (⟨v,hV⟩ : UniformFinite.Value row)
    (⟨A.bid,hB⟩ : UniformFinite.Value row)
    (UniformFinite.actualProductRoot row E.law) (UniformFinite.sourceProductRoot row) hΛ
  have hG:=Crossover.Physical.source_auxiliary_floor_guards row
  have hAerr:=native_above_cap_payoff_error E hc hG.1 hG.2.1 hG.2.2.1
    (auxiliary_guard row E.law) (hReceipt E) i A hA hU hR hv hδ.le hδle hS
  change |(problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v A-
    UniformFinite.productPayoff (Uniform05.xi row) v E.law.multiplier A.bid|≤ _ at hAerr
  calc
    _≤|(problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v A-
        UniformFinite.productPayoff (Uniform05.xi row) v E.law.multiplier A.bid|+
      |UniformFinite.productPayoff (Uniform05.xi row) v E.law.multiplier A.bid-
        UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) A.bid| :=
          abs_sub_le _ _ _
    _< tol := by
      change |UniformFinite.productPayoff (Uniform05.xi row) v E.law.multiplier A.bid-
        UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) A.bid|< tol/2 at hP
      change _≤ C*δ+_ at hAerr
      linarith

end FCAppendix.Affine.Uniform07Finishing.Concrete05
