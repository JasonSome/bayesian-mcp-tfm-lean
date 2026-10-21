import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapTail
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalFamilies

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover Crossover.Physical

theorem source_product_payoff_eq (row : Uniform07.Row) (v b : ℝ) :
    UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) b=
      utilityTwo (Uniform07.eta row) v b (sourceProductMarginal row b)
        ((sourceProductMarginal row b)^2) := by
  have hη : Uniform07.eta row=1-2*Uniform07.xi row := by
    linarith [Uniform07.xi_identity row]
  simp only [UniformFinite.productPayoff,Uniform05.xi_eq_canonical,
    Uniform05.lambda_eq_canonical,sourceProductMarginal,utilityTwo]
  rw [hη]
  ring

theorem source_product_zero_below_quarter (row : Uniform07.Row)
    {b : ℝ} (hb : b≤ Uniform07.cutoff row/4) : sourceProductMarginal row b=0 := by
  have hentry : Uniform07.cutoff row/4≤ Uniform07.entry row := by
    have ht:=Uniform07.cutoff_pos row
    cases row <;> norm_num [Uniform07.entry,Uniform07.x,Uniform07.xQ] at * <;> linarith
  exact ClippedResidual.exposure_zero (hb.trans hentry)

theorem exact_native_two_payoff {row : Uniform07.Row} {M : ℕ}
    (E : UniformFinite.ExactRestrictedLaw row M) (hc : 1≤ Uniform07.capacity M)
    (R : ℝ) (i : Fin M) (v : ℝ) {b : ℝ} (hb : 0≤ b) :
    (problem (exactNativeGame E hc R) i).payoff v (two b)=
      utilityTwo (Uniform07.eta row) v b (q (exactNativeGame E hc R) i b)
        (duplicate (exactNativeGame E hc R) i b) := by
  exact two_payoff (exactNativeGame E hc R) (source_eta_mem row).1
    (source_eta_mem row).2 rfl rfl i v hb

theorem eventual_native_positive_source_menu (row : Uniform07.Row)
    {tol : ℝ} (htol : 0< tol) :
    ∀ᶠ M : ℕ in atTop,∀E : UniformFinite.ExactRestrictedLaw row M,
      ∀hc : 1≤ Uniform07.capacity M,∀i : Fin M,∀v : ℝ,∀A : JointAction 2,
      v∈Icc (0:ℝ) (Uniform07.cutoff row) → A.routeCount=2 →
      0< A.bid → A.bid< sourceLowerPriceCeiling row →
      |(problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v A-
        UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) A.bid|< tol := by
  obtain ⟨K,hK⟩:=eventually_atTop.1 (UniformFinite.uniform_source_raw_menu row htol)
  filter_upwards [eventual_native_above_cap_source_menu row htol,
    eventually_ge_atTop (K+1)] with M hAbove hM
  intro E hc i v A hv hA hpos hR
  by_cases hcap : A.bid≤ Early.bidCap row
  · cases M with
    | zero => have hh:=E.cluster.market_two_le; omega
    | succ N =>
      let own : Uniform05.Bid row:=⟨A.bid,A.bid_nonneg,by simpa only [cap_eq] using hcap⟩
      have hAct : A=Hybrid.lowBroadcast own := UniformFinite.NativeIC.broadcast_eq A hA own rfl
      have hG:=source_auxiliary_floor_guards row
      rw [hAct]
      change |(problem (nativeGame E hc (sourceLowerPriceCeiling row)) i).payoff v
        (Hybrid.lowBroadcast own)-UniformFinite.productPayoff (Uniform05.xi row) v
          (Uniform05.lambda row) (own:ℝ)|< tol
      rw [native_capped_payoff_eq_raw E hc hG.1 hG.2.1 hG.2.2.1
        (auxiliary_guard row E.law) i v own hpos]
      exact hK N (by omega) E.pi E.IC v own
        (by simpa only [Uniform05.t_eq_canonical] using hv)
  · exact hAbove E hc i v A hv hA (lt_of_not_ge hcap) hR

end FCAppendix.Affine.Uniform07Finishing.Concrete05
