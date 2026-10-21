import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05AboveCapTail
import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05JointConull

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine
open scoped BigOperators

theorem source_product_negative_below_cap_value (row : Uniform07.Row)
    {v b : ℝ} (hv : v≤ Uniform05.cap row) (hb : Uniform05.cap row≤ b) :
    UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) b<0 := by
  let p:=ClippedResidual.exposure (Uniform05.xi row) (Uniform05.lambda row) b
  have hb0 : 0< b := (Uniform05.cap_pos row).trans_le hb
  have hpb : Uniform05.lambda row< b :=
    (UniformFinite.Late.Exceptional.source_entry_lt_cap row).trans_le hb
  have hp : 0< p := ClippedResidual.exposure_pos (Uniform05.xi_range row).1
    (Uniform05.lambda_pos row) hpb
  have hp1 : p≤ 1 := ClippedResidual.exposure_le_one _ _ _
  have hS : 0≤ 2*p-p^2 := by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp1)]
  have hη:=Uniform05.eta_range row
  have hcharge : 0< Uniform05.eta row*b*p^2 :=
    mul_pos (mul_pos hη.1 hb0) (sq_pos_of_pos hp)
  have hfirst : (v-b)*(2*p-p^2)≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hv.trans hb)) hS
  have hηeq : Uniform05.eta row=1-2*Uniform05.xi row := by
    unfold Uniform05.xi
    ring
  have hpay : UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) b=
      (v-b)*(2*p-p^2)-Uniform05.eta row*b*p^2 := by
    change v*(2*p-p^2)-2*b*p*(1-Uniform05.xi row*p)=_
    rw [hηeq]
    ring
  rw [hpay]
  linarith

theorem source_below_cap_negative_gap (row : Uniform07.Row) :
    ∃gap : ℝ,0< gap ∧ ∀v b : UniformFinite.Value row,
      (v:ℝ)≤ Uniform05.cap row → Uniform05.cap row≤(b:ℝ) →
      UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) b≤-gap := by
  let S : Set (UniformFinite.Value row×UniformFinite.Value row):=
    {p|(p.1:ℝ)≤ Uniform05.cap row ∧ Uniform05.cap row≤(p.2:ℝ)}
  let f : UniformFinite.Value row×UniformFinite.Value row→ℝ:=fun p=>
    -UniformFinite.productPayoff (Uniform05.xi row) p.1 (Uniform05.lambda row) p.2
  have hS : IsClosed S :=
    (isClosed_le (continuous_subtype_val.comp continuous_fst) continuous_const).inter
      (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd))
  have hne : S.Nonempty := by
    refine ⟨(⟨0,le_rfl,(Uniform05.t_pos row).le⟩,
      ⟨Uniform05.t row,(Uniform05.t_pos row).le,le_rfl⟩),?_⟩
    exact ⟨(Uniform05.cap_pos row).le,(Uniform05.cap_lt_t row).le⟩
  have harg : Continuous (fun p : UniformFinite.Value row×UniformFinite.Value row=>
      ((p.1:ℝ),(p.2:ℝ))) := by fun_prop
  have hf : Continuous f :=
    ((UniformFinite.continuous_product_fixed_root (Uniform05.xi_range row).1
      (Uniform05.lambda_pos row)).comp harg).neg
  obtain ⟨p,hp,hmin⟩:=hS.isCompact.exists_isMinOn hne hf.continuousOn
  have hpos : 0< f p := neg_pos.mpr
    (source_product_negative_below_cap_value row hp.1 hp.2)
  refine ⟨f p,hpos,?_⟩
  intro v b hv hb
  have hm:=hmin (show (v,b)∈S from ⟨hv,hb⟩)
  change f p≤-UniformFinite.productPayoff (Uniform05.xi row) v (Uniform05.lambda row) b at hm
  linarith

theorem eventual_native_broadcast_strict_cap_pi (row : Uniform07.Row) :
    ∀ᶠ M : ℕ in atTop,
      ∀W : UniformFinite.NativeFiniteLowerConstruction row M (sourceLowerPriceCeiling row),
      ∀hc : 1≤ Uniform07.capacity M,
      ∀ᵐp∂(W.finite.restricted.pi.1 : Measure (UniformFinite.Value row×unitInterval)),
        (∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ 0< A.bid→
          A.bid< sourceLowerPriceCeiling row→
          (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff p.1 A≤
            (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff p.1
              (UniformFinite.OriginalPopulation.lowerAction row p)) ∧
        (∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ Early.bidCap row< A.bid→
          A.bid< sourceLowerPriceCeiling row→
          (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff p.1 A<
            (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff p.1
              (UniformFinite.OriginalPopulation.lowerAction row p)) := by
  obtain ⟨gap,hgap,hgapall⟩:=UniformFinite.Late.Exceptional.source_above_cap_gap row
  obtain ⟨negGap,hneg,hnegall⟩:=source_below_cap_negative_gap row
  let tol:=min (gap/4) (negGap/2)
  have ht : 0< tol := lt_min (by positivity) (by positivity)
  obtain ⟨K,hK⟩:=eventually_atTop.1
    (UniformFinite.uniform_source_raw_menu row (show 0< gap/4 by positivity))
  filter_upwards [eventual_native_above_cap_source_menu row ht,eventually_ge_atTop (K+1)]
    with M hNative hM
  intro W hc
  cases M with
  | zero => have hh:=W.finite.restricted.cluster.market_two_le; omega
  | succ N =>
    let E:=W.finite.restricted
    have hG:=Crossover.Physical.source_auxiliary_floor_guards row
    have hguard:=auxiliary_guard row E.law
    have hMenu:=hK N (by omega) E.pi E.IC
    have hCapped:=native_common_capped_positive_IC W hc hG.1 hG.2.1 hG.2.2.1 hguard
    have hNonnegative:=native_common_incumbent_nonnegative E hc hG.1 hG.2.1 hG.2.2.1 hguard
    filter_upwards [E.common_conull_contract,hCapped,hNonnegative] with p hp hcap hn
    have hstrict : ∀i : Fin (N+1),∀A : JointAction 2,A.routeCount=2→ Early.bidCap row< A.bid→
        A.bid< sourceLowerPriceCeiling row→
        (problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff p.1 A<
          (problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff p.1
            (UniformFinite.OriginalPopulation.lowerAction row p) := by
      intro i A hA hU hR
      have hv : (p.1:ℝ)∈Icc (0:ℝ) (Uniform07.cutoff row) := by
        simpa only [UniformFinite.Value,Uniform05.t_eq_canonical] using p.1.property
      have hNativeA:=hNative E hc i p.1 A hv hA hU hR
      have hUpper:=(abs_lt.mp hNativeA).2
      have hB : A.bid∈Icc (0:ℝ) (Uniform05.t row) := by
        exact ⟨A.bid_nonneg,by simpa only [Uniform05.t_eq_canonical] using hR.le.trans hG.2.2.1.le⟩
      have hU' : Uniform05.cap row≤ A.bid := by simpa only [cap_eq] using hU.le
      by_cases hvU : Uniform05.cap row≤(p.1:ℝ)
      · have hval := (UniformFinite.Late.Exceptional.source_entry_lt_cap row).trans_le hvU
        have ha := UniformFinite.source_activeBid_feasible row hval p.1.property.2
        have hplay := hp.2.2.2.2 (Uniform05.activeBid row p.1) ha
        simp only [Nat.add_sub_cancel] at hplay
        have happrox := hMenu p.1 (UniformFinite.sourceActiveBid row p.1) p.1.property
        have hLow:=(abs_lt.mp happrox).1
        have hGap:=hgapall p.1 (⟨A.bid,hB⟩ : UniformFinite.Value row) hvU hU'
        have hInc : (problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff p.1
            (UniformFinite.OriginalPopulation.lowerAction row p)=
          UniformFinite.rawUtility row N E.law p.1 (UniformFinite.baseBid row p) := by
          exact native_capped_payoff_eq_raw E hc hG.1 hG.2.1 hG.2.2.1 hguard i p.1
            (UniformFinite.baseBid row p) hp.2.1
        rw [hInc]
        change -(gap/4)< UniformFinite.rawUtility row N E.law p.1
          (Uniform05.activeBid row p.1)-UniformFinite.sourceProfit row p.1 at hLow
        change gap≤ UniformFinite.sourceProfit row p.1-
          UniformFinite.productPayoff (Uniform05.xi row) p.1 (Uniform05.lambda row) A.bid at hGap
        have htol : tol≤ gap/4 := min_le_left _ _
        linarith
      · have hNeg:=hnegall p.1 (⟨A.bid,hB⟩ : UniformFinite.Value row)
          (le_of_not_ge hvU) hU'
        have htol : tol≤ negGap/2 := min_le_right _ _
        have hnonneg := hn i
        change 0≤(problem (exactNativeGame E hc (sourceLowerPriceCeiling row)) i).payoff p.1
          (UniformFinite.OriginalPopulation.lowerAction row p) at hnonneg
        linarith
    refine ⟨?_,hstrict⟩
    intro i A hA hA0 hR
    by_cases hU : A.bid≤ Early.bidCap row
    · exact hcap i A hA hA0 hU
    · exact (hstrict i A hA (lt_of_not_ge hU) hR).le

theorem eventual_native_broadcast (row : Uniform07.Row) :
    ∀ᶠ M : ℕ in atTop,
      ∀W : UniformFinite.NativeFiniteLowerConstruction row M (sourceLowerPriceCeiling row),
      ∀hc : 1≤ Uniform07.capacity M,
      ∀ᵐx∂(lowerJoint W.finite.restricted : Measure (ℝ×JointAction 2)),
        ∀i : Fin M,∀A : JointAction 2,A.routeCount=2→ 0< A.bid→
          A.bid< sourceLowerPriceCeiling row→
          (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff x.1 A≤
            (problem (exactNativeGame W.finite.restricted hc (sourceLowerPriceCeiling row)) i).payoff x.1 x.2 := by
  filter_upwards [eventual_native_broadcast_strict_cap_pi row] with M hM
  intro W hc
  exact lowerJoint_ae_of_original W.finite.restricted _
    ((hM W hc).mono (fun _ h=>h.1))

end FCAppendix.Affine.Uniform07Finishing.Concrete05
