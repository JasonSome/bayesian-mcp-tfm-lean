import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05Scalars
import FCAppendix.Affine.Uniform07Finishing.Crossover.Received05IntegralBridge
import FCAppendix.Affine.UniformFinite.SourceProductMenu

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Uniform06 Uniform06.LiteralExperiment

theorem rawUtility_eq_source (row : Uniform07.Row) (m : ℕ)
    (E : ReadyLaw row m) (v b : ℝ)
    (hb : b∈Icc (0:ℝ) (ReceiptGap.cap row)) :
    UniformFinite.rawUtility row (m-1) E.1.law v b=
      Rank.payoff (Uniform07.eta row) v b
        (sourceSuccess row m (G row m E) (g row m E) (cm row m E) b)
        (sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b) := by
  let a : Uniform05.Bid row:=⟨b,by
    change b∈Icc (0:ℝ) (Uniform05.cap row)
    rw [cap_eq]
    exact hb⟩
  have hm : m-1+1=m := by have := E.1.cluster.market_two_le; omega
  have h:=Received06.received_rawUtility_eq_source E.1 (m-1) a v
  let F (k : ℕ) : ℝ:=Rank.payoff (Uniform07.eta row) v b
    (sourceSuccess row k (Concrete05.realJoint E.1)
      (Received06.received06GuardData row k E.1.law.multiplier E.1.law.rejectionRoot)
      (Received06.received06CountMargin row k) b)
    (sourceDuplicate row k (Concrete05.realJoint E.1)
      (Received06.received06GuardData row k E.1.law.multiplier E.1.law.rejectionRoot)
      (Received06.received06CountMargin row k) b)
  change UniformFinite.rawUtility row (m-1) E.1.law v b=F (m-1+1) at h
  rw [hm] at h
  exact h

theorem all_action_IC (row : Uniform07.Row) (m : ℕ) (E : ReadyLaw row m) :
    ∀ᵐp∂(G row m E:Measure (ℝ×ℝ)),
      ∀b∈Icc (LowChernoff.physicalFloor row p.1) (min p.1 (ReceiptGap.cap row)),
        Rank.payoff (Uniform07.eta row) p.1 b
          (sourceSuccess row m (G row m E) (g row m E) (cm row m E) b)
          (sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b)≤
        Rank.payoff (Uniform07.eta row) p.1 p.2
          (sourceSuccess row m (G row m E) (g row m E) (cm row m E) p.2)
          (sourceDuplicate row m (G row m E) (g row m E) (cm row m E) p.2) := by
  filter_upwards [realJoint_common_raw_IC E.1,realJoint_shape E.1] with p hIC hp
  intro b hb
  have hf := (LiteralWeakRent.source_floor_bounds row hp.1.1.le).1
  have hb' : b∈Icc (0:ℝ) (ReceiptGap.cap row):=
    ⟨hf.trans hb.1,hb.2.trans (min_le_right _ _)⟩
  have hp' : p.2∈Icc (0:ℝ) (ReceiptGap.cap row):=
    ⟨hIC.1.le,hp.2.2.trans (min_le_right _ _)⟩
  rw [←rawUtility_eq_source row m E p.1 b hb',
    ←rawUtility_eq_source row m E p.1 p.2 hp']
  exact hIC.2 b hb

theorem product_menu (row : Uniform07.Row) (err : ℝ) (herr : 0< err) :
    ∀ᶠ m in atTop,∀E : ReadyLaw row m,∀v∈Icc (0:ℝ) (Uniform07.cutoff row),
      ∀b∈Icc (LowChernoff.physicalFloor row v) (min v (ReceiptGap.cap row)),
        |Rank.payoff (Uniform07.eta row) v b
          (sourceSuccess row m (G row m E) (g row m E) (cm row m E) b)
          (sourceDuplicate row m (G row m E) (g row m E) (cm row m E) b)-
            ActiveLocalization.product (Uniform07.xi row) v (g row m E).multiplier b|≤ err := by
  obtain ⟨N,hN⟩:=eventually_atTop.mp (UniformFinite.Source.uniform_product_menu row err herr)
  filter_upwards [eventually_ge_atTop (N+1)] with m hm
  intro E v hv b hb
  have hb' : b∈Icc (0:ℝ) (ReceiptGap.cap row):=
    ⟨(LiteralWeakRent.source_floor_bounds row hv.1).1.trans hb.1,
      hb.2.trans (min_le_right _ _)⟩
  let a : Uniform05.Bid row:=⟨b,by
    change b∈Icc (0:ℝ) (Uniform05.cap row)
    rw [cap_eq]
    exact hb'⟩
  have h:=hN (m-1) (by omega) E.1.law v a
    (by simpa only [Uniform05.t_eq_canonical] using hv)
  rw [←rawUtility_eq_source row m E v b hb']
  simpa only [a,UniformFinite.productPayoff,ActiveLocalization.product,
    Uniform05.xi_eq_canonical,g,Received06.received06GuardData,
    SourcePrefixConstructor.sourceGuard] using h.le

theorem earlyMenu (row : Uniform07.Row) :
    SourceEarlyFamily.EarlyMenuFields (G row) (g row) (cm row) row where
  value_marginal:=value row
  permitted:=permitted row
  all_action_IC:=all_action_IC row
  product_menu:=product_menu row
  comparison:=comparison row
  root_limit:=root_limit row

end FCAppendix.Affine.Uniform07Finishing.Crossover.Received05
