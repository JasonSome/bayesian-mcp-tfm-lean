import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalOptimizerCover
import FCAppendix.Affine.Uniform07Finishing.Crossover.PhysicalNativeMoments
import FCAppendix.Affine.Uniform07Finishing.Native.LowerChainFamily
import FCAppendix.Affine.Uniform07Finishing.Native.BroadcastFloorTransfer

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Crossover
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Topology
namespace Physical

theorem source_auxiliary_floor_guards (row : Uniform07.Row) :
    0< sourceLowerPriceCeiling row ∧
    Early.bidCap row< sourceLowerPriceCeiling row ∧
    sourceLowerPriceCeiling row< Uniform07.cutoff row ∧
    Uniform07.kappa row*sourceLowerPriceCeiling row+Early.nativeRadius row<
      (27/50:ℝ)*Uniform07.cutoff row := by
  have ht := Uniform07.cutoff_pos row
  have hk := source_kappa_positive row
  have ha := (Early.native_sampling_margin_guards row).1
  have hk54 : (27/50:ℝ)< Uniform07.kappa row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xiQ,Uniform07.etaQ]
  have hroot : sourceLowerRootBound row/Uniform07.kappa row< Uniform07.cutoff row := by
    apply (div_lt_iff₀ hk).2
    have hmul := mul_lt_mul_of_pos_right hk54 ht
    unfold sourceLowerRootBound
    linarith
  have hceil : sourceLowerPriceCeiling row< Uniform07.cutoff row := by
    have hlim := (Early.upper_floor_interface row).2.2.2.1
    unfold sourceLowerPriceCeiling
    linarith
  have hguard := sourceLowerPriceCeiling_root_guard row
  refine ⟨sourceLowerPriceCeiling_pos row,
    (Early.upper_floor_interface row).2.2.1.trans (sourceLowerPriceCeiling_above_limit row),
    hceil,?_⟩
  unfold sourceLowerRootBound at hguard
  linarith

def replaceUpperFloor {row : Uniform07.Row} {m : ℕ}
    (D : UniformMarketData row m) (R : ℝ)
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row) :
    UniformMarketData row m :=
  { D with R:=R, floor_positive:=hR, cap_lt_floor:=hUR, floor_lt_cutoff:=hRt }

variable {row : Uniform07.Row} {m : ℕ}

theorem replaceUpperFloor_native_outcome
    (D : UniformMarketData row m) {R : ℝ}
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (i : Fin m) (a : JointAction 2) (ha0 : a.bid< D.R) (ha : a.bid< R) :
    (problem D.native i).outcome a=
      (problem (replaceUpperFloor D R hR hUR hRt).native i).outcome a := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  simpa only [UniformMarketData.native,replaceUpperFloor] using
    sourceNativeGame_raw_lower_outcome_floor_invariant row D.market_ge_two D.capacity_positive
      D.floor_positive D.cap_lt_floor D.floor_lt_cutoff hR hUR hRt
      (source_guard_multiplier_positive row D.multiplier_lower) D.lower D.lower_value D.lower_routes
      (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
      (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin)
      i a ha0 ha

theorem replaceUpperFloor_native_payoff
    (D : UniformMarketData row m) {R : ℝ}
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (i : Fin m) (v : ℝ) (a : JointAction 2) (ha0 : a.bid< D.R) (ha : a.bid< R) :
    (problem D.native i).payoff v a=
      (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff v a := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  simpa only [UniformMarketData.native,replaceUpperFloor] using
    sourceNativeGame_raw_lower_payoff_floor_invariant row D.market_ge_two D.capacity_positive
      D.floor_positive D.cap_lt_floor D.floor_lt_cutoff hR hUR hRt
      (source_guard_multiplier_positive row D.multiplier_lower) D.lower D.lower_value D.lower_routes
      (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
      (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin)
      i v a ha0 ha

theorem replaceUpperFloor_singleton_of_capped_winners
    (D : UniformMarketData row m) {R : ℝ}
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hRR : R≤ D.R)
    (hcross : ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ i : Fin m,
      ∀ a : JointAction 2, a.routeCount=1 → a.bid< D.R →
        ∃ b∈Icc (0:ℝ) (Early.bidCap row),
          (problem D.native i).payoff v a<(problem D.native i).payoff v (two b)) :
    ∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ i : Fin m,
      ∀ a : JointAction 2, a.routeCount=1 → a.bid< R →
        ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid< R ∧
          (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff v a<
            (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff v b := by
  intro v hv hvt i a ha hab
  have ha0 := hab.trans_le hRR
  obtain ⟨b,hb,hgain⟩ := hcross v hv hvt i a ha ha0
  have hb0 : (two b).bid< D.R := by
    simpa only [two_bid hb.1] using hb.2.trans_lt D.cap_lt_floor
  have hbR : (two b).bid< R := by
    simpa only [two_bid hb.1] using hb.2.trans_lt hUR
  rw [replaceUpperFloor_native_payoff D hR hUR hRt i v a ha0 hab,
    replaceUpperFloor_native_payoff D hR hUR hRt i v (two b) hb0 hbR] at hgain
  exact ⟨two b,two_routes b,hbR,hgain⟩

theorem replaceUpperFloor_lower_broadcast_IC
    (D : UniformMarketData row m) {R : ℝ}
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hRR : R≤ D.R)
    (hIC : ∀ᵐ x ∂(D.lower : Measure (ℝ×JointAction 2)),
      ∀ i : Fin m, ∀ a : JointAction 2, a.routeCount=2 → a.bid< D.R →
        (problem D.native i).payoff x.1 a≤(problem D.native i).payoff x.1 x.2) :
    ∀ᵐ x ∂(D.lower : Measure (ℝ×JointAction 2)),
      ∀ i : Fin m, ∀ a : JointAction 2, a.routeCount=2 → a.bid< R →
        (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff x.1 a≤
          (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff x.1 x.2 := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  simpa only [UniformMarketData.native,replaceUpperFloor,actualBroadcastBestBelow] using
    sourceNativeGame_broadcast_IC_floor_replace row D.market_ge_two D.capacity_positive
      D.floor_positive D.cap_lt_floor D.floor_lt_cutoff hR hUR hRt
      (source_guard_multiplier_positive row D.multiplier_lower) D.lower D.lower_value D.lower_routes
      (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
      (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin) hRR hIC

theorem replaceUpperFloor_positive_bid_continuity
    (D : UniformMarketData row m) {R : ℝ}
    (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hpay : ∀ i : Fin m, ∀ z : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem D.native i).payoff w.1 (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z) :
    ∀ i : Fin m, ∀ z : ℝ×Icc (0:ℝ) (Early.bidCap row), 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) (Early.bidCap row)=>
        (problem (replaceUpperFloor D R hR hUR hRt).native i).payoff w.1
          (sourceLowerBroadcastAction (Early.bidCap row) w.2)) z := by
  letI : Nonempty (Fin m):=D.fin_nonempty
  simpa only [UniformMarketData.native,replaceUpperFloor] using
    sourceNativeGame_positive_payoff_continuous_floor_replace row D.market_ge_two D.capacity_positive
      D.floor_positive D.cap_lt_floor D.floor_lt_cutoff hR hUR hRt
      (source_guard_multiplier_positive row D.multiplier_lower) D.lower D.lower_value D.lower_routes
      (literalSourceAlpha row D.Λ D.z D.width D.guardMargin)
      (measurable_literalSourceAlpha row D.multiplier_lower D.z D.width D.guardMargin) hpay

section Families
variable {population : ℕ→ℕ}
variable (row : Uniform07.Row) (D : ∀ k, UniformMarketData row (population k))

structure AuxiliaryLowerData05_06 where
  crossover : CrossoverFamily06 (fun k=>(D k).native) row
  low : LowFamily06 (fun k=>(D k).native) row
  product : ProductFamily05 (fun k=>(D k).native) row (fun k=>(D k).R)
  entry : EntryFullMenu06 (fun k=>(D k).native) row
  canonical : CanonicalOptimizer06 (fun k=>(D k).native) row

variable {row D}

theorem AuxiliaryLowerData05_06.eventually_after_every_smaller_floor
    (F : AuxiliaryLowerData05_06 row D) :
    ∀ᶠ k in atTop, ∀ R : ℝ, ∀ hR : 0< R, ∀ hUR : Early.bidCap row< R,
      ∀ hRt : R< Uniform07.cutoff row, R≤(D k).R →
      (∀ v : ℝ, 0< v → v≤ Uniform07.cutoff row → ∀ i : Fin (population k),
        ∀ a : JointAction 2, a.routeCount=1 → a.bid< R →
          ∃ b : JointAction 2, b.routeCount=2 ∧ b.bid< R ∧
            (problem (replaceUpperFloor (D k) R hR hUR hRt).native i).payoff v a<
              (problem (replaceUpperFloor (D k) R hR hUR hRt).native i).payoff v b) ∧
      (∀ i : Fin (population k), ∀ b : Icc (0:ℝ) (Early.bidCap row),
        |((problem (replaceUpperFloor (D k) R hR hUR hRt).native i).outcome
          (sourceLowerBroadcastAction (Early.bidCap row) b)).load-2*sourceProductProbability row b|≤
            F.product.nativeMomentError k ∧
        |((problem (replaceUpperFloor (D k) R hR hUR hRt).native i).outcome
          (sourceLowerBroadcastAction (Early.bidCap row) b)).duplicates-(sourceProductProbability row b)^2|≤
            F.product.nativeMomentError k) := by
  have hcross := eventually_every_native_lower_singleton_capped_winner
    F.crossover F.low F.product F.entry F.canonical (fun _=>rfl) (fun _=>rfl)
  filter_upwards [hcross,F.product.eventually_native_moments] with k hC hM
  intro R hR hUR hRt hRR
  refine ⟨replaceUpperFloor_singleton_of_capped_winners (D k) hR hUR hRt hRR hC,?_⟩
  intro i b
  rw [←replaceUpperFloor_native_outcome (D k) hR hUR hRt i
    (sourceLowerBroadcastAction (Early.bidCap row) b)
    (b.2.2.trans_lt (D k).cap_lt_floor) (b.2.2.trans_lt hUR)]
  exact hM i b

end Families
end Physical
end FCAppendix.Affine.Uniform07Finishing.Crossover
