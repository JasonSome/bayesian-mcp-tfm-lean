import FCAppendix.Affine.Uniform07Finishing.Native.EndogenousBoundaryMatch

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open StrictNative

variable {m : ℕ} [Nonempty (Fin m)]
variable (row : Uniform07.Row) (hm : 2≤ m) (hc : 1≤ Uniform07.capacity m)
  {R₀ R Λ : ℝ} (hR₀ : 0< R₀) (hUR₀ : Early.bidCap row< R₀)
  (hR₀t : R₀< Uniform07.cutoff row)
  (hR : 0< R) (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
  (hΛ : 0<Λ) (PL : ProbabilityMeasure (ℝ×JointAction 2))
  (hLvalue : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=
    (sourceLowerValueLaw row : Measure ℝ))
  (hLroute : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
    x.2.bid≤ Early.bidCap row ∧ x.2.routeCount=2)
  (α : ClassifiedContext m→ unitInterval) (hα : Measurable α)

local notation "Γ₀" => sourceNativeGame row hc R₀ Λ hΛ PL α hα
local notation "Γ" => sourceNativeGame row hc R Λ hΛ PL α hα
local notation "U" => Early.bidCap row

include hm hR₀ hUR₀ hR₀t hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_broadcast_IC_floor_replace (hRR₀ : R≤ R₀)
    (hIC : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
      actualBroadcastBestBelow Γ₀ R₀ x.1 x.2) :
    ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)),
      actualBroadcastBestBelow Γ R x.1 x.2 := by
  filter_upwards [hLroute,hIC] with x hx hbest
  intro u a ha hab
  have hx₀ : x.2.bid< R₀ := hx.1.trans_lt hUR₀
  have hxR : x.2.bid< R := hx.1.trans_lt hUR
  have ha₀ : a.bid< R₀ := hab.trans_le hRR₀
  rw [←sourceNativeGame_raw_lower_payoff_floor_invariant row hm hc
    hR₀ hUR₀ hR₀t hR hUR hRt hΛ PL hLvalue hLroute α hα u x.1 a ha₀ hab,
    ←sourceNativeGame_raw_lower_payoff_floor_invariant row hm hc
    hR₀ hUR₀ hR₀t hR hUR hRt hΛ PL hLvalue hLroute α hα u x.1 x.2 hx₀ hxR]
  exact hbest u a ha ha₀

include hm hR₀ hUR₀ hR₀t hR hUR hRt hLvalue hLroute in

theorem sourceNativeGame_positive_payoff_continuous_floor_replace
    (hpay : ∀ u : Fin m, ∀ z : ℝ×Icc (0:ℝ) U, 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) U=>
        (problem Γ₀ u).payoff w.1 (sourceLowerBroadcastAction U w.2)) z) :
    ∀ u : Fin m, ∀ z : ℝ×Icc (0:ℝ) U, 0<(z.2:ℝ) →
      ContinuousAt (fun w : ℝ×Icc (0:ℝ) U=>
        (problem Γ u).payoff w.1 (sourceLowerBroadcastAction U w.2)) z := by
  intro u z hz
  have he : (fun w : ℝ×Icc (0:ℝ) U=>
      (problem Γ u).payoff w.1 (sourceLowerBroadcastAction U w.2)) =
      (fun w : ℝ×Icc (0:ℝ) U=>
      (problem Γ₀ u).payoff w.1 (sourceLowerBroadcastAction U w.2)) := by
    funext w
    exact (sourceNativeGame_raw_lower_payoff_floor_invariant row hm hc
      hR₀ hUR₀ hR₀t hR hUR hRt hΛ PL hLvalue hLroute α hα u w.1
      (sourceLowerBroadcastAction U w.2)
      (w.2.2.2.trans_lt hUR₀) (w.2.2.2.trans_lt hUR)).symm
  rw [he]
  exact hpay u z hz

end FCAppendix.Affine.Uniform07Finishing
