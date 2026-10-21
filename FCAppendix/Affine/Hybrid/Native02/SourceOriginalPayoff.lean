import FCAppendix.Affine.Hybrid.Native02.SourceRowFallback

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open scoped BigOperators

theorem closed_broadcast_count_categories {N c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R) (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U) = physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (act : JointAction 2) (hb : act.bid ≤ U)
    (hk : act.routeCount = 2) (f : Fin 3 → ℝ) :
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect f =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum μ) N).expect (fun kind =>
        ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
          (privateContextLaw C (NativeContinuation.reindexContext
            (NativeContinuation.focalIndex i).symm
            (FullContext.sourceRowContext kind low active act.bid)) i).expect f
          ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B)) := by
  rw [closed_broadcast_count_physicalRows C Γ hdU hUR hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i act hb hk]
  let F : (Fin N → RowRival) → ℝ := fun r =>
    (privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect f
  have hF : Measurable F := (measurable_privateContextLaw_expect C i f).comp
    (measurable_reindexedPhysicalContext i act.bid)
  let M := ∑ k : Fin 3, |f k|
  have hfbound (k : Fin 3) : |f k| ≤ M := by
    exact Finset.single_le_sum (f:=fun k : Fin 3 => |f k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  have hbound (r : Fin N → RowRival) : |F r| ≤ M :=
    ((privateContextLaw C (reindexedPhysicalContext i act.bid r) i).abs_expect_le f).trans
      ((privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect_le_const hfbound)
  rw [integral_physicalRowProfile s a h hs ha hh hsum μ B N F hF M
    (ae_of_all _ (fun p => hbound (physicalRowProfile N p)))]
  apply FiniteLaw.expect_congr
  intro kind
  let H := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    F (fun j => physicalRowPoint (kind j, p.1 j, p.2 j))
  have hm : Measurable H := hF.comp (measurable_pi_lambda _ (fun j =>
    measurable_physicalRowPoint.comp (measurable_const.prodMk
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)))))
  have hi : Integrable H ((Measure.pi (fun _ : Fin N => μ)).prod
      (Measure.pi (fun _ : Fin N => B))) :=
    Integrable.of_bound hm.aestronglyMeasurable M
      (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hbound _))
  calc
    _ = ∫ low : Fin N → ℝ, ∫ active : Fin N → ℝ, H (low,active)
        ∂Measure.pi (fun _ : Fin N => B) ∂Measure.pi (fun _ : Fin N => μ) :=
      integral_prod H hi
    _ = ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ, H (low,active)
        ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B) :=
      integral_integral_swap hi
    _ = _ := rfl

namespace FullContext

def physicalSourceUtility (N c : ℕ) (xi z L U s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] (v b : ℝ) : ℝ :=
  (CommonList.iid (categoryLaw s a h hs ha hh hsum μ) N).expect (fun kind =>
    ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
      activePhysicalPatternPayoff xi z L U c kind (v,b,low,active)
      ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B))

theorem closed_broadcast_payoff_sourceRows {N c : ℕ} {xi d L U R : ℝ}
    (hxi : 0 < xi) (hxih : xi ≤ 1/2) (z : ℝ)
    (Γ : FiniteGame (N+1) 2 c unitInterval)
    (hA : Γ.A = Schedule.affine 2 (1-2*xi) (by linarith) (by linarith))
    (hg : Γ.g = 0) (hseed : Γ.seedLaw = volume)
    (hd : 0 ≤ d) (hL : 0 < L) (hgap : d < (1-xi)*L) (hUR : U < R)
    (hfull : ∀ᵐ p ∂userProfileLaw Γ, p ∈ closedProfiles (N+1) R)
    (hpopgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hμnull : ∀ y, μ {y} = 0) (hBnull : ∀ y, B {y} = 0)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc 0 d) (hB : ∀ᵐ y ∂B, y ∈ Icc L U)
    (hrow : (userLaw Γ).map (physicalRow d U) = physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid ∈ Icc L U)
    (hk : act.routeCount = 2) :
    (problem (ClosedPolicy.nativeGame (contextPolicy hxi (by linarith) d L U z c μ) Γ R) i).payoff v act =
      physicalSourceUtility N c xi z L U s a h hs ha hh hsum μ B v act.bid := by
  have hxi1 : xi < 1 := by linarith
  let C : ContextPolicy (N+1) c unitInterval := contextPolicy hxi hxi1 d L U z c μ
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hdU : d ≤ U := hsep.le.trans (hb.1.trans hb.2)
  have htest : (fun k : Fin 3 => userPayoff v act.bid Γ.g Γ.A.charge Γ.G.charge k.val) =
      fun k => realizedPayoff (1-2*xi) v act.bid k.val := by
    funext k
    rw [hg, hA]
    fin_cases k <;> norm_num [userPayoff, Schedule.affine, successIndicator, realizedPayoff]
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect
    (fun k => userPayoff v act.bid Γ.g Γ.A.charge Γ.G.charge k.val) = _
  rw [htest, closed_broadcast_count_categories C Γ hdU hUR hseed hfull hpopgap
    s a h hs ha hh hsum μ B hrow i act hb.2 hk]
  apply FiniteLaw.expect_congr
  intro kind
  simpa only [Equiv.symm_symm, NativeContinuation.focalIndex_zero] using
    sourceRow_payoff_physical hxi hxi1 z c μ B hμnull hBnull hd hL hgap hμ hB
      kind v act.bid hb (NativeContinuation.focalIndex i).symm

end FullContext
end FCAppendix.Affine.Hybrid.Native02
