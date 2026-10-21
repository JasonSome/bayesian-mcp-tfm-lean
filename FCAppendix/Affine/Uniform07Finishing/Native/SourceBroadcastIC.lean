import FCAppendix.Affine.Uniform07Finishing.Native.ZeroBroadcastDomination

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative Weighted
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

def literalSourceBroadcastUtility (row : Uniform07.Row) (hc : 1 ≤ Uniform07.capacity m)
    (R Λ zG width ε : ℝ) (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (reference : Fin m) (v : ℝ) (a : JointAction 2) : ℝ :=
  ∫x : UserProfile m 2 × Equiv.Perm (Fin 2),
    sourcePhysicalCountTestOfRow row R Λ zG width ε reference a
      (fun r : Fin 3 => userPayoff v a.bid 0
        (Schedule.affine 2 (Uniform07.eta row) (Uniform07.eta_pos row).le
          (source_eta_lt_one row).le).charge
        (Schedule.once 2).charge r.val) x
    ∂(Measure.pi (fun _ : Fin m =>
      (sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).prod (permLaw 2))).prod
        (permLaw 2)

theorem literalSourceNativeGame_positive_broadcast_payoff_eq_physical
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (reference : Fin m) (v : ℝ) (a : JointAction 2) (ha0 : 0 < a.bid)
    (haR : a.bid < R) (ha2 : a.routeCount = 2) :
    (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) reference).payoff v a =
      literalSourceBroadcastUtility row hc R Λ zG width ε PL reference v a := by
  let α : ClassifiedContext m → unitInterval := literalSourceAlpha row Λ zG width ε
  have hα : Measurable α := measurable_literalSourceAlpha row hΛ zG width ε
  have hΛ0 := source_guard_multiplier_positive row hΛ
  let Γ := sourceNativeGame row hc R Λ hΛ0 PL α hα
  let q : Fin 3 → ℝ := fun r => userPayoff v a.bid 0
    (Schedule.affine 2 (Uniform07.eta row) (Uniform07.eta_pos row).le
      (source_eta_lt_one row).le).charge (Schedule.once 2).charge r.val
  unfold literalSourceNativeGame
  rw [completeSourceNativeGame_payoff]
  change ((problem Γ reference).outcome a).expect q = _
  rw [sourceNativeGame_broadcast_count_expect_physical row hm hc hR hUR hRt hΛ
    hguard hzG hε PL hLvalue hLroute hLatom reference a ha0 haR ha2 q]
  have huser : userLaw Γ =
      (sourcePopulation row m hc R PL : Measure (ℝ × JointAction 2)).prod (permLaw 2) :=
    sourceNativeGame_user_law row hm hc hR hRt hΛ0 PL hLvalue hLroute α hα
  dsimp only [Γ,α,hα] at huser
  simp only [userProfileLaw,huser,literalSourceBroadcastUtility,q]

theorem literalSourceNativeGame_common_broadcast_IC_of_physical
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst = (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (reference : Fin m)
    (hphysical : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), ∀ a : JointAction 2,
      0 < a.bid → a.routeCount = 2 → a.bid < R →
        literalSourceBroadcastUtility row hc R Λ zG width ε PL reference x.1 a ≤
          literalSourceBroadcastUtility row hc R Λ zG width ε PL reference x.1 x.2) :
    ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), ∀ i : Fin m, ∀ a : JointAction 2,
      a.routeCount = 2 → a.bid < R →
      (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff x.1 a ≤
        (problem (literalSourceNativeGame row hc R Λ zG width ε hΛ PL) i).payoff x.1 x.2 := by
  apply literalSourceNativeGame_common_broadcast_IC_of_positive_reference row hm hc
    hR hUR hRt hΛ hguard hzG hε PL hLvalue hLroute hLatom reference
  have hnonzero : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (hLatom 0)
  filter_upwards [hphysical,hLroute,hnonzero] with x hx hshape hnonzero
  intro a ha0 ha2 haR
  have hx0 : 0 < x.2.bid := lt_of_le_of_ne x.2.bid_nonneg (Ne.symm hnonzero)
  rw [literalSourceNativeGame_positive_broadcast_payoff_eq_physical row hm hc hR hUR hRt
      hΛ hguard hzG hε PL hLvalue hLroute hLatom reference x.1 a ha0 haR ha2,
    literalSourceNativeGame_positive_broadcast_payoff_eq_physical row hm hc hR hUR hRt
      hΛ hguard hzG hε PL hLvalue hLroute hLatom reference x.1 x.2 hx0
        (hshape.1.trans_lt hUR) hshape.2]
  exact hx a ha0 ha2 haR

end FCAppendix.Affine.Uniform07Finishing
