import FCAppendix.Affine.Hybrid.Native02.ClosedUpperTransport
import FCAppendix.Affine.Hybrid.NativeLowStrictPrimitive

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open scoped BigOperators

def LowContextAgreement {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C D : ContextPolicy m c Seed) (d : ℝ) : Prop :=
  ∀ j X, NonnegativeList X.1 → ∀ s i b, X.1 i = some b → b ≤ d →
    (i ∈ C.select j X s ↔ i ∈ D.select j X s)

section ExactTransport
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma nonnegative_observe_realization (x : Realization m 2) (j : Fin 2) :
    NonnegativeList (observe x j) := by
  intro i
  by_cases hj : j ∈ x.recipients i
  · simpa [observe, hj, entryBid] using (x.action i).bid_nonneg
  · simp [observe, hj, entryBid]

theorem low_selection_iff_old (C D : ContextPolicy m c Seed)
    {d U R b : ℝ} (hdU : d ≤ U) (hUR : U < R) (hagree : LowContextAgreement C D d)
    (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) (hgap : NoGapEntries U R L)
    (s : Seed) (i : Fin m) (hi : L i = some b) (hb : b ≤ d) :
    i ∈ ClosedPolicy.selection C R j L s ↔ i ∈ D.selection U j L s := by
  have hbU : b ≤ U := hb.trans hdU
  have hbR : b < R := hbU.trans_lt hUR
  have hclow : lowerPart R L i ≠ none := by
    rw [lowerPart_some L i hi hbR]
    exact Option.some_ne_none b
  have holow : broadcastPart U L i ≠ none := by
    rw [broadcastPart_some L i hi hbU]
    exact Option.some_ne_none b
  rw [ClosedPolicy.factors C R j L s i hclow, D.factors U j L s i holow,
    observedClosedContext_eq_old_on_gap hUR j L hgap]
  exact hagree j (observedContext U j L)
    (NativeContinuation.nonnegative_observedContext U j L hL) s i b
    (broadcastPart_some L i hi hbU) hb

theorem low_inclusionCount_eq_old (C D : ContextPolicy m c Seed)
    {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R) (hagree : LowContextAgreement C D d)
    (x : Realization m 2) (hx : ∀ k, (x.action k).bid ≤ U ∨ R ≤ (x.action k).bid)
    (s : Fin 2 → Seed) (i : Fin m) (hi : (x.action i).bid ≤ d) :
    inclusionCount x (ClosedPolicy.localPolicy C R) s i =
      inclusionCount x (D.localPolicy U) s i := by
  rw [inclusionCount_eq_sum, inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ x.recipients i
  · have ho : observe x j i = some (x.action i).bid := by simp [observe, hj]
    have hh := low_selection_iff_old C D hdU hUR hagree j (observe x j)
      (nonnegative_observe_realization x j) (noGapEntries_observe x hx j) (s j) i ho hi
    change (if i ∈ ClosedPolicy.selection C R j (observe x j) (s j) then 1 else 0) =
      (if i ∈ D.selection U j (observe x j) (s j) then 1 else 0)
    simp only [hh]
  · have hn : observe x j i = none := by simp [observe, hj]
    have hclosed : i ∉ allocation x (ClosedPolicy.localPolicy C R) s j := by
      intro hin
      exact ((ClosedPolicy.localPolicy C R j (observe x j) (s j)).property.2 i hin) hn
    have hold : i ∉ allocation x (D.localPolicy U) s j := by
      intro hin
      exact ((D.localPolicy U j (observe x j) (s j)).property.2 i hin) hn
    simp only [if_neg hclosed, if_neg hold]

theorem low_focalCount_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (hagree : LowContextAgreement C D d)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (act : JointAction 2) (hb : act.bid ≤ d) :
    focalCount (ClosedPolicy.nativeGame C Γ R) i act =ᵐ[sampleLaw Γ]
      focalCount (D.nativeGame Γ U) i act := by
  filter_upwards [sample_noGap_support Γ U R hgap] with ω hω
  have hx : ∀ k, ((deviated i act ω).action k).bid ≤ U ∨
      R ≤ ((deviated i act ω).action k).bid := by
    intro k
    by_cases hk : k = i
    · subst k
      left
      simpa only [deviated_bid_self] using hb.trans hdU
    · simpa only [deviated_bid_other i k hk] using hω k
  apply Fin.ext
  exact low_inclusionCount_eq_old C D hdU hUR hagree (deviated i act ω) hx ω.1.2 i
    (by simpa only [deviated_bid_self] using hb)

theorem low_outcome_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (hagree : LowContextAgreement C D d)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (act : JointAction 2) (hb : act.bid ≤ d) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).outcome act =
      (problem (D.nativeGame Γ U) i).outcome act := by
  rw [problem_outcome, problem_outcome]
  exact CountLaw.ofMeasure_congr_ae (sampleLaw Γ) _ _
    (measurable_focalCount (ClosedPolicy.nativeGame C Γ R) i act)
    (measurable_focalCount (D.nativeGame Γ U) i act)
    (low_focalCount_eq_old C D Γ hdU hUR hagree hgap i act hb)

theorem low_payoff_eq_old (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (hagree : LowContextAgreement C D d)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (v : ℝ) (act : JointAction 2) (hb : act.bid ≤ d) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act =
      (problem (D.nativeGame Γ U) i).payoff v act := by
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).utility
      v act.bid Γ.g Γ.A Γ.G =
    ((problem (D.nativeGame Γ U) i).outcome act).utility v act.bid Γ.g Γ.A Γ.G
  rw [low_outcome_eq_old C D Γ hdU hUR hagree hgap i act hb]

theorem low_bestResponse_of_agreement (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {d U R v : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (hg : Γ.g = 0) (hagree : LowContextAgreement C D d)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (star : JointAction 2) (hb : star.bid ≤ d) (hv : v ≤ d)
    (hbest : (problem (D.nativeGame Γ U) i).BestResponse v star) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).BestResponse v star := by
  have hstar := low_payoff_eq_old C D Γ hdU hUR hagree hgap i v star hb
  have hn : 0 ≤ (problem (D.nativeGame Γ U) i).payoff v star := by
    simpa only [Interim.Problem.payoff_abstain] using hbest (Interim.abstain 2)
  intro act
  by_cases had : act.bid ≤ d
  · rw [low_payoff_eq_old C D Γ hdU hUR hagree hgap i v act had, hstar]
    exact hbest act
  · have hav : v ≤ act.bid := hv.trans (le_of_not_ge had)
    exact (NativeLowIncentives.payoff_nonpos_of_value_le_bid
      (ClosedPolicy.nativeGame C Γ R) hg i v act hav).trans (hstar.symm ▸ hn)

theorem low_strict_singleton_of_agreement (C D : ContextPolicy m c Seed)
    (Γ : FiniteGame m 2 c Seed) {d U R v : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (hg : Γ.g = 0) (hagree : LowContextAgreement C D d)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (i : Fin m) (star : JointAction 2) (hb : star.bid ≤ d)
    (hv0 : 0 ≤ v) (hv : v ≤ d)
    (hstrict : ∀ act : JointAction 2, act.routeCount = 1 →
      (problem (D.nativeGame Γ U) i).payoff v act <
        (problem (D.nativeGame Γ U) i).payoff v star) :
    ∀ act : JointAction 2, act.routeCount = 1 →
      (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act <
        (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v star := by
  have hstar := low_payoff_eq_old C D Γ hdU hUR hagree hgap i v star hb
  let zeroSingleton : JointAction 2 := ⟨0, le_rfl, 1, by omega⟩
  have hz : 0 ≤ (problem (D.nativeGame Γ U) i).payoff v zeroSingleton := by
    change 0 ≤ ((problem (D.nativeGame Γ U) i).outcome zeroSingleton).utility
      v 0 Γ.g Γ.A Γ.G
    rw [hg, CountLaw.utility_eq]
    simpa only [zero_mul, sub_zero] using
      mul_nonneg hv0 ((problem (D.nativeGame Γ U) i).outcome zeroSingleton).success_nonneg
  have hpos : 0 < (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v star := by
    rw [hstar]
    exact hz.trans_lt (hstrict zeroSingleton rfl)
  intro act hk
  by_cases had : act.bid ≤ d
  · rw [low_payoff_eq_old C D Γ hdU hUR hagree hgap i v act had, hstar]
    exact hstrict act hk
  · exact (NativeLowIncentives.payoff_nonpos_of_value_le_bid
      (ClosedPolicy.nativeGame C Γ R) hg i v act (hv.trans (le_of_not_ge had))).trans_lt hpos

end ExactTransport

section ActualLow
open LowBody
open Existence.Distributional
variable {N c : ℕ} {d U R η : ℝ}

lemma lowJoint_value_bid_support (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A := LowValue d) mu) :
    ∀ᵐ x ∂(lowJoint mu pi : Measure (ℝ × JointAction 2)),
      0 ≤ x.1 ∧ x.1 ≤ d ∧ x.2.bid ≤ d := by
  change ∀ᵐ x ∂(pi.1 : Measure (LowValue d × LowValue d)).map
    (fun x => (x.1.1, lowBroadcast x.2)), _
  apply (measurableEmbedding_lowJointPoint d).ae_map_iff.mpr
  exact ae_of_all _ (fun x => ⟨x.1.property.1, x.1.property.2, x.2.property.2⟩)

theorem closed_population_low_actual_strict_one_route
    (hd : 0 ≤ d) (hdU : d ≤ U) (hUR : U < R)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h = 1)
    (Gref : Measure ℝ) [IsProbabilityMeasure Gref]
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (hη0 : 0 ≤ η) (hη1 : η < 1)
    (L : ActualAtomlessLowLimit N d ((1-η)/2) c
      (categoryLaw s a h hs ha hh hsum Gref) mu)
    (PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hactive : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      d < ((1+η)/2)*x.2.bid ∧ x.2.bid ≤ U ∧ x.2.routeCount = 2)
    (hupper : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), R ≤ x.2.bid ∧ x.2.routeCount = 1)
    (hell : 0 < (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0))
    (hsmall : (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (BothUnderflow c) ≤
      (CommonList.iid (categoryLaw s a h hs ha hh hsum Gref) N).prob (LocalUnderflow c 0)/4)
    (C : ContextPolicy (N+1) c unitInterval)
    (hagree : LowContextAgreement C
      (NativeContinuation.contextPolicy (m := N+1) ((1-η)/2)
        (by linarith : 0 < (1-η)/2) (by linarith : (1-η)/2 < 1) c) d)
    (i : Fin (N+1)) :
    let P := populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH
    let Gamma := PopulationGame.game (N+1) c P η hη0 hη1 U
    let game := ClosedPolicy.nativeGame C Gamma R
    ∀ᵐ x ∂(lowJoint mu L.joint : Measure (ℝ × JointAction 2)),
      (problem game i).BestResponse x.1 x.2 ∧
        ∀ act : JointAction 2, act.routeCount = 1 →
          (problem game i).payoff x.1 act < (problem game i).payoff x.1 x.2 := by
  let P := populationLaw s a h hs ha hh hsum (lowJoint mu L.joint) PA PH
  let Gamma := PopulationGame.game (N+1) c P η hη0 hη1 U
  let D := NativeContinuation.contextPolicy (m := N+1) ((1-η)/2)
    (by linarith : 0 < (1-η)/2) (by linarith : (1-η)/2 < 1) c
  have hhigh : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid ∧ x.2.routeCount = 1 :=
    hupper.mono (fun _ hx => ⟨hUR.trans_le hx.1, hx.2⟩)
  have hold := population_low_actual_strict_one_route hd hdU s a h hs ha hh hsum
    Gref mu hη0 hη1 L PA PH hactive hhigh hell hsmall i
  have hsupport := lowJoint_value_bid_support mu L.joint
  have hgap : ∀ᵐ x ∂Gamma.F ⊗ₘ Gamma.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid := by
    rw [PopulationGame.joint_law]
    exact population_noGap_support s a h U R hs ha hh hsum (lowJoint mu L.joint) PA PH
      (hsupport.mono (fun _ hx => hx.2.2.trans hdU))
      (hactive.mono (fun _ hx => hx.2.1)) (hupper.mono (fun _ hx => hx.1))
  filter_upwards [hold, hsupport] with x hx hsx
  refine ⟨low_bestResponse_of_agreement C D Gamma hdU hUR rfl hagree hgap i x.2
    hsx.2.2 hsx.2.1 hx.1, ?_⟩
  exact low_strict_singleton_of_agreement C D Gamma hdU hUR rfl hagree hgap i x.2
    hsx.2.2 hsx.1 hsx.2.1 hx.2

end ActualLow
end FCAppendix.Affine.Hybrid.Native02
