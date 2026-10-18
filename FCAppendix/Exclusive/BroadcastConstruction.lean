import FCAppendix.Exclusive.CanonicalPolicy
import FCAppendix.Exclusive.BroadcastCapacity
import FCAppendix.Game.PosteriorFeasible

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction

open MeasureTheory ProbabilityTheory Game Set Filter Exclusive
open scoped ProbabilityTheory

def pureAction (n : ℕ) (E : Set ℝ) (b : ℝ → ℝ) (v : ℝ) : JointAction n := by
  classical
  exact if v ∈ E then ⟨max (b v) 0, le_max_right _ _, n, le_rfl⟩ else Interim.abstain n

theorem measurable_pureAction (n : ℕ) {E : Set ℝ} (hE : MeasurableSet E)
    {b : ℝ → ℝ} (hb : Measurable b) : Measurable (pureAction n E b) := by
  classical
  unfold pureAction
  apply Measurable.ite hE _ measurable_const
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  exact ((hb.max measurable_const).prodMk measurable_const).comap_le

def game (m n c : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (policy : LocalPolicy m c unitInterval)
    (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)) :
    FiniteGame m n c unitInterval where
  F := F
  hF := inferInstance
  σ := Kernel.deterministic (pureAction n E b) (measurable_pureAction n hE hb)
  hσ := inferInstance
  seedLaw := volume
  hseed := inferInstance
  policy := fun _ => policy
  policy_measurable := fun _ => hpolicy
  A := A
  G := G
  g := g
  g_nonneg := hg

variable {m n c : ℕ} {F : Measure ℝ} [IsProbabilityMeasure F]
  {E : Set ℝ} (hE : MeasurableSet E) {b : ℝ → ℝ} (hb : Measurable b)
  (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
  (policy : LocalPolicy m c unitInterval)
  (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val))

local notation "Γ" => game m n c F E hE b hb A G g hg policy hpolicy

theorem value_action_law : (Γ).F ⊗ₘ (Γ).σ =
    F.map (fun v => (v, pureAction n E b v)) :=
  Measure.compProd_deterministic (measurable_pureAction n hE hb)

theorem pureAction_active {v : ℝ} (hv : v ∈ E) (hvpos : 0 < b v) :
    (pureAction n E b v).bid = b v ∧ (pureAction n E b v).routeCount = n := by
  simp only [pureAction, if_pos hv, max_eq_left hvpos.le, and_self]

theorem pureAction_inactive {v : ℝ} (hv : v ∉ E) :
    (pureAction n E b v).routeCount = 0 := by
  simp [pureAction, hv, Interim.abstain]

theorem broadcast_on (hpos : ∀ᵐ v ∂F, v ∈ E → 0 < b v) :
    ExclusiveBroadcastOn Γ E := by
  unfold ExclusiveBroadcastOn
  rw [value_action_law hE hb A G g hg policy hpolicy]
  apply (ae_map_iff ((measurable_id).prodMk (measurable_pureAction n hE hb)).aemeasurable ?_).mpr
  · filter_upwards [hpos] with v hv
    constructor
    · intro he
      have ha := pureAction_active (n := n) he (hv he)
      exact ⟨ha.1.symm ▸ hv he, ha.2⟩
    · exact pureAction_inactive
  · have hval : MeasurableSet {x : ℝ × JointAction n | x.1 ∈ E} := measurable_fst hE
    have hbid : MeasurableSet {x : ℝ × JointAction n | 0 < x.2.bid} :=
      measurableSet_lt measurable_const ((measurable_bid n).comp measurable_snd)
    have hn : MeasurableSet {x : ℝ × JointAction n | x.2.routeCount = n} :=
      measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const
    have hzero : MeasurableSet {x : ℝ × JointAction n | x.2.routeCount = 0} :=
      measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const
    simpa only [imp_iff_not_or, setOf_and, setOf_or, compl_setOf, not_not]
      using (hval.compl.union (hbid.inter hn)).inter (hval.union hzero)

theorem symmetric_at_list (j : Fin n) (L : LocalList m) :
    SymmetricAtList Γ L (seedLottery Γ j L) := by
  intro l
  rfl

theorem symmetric_on_path : SymmetricProposersOnPath Γ :=
  fun j => Eventually.of_forall (symmetric_at_list hE hb A G g hg policy hpolicy j)

theorem ae_profile_zero_or_full : ∀ᵐ d ∂userProfileLaw Γ,
    ∀ i, (d i).1.2.routeCount = 0 ∨ (d i).1.2.routeCount = n := by
  have ha : ∀ᵐ x ∂((Γ).F ⊗ₘ (Γ).σ), x.2.routeCount = 0 ∨ x.2.routeCount = n := by
    rw [value_action_law hE hb A G g hg policy hpolicy]
    apply (ae_map_iff ((measurable_id).prodMk (measurable_pureAction n hE hb)).aemeasurable ?_).mpr
    · exact Eventually.of_forall fun v => by
        by_cases hv : v ∈ E <;> simp [pureAction, hv, Interim.abstain]
    · exact (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd)
        measurable_const).union
        (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const)
  have hu : ∀ᵐ u ∂userLaw Γ, u.1.2.routeCount = 0 ∨ u.1.2.routeCount = n :=
    (measurePreserving_fst (μ := (Γ).F ⊗ₘ (Γ).σ) (ν := permLaw n)).quasiMeasurePreserving.ae ha
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

end FCAppendix.Bayes.ExclusiveConstruction
