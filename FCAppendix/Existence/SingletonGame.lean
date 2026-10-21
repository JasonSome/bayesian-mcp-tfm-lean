import FCAppendix.Existence.SingletonPosterior
import FCAppendix.Existence.HighestBidPolicy
import FCAppendix.Game.CommonListSeeds

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter Classical

def pureAction (n : ℕ) (hn : 0 < n) (g : ℝ) (b : ℝ → ℝ) (v : ℝ) : JointAction n :=
  if g < v then ⟨max (b (v-g)) 0, le_max_right _ _, 1, hn⟩ else Interim.abstain n

theorem measurable_pureAction (n : ℕ) (hn : 0 < n) (g : ℝ)
    (b : ℝ → ℝ) (hb : Measurable b) : Measurable (pureAction n hn g b) := by
  unfold pureAction
  apply Measurable.ite measurableSet_Ioi _ measurable_const
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  exact (((hb.comp (measurable_id.sub_const g)).max measurable_const).prodMk
    measurable_const).comap_le

def singletonGame (m n c : ℕ) (hn : 0 < n)
    (F : Measure ℝ) [IsProbabilityMeasure F] (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g) : FiniteGame m n c Unit where
  F := F
  hF := inferInstance
  σ := Kernel.deterministic (pureAction n hn g b) (measurable_pureAction n hn g b hb)
  hσ := inferInstance
  seedLaw := Measure.dirac ()
  hseed := inferInstance
  policy := fun _ => HighestBid.localPolicy m c
  policy_measurable := fun _ => HighestBid.measurable_localPolicy m c
  A := A
  G := G
  g := g
  g_nonneg := hg

variable {m n c : ℕ} (hn : 0 < n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (b : ℝ → ℝ) (hb : Measurable b) (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)

local notation "Γ" => singletonGame m n c hn F b hb A G g hg

theorem singletonGame_value_action_law :
    (Γ).F ⊗ₘ (Γ).σ = F.map (fun v => (v, pureAction n hn g b v)) :=
  Measure.compProd_deterministic (measurable_pureAction n hn g b hb)

theorem pureAction_route_le_one (v : ℝ) : (pureAction n hn g b v).routeCount ≤ 1 := by
  by_cases hv : g < v <;> simp [pureAction, hv, Interim.abstain]

theorem singletonGame_profile_support :
    ∀ᵐ d ∂userProfileLaw Γ, d ∈ singletonProfiles m n := by
  have ha : ∀ᵐ x ∂((Γ).F ⊗ₘ (Γ).σ), x.2.routeCount ≤ 1 := by
    rw [singletonGame_value_action_law hn F b hb A G g hg]
    apply (ae_map_iff ((measurable_id).prodMk (measurable_pureAction n hn g b hb)).aemeasurable
      (measurableSet_le ((measurable_routeCount n).comp measurable_snd) measurable_const)).mpr
    exact ae_of_all _ (pureAction_route_le_one hn b g)
  have hu : ∀ᵐ u ∂userLaw Γ, u.1.2.routeCount ≤ 1 :=
    (measurePreserving_fst (μ := (Γ).F ⊗ₘ (Γ).σ) (ν := permLaw n)).quasiMeasurePreserving.ae ha
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) i).quasiMeasurePreserving.ae hu

def gamePosterior : PosteriorSystem Γ :=
  singletonPosterior Γ hn (singletonGame_profile_support hn F b hb A G g hg)

theorem singletonGame_proposer_optimal :
    PosteriorProposerOptimalAE Γ (gamePosterior hn F b hb A G g hg) := by
  intro j L hL
  have hr := singletonPosterior_receipts Γ hn
    (singletonGame_profile_support hn F b hb A G g hg) j L hL
  change ∀ᵐ s ∂(Γ).seedLaw, Finite.Optimal c
    (beliefReceipts (Γ).A (posteriorCountBelief Γ
      (singletonPosterior Γ hn (singletonGame_profile_support hn F b hb A G g hg)) j L) L)
    ((Γ).policy j L s).val
  rw [hr]
  exact ae_of_all _ fun _ => HighestBid.selection_optimal L c

theorem singletonGame_symmetric_at_list (j : Fin n) (L : LocalList m) :
    SymmetricAtList Γ L (seedLottery Γ j L) := fun _ => rfl

end FCAppendix.Bayes.SingletonConstruction
