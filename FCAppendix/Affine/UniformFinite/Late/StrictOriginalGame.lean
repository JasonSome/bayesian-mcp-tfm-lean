import FCAppendix.Affine.UniformFinite.OriginalPopulation
import FCAppendix.Affine.UniformFinite.Late.StrictAllocation

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.StrictOriginal
open MeasureTheory ProbabilityTheory Bayes Game Set Filter Classical
open Uniform05
open scoped BigOperators

variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

def game (E : ExactRestrictedLaw i M) (H : OriginalPopulation.UpperPriorityLaw i R) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  Strict.constructedGame i E.law (OriginalPopulation.seedLaw E)
    (OriginalPopulation.primitiveGame E H) R

theorem original_fields (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    (game E H).F=(OriginalPopulation.primitiveGame E H).F ∧
    (game E H).σ=(OriginalPopulation.primitiveGame E H).σ ∧
    (game E H).seedLaw=(OriginalPopulation.primitiveGame E H).seedLaw ∧
    (game E H).A=(OriginalPopulation.primitiveGame E H).A ∧
    (game E H).G=(OriginalPopulation.primitiveGame E H).G ∧
    (game E H).g=(OriginalPopulation.primitiveGame E H).g := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem original_userLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    userLaw (game E H)=userLaw (OriginalPopulation.primitiveGame E H) := rfl

theorem original_backgroundLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    backgroundLaw (game E H)=backgroundLaw (OriginalPopulation.primitiveGame E H) := rfl

theorem original_sampleLaw (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    sampleLaw (game E H)=sampleLaw (OriginalPopulation.primitiveGame E H) := rfl

theorem game_value (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    (game E H).F=OriginalPopulation.uniformValue := rfl

theorem game_joint (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    (game E H).F⊗ₘ(game E H).σ=(OriginalPopulation.fullLaw E H : Measure (ℝ×JointAction 2)) := rfl

theorem game_lower_kernel (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (v : Value i) :
    (game E H).σ v=(E.sigma v).map (fun q => OriginalPopulation.lowerAction i (v,q)) :=
  OriginalPopulation.fullKernel_at_lower E H v

theorem game_nonlower_kernel (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (v : ℝ) (hv : v∉Icc (0:ℝ) (t i)) :
    (game E H).σ v=H.sigma v := by
  change OriginalPopulation.fullKernel E H v=H.sigma v
  simp only [OriginalPopulation.fullKernel,Kernel.piecewise_apply,if_neg hv]

omit [NeZero M] in
theorem fullLaw_strong (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐx ∂(OriginalPopulation.fullLaw E H : Measure (ℝ×JointAction 2)),
      (x.2.bid≤ cap i ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1) := by
  rw [OriginalPopulation.fullLaw_mixture]
  apply ae_add_measure_iff.mpr
  exact ⟨Measure.ae_smul_measure
      ((OriginalPopulation.lowerJoint_shape E).mono (fun _ h => Or.inl h)) _,
    Measure.ae_smul_measure
      ((OriginalPopulation.upperJoint_shape H).mono (fun _ h => Or.inr h)) _⟩

theorem game_profile_support (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) :
    ∀ᵐd ∂userProfileLaw (game E H),d∈Strict.strongProfiles M (cap i) R := by
  have hj : ∀ᵐx ∂(game E H).F⊗ₘ(game E H).σ,
      (x.2.bid≤ cap i ∧ x.2.routeCount=2) ∨ (R≤ x.2.bid ∧ x.2.routeCount=1) := fullLaw_strong E H
  have hu : ∀ᵐu ∂userLaw (game E H),
      (u.1.2.bid≤ cap i ∧ u.1.2.routeCount=2) ∨ (R≤ u.1.2.bid ∧ u.1.2.routeCount=1) :=
    (measurePreserving_fst (μ:=(game E H).F⊗ₘ(game E H).σ) (ν:=permLaw 2)).quasiMeasurePreserving.ae hj
  exact ae_all_iff.mpr (fun a =>
    (measurePreserving_eval (fun _ : Fin M => userLaw (game E H)) a).quasiMeasurePreserving.ae hu)

def belief (E : ExactRestrictedLaw i M) (H : OriginalPopulation.UpperPriorityLaw i R) :
    PosteriorSystem (game E H) := Strict.posterior (game E H) (game_profile_support E H)

theorem belief_support (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) :
    ∀ᵐd ∂(belief E H).posterior j L,
      observe (drawsRealization d) j=L ∧ d∈Strict.profiles M R :=
  Strict.posterior_support (game E H) (cap_pos i).le hR (game_profile_support E H) j L hL

theorem belief_exceptional (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R)
    (j : Fin 2) (L : LocalList M) (a : Fin M) (b : ℝ) (ha : L a=some b)
    (hUb : cap i< b) (hbR : b< R) :
    (belief E H).posterior j L=Measure.dirac (Strict.completedProfile M R j L) :=
  Strict.posterior_exceptional (game E H) (game_profile_support E H) j L a b ha hUb hbR

theorem game_proposer_optimal (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀j L,FeasibleObservedList j L → ∀s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (game E H).A
          (posteriorCountBelief (game E H) (belief E H) j L) L)
        ((game E H).policy j L s).val :=
  Strict.constructed_proposer_optimal i E.law (OriginalPopulation.seedLaw E)
    (OriginalPopulation.primitiveGame E H) rfl hR rfl (game_profile_support E H)

theorem policy_on_original_list (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R)
    (j : Fin 2) (L : LocalList M) (hL : Strict.OriginalList (cap i) R L) (s : unitInterval) :
    ((game E H).policy j L s).val=((OriginalPopulation.game E H).policy j L s).val :=
  Strict.constructed_selection_on_path i E.law (OriginalPopulation.seedLaw E) hR j L hL s

theorem policy_original_ae (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐd ∂userProfileLaw (game E H),∀j : Fin 2,∀s : unitInterval,
      ((game E H).policy j (observe (drawsRealization d) j) s).val=
        ((OriginalPopulation.game E H).policy j (observe (drawsRealization d) j) s).val := by
  filter_upwards [game_profile_support E H] with d hd
  intro j s
  exact policy_on_original_list E H hR j _ (Strict.original_observe d hd j) s

theorem allocation_original_ae (E : ExactRestrictedLaw i M)
    (H : OriginalPopulation.UpperPriorityLaw i R) (hR : cap i< R) :
    ∀ᵐd ∂userProfileLaw (game E H),∀s : Fin 2→ unitInterval,
      allocation (drawsRealization d) (game E H).policy s=
        allocation (drawsRealization d) (OriginalPopulation.game E H).policy s := by
  filter_upwards [policy_original_ae E H hR] with d hd
  intro s
  funext j
  exact hd j (s j)

end FCAppendix.Affine.UniformFinite.Late.StrictOriginal
