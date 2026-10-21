import FCAppendix.AppendixRepair.GeneralLow.HigherPosterior

noncomputable section
namespace FCAppendix.Appendix08.GeneralLow.HigherReceipts
open MeasureTheory ProbabilityTheory Game Bayes Set Filter
open HigherPosterior HigherPolicy
open scoped BigOperators

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem countBelief_congr (Γ : FiniteGame m 2 c Seed) (B D : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m) (h : B.posterior j L = D.posterior j L) :
    posteriorCountBelief Γ B j L = posteriorCountBelief Γ D j L := by
  funext i
  apply FiniteLaw.ext
  intro r
  simp only [posteriorCountBelief, FiniteLaw.ofMeasure_mass, posteriorBackground, h]

theorem other_eq (j : Fin 2) : Information.other j = Affine.Hybrid.otherProposer j := rfl

theorem opposite_high_card (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ) (j : Fin 2) :
    (highSet C (observe (drawsRealization x) (Affine.Hybrid.otherProposer j))).card =
      otherHigh C (observe (drawsRealization x) j) := by
  have hc := Information.local_counts_correct C (kind C x) (drawsRealization x)
    (correct_kind C x) (routes_kind C d κ x hx)
  have hp := Information.reconstruct_other_private C (kind C x) (drawsRealization x)
    (correct_kind C x) (routes_kind C d κ x hx) j
  rw [other_eq] at hp
  have hs := localCounts_sum C (observe (drawsRealization x) j)
  rw [highSet_card, (hc (Affine.Hybrid.otherProposer j)).2.1,
    (hc (Affine.Hybrid.otherProposer j)).2.2, hp]
  unfold otherHigh
  rw [← (hc j).2.1]
  omega

theorem decoded_low_opposite (C : Information.Classifier) (c : ℕ) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ) (j : Fin 2) :
    Information.part C 0 (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) =
      Information.part C 0 (observe (drawsRealization x) j) ∧
    Information.ownResidual C c (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) =
      Information.otherResidual C c (observe (drawsRealization x) j) ∧
    Information.otherResidual C c (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) =
      Information.ownResidual C c (observe (drawsRealization x) j) := by
  have hc := correct_kind C x
  have hr := routes_kind C d κ x hx
  have hj := Information.residuals_correct C c (kind C x) (drawsRealization x) hc hr j
  have ho := Information.residuals_correct C c (kind C x) (drawsRealization x) hc hr
    (Affine.Hybrid.otherProposer j)
  refine ⟨(Information.common_broadcast_parts C (kind C x) (drawsRealization x) hc hr
    (Affine.Hybrid.otherProposer j) j).1, ?_, ?_⟩
  · rw [ho.1, hj.2, other_eq]
  · rw [ho.2, hj.1, other_eq, Affine.Hybrid.otherProposer_other]

theorem listed_bid (x : UserProfile m 2) (j : Fin 2) (i : Fin m) (b : ℝ)
    (hi : observe (drawsRealization x) j i = some b) : (x i).1.2.bid = b := by
  have hj : j ∈ (drawsRealization x).recipients i := by
    by_contra hn
    simp only [observe, if_neg hn] at hi
    cases hi
  change ((drawsRealization x).action i).bid = b
  apply Option.some.inj
  simpa only [observe, if_pos hj] using hi

theorem private_other_absent (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ)
    (j : Fin 2) (i : Fin m) (b : ℝ)
    (hi : observe (drawsRealization x) j i = some b) (hb : C.label b = 2) :
    observe (drawsRealization x) (Affine.Hybrid.otherProposer j) i = none := by
  have hj : j ∈ (drawsRealization x).recipients i := by
    by_contra hn
    simp only [observe, if_neg hn] at hi
    cases hi
  have hbid := listed_bid x j i b hi
  have hr : (x i).1.2.routeCount = 1 := by
    simpa only [hbid, hb, if_true] using (hx i).2
  have hc : ((drawsRealization x).recipients i).card = 1 := by
    rw [(drawsRealization x).chosen_size]
    exact hr
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hc
  have hlj : l = j := by
    rw [hl] at hj
    exact (Finset.mem_singleton.mp hj).symm
  rw [hlj] at hl
  simp only [observe, hl, Finset.mem_singleton, Affine.Hybrid.otherProposer_ne, if_false]

theorem active_other_visible (C : Information.Classifier) (d κ : ℝ)
    (x : UserProfile m 2) (hx : x ∈ profiles C d κ)
    (j : Fin 2) (i : Fin m) (b : ℝ)
    (hi : observe (drawsRealization x) j i = some b) (hb : C.label b = 1) :
    observe (drawsRealization x) (Affine.Hybrid.otherProposer j) i = some b := by
  have hbid := listed_bid x j i b hi
  have hr : (x i).1.2.routeCount = 2 := by
    simpa only [hbid, hb, show (1 : Fin 3) ≠ 2 by decide, if_false] using (hx i).2
  simp [observe, drawsRealization, hr, Affine.Hybrid.firstK_full_two, hbid]

theorem private_mean_of_support (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (C : Information.Classifier) (d κ : ℝ) (j : Fin 2) (L : LocalList m)
    (hsupport : ∀ᵐ x ∂B.posterior j L,
      observe (drawsRealization x) j = L ∧ x ∈ profiles C d κ)
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : C.label b = 2) :
    Affine.Hybrid.posteriorOtherMean Γ B j L i = 0 := by
  classical
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [hsupport] with x hx
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  have ho : observe (drawsRealization x) j i = some b := by rw [hx.1, hi]
  have hn := private_other_absent C d κ x hx.2 j i b ho hb
  have hnot : i ∉ allocation (drawsRealization x) Γ.policy z (Affine.Hybrid.otherProposer j) := by
    intro hin
    exact ((Γ.policy (Affine.Hybrid.otherProposer j)
      (observe (drawsRealization x) (Affine.Hybrid.otherProposer j))
      (z (Affine.Hybrid.otherProposer j))).property.2 i hin) hn
  change ((otherInclusionCount Γ j i (x,z)).val : ℝ) = 0
  rw [Affine.Hybrid.otherInclusionCount_two, if_neg hnot]
  norm_num

theorem mean_of_private_posterior (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m)
    (hB : B.posterior j L = Measure.dirac (privateProfile j L)) (i : Fin m) :
    Affine.Hybrid.posteriorOtherMean Γ B j L i = 0 := by
  classical
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral, hB, integral_dirac]
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  have hn : i ∉ allocation (drawsRealization (privateProfile j L)) Γ.policy z
      (Affine.Hybrid.otherProposer j) := by
    intro hin
    exact ((Γ.policy (Affine.Hybrid.otherProposer j)
      (observe (drawsRealization (privateProfile j L)) (Affine.Hybrid.otherProposer j))
      (z (Affine.Hybrid.otherProposer j))).property.2 i hin)
      (privateProfile_other_absent j L i)
  change ((otherInclusionCount Γ j i (privateProfile j L, z)).val : ℝ) = 0
  rw [Affine.Hybrid.otherInclusionCount_two, if_neg hn]
  norm_num

theorem receipts_of_private_posterior (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m)
    (hB : B.posterior j L = Measure.dirac (privateProfile j L)) :
    beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L = fun i => entryBid (L i) := by
  funext i
  cases hi : L i with
  | none => simp only [beliefReceipts, hi, entryBid]
  | some b =>
      simp only [beliefReceipts, hi, entryBid]
      rw [Affine.Hybrid.posterior_affine_receipt Γ B η hη0 hη1 hA,
        mean_of_private_posterior Γ B j L hB i]
      ring

def HighFactors (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier) (d κ : ℝ)
    (HC : HigherSelector (m := m) C c Seed) : Prop :=
  ∀ j L, CompatibleList C d κ L → ∀ z i, i ∈ highSet C L →
    (i ∈ (Γ.policy j L z).val ↔ i ∈ highSelection C κ c HC j L z)

theorem posterior_private_mean (Γ : FiniteGame m 2 c Seed) (C : Information.Classifier)
    (d κ R : ℝ) (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d κ L) (i : Fin m) (b : ℝ)
    (hi : L i = some b) (hb : C.label b = 2) :
    Affine.Hybrid.posteriorOtherMean Γ (posterior Γ C d κ R hfull) j L i = 0 := by
  classical
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [posterior_support Γ C d κ R hR hRC hdR hfull j L hL hcomp] with x hx
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro z
  have ho : observe (drawsRealization x) j i = some b := by rw [hx.1, hi]
  have hn := private_other_absent C d κ x hx.2 j i b ho hb
  have hnot : i ∉ allocation (drawsRealization x) Γ.policy z (Affine.Hybrid.otherProposer j) := by
    intro hin
    exact ((Γ.policy (Affine.Hybrid.otherProposer j)
      (observe (drawsRealization x) (Affine.Hybrid.otherProposer j))
      (z (Affine.Hybrid.otherProposer j))).property.2 i hin) hn
  change ((otherInclusionCount Γ j i (x, z)).val : ℝ) = 0
  rw [Affine.Hybrid.otherInclusionCount_two, if_neg hnot]
  norm_num

theorem posterior_active_mean_of_spare (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (d κ R : ℝ)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (HC : HigherSelector (m := m) C c Seed) (hfactor : HighFactors Γ C d κ HC)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d κ L) (hspare : otherHigh C L < c)
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : C.label b = 1) :
    Affine.Hybrid.posteriorOtherMean Γ (posterior Γ C d κ R hfull) j L i = 1 := by
  classical
  rw [Affine.Hybrid.posteriorOtherMean_eq_profile_integral]
  have he : ∀ᵐ x ∂(posterior Γ C d κ R hfull).posterior j L,
      (∫ z : Fin 2 → Seed, ((otherInclusionCount Γ j i (x, z)).val : ℝ)
        ∂Measure.pi (fun _ : Fin 2 => Γ.seedLaw)) = 1 := by
    filter_upwards [posterior_support Γ C d κ R hR hRC hdR hfull j L hL hcomp] with x hx
    have ho : observe (drawsRealization x) j i = some b := by rw [hx.1, hi]
    have hv := active_other_visible C d κ x hx.2 j i b ho hb
    have hhigh : i ∈ highSet C (observe (drawsRealization x) (Affine.Hybrid.otherProposer j)) := by
      apply (mem_highSet C _ i).mpr
      left
      simp [hv, Information.tag, hb]
    have hcap : (highSet C (observe (drawsRealization x)
        (Affine.Hybrid.otherProposer j))).card < c := by
      rw [opposite_high_card C d κ x hx.2 j, hx.1]
      exact hspare
    have hz (z : Fin 2 → Seed) : ((otherInclusionCount Γ j i (x, z)).val : ℝ) = 1 := by
      have hf := hfactor (Affine.Hybrid.otherProposer j)
        (observe (drawsRealization x) (Affine.Hybrid.otherProposer j))
        (observe_compatible C d κ x hx.2 _) (z (Affine.Hybrid.otherProposer j)) i hhigh
      rw [highSelection_eq_all C κ c HC _ _ _ hcap] at hf
      have hin : i ∈ allocation (drawsRealization x) Γ.policy z
          (Affine.Hybrid.otherProposer j) := hf.mpr hhigh
      rw [Affine.Hybrid.otherInclusionCount_two, if_pos hin]
      norm_num
    rw [integral_congr_ae (Eventually.of_forall hz)]
    simp
  rw [integral_congr_ae he]
  simp

theorem posterior_private_receipt (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (d κ R η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d κ L) (i : Fin m) (b : ℝ)
    (hi : L i = some b) (hb : C.label b = 2) :
    Finite.conditionalReceipt Γ.A
      (posteriorCountBelief Γ (posterior Γ C d κ R hfull) j L i) b = b := by
  rw [Affine.Hybrid.posterior_affine_receipt Γ _ η hη0 hη1 hA,
    posterior_private_mean Γ C d κ R hR hRC hdR hfull j L hL hcomp i b hi hb]
  ring

theorem posterior_active_receipt_of_spare (Γ : FiniteGame m 2 c Seed)
    (C : Information.Classifier) (d κ R η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (hκ : κ = (1 + η) / 2)
    (hR : 0 ≤ R) (hRC : C.label R = 2) (hdR : d < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ profiles C d κ)
    (HC : HigherSelector (m := m) C c Seed) (hfactor : HighFactors Γ C d κ HC)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (hcomp : CompatibleList C d κ L) (hspare : otherHigh C L < c)
    (i : Fin m) (b : ℝ) (hi : L i = some b) (hb : C.label b = 1) :
    Finite.conditionalReceipt Γ.A
      (posteriorCountBelief Γ (posterior Γ C d κ R hfull) j L i) b = κ*b := by
  rw [Affine.Hybrid.posterior_affine_receipt Γ _ η hη0 hη1 hA,
    posterior_active_mean_of_spare Γ C d κ R hR hRC hdR hfull HC hfactor
      j L hL hcomp hspare i b hi hb, hκ]
  ring

theorem posterior_mean_bounds (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m) (i : Fin m) :
    0 ≤ Affine.Hybrid.posteriorOtherMean Γ B j L i ∧
      Affine.Hybrid.posteriorOtherMean Γ B j L i ≤ 1 := by
  constructor
  · exact FiniteLaw.expect_nonneg _ (fun r => Nat.cast_nonneg r.val)
  · exact FiniteLaw.expect_le_const _ (fun r => by exact_mod_cast Nat.le_of_lt_succ r.isLt)

theorem affine_receipt_bounds (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hA : Γ.A = Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) (i : Fin m) (b : ℝ) (hb : 0 ≤ b) :
    ((1+η)/2)*b ≤ Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j L i) b ∧
      Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j L i) b ≤ b := by
  rw [Affine.Hybrid.posterior_affine_receipt Γ B η hη0 hη1 hA]
  obtain ⟨hp0, hp1⟩ := posterior_mean_bounds Γ B j L i
  have hξ : 0 ≤ (1-η)/2 := by linarith
  have hprod0 := mul_nonneg hb (mul_nonneg hξ hp0)
  have hprod1 := mul_nonneg hb (mul_nonneg hξ (sub_nonneg.mpr hp1))
  constructor <;> nlinarith

end FCAppendix.Appendix08.GeneralLow.HigherReceipts
