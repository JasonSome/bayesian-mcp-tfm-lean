import FCAppendix.Affine.UniformFinite.SeedPayoffRejection

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine
open Set MeasureTheory Filter Topology Classical
open scoped BigOperators

namespace FiniteSelector
variable {A : Type*} [Fintype A] [Nonempty A]

theorem select_eq_of_decrease (f g : A → ℝ) (hle : ∀ a, g a ≤ f a)
    (he : g (select f) = f (select f)) : select g = select f := by
  apply (select_eq_iff g (select f)).mpr
  have hf := (select_eq_iff f (select f)).mp rfl
  constructor
  · intro a
    rw [he]
    exact (hle a).trans (hf.1 a)
  · intro a ha
    rw [he]
    exact (hle a).trans_lt (hf.2 a ha)

end FiniteSelector

namespace UniformFinite.SeedErasure
open Uniform05 ClippedResidual WeightedSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def erase (S : Finset ι) (b : ι → ℝ) : ι → ℝ := fun a => if a ∈ S then 0 else b a

omit [Fintype ι] in
theorem erase_le (S : Finset ι) (b : ι → ℝ) (hb : ∀ a, 0 ≤ b a) :
    ∀ a, erase S b a ≤ b a := by
  intro a
  by_cases ha : a ∈ S <;> simp [erase, ha, hb a]

theorem pure_selection_erase (T : LowBody.PureTemplate ι) {κ z : ℝ}
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1) (b : ι → ℝ) (hb : ∀ a, 0 ≤ b a)
    (S : Finset ι) (hS : ∀ a ∈ S, b a ≤ z)
    (hhigh : T.residual₀+T.residual₁ < (T.support.filter (fun a => z < b a)).card) :
    T.selection κ (erase S b) = T.selection κ b := by
  let f : T.Candidate → ℝ := fun P => LowBody.CompleteInformation.potential κ b P.1.1 P.1.2
  let g : T.Candidate → ℝ := fun P => LowBody.CompleteInformation.potential κ (erase S b) P.1.1 P.1.2
  have hle (P : T.Candidate) : g P ≤ f P := by
    exact add_le_add (Finset.sum_le_sum (fun a _ => erase_le S b hb a))
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => erase_le S b hb a)) hκ)
  have hs : ∀ a ∈ S, a ∉ (T.selection κ b).1 ∪ (T.selection κ b).2 := by
    intro a ha
    obtain ⟨h0,h1⟩ := SeedRejection.pure_selection_rejects T hκ1 b hb hhigh a (hS a ha)
    simpa only [Finset.mem_union, not_or] using And.intro h0 h1
  have he : g (FiniteSelector.select f) = f (FiniteSelector.select f) := by
    change LowBody.CompleteInformation.potential κ (erase S b)
      (T.selection κ b).1 (T.selection κ b).2 =
      LowBody.CompleteInformation.potential κ b (T.selection κ b).1 (T.selection κ b).2
    unfold LowBody.CompleteInformation.potential
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      exact if_neg (fun h => hs a h ha)
    · congr 1
      apply Finset.sum_congr rfl
      intro a ha
      exact if_neg (fun h => hs a h (Finset.mem_union_left _ (Finset.mem_inter.mp ha).1))
  exact congrArg Subtype.val (FiniteSelector.select_eq_of_decrease f g hle he)

omit [Fintype ι] in
theorem exposure_erase {ξ z s : ℝ} (S : Finset ι) (b : ι → ℝ)
    (hS : ∀ a ∈ S, b a ≤ s) (hs : 0 ≤ s) (hsz : s ≤ z) (a : ι) :
    exposure ξ z (erase S b a) = exposure ξ z (b a) := by
  by_cases ha : a ∈ S
  · rw [erase, if_pos ha, exposure_zero (hs.trans hsz), exposure_zero ((hS a ha).trans hsz)]
  · simp only [erase, if_neg ha]

theorem remainingDemand_erase {ξ z s : ℝ} (S E : Finset ι) (b : ι → ℝ)
    (hS : ∀ a ∈ S, b a ≤ s) (hs : 0 ≤ s) (hsz : s ≤ z) :
    remainingDemand ξ (erase S b) E z = remainingDemand ξ b E z := by
  unfold remainingDemand
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ E
  · simp only [if_pos ha]
  · simp only [if_neg ha, exposure_erase S b hS hs hsz a]

theorem root_congr {ξ lo hi : ℝ} (b b' : ι → ℝ) (E : Finset ι) (d : ℕ)
    (he : ∀ z ∈ Icc lo hi, remainingDemand ξ b E z = remainingDemand ξ b' E z) :
    Literal.root ξ lo hi b E d = Literal.root ξ lo hi b' E d := by
  have hp : (fun z => z ∈ Icc lo hi ∧ remainingDemand ξ b E z = (d:ℝ)) =
      (fun z => z ∈ Icc lo hi ∧ remainingDemand ξ b' E z = (d:ℝ)) := by
    funext z
    apply propext
    by_cases hz : z ∈ Icc lo hi
    · simp only [hz, true_and, he z hz]
    · simp only [hz, false_and]
  unfold Literal.root
  change (if h : ∃ z, (fun z => z ∈ Icc lo hi ∧ remainingDemand ξ b E z = (d:ℝ)) z
      then h.choose else 0) = _
  rw [hp]

variable {M : ℕ}

theorem lowerBids_erase (row : Source.CountRow M) (S : Finset (Fin M)) (b : Fin M → ℝ) :
    Source.lowerBids row (erase S b) = erase S (Source.lowerBids row b) := by
  funext a
  by_cases ha : a ∈ S <;> by_cases hl : a ∈ row.lower <;> simp [Source.lowerBids, erase, ha, hl]

theorem seed_le_rootLo (i : Row) (G : RestrictedLaw i) : t i/2 ≤ Source.rootLo i G :=
  (SeedRejection.cutoffNeighborhood_gt_seed i).le.trans
    (SeedRejection.cutoffNeighborhood_lt_rootLo i G).le

theorem seed_le_rejectionRoot (i : Row) (G : RestrictedLaw i) : t i/2 ≤ G.rejectionRoot :=
  (SeedRejection.cutoffNeighborhood_gt_seed i).le.trans
    (SeedRejection.cutoffNeighborhood_lt_rejectionRoot i G).le

theorem lower_seed_bound (i : Row) (row : Source.CountRow M) (S : Finset (Fin M))
    (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    ∀ a ∈ S, Source.lowerBids row b a ≤ t i/2 := by
  intro a ha
  by_cases hl : a ∈ row.lower
  · simpa only [Source.lowerBids_of_mem row b hl] using hS a ha
  · simp only [Source.lowerBids_of_not_mem row b hl]
    linarith [t_pos i]

theorem sourceWeights_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    Source.sourceWeights i G row (erase S b) = Source.sourceWeights i G row b := by
  apply Subtype.ext
  funext a
  by_cases hl : a ∈ row.lower
  · simp only [Source.sourceWeights, if_pos hl, lawWeight]
    congr 1
    apply exposure_erase S b hS (by linarith [t_pos i])
    have hlo := seed_le_rootLo i G
    have ha := guardRadius_pos i
    dsimp [Source.rootLo] at hlo
    linarith
  · simp only [Source.sourceWeights, if_neg hl]

theorem sourceSlacks_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    Source.sourceSlacks i G row (erase S b) = Source.sourceSlacks i G row b := by
  have hlo : Source.lowDemand i G row (erase S b) = Source.lowDemand i G row b := by
    unfold Source.lowDemand
    rw [lowerBids_erase]
    apply Finset.sum_congr rfl
    intro a _
    exact exposure_erase S _ (lower_seed_bound i row S b hS)
      (by linarith [t_pos i]) (seed_le_rootLo i G) a
  have hhi : Source.highDemand i G row (erase S b) = Source.highDemand i G row b := by
    unfold Source.highDemand
    rw [lowerBids_erase]
    apply Finset.sum_congr rfl
    intro a _
    exact exposure_erase S _ (lower_seed_bound i row S b hS)
      (by linarith [t_pos i]) ((seed_le_rootLo i G).trans (Source.rootBounds i G).2.1.le) a
  have hre : Source.rejectionSum i G row (erase S b) = Source.rejectionSum i G row b := by
    unfold Source.rejectionSum
    rw [lowerBids_erase]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ S
    · rw [erase, if_pos ha, rejectionExposure_zero
        ((by linarith [t_pos i] : 0 ≤ t i/2).trans (seed_le_rejectionRoot i G)),
        rejectionExposure_zero ((lower_seed_bound i row S b hS a ha).trans (seed_le_rejectionRoot i G))]
    · simp only [erase, if_neg ha]
  simp only [Source.sourceSlacks, hlo, hhi, hre, sourceWeights_erase i G row S b hS]

theorem rawAlpha_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    Source.rawAlpha i G row (erase S b) = Source.rawAlpha i G row b := by
  simp only [Source.rawAlpha, sourceSlacks_erase i G row S b hS]

theorem seedCount_erase (i : Row) (row : Source.CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    Source.seedCount i row (erase S b) = Source.seedCount i row b := by
  unfold Source.seedCount
  congr 1
  ext a
  by_cases ha : a ∈ S
  · simp only [erase, if_pos ha, Finset.mem_filter,
      show (0:ℝ) ≤ t i/2 by linarith [t_pos i], hS a ha, and_true]
  · simp only [Finset.mem_filter, erase, if_neg ha]

theorem guardAlpha_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀ a ∈ S, b a ≤ t i/2) :
    Source.guardAlpha i G row (erase S b) = Source.guardAlpha i G row b := by
  simp only [Source.guardAlpha, seedCount_erase i row S b hS, rawAlpha_erase i G row S b hS]

theorem canonicalLaw_erase [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (S : Finset (Fin M)) (b : Fin M → ℝ)
    (hb : ∀ a, b a ∈ Icc (0:ℝ) (cap i)) (hS : ∀ a ∈ S, b a ≤ t i/2)
    (hraw : 0 < Source.rawAlpha i G row b) :
    canonicalLaw i G row (erase S b) = canonicalLaw i G row b := by
  have hr (E : Finset (Fin M)) :
      Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
        (Source.lowerBids row (erase S b)) E (Source.small row) =
      Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
        (Source.lowerBids row b) E (Source.small row) := by
    apply root_congr
    intro z hz
    rw [lowerBids_erase]
    exact remainingDemand_erase S E _ (lower_seed_bound i row S b hS)
      (by linarith [t_pos i]) ((seed_le_rootLo i G).trans hz.1)
  let x : SourceContinuity.Guarded i row :=
    ⟨(G, fun a => ⟨b a,hb a⟩),hraw⟩
  have hc (p : Path (Fin M) (Source.imbalance row)) :
      Literal.conditionalCompletion (xi i)
        (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
          (Source.lowerBids row (erase S b)) (finalSet (Source.imbalance row) ∅ p) (Source.small row))
        (Source.lowerBids row (erase S b)) (finalSet (Source.imbalance row) ∅ p) =
      Literal.conditionalCompletion (xi i)
        (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
          (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p) (Source.small row))
        (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p) := by
    rw [hr]
    have hz := (SourceContinuity.pathRoot_spec i row p x).1.1
    have hp : smallMarginal (xi i)
        (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
          (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p) (Source.small row))
        (Source.lowerBids row (erase S b)) (finalSet (Source.imbalance row) ∅ p) =
      smallMarginal (xi i)
        (Literal.root (xi i) (Source.rootLo i G) (Source.rootHi i G)
          (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p) (Source.small row))
        (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p) := by
      funext a
      unfold smallMarginal
      by_cases ha : a ∈ finalSet (Source.imbalance row) ∅ p
      · simp only [if_pos ha]
      · simp only [if_neg ha, lowerBids_erase]
        exact exposure_erase S _ (lower_seed_bound i row S b hS)
          (by linarith [t_pos i]) ((seed_le_rootLo i G).trans hz) a
    simp only [Literal.conditionalCompletion, Literal.largeCompletion, Literal.completion, hp]
  unfold canonicalLaw Literal.weightedExperiment
  rw [sourceWeights_erase i G row S b hS]
  exact congrArg (fun K : Path (Fin M) (Source.imbalance row)→FiniteLaw (Allocation M) =>
    (WeightedSampling.pairLaw
      (pathLaw (Source.sourceWeights i G row b) (Source.imbalance row) ∅) K).map
        (fun out=>orient row out.2)) (funext hc)

theorem pureLaw_erase [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (S : Finset (Fin M)) (b : Fin M → ℝ)
    (hb : ∀ a, 0 ≤ b a) (hS : ∀ a ∈ S, b a ≤ t i/2)
    (hraw : 0 < Source.rawAlpha i G row b) :
    pureLaw i row (erase S b) = pureLaw i row b := by
  unfold pureLaw
  rw [lowerBids_erase]
  congr 1
  apply pure_selection_erase (Source.lowerTemplate row) (kappa_range i).1.le (kappa_range i).2.le
  · intro a
    by_cases ha : a ∈ row.lower
    · simpa only [Source.lowerBids_of_mem row b ha] using hb a
    · simp [Source.lowerBids,ha]
  · intro a ha
    exact (lower_seed_bound i row S b hS a ha).trans (seed_le_rejectionRoot i G)
  · exact SeedRejection.raw_guard_high_count i G row b hraw

end UniformFinite.SeedErasure
end FCAppendix.Affine
