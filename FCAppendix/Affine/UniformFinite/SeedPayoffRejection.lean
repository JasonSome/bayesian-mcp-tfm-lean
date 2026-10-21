import FCAppendix.Affine.UniformFinite.SourcePayoffContinuity
import FCAppendix.Affine.UniformFinite.ActualAtomCrossing

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators

namespace SeedRejection
open Uniform05

private theorem pure_best_reply_rejects {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : LowBody.PureTemplate ι) {κ z : ℝ} (hκ : κ≤1)
    (b : ι→ℝ) (hb0 : ∀k,0≤ b k) (S R : Finset ι)
    (hS : S.card≤ T.residual₀) (hSs : S⊆T.support)
    (hR : R.card≤ T.residual₁) (_hRs : R⊆T.support)
    (hhigh : T.residual₀+T.residual₁<(T.support.filter (fun k=> z< b k)).card)
    (hN : ∀ D, D.card≤ T.residual₀ → D⊆T.support →
      LowBody.CompleteInformation.revenue κ b D R ≤
        LowBody.CompleteInformation.revenue κ b S R)
    (a : ι) (ha : b a≤ z) : a∉S := by
  intro haS
  have hcard : (S∪R).card<(T.support.filter (fun k=> z< b k)).card :=
    ((Finset.card_union_le S R).trans (Nat.add_le_add hS hR)).trans_lt hhigh
  obtain ⟨j,hj,hjSR⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hjT := (Finset.mem_filter.mp hj).1
  have hjz := (Finset.mem_filter.mp hj).2
  have hjS : j∉S := fun hjS => hjSR (Finset.mem_union_left _ hjS)
  have hjR : j∉R := fun hjR => hjSR (Finset.mem_union_right _ hjR)
  have hjE : j∉S.erase a := fun hjE => hjS (Finset.mem_of_mem_erase hjE)
  have hDcard : (insert j (S.erase a)).card≤ T.residual₀ := by
    rw [Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem haS]
    have hp : 0< S.card := Finset.card_pos.mpr ⟨a,haS⟩
    omega
  have hDsub : insert j (S.erase a)⊆T.support := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact hk ▸ hjT
    · exact hSs (Finset.mem_of_mem_erase hk)
  have hn := hN (insert j (S.erase a)) hDcard hDsub
  have hs := Finset.sum_erase_add S
    (fun k => if k∈R then κ*b k else b k) haS
  unfold LowBody.CompleteInformation.revenue at hn
  rw [Finset.sum_insert hjE, if_neg hjR] at hn
  have hreceipt : (if a∈R then κ*b a else b a)≤ b a := by
    split_ifs
    · exact mul_le_of_le_one_left (hb0 a) hκ
    · exact le_rfl
  linarith

theorem pure_selection_rejects {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : LowBody.PureTemplate ι) {κ z : ℝ} (hκ : κ≤1)
    (b : ι→ℝ) (hb0 : ∀k,0≤ b k)
    (hhigh : T.residual₀+T.residual₁<(T.support.filter (fun k=> z< b k)).card)
    (a : ι) (ha : b a≤ z) :
    a∉(T.selection κ b).1 ∧ a∉(T.selection κ b).2 := by
  have hf := T.selection_feasible κ b
  have hn := T.selection_nash κ b
  constructor
  · exact pure_best_reply_rejects T hκ b hb0 _ _ hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
      hhigh hn.1 a ha
  · let T' : LowBody.PureTemplate ι :=
      ⟨T.support, T.residual₁, T.residual₀⟩
    exact pure_best_reply_rejects T' hκ b hb0 _ _ hf.2.2.1 hf.2.2.2 hf.1 hf.2.1
      (by simpa [T', Nat.add_comm] using hhigh) hn.2 a ha

def cutoffNeighborhood (i : Row) : ℝ := (51:ℝ)/100*t i

lemma cutoffNeighborhood_gt_seed (i : Row) : t i/2< cutoffNeighborhood i := by
  unfold cutoffNeighborhood
  nlinarith [t_pos i]

lemma cutoffNeighborhood_lt_rootLo (i : Row) (G : RestrictedLaw i) :
    cutoffNeighborhood i< Source.rootLo i G := by
  have h := (le_max_right _ _).trans_lt (shifted_multiplier_guards i G)
  change (52:ℝ)/100*t i< Source.rootLo i G at h
  unfold cutoffNeighborhood
  nlinarith [t_pos i]

lemma cutoffNeighborhood_lt_rejectionRoot (i : Row) (G : RestrictedLaw i) :
    cutoffNeighborhood i< G.rejectionRoot := by
  have h := G.rejectionRoot_guards.1
  unfold cutoffNeighborhood
  nlinarith [t_pos i]

theorem raw_guard_high_count {M : ℕ} [NeZero M] (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (b : Fin M→ℝ)
    (ha : 0< Source.rawAlpha i G row b) :
    Source.residual row 0+Source.residual row 1 <
      (row.lower.filter (fun a=> G.rejectionRoot< Source.lowerBids row b a)).card := by
  have hMr : 0<(M:ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne M))
  have h := Source.rawAlpha_pos_slacks i G row b ha 3
  norm_num only [Source.sourceSlacks, Matrix.cons_val_succ, Matrix.cons_val_zero] at h
  have hg := (lt_div_iff₀ hMr).mp h
  have hstat := Literal.rejection_count (rejectionScale_pos i) (Source.lowerBids row b)
    (z:=G.rejectionRoot)
  have hrpos : 0< G.rejectionRoot := (rejectionLo_pos i).trans G.rejectionRoot_guards.1
  have he : Finset.univ.filter (fun a=> G.rejectionRoot< Source.lowerBids row b a) =
      row.lower.filter (fun a=> G.rejectionRoot< Source.lowerBids row b a) := by
    ext a
    by_cases hal : a∈row.lower
    · simp [hal]
    · simp [hal, Source.lowerBids, not_lt_of_ge hrpos.le]
  rw [he] at hstat
  have hslack : 0< Source.commonGuardMargin i*(M:ℝ) :=
    mul_pos (Source.common_guard_margin i) hMr
  have hreal : ((Source.residual row 0+Source.residual row 1:ℕ):ℝ) <
      ((row.lower.filter (fun a=> G.rejectionRoot< Source.lowerBids row b a)).card:ℝ) := by
    change Source.rejectionSum i G row b≤ _ at hstat
    simp only [Source.totalResidual, Nat.cast_add] at hg ⊢
    linarith
  exact_mod_cast hreal

theorem purePayoff_zero_near_seed {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (x : ℝ×SourceContinuity.State i M)
    (hraw : 0< SourceContinuity.rawWeight i row x.2)
    (hbid : SourceContinuity.bids i x.2 a≤ cutoffNeighborhood i) :
    SourceContinuity.purePayoff i row a x=0 := by
  have hr := pure_selection_rejects (Source.lowerTemplate row)
    (kappa_range i).2.le (Source.lowerBids row (SourceContinuity.bids i x.2))
    (fun k=> by
      by_cases hk : k∈row.lower
      · simpa only [Source.lowerBids_of_mem row _ hk] using
          (SourceContinuity.bids_bounds i x.2 k).1
      · simp [Source.lowerBids, hk])
    (raw_guard_high_count i x.2.1 row (SourceContinuity.bids i x.2) hraw) a
    (by simpa only [Source.lowerBids_of_mem row _ ha] using
      hbid.trans (cutoffNeighborhood_lt_rejectionRoot i x.2.1).le)
  simp [SourceContinuity.purePayoff, pairPayoff, Literal.firstCopy,
    Literal.duplicateCopy, WeightedSampling.indicator, hr.1, hr.2]

theorem canonicalPayoff_zero_near_seed {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (x : ℝ×SourceContinuity.State i M)
    (hraw : 0< SourceContinuity.rawWeight i row x.2)
    (hbid : SourceContinuity.bids i x.2 a≤ cutoffNeighborhood i) :
    SourceContinuity.canonicalPayoff i row a x=0 := by
  let y : SourceContinuity.Guarded i row := ⟨x.2,hraw⟩
  have hg := SourceContinuity.guarded_data i row y
  have hr := Source.rootBounds i x.2.1
  change (canonicalLaw i x.2.1 row (SourceContinuity.bids i x.2)).expect _=0
  rw [SourceContinuity.canonical_expected_eq_path i row a ha x.1 y]
  unfold FiniteLaw.expect
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : (WeightedSampling.pathLaw
      (Source.sourceWeights i x.2.1 row (SourceContinuity.bids i x.2))
      (Source.imbalance row) ∅).mass p=0
  · rw [hp, zero_mul]
  · have hp0 : 0<(WeightedSampling.pathLaw
        (Source.sourceWeights i x.2.1 row (SourceContinuity.bids i x.2))
        (Source.imbalance row) ∅).mass p :=
      lt_of_le_of_ne (FiniteLaw.nonneg _ p) (Ne.symm hp)
    have hpath := Literal.weighted_path_root
      (Source.lowerBids row (SourceContinuity.bids i x.2))
      (Source.sourceWeights i x.2.1 row (SourceContinuity.bids i x.2))
      (Source.small row) (Source.imbalance row) (xi_range i).1 (xi_range i).2
      (cap_pos i) hr.1 hr.2.1 hr.2.2 hg.2.1 hg.2.2 hg.1 p hp0
    have haLo : Source.lowerBids row (SourceContinuity.bids i x.2) a< Source.rootLo i x.2.1 := by
      rw [Source.lowerBids_of_mem row _ ha]
      exact hbid.trans_lt (cutoffNeighborhood_lt_rootLo i x.2.1)
    have haE : a∉WeightedSampling.finalSet (Source.imbalance row) ∅ p := by
      intro haE
      have he := hpath.2.2.2 a haE
      linarith [hr.2.1]
    have haZ : Source.lowerBids row (SourceContinuity.bids i x.2) a ≤
        Literal.root (xi i) (Source.rootLo i x.2.1) (Source.rootHi i x.2.1)
          (Source.lowerBids row (SourceContinuity.bids i x.2))
          (WeightedSampling.finalSet (Source.imbalance row) ∅ p) (Source.small row) :=
      haLo.le.trans hpath.2.1.1
    have he0 := exposure_zero (ξ := xi i) haZ
    dsimp only [y]
    simp only [Literal.pathPayoff, haE, if_false, he0]
    ring

theorem guarded_correction_zero_near_seed {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (x : ℝ×SourceContinuity.State i M)
    (hbid : SourceContinuity.bids i x.2 a≤ cutoffNeighborhood i) :
    Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2) *
      (SourceContinuity.canonicalPayoff i row a x - SourceContinuity.purePayoff i row a x)=0 := by
  by_cases hz : Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2)=0
  · rw [hz, zero_mul]
  have hp : 0< Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2) :=
    lt_of_le_of_ne (Source.guardAlpha_bounds i _ row _).1 (Ne.symm hz)
  have hr : 0< SourceContinuity.rawWeight i row x.2 := by
    dsimp only [SourceContinuity.rawWeight]
    unfold Source.guardAlpha at hp
    split_ifs at hp with hseed
    · exact False.elim (lt_irrefl _ hp)
    · exact hp
  rw [canonicalPayoff_zero_near_seed i row a ha x hr hbid,
    purePayoff_zero_near_seed i row a ha x hr hbid, sub_self, mul_zero]

theorem rowPayoff_eq_pure_near_seed {M : ℕ} [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (ha : a∈row.lower)
    (hne : Source.residual row 0≠Source.residual row 1)
    (x : ℝ×SourceContinuity.State i M)
    (hbid : SourceContinuity.bids i x.2 a≤ cutoffNeighborhood i) :
    rowPayoff i x.2.1 row x.1 (SourceContinuity.bids i x.2) a =
      SourceContinuity.purePayoff i row a x := by
  rw [rowPayoff_unequal i _ row _ _ a hne]
  have he := guarded_correction_zero_near_seed i row a ha x hbid
  change Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2) *
      (canonicalLaw i x.2.1 row (SourceContinuity.bids i x.2)).expect
        (pairPayoff (eta i) x.1 (SourceContinuity.bids i x.2 a) a) +
      (1-Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2)) *
        SourceContinuity.purePayoff i row a x = _
  change Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2) *
      (SourceContinuity.canonicalPayoff i row a x-SourceContinuity.purePayoff i row a x)=0 at he
  change Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2) *
      SourceContinuity.canonicalPayoff i row a x +
      (1-Source.guardAlpha i x.2.1 row (SourceContinuity.bids i x.2)) *
        SourceContinuity.purePayoff i row a x = _
  nlinarith

end SeedRejection
end FCAppendix.Affine.UniformFinite
