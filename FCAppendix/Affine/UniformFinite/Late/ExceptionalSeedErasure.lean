import FCAppendix.Affine.UniformFinite.Late.ExceptionalContinuation
import FCAppendix.Affine.UniformFinite.SeedErasure

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Exceptional
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Uniform05 Source ClippedResidual WeightedSampling
open scoped BigOperators

variable {M : ℕ} [NeZero M]

omit [NeZero M] in
theorem ordinary_erase (row : CountRow M) (S : Finset (Fin M))
    (b : Fin M → ℝ) (a : Fin M) :
    ordinary row (SeedErasure.erase S b) a=SeedErasure.erase S (ordinary row b a) := by
  funext j
  by_cases hja : j=a
  · subst j
    by_cases hj : a ∈ S <;> simp [ordinary,SeedErasure.erase,hj]
  · by_cases hj : j ∈ S <;> by_cases hl : j ∈ row.lower <;>
      simp [ordinary,SeedErasure.erase,lowerBids,hj,hl,hja]

omit [NeZero M] in
theorem ordinary_seed_bound (i : Row) (row : CountRow M) (S : Finset (Fin M))
    (b : Fin M → ℝ) (a : Fin M) (hS : ∀j ∈ S,b j ≤ t i/2) :
    ∀j ∈ S,ordinary row b a j ≤ t i/2 := by
  intro j hj
  by_cases hja : j=a
  · subst j
    simp only [ordinary,Function.update_self]
    linarith [t_pos i]
  · simpa only [ordinary,Function.update_of_ne hja] using
      SeedErasure.lower_seed_bound i row S b hS j hj

omit [NeZero M] in
theorem weight_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M)
    (hS : ∀j ∈ S,b j ≤ t i/2) :
    weight i G row (SeedErasure.erase S b) a=weight i G row b a := by
  unfold weight
  rw [ordinary_erase]
  exact SeedErasure.sourceWeights_erase i G row S (ordinary row b a)
    (ordinary_seed_bound i row S b a hS)

omit [NeZero M] in
theorem alpha_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M)
    (hS : ∀j ∈ S,b j ≤ t i/2) :
    alpha i G row (SeedErasure.erase S b) a=alpha i G row b a := by
  have hgate : (SeedErasure.erase S b a ≤ t i) ↔ b a ≤ t i := by
    by_cases ha : a ∈ S
    · have hb : b a ≤ t i := by linarith [hS a ha,t_pos i]
      simp [SeedErasure.erase,ha,hb,(t_pos i).le]
    · simp only [SeedErasure.erase,if_neg ha]
  simp only [alpha,ordinary_erase,
    SeedErasure.seedCount_erase i row S (ordinary row b a) (ordinary_seed_bound i row S b a hS),
    SeedErasure.rawAlpha_erase i G row S (ordinary row b a) (ordinary_seed_bound i row S b a hS),hgate]

omit [NeZero M] in

theorem actualRoot_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀j ∈ S,b j ≤ t i/2)
    (E : Finset (Fin M)) :
    Literal.root (xi i) (rootLo i G) (rootHi i G)
      (lowerBids row (SeedErasure.erase S b)) E (small row)=
    Literal.root (xi i) (rootLo i G) (rootHi i G)
      (lowerBids row b) E (small row) := by
  apply SeedErasure.root_congr
  intro z hz
  rw [SeedErasure.lowerBids_erase]
  exact SeedErasure.remainingDemand_erase S E _
    (SeedErasure.lower_seed_bound i row S b hS)
    (by linarith [t_pos i]) ((SeedErasure.seed_le_rootLo i G).trans hz.1)

omit [NeZero M] in
theorem lowerBids_nonnegative (row : CountRow M) (b : Fin M → ℝ)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j) : ∀j,0 ≤ lowerBids row b j := by
  intro j
  by_cases hj : j ∈ row.lower
  · simpa only [lowerBids_of_mem row b hj] using hb0 j hj
  · simp [lowerBids,hj]

omit [NeZero M] in
theorem ordinary_le_actual (row : CountRow M) (b : Fin M → ℝ)
    (a : Fin M) (hb0 : ∀j ∈ row.lower,0 ≤ b j) :
    ∀j,lowerBids row (ordinary row b a) j ≤ lowerBids row b j := by
  rw [lowerBids_ordinary]
  intro j
  by_cases hja : j=a
  · subst j
    simpa only [ordinary,Function.update_self] using lowerBids_nonnegative row b hb0 a
  · simp only [ordinary,Function.update_of_ne hja,le_refl]

theorem guarded_actual_high_count (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hapos : 0 < alpha i G row b a) :
    residual row 0+residual row 1 <
      (row.lower.filter (fun j => G.rejectionRoot < lowerBids row b j)).card := by
  have hr := (alpha_pos_data i G row b a hapos).2.2.2.2
  have hhigh := SeedRejection.raw_guard_high_count i G row (ordinary row b a) hr
  have hsub : row.lower.filter (fun j => G.rejectionRoot < lowerBids row (ordinary row b a) j) ⊆
      row.lower.filter (fun j => G.rejectionRoot < lowerBids row b j) := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
      (Finset.mem_filter.mp hj).2.trans_le (ordinary_le_actual row b a hb0 j)⟩
  exact hhigh.trans_le (Finset.card_le_card hsub)

theorem pure_selection_reject_seed (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hapos : 0 < alpha i G row b a) (s : Fin M) (hs : b s ≤ t i/2) :
    s ∉ ((lowerTemplate row).selection (kappa i) (lowerBids row b)).1 ∧
    s ∉ ((lowerTemplate row).selection (kappa i) (lowerBids row b)).2 := by
  apply SeedRejection.pure_selection_rejects (lowerTemplate row) (kappa_range i).2.le
    (lowerBids row b) (lowerBids_nonnegative row b hb0)
    (guarded_actual_high_count i G row b a hb0 hapos) s
  exact (SeedErasure.lower_seed_bound i row {s} b (by simpa using hs) s (by simp)).trans
    (SeedErasure.seed_le_rejectionRoot i G)

theorem pure_selection_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j) (hS : ∀j ∈ S,b j ≤ t i/2)
    (hapos : 0 < alpha i G row b a) :
    (lowerTemplate row).selection (kappa i) (lowerBids row (SeedErasure.erase S b))=
      (lowerTemplate row).selection (kappa i) (lowerBids row b) := by
  rw [SeedErasure.lowerBids_erase]
  apply SeedErasure.pure_selection_erase (lowerTemplate row)
    (kappa_range i).1.le (kappa_range i).2.le _ (lowerBids_nonnegative row b hb0)
  · intro j hj
    exact (SeedErasure.lower_seed_bound i row S b hS j hj).trans
      (SeedErasure.seed_le_rejectionRoot i G)
  · exact guarded_actual_high_count i G row b a hb0 hapos

theorem pureLaw_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j) (hS : ∀j ∈ S,b j ≤ t i/2)
    (hapos : 0 < alpha i G row b a) :
    UniformFinite.pureLaw i row (SeedErasure.erase S b)=UniformFinite.pureLaw i row b := by
  simp only [UniformFinite.pureLaw,pure_selection_erase i G row S b a hb0 hS hapos]

theorem guarded_private_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i)
    (hS : ∀j ∈ S,b j ≤ t i/2) (hapos : 0 < alpha i G row b a)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p) :
    let E := finalSet (imbalance row) ∅ p
    completion (xi i) (small row) (lowerBids row (SeedErasure.erase S b)) E=
      completion (xi i) (small row) (lowerBids row b) E ∧
    largeCompletion (xi i) (small row) (lowerBids row (SeedErasure.erase S b)) E=
      largeCompletion (xi i) (small row) (lowerBids row b) E ∧
    conditionalCompletion (xi i) (small row) (lowerBids row (SeedErasure.erase S b)) E=
      conditionalCompletion (xi i) (small row) (lowerBids row b) E := by
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b a ha hb hapos p hp
  let E := finalSet (imbalance row) ∅ p
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
  have hz0 : 0 < z := (rootBounds i G).1.trans_le hz.1
  have hdata := alpha_pos_data i G row b a hapos
  have hg := (guarded_new_state i G row b a ha hb hapos).1
  have hbase0 := lowerBids_nonnegative row b hb0
  have hseed := SeedErasure.lower_seed_bound i row S b hS
  have hs0 : 0 ≤ t i/2 := by linarith [t_pos i]
  have hsz : t i/2 ≤ z := (SeedErasure.seed_le_rootLo i G).trans hz.1
  have hb0' (j : Fin M) : 0 ≤ lowerBids row (SeedErasure.erase S b) j := by
    rw [SeedErasure.lowerBids_erase]
    by_cases hj : j ∈ S
    · simp only [SeedErasure.erase,if_pos hj,le_refl]
    · simpa only [SeedErasure.erase,if_neg hj] using hbase0 j
  have hbT' (j : Fin M) : lowerBids row (SeedErasure.erase S b) j ≤ t i := by
    rw [SeedErasure.lowerBids_erase]
    exact (SeedErasure.erase_le S _ hbase0 j).trans (hg.1 j)
  have hclear' : remainingDemand (xi i) (lowerBids row (SeedErasure.erase S b)) E z=(small row:ℝ) := by
    rw [SeedErasure.lowerBids_erase,SeedErasure.remainingDemand_erase S E _ hseed hs0 hsz]
    exact hclear
  have hp0 := completion_eq_literal (xi_range i).1 (xi_range i).2 hz0 (t_pos i).le
    (hdata.2.1.trans hz.1) (small row) (lowerBids row b) E hbase0 hg.1 hclear
  have hp1 := completion_eq_literal (xi_range i).1 (xi_range i).2 hz0 (t_pos i).le
    (hdata.2.1.trans hz.1) (small row) (lowerBids row (SeedErasure.erase S b)) E hb0' hbT' hclear'
  have hsm : smallMarginal (xi i) z (lowerBids row (SeedErasure.erase S b)) E=
      smallMarginal (xi i) z (lowerBids row b) E := by
    funext j
    by_cases hj : j ∈ E
    · simp only [smallMarginal,if_pos hj]
    · simp only [smallMarginal,if_neg hj,SeedErasure.lowerBids_erase]
      exact SeedErasure.exposure_erase S _ hseed hs0 hsz j
  have he : completion (xi i) (small row) (lowerBids row (SeedErasure.erase S b)) E=
      completion (xi i) (small row) (lowerBids row b) E := by
    simp only [hp1,hp0,Literal.completion,hsm]
  dsimp only [E] at he
  refine ⟨he,?_,?_⟩
  · simp only [largeCompletion,he]
  · simp only [conditionalCompletion,largeCompletion,he]

theorem guarded_private_reject_seed (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i) (hapos : 0 < alpha i G row b a)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p)
    (s : Fin M) (hs : b s ≤ t i/2) :
    let E := finalSet (imbalance row) ∅ p
    (∀T,(completion (xi i) (small row) (lowerBids row b) E).mass T ≠ 0 → s ∉ T) ∧
    (∀T,(largeCompletion (xi i) (small row) (lowerBids row b) E).mass T ≠ 0 → s ∉ T) := by
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b a ha hb hapos p hp
  let E := finalSet (imbalance row) ∅ p
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
  have hi := guarded_private_implements i G row b a ha hb0 hb hapos p hp
  have hsb : lowerBids row b s ≤ t i/2 := by
    by_cases hsl : s ∈ row.lower
    · simpa only [lowerBids_of_mem row b hsl] using hs
    · simp only [lowerBids_of_not_mem row b hsl]
      linarith [t_pos i]
  have hseedRoot : t i/2 ≤ z := (SeedErasure.seed_le_rootLo i G).trans hz.1
  have hsE : s ∉ E := by
    intro hmem
    have h := hsel s hmem
    have hsep : t i/2 < rootHi i G :=
      (SeedErasure.seed_le_rootLo i G).trans_lt (rootBounds i G).2.1
    linarith
  have hsmall : Proposer.marginal (completion (xi i) (small row) (lowerBids row b) E) s=0 := by
    change (completion (xi i) (small row) (lowerBids row b) E).prob (fun T => s ∈ T)=0
    rw [hi.1.2 s]
    change smallMarginal (xi i) z (lowerBids row b) E s = 0
    simp only [smallMarginal,if_neg hsE,exposure_zero (hsb.trans hseedRoot)]
  have hlarge : Proposer.marginal (largeCompletion (xi i) (small row) (lowerBids row b) E) s=0 := by
    change (largeCompletion (xi i) (small row) (lowerBids row b) E).prob (fun T => s ∈ T)=0
    rw [hi.2.1.2 s]
    change largeMarginal (xi i) z (lowerBids row b) E s = 0
    simp only [largeMarginal,if_neg hsE,exposure_zero (hsb.trans hseedRoot)]
  exact ⟨fun T hT => Literal.zero_marginal_omitted _ s hsmall T hT,
    fun T hT => Literal.zero_marginal_omitted _ s hlarge T hT⟩

theorem canonicalLaw_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i)
    (hS : ∀j ∈ S,b j ≤ t i/2) (hapos : 0 < alpha i G row b a) :
    canonicalLaw i G row (SeedErasure.erase S b) a=canonicalLaw i G row b a := by
  apply FiniteLaw.ext_expect
  intro f
  simp only [canonicalLaw,FiniteLaw.expect_map,WeightedSampling.expect_pairLaw,
    weight_erase i G row S b a hS]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (pathLaw (weight i G row b a) (imbalance row) ∅).mass p=0
  · simp only [hp,zero_mul]
  · have hpos : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p :=
      lt_of_le_of_ne (FiniteLaw.nonneg _ p) (Ne.symm hp)
    dsimp only
    rw [(guarded_private_erase i G row S b a ha hb0 hb hS hapos p hpos).2.2]

theorem continuationLaw_erase (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (hne : residual row 0 ≠ residual row 1)
    (S : Finset (Fin M)) (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i)
    (hS : ∀j ∈ S,b j ≤ t i/2) (hapos : 0 < alpha i G row b a) :
    continuationLaw i G row (SeedErasure.erase S b) a=continuationLaw i G row b a := by
  apply FiniteLaw.ext
  intro P
  simp only [continuationLaw,if_neg hne,FiniteLaw.mixture,
    alpha_erase i G row S b a hS,
    canonicalLaw_erase i G row S b a ha hb0 hb hS hapos,
    pureLaw_erase i G row S b a hb0 hS hapos]

end FCAppendix.Affine.UniformFinite.Late.Exceptional
