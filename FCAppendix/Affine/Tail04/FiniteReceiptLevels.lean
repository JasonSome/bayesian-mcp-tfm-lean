import FCAppendix.Finite.ReceiptOrder

noncomputable section
namespace FCAppendix.Affine.Tail04.FiniteReceiptLevels
open Set Classical
open scoped BigOperators

variable {J : Type*} [Fintype J] (c : ℕ) (r : J→ℝ)

theorem filter_card_of_upperSet (P : J→ Prop) (hpos : ∀ j,P j→0< r j)
    (hup : ∀ i j,P j→ r j≤ r i→ P i)
    (S : Finset J) (hS : Finite.Optimal c r S) :
    (S.filter P).card=min c (Finset.univ.filter P).card := by
  by_cases hsub : Finset.univ.filter P⊆S
  · have he : S.filter P=Finset.univ.filter P := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h => h.2,fun h => ⟨hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩),h⟩⟩
    rw [he,min_eq_right]
    exact (Finset.card_le_card hsub).trans hS.1
  · obtain ⟨j,hj,hnot⟩ := Finset.not_subset.mp hsub
    have hjP := (Finset.mem_filter.mp hj).2
    have hfill := Finite.optimal_fills c r S hS j hnot (hpos j hjP)
    have he : S.filter P=S := Finset.filter_eq_self.mpr (fun i hi =>
      hup i j hjP (Finite.optimal_swap c r S hS i j hi hnot))
    have hs : S⊆Finset.univ.filter P := fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hup i j hjP
        (Finite.optimal_swap c r S hS i j hi hnot)⟩
    have hcount : c≤(Finset.univ.filter P).card := by
      rw [←hfill]
      exact Finset.card_le_card hs
    rw [he,hfill,min_eq_left hcount]

theorem ge_card (a : ℝ) (ha : 0< a) (S : Finset J) (hS : Finite.Optimal c r S) :
    (S.filter fun j => a≤ r j).card=min c (Finset.univ.filter fun j => a≤ r j).card :=
  filter_card_of_upperSet c r _ (fun _ hj => ha.trans_le hj)
    (fun _ _ hj hji => hj.trans hji) S hS

theorem gt_card (a : ℝ) (ha : 0≤ a) (S : Finset J) (hS : Finite.Optimal c r S) :
    (S.filter fun j => a< r j).card=min c (Finset.univ.filter fun j => a< r j).card :=
  filter_card_of_upperSet c r _ (fun _ hj => ha.trans_lt hj)
    (fun _ _ hj hji => hj.trans_le hji) S hS

omit [Fintype J] in
lemma level_partition (a : ℝ) (S : Finset J) :
    (S.filter fun j => a≤ r j).card=
      (S.filter fun j => a< r j).card+(S.filter fun j => r j=a).card := by
  have he : S.filter (fun j => a≤ r j)=
      (S.filter fun j => a< r j)∪(S.filter fun j => r j=a) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨hj,hja⟩
      rcases lt_or_eq_of_le hja with hlt|heq
      · exact Or.inl ⟨hj,hlt⟩
      · exact Or.inr ⟨hj,heq.symm⟩
    · rintro (⟨hj,hlt⟩|⟨hj,heq⟩)
      · exact ⟨hj,hlt.le⟩
      · exact ⟨hj,heq.ge⟩
  have hd : Disjoint (S.filter fun j => a< r j) (S.filter fun j => r j=a) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hlt := (Finset.mem_filter.mp hj).2
    have heq := (Finset.mem_filter.mp hj').2
    exact (ne_of_gt hlt) heq
  rw [he,Finset.card_union_of_disjoint hd]

theorem level_card_eq (a : ℝ) (ha : 0< a) (S T : Finset J)
    (hS : Finite.Optimal c r S) (hT : Finite.Optimal c r T) :
    (S.filter fun j => r j=a).card=(T.filter fun j => r j=a).card := by
  have hge := (ge_card c r a ha S hS).trans (ge_card c r a ha T hT).symm
  have hgt := (gt_card c r a ha.le S hS).trans (gt_card c r a ha.le T hT).symm
  have hs := level_partition r a S
  have ht := level_partition r a T
  omega

end FCAppendix.Affine.Tail04.FiniteReceiptLevels
