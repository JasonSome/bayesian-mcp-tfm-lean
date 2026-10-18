import FCAppendix.Exclusive.MarkerConstructionSorted

namespace FCAppendix.Exclusive.Marker
open MeasureTheory ProbabilityTheory Game Bayes Set

variable {m n c : ℕ}

theorem positives_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    positives (L ∘ e.symm) = (positives L).map e.toEmbedding := by
  classical
  ext j
  simp only [positives,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,
    Function.comp_apply,Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e.symm j,h,e.apply_symm_apply j⟩
  · rintro ⟨i,hi,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hi

theorem lows_relabel (e : Equiv.Perm (Fin m)) (cutoff : ℝ) (L : LocalList m) :
    lows cutoff (L ∘ e.symm) = (lows cutoff L).map e.toEmbedding := by
  classical
  ext j
  simp only [lows,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,
    Function.comp_apply,Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e.symm j,h,e.apply_symm_apply j⟩
  · rintro ⟨i,hi,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hi

theorem zeros_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    zeros (L ∘ e.symm) = (zeros L).map e.toEmbedding := by
  classical
  ext j
  simp only [zeros,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,
    Function.comp_apply,Equiv.toEmbedding_apply]
  constructor
  · intro h
    exact ⟨e.symm j,h,e.apply_symm_apply j⟩
  · rintro ⟨i,hi,rfl⟩
    simpa only [Equiv.symm_apply_apply] using hi

theorem rankVector_relabel (hm : 0 < m) (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    rankVector hm (L ∘ e.symm) = rankVector hm L ∘ e.symm := by
  funext j
  have hh := rankLabel_relabel hm e (positives L) (fun i => (L i).getD 0) (e.symm j)
  simpa only [Equiv.apply_symm_apply,rankVector,positives_relabel,Function.comp_apply] using hh

theorem injOn_relabel_iff {α : Type*} (e : Equiv.Perm (Fin m))
    (P : Finset (Fin m)) (f : Fin m → α) :
    Set.InjOn (f ∘ e.symm) (P.map e.toEmbedding) ↔ Set.InjOn f P := by
  classical
  constructor
  · intro h i hi j hj he
    apply e.injective
    apply h (Finset.mem_map.mpr ⟨i,hi,rfl⟩) (Finset.mem_map.mpr ⟨j,hj,rfl⟩)
    simpa only [Function.comp_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using he
  · intro h i hi j hj he
    obtain ⟨i',hi',rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨j',hj',rfl⟩ := Finset.mem_map.mp hj
    apply congrArg e
    apply h hi' hj'
    simpa only [Function.comp_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using he

theorem sourceEligible_relabel_iff (hm : 0 < m) (e : Equiv.Perm (Fin m))
    (cutoff : ℝ) (L : LocalList m) :
    SourceEligible hm cutoff (L ∘ e.symm) n c ↔ SourceEligible hm cutoff L n c := by
  simp only [SourceEligible,Eligible,EligibleCode,positives_relabel,lows_relabel,
    zeros_relabel,Finset.card_map,rankVector_relabel,injOn_relabel_iff]

theorem targetOfSingleton_relabel (e : Equiv.Perm (Fin m))
    (T : Finset (Fin m)) (hT : T.card = 1) (hT' : (T.map e.toEmbedding).card=1) :
    targetOfSingleton (T.map e.toEmbedding) hT' = e (targetOfSingleton T hT) := by
  have hh := singleton_target T hT
  have hmap : T.map e.toEmbedding = {e (targetOfSingleton T hT)} := by
    exact (congrArg (fun S : Finset (Fin m) => S.map e.toEmbedding) hh).trans
      (Finset.map_singleton _ _)
  have hm := singleton_target (T.map e.toEmbedding) hT'
  exact Finset.singleton_injective ((hm.symm).trans hmap)

theorem rankSelected_relabel (hn : 2 ≤ n) (hc : 0 < c) (e : Equiv.Perm (Fin m))
    (P T Z : Finset (Fin m)) (L : Fin m → Fin m) :
    rankSelected hn hc (P.map e.toEmbedding) (T.map e.toEmbedding) (Z.map e.toEmbedding)
      (L ∘ e.symm) = (rankSelected hn hc P T Z L).map e.toEmbedding := by
  classical
  have hcode : EligibleCode (P.map e.toEmbedding) (T.map e.toEmbedding)
      (Z.map e.toEmbedding) n c ↔ EligibleCode P T Z n c := by
    simp only [EligibleCode,Finset.card_map]
  by_cases h : EligibleCode P T Z n c
  · have h' := hcode.mpr h
    have ht := targetOfSingleton_relabel e T h.2.1 h'.2.1
    simp only [rankSelected,dif_pos h,dif_pos h',Finset.card_map,ht,Function.comp_apply,
      Equiv.symm_apply_apply]
    ext j
    simp only [Finset.mem_filter,Finset.mem_map,Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨⟨i,hi,rfl⟩,hsel⟩
      exact ⟨i,⟨hi,by simpa only [Equiv.symm_apply_apply] using hsel⟩,rfl⟩
    · rintro ⟨i,⟨hi,hsel⟩,rfl⟩
      exact ⟨⟨i,hi,rfl⟩,by simpa only [Equiv.symm_apply_apply] using hsel⟩
  · have h' : ¬ EligibleCode (P.map e.toEmbedding) (T.map e.toEmbedding)
        (Z.map e.toEmbedding) n c := fun hh => h (hcode.mp hh)
    simp only [rankSelected,dif_neg h,dif_neg h',Finset.map_empty]

theorem sourceContinuation_relabel_of_eligible {Seed : Type*}
    (hm : 0 < m) (hn : 2 ≤ n) (hc : 0 < c) (cutoff : ℝ)
    (fallback : LocalPolicy m c Seed) (e : Equiv.Perm (Fin m)) (L : LocalList m)
    (hL : SourceEligible hm cutoff L n c) (s t : Seed) :
    (sourceContinuation hm hn hc cutoff fallback (L ∘ e.symm) s).val =
      (sourceContinuation hm hn hc cutoff fallback L t).val.map e.toEmbedding := by
  classical
  have hL' := (sourceEligible_relabel_iff hm e cutoff L).mpr hL
  simp only [sourceContinuation,dif_pos hL,dif_pos hL',positives_relabel,lows_relabel,
    zeros_relabel,rankVector_relabel,rankSelected_relabel]

end FCAppendix.Exclusive.Marker
