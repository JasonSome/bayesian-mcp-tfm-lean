import FCAppendix.Affine.Tail04.PrivateRowSorting
import FCAppendix.Affine.Tail04.BidDependentFlags
import FCAppendix.Affine.Tail04.FlagAtomPrimitives

noncomputable section
namespace FCAppendix.Affine.Tail04.SortedPrivateMarks
open MeasureTheory Set Classical
open EqualPrivateSignal PrivateRowSorting SortedCoordinates

def prefixMarks {H : ℕ} (z : Marks H) : Marks H := fun i => decide (i.val< upperCount z)

theorem marks_sortSignal (E : Observable.Regions) (H : ℕ) (t : Signal H E.R E.Rp) :
    marks (sortSignal E H t)=prefixMarks (marks t) := by
  let key : Fin H → ℝ := fun k => LocalCoordinates.signalKey E (t k)
  let U : Finset (Fin H) := Finset.univ.filter fun k => isUpper (t k)=true
  funext i
  let j : Fin H := permutation key i
  have hr : (preceding Finset.univ key j).card=i.val := by
    have h := congrArg Fin.val (rank_enumerate Finset.univ key (Fin.cast (by simp) i))
    change (preceding Finset.univ key
      (enumerate Finset.univ key (Fin.cast (by simp) i)).val).card=i.val at h
    exact h
  have hcount : upperCount (marks t)=U.card := rfl
  cases hj : t j with
  | inl upper =>
    have hjU : j∈U := by simp [U,hj,isUpper]
    have hsub : preceding Finset.univ key j⊆U := by
      intro k hk
      have hk' : before key k j := (Finset.mem_filter.mp hk).2
      cases hkval : t k with
      | inl u => simp [U,hkval,isUpper]
      | inr p =>
        exfalso
        rcases hk' with hlt | ⟨heq,_⟩
        · simp only [key,LocalCoordinates.signalKey,hj,hkval] at hlt
          linarith [p.2.2]
        · simp only [key,LocalCoordinates.signalKey,hj,hkval] at heq
          linarith [p.2.2]
    have hstrict : preceding Finset.univ key j⊂U := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
      intro he
      have hh : j∈preceding Finset.univ key j := he.symm ▸ hjU
      exact before_irrefl key j (Finset.mem_filter.mp hh).2
    have hi : i.val< upperCount (marks t) := by
      rw [hcount,←hr]
      exact Finset.card_lt_card hstrict
    simp only [marks,sortSignal,prefixMarks,j,key,hj,isUpper,hi,decide_true]
  | inr p =>
    have hsub : U⊆preceding Finset.univ key j := by
      intro k hk
      have hkU : isUpper (t k)=true := (Finset.mem_filter.mp hk).2
      cases hkval : t k with
      | inl u =>
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Or.inl ?_⟩
        simp only [key,LocalCoordinates.signalKey,hj,hkval]
        linarith [p.2.2]
      | inr q => simp [hkval,isUpper] at hkU
    have hi : ¬i.val< upperCount (marks t) := by
      apply not_lt.mpr
      rw [hcount,←hr]
      exact Finset.card_le_card hsub
    simp only [marks,sortSignal,prefixMarks,j,key,hj,isUpper,hi,decide_false]

def law (H : ℕ) (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1) : FiniteLaw (Marks H) :=
  (independentFlagLaw (fun _ : Fin H => p) (fun _ => hp0) (fun _ => hp1)).map prefixMarks

theorem original_sorted_markLaw (E : Observable.Regions) (H : ℕ)
    (θ : Measure (Signal H E.R E.Rp)) [IsProbabilityMeasure θ]
    (p : ℝ) (hp0 : 0≤ p) (hp1 : p≤1)
    (hθ : θ.map marks=FiniteLaw.probabilityMeasure
      (independentFlagLaw (fun _ : Fin H => p) (fun _ => hp0) (fun _ => hp1))) :
    (θ.map (sortSignal E H)).map marks=FiniteLaw.probabilityMeasure (law H p hp0 hp1) := by
  have hmark : Measurable (marks : Signal H E.R E.Rp → Marks H) :=
    (continuous_pi fun i => continuous_isUpper.comp (continuous_apply i)).measurable
  rw [Measure.map_map hmark (continuous_sortSignal E H).measurable]
  have he : marks ∘ sortSignal E H=prefixMarks ∘ marks := funext (marks_sortSignal E H)
  rw [he,←Measure.map_map (measurable_of_countable prefixMarks) hmark,hθ]
  let ν := independentFlagLaw (fun _ : Fin H => p) (fun _ => hp0) (fun _ => hp1)
  have hν : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure ν) id measurable_id=ν :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ id measurable_id ν Measure.map_id
  have hmap := FiniteLaw.probabilityMeasure_ofMeasure (FiniteLaw.probabilityMeasure ν)
    prefixMarks (measurable_of_countable prefixMarks)
  have hemap : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure ν) prefixMarks
      (measurable_of_countable prefixMarks) = ν.map prefixMarks := by
    simpa only [Function.comp_id, hν] using
      (FiniteLaw.ofMeasure_map (FiniteLaw.probabilityMeasure ν) id measurable_id
        prefixMarks (measurable_of_countable prefixMarks)).symm
  rw [hemap] at hmap
  exact hmap.symm

end FCAppendix.Affine.Tail04.SortedPrivateMarks
