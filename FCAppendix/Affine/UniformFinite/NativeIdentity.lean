import FCAppendix.Affine.UniformFinite.SourceRelabel
import FCAppendix.Affine.Hybrid.NativeFocalReindex

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open Uniform05 SourceContinuity LowBody
open scoped BigOperators

namespace NativeIndexed
variable {M : ℕ} [NeZero M]

omit [NeZero M] in
lemma fixedKind_relabel (e : Equiv.Perm (Fin M)) (a : Fin M) (k : Fin M→ Fin 3) :
    fixedKind (e a) (k∘e.symm)=fixedKind a k∘e.symm := by
  funext j
  by_cases hj : e.symm j=a
  · have he : j=e a := by simpa using congrArg e hj
    simp [fixedKind,he]
  · have he : j≠e a := fun h=> hj (by simp [h])
    simp [fixedKind,Function.update_of_ne hj,Function.update_of_ne he]

omit [NeZero M] in
lemma fixedRow_relabel (e : Equiv.Perm (Fin M)) (a : Fin M) (k : Fin M→ Fin 3) :
    fixedRow (e a) (k∘e.symm)=SourceRelabel.row e (fixedRow a k) := by
  rw [fixedRow,fixedKind_relabel,SourceRelabel.countRowOfKind]
  rfl

omit [NeZero M] in
lemma fixedBids_relabel (e : Equiv.Perm (Fin M)) (i : Row) (a : Fin M)
    (own : Bid i) (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    fixedBids i (e a) own (k∘e.symm) (b∘e.symm)=fixedBids i a own k b∘e.symm := by
  funext j
  by_cases hj : e.symm j=a
  · have he : j=e a := by simpa using congrArg e hj
    simp [fixedBids,coordinate,he]
  · have he : j≠e a := fun h=> hj (by simp [h])
    simp [fixedBids,coordinate,hj,he]

omit [NeZero M] in
lemma fixed_lowerBids (i : Row) (G : RestrictedLaw i) (a : Fin M) (own : Bid i)
    (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    Source.lowerBids (fixedRow a k) (bids i (G,fixedBids i a own k b))=
      bids i (G,fixedBids i a own k b) := by
  funext j
  by_cases hj : j=a
  · subst j
    simp only [Source.lowerBids_of_mem _ _ (fixedRow_self a k)]
  · by_cases hk : k j=0
    · rw [Source.lowerBids_of_mem _ _ ((fixedRow_other a j k hj).mpr hk)]
    · have hn : j∉(fixedRow a k).lower := fun h=> hk ((fixedRow_other a j k hj).mp h)
      simp [Source.lowerBids,hn,SourceContinuity.bids,fixedBids,coordinate,hj,hk,Noisy.zeroBid]

def tieCoefficient (κ : ℝ) (a : Fin M) (k : Fin M→ Fin 3) (P Q : Allocation M)
    (j : Fin M) : ℝ :=
  if j=a then 0 else if k j=0 then copyCoefficient κ P j-copyCoefficient κ Q j else 0

omit [NeZero M] in
lemma fixed_potential_difference (i : Row) (G : RestrictedLaw i) (a : Fin M)
    (own : Bid i) (k : Fin M→ Fin 3) (b : Fin M→ Bid i) (P Q : Allocation M) :
    CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (bids i (G,fixedBids i a own k b))) P.1 P.2-
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (bids i (G,fixedBids i a own k b))) Q.1 Q.2=
      (copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*(own:ℝ)+
        ∑j,tieCoefficient (kappa i) a k P Q j*(b j:ℝ) := by
  rw [fixed_lowerBids,potential_eq_copyCoefficient,potential_eq_copyCoefficient,
    ← Finset.sum_sub_distrib]
  have he (j : Fin M) :
      copyCoefficient (kappa i) P j*bids i (G,fixedBids i a own k b) j-
        copyCoefficient (kappa i) Q j*bids i (G,fixedBids i a own k b) j=
      (if j=a then (copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*(own:ℝ) else 0)+
        tieCoefficient (kappa i) a k P Q j*(b j:ℝ) := by
    by_cases hj : j=a
    · subst j
      simp [SourceContinuity.bids,fixedBids,coordinate,tieCoefficient]; ring
    · by_cases hk : k j=0 <;>
        simp [SourceContinuity.bids,fixedBids,coordinate,tieCoefficient,hj,hk,Noisy.zeroBid]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

omit [NeZero M] in

theorem ae_fixed_generic (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin M) (own : Bid i) (hown : 0<(own:ℝ)) (k : Fin M→ Fin 3) :
    ∀ᵐb∂(rowLaw M G.bidLaw : Measure (Fin M→ Bid i)),∀P Q : Allocation M,
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (bids i (G,fixedBids i a own k b))) P.1 P.2=
      CompleteInformation.potential (kappa i)
        (Source.lowerBids (fixedRow a k) (bids i (G,fixedBids i a own k b))) Q.1 Q.2→
      focalCopy P a=focalCopy Q a := by
  rw [rowLaw_eq_pi]
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hcopy : focalCopy P a=focalCopy Q a
  · exact ae_of_all _ (fun _ _=> hcopy)
  · have hκ : 0< kappa i := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (ActualAtoms.kappa_ge_half i)
    have ha : copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a≠0 :=
      sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q a hcopy)
    by_cases hr : ∃j,tieCoefficient (kappa i) a k P Q j≠0
    · obtain ⟨j,hj⟩:=hr
      filter_upwards [ae_iid_linear_ne (G.bidLaw : Measure (Bid i))
        (tieCoefficient (kappa i) a k P Q) j hj
        (-(copyCoefficient (kappa i) P a-copyCoefficient (kappa i) Q a)*(own:ℝ))]
        with b hb hpot
      apply False.elim (hb ?_)
      have h:=fixed_potential_difference i G a own k b P Q
      rw [hpot,sub_self] at h
      linarith
    · have hz : ∀j,tieCoefficient (kappa i) a k P Q j=0 := by
        simpa only [not_exists,not_not] using hr
      apply ae_of_all
      intro b hpot
      have h:=fixed_potential_difference i G a own k b P Q
      rw [hpot,sub_self] at h
      simp only [hz,zero_mul,Finset.sum_const_zero,add_zero] at h
      exact False.elim ((mul_ne_zero ha hown.ne') h.symm)

omit [NeZero M] in
lemma category_relabel_preserving (i : Row) (e : Equiv.Perm (Fin M)) :
    MeasurePreserving (fun k : Fin M→ Fin 3=> k∘e.symm)
      (FiniteLaw.probabilityMeasure (categoryRowLaw i M))
      (FiniteLaw.probabilityMeasure (categoryRowLaw i M)) := by
  rw [categoryRowLaw,LowBody.probabilityMeasure_iid]
  convert! measurePreserving_piCongrLeft
    (fun _ : Fin M=> FiniteLaw.probabilityMeasure (categoryLaw i)) e using 1
  funext k a
  simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']

omit [NeZero M] in
lemma bids_relabel_preserving (i : Row) (G : RestrictedLaw i) (e : Equiv.Perm (Fin M)) :
    MeasurePreserving (fun b : Fin M→ Bid i=> b∘e.symm)
      (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))
      (rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) := by
  rw [rowLaw_eq_pi]
  convert! measurePreserving_piCongrLeft (fun _ : Fin M=>(G.bidLaw : Measure (Bid i))) e using 1
  funext b a
  simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']

def rowUtility (i : Row) (G : RestrictedLaw i) (a : Fin M) (v : ℝ) (own : Bid i)
    (p : (Fin M→ Fin 3)×(Fin M→ Bid i)) : ℝ :=
  rowPayoff i G (fixedRow a p.1) v (bids i (G,fixedBids i a own p.1 p.2)) a

lemma measurable_rowUtility (i : Row) (G : RestrictedLaw i) (a : Fin M) (v : ℝ) (own : Bid i) :
    Measurable (rowUtility i G a v own) :=
  measurable_from_prod_countable_right (measurable_row_utility i G a v own)

lemma integrable_rowUtility (i : Row) (G : RestrictedLaw i) (a : Fin M) (v : ℝ) (own : Bid i) :
    Integrable (rowUtility i G a v own)
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) :=
  Integrable.of_bound (measurable_rowUtility i G a v own).aestronglyMeasurable
    (|v|+(1+|eta i|)*|(own:ℝ)|) (ae_of_all _ (fun p=> by
      simpa only [Real.norm_eq_abs,rowUtility,SourceContinuity.bids,fixedBids_self] using
        rowPayoff_bound i G (fixedRow a p.1) v (bids i (G,fixedBids i a own p.1 p.2)) a))

theorem utility_source_integral (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))] (a : Fin M) (v : ℝ) (own : Bid i) :
    utility i G a v own=∫p,rowUtility i G a v own p
      ∂((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := by
  rw [integral_prod _ (integrable_rowUtility i G a v own),LowBody.integral_probabilityMeasure,
    utility_source]
  rfl

theorem utility_relabel (i : Row) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (e : Equiv.Perm (Fin M)) (a : Fin M) (v : ℝ) (own : Bid i) (hown : 0<(own:ℝ)) :
    utility i G (e a) v own=utility i G a v own := by
  let μ:=(FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
    (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))
  let reindex : ((Fin M→ Fin 3)×(Fin M→ Bid i))→((Fin M→ Fin 3)×(Fin M→ Bid i)) :=
    fun p=>(p.1∘e.symm,p.2∘e.symm)
  have hp : MeasurePreserving reindex μ μ :=
    (category_relabel_preserving i e).prod (bids_relabel_preserving i G e)
  rw [utility_source_integral,utility_source_integral]
  calc
    _=∫p,rowUtility i G (e a) v own (reindex p) ∂μ := by
      have hmap:=integral_map (μ:=μ) hp.measurable.aemeasurable
        (measurable_rowUtility i G (e a) v own).aestronglyMeasurable
      rw [hp.map_eq] at hmap
      exact hmap
    _=∫p,rowUtility i G a v own p ∂μ := by
      have hnew : Integrable (fun p=> rowUtility i G (e a) v own (reindex p)) μ :=
        hp.integrable_comp_of_integrable (integrable_rowUtility i G (e a) v own)
      rw [show μ=(FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i)) from rfl,
        integral_prod _ hnew,integral_prod _ (integrable_rowUtility i G a v own)]
      apply integral_congr_ae
      apply ae_of_all
      intro k
      apply integral_congr_ae
      filter_upwards [ae_fixed_generic i G a own hown k] with b hb
      have h:=SourceRelabel.rowPayoff e i G (fixedRow a k) (fixedBids i a own k b)
        v a (fixedRow_self a k) hb
      simp only [rowUtility,reindex,fixedRow_relabel,fixedBids_relabel]
      convert! h using 1

theorem utility_positive_eq_raw (i : Row) (N : ℕ) (G : RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (a : Fin (N+1)) (v : ℝ) (own : Bid i) (hown : 0<(own:ℝ)) :
    utility i G a v own=rawUtility i N G v own := by
  have h:=utility_relabel i G (Hybrid.NativeContinuation.focalIndex a) 0 v own hown
  rw [Hybrid.NativeContinuation.focalIndex_zero,utility_zero] at h
  exact h

omit [NeZero M] in
lemma fixedBids_update (i : Row) (a : Fin M) (x y : Bid i)
    (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
    Function.update (fixedBids i a x k b) a y=fixedBids i a y k b := by
  funext j
  by_cases hj : j=a
  · subst j; simp [fixedBids,coordinate]
  · simp [fixedBids,coordinate,hj]

theorem zero_right_bound (i : Row) {err : ℝ} (herr : 0< err) :
    ∃radius : ℝ,0< radius ∧ ∀(G : RestrictedLaw i)
      (_hG : NullSingletonClass (G.bidLaw : Measure (Bid i))),
      ∀a : Fin M,∀v : Value i,∀b : Bid i,
      0<(b:ℝ)→(b:ℝ)< radius→
      utility i G a v (Noisy.zeroBid i)≤ utility i G a v b+(1+eta i)*(b:ℝ)+err := by
  obtain ⟨r,hr,h⟩:=ActualAtoms.exists_actual_zero_raise_modulus (M:=M) i herr
  refine ⟨r,hr,?_⟩
  intro G hG a v target ht htr
  letI := hG
  let z : Bid i:=⟨0,le_rfl,(cap_pos i).le⟩
  have hrow (k : Fin M→ Fin 3) (b : Fin M→ Bid i) :
      rowUtility i G a v z (k,b)≤ rowUtility i G a v target (k,b)+(1+eta i)*(target:ℝ)+err := by
    let x : OwnBid.Box i M:=(v,G,fixedBids i a z k b)
    have hh:=h (fixedRow a k) a (fixedRow_self a k) x target
      (by simpa [x,SourceContinuity.bids,fixedBids_self,z] using v.property.1)
      (by simpa [x,SourceContinuity.bids,fixedBids_self,z] using ht)
      (by simpa [x,SourceContinuity.bids,fixedBids_self,z] using htr)
    have hbid : bids i (OwnBid.change i x a target).2=bids i (G,fixedBids i a target k b) := by
      simp only [OwnBid.change,x,fixedBids_update]
    simp only [hbid,x,SourceContinuity.bids,fixedBids_self,z,Subtype.coe_mk,
      sub_zero] at hh
    dsimp only [rowUtility]
    linarith
  rw [utility_source_integral,utility_source_integral]
  have hc : Integrable (fun _ : (Fin M→ Fin 3)×(Fin M→ Bid i)=>(1+eta i)*(target:ℝ)+err)
      ((FiniteLaw.probabilityMeasure (categoryRowLaw i M)).prod
        (rowLaw M G.bidLaw : Measure (Fin M→ Bid i))) := integrable_const _
  have hh:=integral_mono (integrable_rowUtility i G a v z)
    ((integrable_rowUtility i G a v target).add hc) (fun p=> by
      simpa only [Pi.add_apply,add_assoc] using hrow p.1 p.2)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_rowUtility i G a v target) hc] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,z,Noisy.zeroBid,add_assoc] using hh

end NativeIndexed
end FCAppendix.Affine.UniformFinite
