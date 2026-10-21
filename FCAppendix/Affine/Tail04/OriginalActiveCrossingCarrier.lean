import FCAppendix.Affine.Tail04.ActiveClusterCarrier
import FCAppendix.Probability.ConditionalAveraging

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalActiveCrossingCarrier
open MeasureTheory ProbabilityTheory Set Classical
open ActiveClusterCarrier
open scoped BigOperators

variable {X : Type*} [MeasurableSpace X] {N : ℕ}

def restore (j : Fin (N+1)) (y : X) (row : Fin N → X) : Fin (N+1) → X :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j).symm (y,row)

lemma measurable_restore (j : Fin (N+1)) :
    Measurable (fun p : X×(Fin N → X) => restore j p.1 p.2) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j).symm.measurable

@[simp] lemma restore_self (j : Fin (N+1)) (y : X) (row : Fin N → X) :
    restore j y row j=y := by
  have h := congrArg Prod.fst
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j).apply_symm_apply (y,row))
  exact h

@[simp] lemma restore_delete (j : Fin (N+1)) (row : Fin (N+1) → X) :
    restore j (row j) (fun k => row (j.succAbove k))=row :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j).symm_apply_apply row

theorem integral_delete (μ : Measure X) [IsProbabilityMeasure μ]
    (j : Fin (N+1)) (f : (Fin (N+1) → X) → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ row,‖f row‖≤ B) :
    (∫ row,f row ∂Measure.pi (fun _ : Fin (N+1) => μ))=
      ∫ y,∫ row,f (restore j y row) ∂Measure.pi (fun _ : Fin N => μ) ∂μ := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j
  have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) j
  have hm : Measurable (fun p : X×(Fin N → X) => f (restore j p.1 p.2)) :=
    hf.comp (measurable_restore j)
  have hi : Integrable (fun p : X×(Fin N → X) => f (restore j p.1 p.2))
      (μ.prod (Measure.pi (fun _ : Fin N => μ))) :=
    Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun p => hB _)
  have he := integral_map (μ:=Measure.pi (fun _ : Fin (N+1) => μ)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  have he' : (∫ p : X×(Fin N → X),f (restore j p.1 p.2)
      ∂μ.prod (Measure.pi (fun _ : Fin N => μ)))=
      ∫ row,f row ∂Measure.pi (fun _ : Fin (N+1) => μ) := by
    have hdelete (row : Fin (N+1) → X) :
        restore j ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j) row).1
          ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => X) j) row).2=row :=
      e.symm_apply_apply row
    simpa only [hdelete] using he
  exact he'.symm.trans (integral_prod _ hi)

def crossing (active : Set X) (bid raised : X → ℝ) (x y : X) : Prop :=
  y∈active ∧ bid x≤ bid y ∧ bid y≤ raised x

def crossingCount (active : Set X) (bid raised : X → ℝ)
    (z : X×(Fin (N+1) → X)) : ℝ :=
  ∑ j : Fin (N+1),if crossing active bid raised z.1 (z.2 j) then 1 else 0

lemma measurableSet_crossing (active : Set X) (ha : MeasurableSet active)
    (bid raised : X → ℝ) (hb : Measurable bid) (hr : Measurable raised) :
    MeasurableSet {p : X×X | crossing active bid raised p.1 p.2} :=
  (ha.preimage measurable_snd).inter
    ((measurableSet_le (hb.comp measurable_fst) (hb.comp measurable_snd)).inter
      (measurableSet_le (hb.comp measurable_snd) (hr.comp measurable_fst)))

lemma measurable_crossingCount (active : Set X) (ha : MeasurableSet active)
    (bid raised : X → ℝ) (hb : Measurable bid) (hr : Measurable raised) :
    Measurable (crossingCount (N:=N) active bid raised) := by
  apply Finset.measurable_sum
  intro j _
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_crossing active ha bid raised hb hr).preimage
    (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

omit [MeasurableSpace X] in
lemma crossingCount_bounds (active : Set X) (bid raised : X → ℝ)
    (z : X×(Fin (N+1) → X)) :
    crossingCount active bid raised z∈Icc (0:ℝ) (N+1:ℕ) := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _j : Fin (N+1),(1:ℝ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> norm_num)
      _ = _ := by simp

lemma integrable_crossingCount (μ : Measure X) [IsProbabilityMeasure μ]
    (E active : Set X) (ha : MeasurableSet active)
    (bid raised : X → ℝ) (hb : Measurable bid) (hr : Measurable raised) :
    Integrable (crossingCount (N:=N) active bid raised)
      ((μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))) :=
  Integrable.of_bound (measurable_crossingCount active ha bid raised hb hr).aestronglyMeasurable
    (N+1:ℕ) (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (crossingCount_bounds active bid raised z).1]
      exact (crossingCount_bounds active bid raised z).2)

def orderedCoordinate (E : Set X) (bid : X → ℝ)
    (j : Fin (N+1)) (z : X×(Fin (N+1) → X)) : ℝ :=
  if z.2 j∈E ∧ bid z.1≤ bid (z.2 j) then 1 else 0

lemma measurable_orderedCoordinate (E : Set X) (hE : MeasurableSet E)
    (bid : X → ℝ) (hb : Measurable bid) (j : Fin (N+1)) :
    Measurable (orderedCoordinate E bid j) :=
  Measurable.ite
    ((hE.preimage ((measurable_pi_apply j).comp measurable_snd)).inter
      (measurableSet_le (hb.comp measurable_fst)
        (hb.comp ((measurable_pi_apply j).comp measurable_snd))))
    measurable_const measurable_const

lemma integrable_orderedCoordinate (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (bid : X → ℝ) (hb : Measurable bid)
    (j : Fin (N+1)) :
    Integrable (orderedCoordinate E bid j)
      ((μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))) :=
  Integrable.of_bound (measurable_orderedCoordinate E hE bid hb j).aestronglyMeasurable 1
    (ae_of_all _ fun z => by dsimp [orderedCoordinate];split_ifs <;> norm_num)

theorem orderedCoordinate_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (bid : X → ℝ) (hb : Measurable bid)
    (j : Fin (N+1)) :
    (∫ z,orderedCoordinate E bid j z
      ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)))=
        ((μ.restrict E).prod (μ.restrict E)).real (ordered bid) := by
  let f : X×X → ℝ := fun p => if bid p.1≤ bid p.2 then 1 else 0
  have hf : Measurable f := Measurable.ite (measurableSet_ordered bid hb)
    measurable_const measurable_const
  have hfi : Integrable f ((μ.restrict E).prod (μ.restrict E)) :=
    Integrable.of_bound hf.aestronglyMeasurable 1
      (ae_of_all _ fun p => by dsimp [f];split_ifs <;> norm_num)
  rw [integral_prod _ (integrable_orderedCoordinate μ E hE bid hb j)]
  calc
    _ = ∫ x,∫ y,f (x,y) ∂μ.restrict E ∂μ.restrict E := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        let g : X → ℝ := fun y => if y∈E ∧ bid x≤ bid y then 1 else 0
        have hg : Measurable g := Measurable.ite
          (hE.inter (measurableSet_le measurable_const hb)) measurable_const measurable_const
        change (∫ row,g (row j) ∂Measure.pi (fun _ : Fin (N+1) => μ))=_
        rw [integral_comp_eval (μ:=fun _ : Fin (N+1) => μ) hg.aestronglyMeasurable]
        have he : g=E.indicator (fun y => f (x,y)) := by
          funext y
          simp only [g,f,Set.indicator]
          split_ifs <;> simp_all
        rw [he,integral_indicator hE])
    _ = ∫ p,f p ∂(μ.restrict E).prod (μ.restrict E) := (integral_prod _ hfi).symm
    _ = _ := by
      simpa only [f,ordered,Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
        (integral_indicator_one (μ:=(μ.restrict E).prod (μ.restrict E))
          (measurableSet_ordered bid hb))

def orderedCount (E : Set X) (bid : X → ℝ) (z : X×(Fin (N+1) → X)) : ℝ :=
  ∑ j : Fin (N+1),orderedCoordinate E bid j z

omit [MeasurableSpace X] in
lemma orderedCount_bounds (E : Set X) (bid : X → ℝ) (z : X×(Fin (N+1) → X)) :
    orderedCount E bid z∈Icc (0:ℝ) (N+1:ℕ) := by
  constructor
  · exact Finset.sum_nonneg (fun j _ => by dsimp [orderedCoordinate];split_ifs <;> norm_num)
  · calc
      _ ≤ ∑ _j : Fin (N+1),(1:ℝ) := Finset.sum_le_sum (fun j _ => by
        dsimp [orderedCoordinate];split_ifs <;> norm_num)
      _ = _ := by simp

lemma measurable_orderedCount (E : Set X) (hE : MeasurableSet E)
    (bid : X → ℝ) (hb : Measurable bid) : Measurable (orderedCount (N:=N) E bid) :=
  Finset.measurable_sum _ (fun j _ => measurable_orderedCoordinate E hE bid hb j)

lemma integrable_orderedCount (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (bid : X → ℝ) (hb : Measurable bid) :
    Integrable (orderedCount (N:=N) E bid)
      ((μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))) :=
  integrable_finsetSum _ (fun j _ => integrable_orderedCoordinate μ E hE bid hb j)

theorem orderedCount_integral_lower (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (bid : X → ℝ) (hb : Measurable bid) :
    ((N+1:ℕ):ℝ)*(μ.real E)^2/2≤
      ∫ z,orderedCount E bid z
        ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)) := by
  unfold orderedCount
  rw [integral_finsetSum _ (fun j _ => integrable_orderedCoordinate μ E hE bid hb j)]
  simp_rw [orderedCoordinate_integral μ E hE bid hb]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_left (ordered_pair_mass_ge_half (μ.restrict E) bid hb)
    (by positivity : (0:ℝ)≤(N+1:ℕ))
  simpa only [measureReal_def,Measure.restrict_apply_univ,mul_div_assoc] using hh

theorem marked_coordinate_error (μ : Measure X) [IsProbabilityMeasure μ]
    (F : Set X) (hF : MeasurableSet F) (j : Fin (N+1))
    (β : (Fin (N+1) → X) → ℝ) (hβ : Measurable β)
    (K : ℝ) (hK : 0≤ K) (hbound : ∀ row,β row∈Icc (0:ℝ) K)
    (ε : ℝ)
    (hconditional : ∀ y∈F,
      (∫ row,β (restore j y row) ∂Measure.pi (fun _ : Fin N => μ))≤ ε) :
    (∫ row,if row j∈F then β row else 0 ∂Measure.pi (fun _ : Fin (N+1) => μ))≤
      ε*μ.real F := by
  let f : (Fin (N+1) → X) → ℝ := fun row => if row j∈F then β row else 0
  have hf : Measurable f := Measurable.ite (hF.preimage (measurable_pi_apply j)) hβ measurable_const
  have hfb (row : Fin (N+1) → X) : ‖f row‖≤ K := by
    dsimp [f]
    split_ifs
    · rw [abs_of_nonneg (hbound row).1]
      exact (hbound row).2
    · simpa using hK
  have hpair : Measurable (fun p : X×(Fin N → X) => f (restore j p.1 p.2)) :=
    hf.comp (measurable_restore j)
  have hpi : Integrable (fun p : X×(Fin N → X) => f (restore j p.1 p.2))
      (μ.prod (Measure.pi (fun _ : Fin N => μ))) :=
    Integrable.of_bound hpair.aestronglyMeasurable K (ae_of_all _ fun p => hfb _)
  change (∫ row,f row ∂Measure.pi (fun _ : Fin (N+1) => μ))≤_
  rw [integral_delete μ j f hf K hfb]
  have hh := integral_mono hpi.integral_prod_left ((integrable_const ε).indicator hF)
    (fun y => by
      by_cases hy : y∈F
      · simpa only [f,restore_self,if_pos hy,Set.indicator_of_mem hy] using hconditional y hy
      · simp only [f,restore_self,if_neg hy,integral_zero,Set.indicator_of_notMem hy,le_refl])
  rw [integral_indicator_const ε hF] at hh
  simpa only [smul_eq_mul,mul_comm] using hh

theorem sum_localized_error (μ : Measure X) [IsProbabilityMeasure μ]
    (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (term : Fin (N+1) → X×(Fin (N+1) → X) → ℝ)
    (ht : ∀ j,Measurable (term j)) (htbound : ∀ j z,term j z∈Icc (0:ℝ) 1)
    (hlocal : ∀ j,∀ x∈E,∀ row,row j∉F → term j (x,row)=0)
    (β : X×(Fin (N+1) → X) → ℝ) (hβ : Measurable β)
    (K : ℝ) (hK : 0≤ K) (hbound : ∀ z,β z∈Icc (0:ℝ) K)
    (ε : ℝ)
    (hconditional : ∀ j,∀ x∈E,∀ y∈F,
      (∫ row,β (x,restore j y row) ∂Measure.pi (fun _ : Fin N => μ))≤ ε) :
    (∫ z,(∑ j : Fin (N+1),term j z)*β z
      ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)))≤
        (N+1:ℕ)*ε*μ.real E*μ.real F := by
  let ν := (μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))
  have hi (j : Fin (N+1)) : Integrable (fun z => term j z*β z) ν := by
    apply Integrable.of_bound ((ht j).mul hβ).aestronglyMeasurable K
    exact ae_of_all _ (fun z => by
      change ‖term j z*β z‖≤K
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (htbound j z).1 (hbound z).1)]
      exact (mul_le_of_le_one_left (hbound z).1 (htbound j z).2).trans (hbound z).2)
  have he (j : Fin (N+1)) :
      (∫ z,term j z*β z ∂ν)≤ ε*μ.real E*μ.real F := by
    rw [integral_prod _ (hi j)]
    have hinner : ∀ᵐ x ∂μ.restrict E,
        (∫ row,term j (x,row)*β (x,row) ∂Measure.pi (fun _ : Fin (N+1) => μ))≤
          ε*μ.real F := by
      filter_upwards [ae_restrict_mem hE] with x hx
      have hm : Measurable (fun row => if row j∈F then β (x,row) else 0) :=
        Measurable.ite (hF.preimage (measurable_pi_apply j))
          (hβ.comp (measurable_const.prodMk measurable_id)) measurable_const
      have him : Integrable (fun row => if row j∈F then β (x,row) else 0)
          (Measure.pi (fun _ : Fin (N+1) => μ)) :=
        Integrable.of_bound hm.aestronglyMeasurable K (ae_of_all _ fun row => by
          split_ifs
          · rw [Real.norm_eq_abs,abs_of_nonneg (hbound (x,row)).1]
            exact (hbound (x,row)).2
          · simpa using hK)
      have hit : Integrable (fun row => term j (x,row)*β (x,row))
          (Measure.pi (fun _ : Fin (N+1) => μ)) := by
        apply Integrable.of_bound
          (((ht j).mul hβ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable K
        exact ae_of_all _ (fun row => by
          change ‖term j (x,row)*β (x,row)‖≤K
          rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (htbound j (x,row)).1 (hbound (x,row)).1)]
          exact (mul_le_of_le_one_left (hbound (x,row)).1 (htbound j (x,row)).2).trans (hbound (x,row)).2)
      apply (integral_mono hit him (fun row => ?_)).trans
        (marked_coordinate_error μ F hF j (fun row => β (x,row))
          (hβ.comp (measurable_const.prodMk measurable_id)) K hK (fun row => hbound (x,row))
          ε (hconditional j x hx))
      by_cases hr : row j∈F
      · simp only [if_pos hr]
        exact mul_le_of_le_one_left (hbound (x,row)).1 (htbound j (x,row)).2
      · simp only [if_neg hr,hlocal j x hx row hr,zero_mul,le_refl]
    have hh := integral_mono_ae (hi j).integral_prod_left (integrable_const (ε*μ.real F)) hinner
    rw [integral_const] at hh
    simpa only [measureReal_def,Measure.restrict_apply_univ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using hh
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ∑ _j : Fin (N+1),ε*μ.real E*μ.real F := Finset.sum_le_sum (fun j _ => he j)
    _ = _ := by simp;ring

theorem orderedCount_without_equal_lower (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (bid : X → ℝ) (hb : Measurable bid)
    (equal : X×(Fin (N+1) → X) → Prop) (heq : MeasurableSet {z | equal z})
    (ε : ℝ)
    (hconditional : ∀ j,∀ x∈E,∀ y∈E,
      (Measure.pi (fun _ : Fin N => μ)).real {row | equal (x,restore j y row)}≤ ε) :
    (N+1:ℕ)*(1/2-ε)*(μ.real E)^2≤
      ∫ z,(if equal z then 0 else orderedCount E bid z)
        ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)) := by
  let β : X×(Fin (N+1) → X) → ℝ := fun z => if equal z then 1 else 0
  have hβ : Measurable β := Measurable.ite heq measurable_const measurable_const
  have hbound (z : X×(Fin (N+1) → X)) : β z∈Icc (0:ℝ) 1 := by
    dsimp [β];split_ifs <;> constructor <;> norm_num
  have hcond (j : Fin (N+1)) (x : X) (hx : x∈E) (y : X) (hy : y∈E) :
      (∫ row,β (x,restore j y row) ∂Measure.pi (fun _ : Fin N => μ))≤ ε := by
    have hm : MeasurableSet {row | equal (x,restore j y row)} :=
      heq.preimage (measurable_const.prodMk
        ((measurable_restore j).comp (measurable_const.prodMk measurable_id)))
    have hi := integral_indicator_one (μ:=Measure.pi (fun _ : Fin N => μ)) hm
    change (∫ row,β (x,restore j y row) ∂Measure.pi (fun _ : Fin N => μ))=_ at hi
    rw [hi]
    exact hconditional j x hx y hy
  have herr := sum_localized_error μ E E hE hE (orderedCoordinate E bid)
    (measurable_orderedCoordinate E hE bid hb)
    (fun j z => by dsimp [orderedCoordinate];split_ifs <;> constructor <;> norm_num)
    (fun j x hx row hr => by simp [orderedCoordinate,hr]) β hβ 1 (by norm_num) hbound ε hcond
  have ho := integrable_orderedCount (N:=N) μ E hE bid hb
  have hloss : Integrable (fun z => orderedCount E bid z*β z)
      ((μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ))) := by
    apply Integrable.of_bound ((measurable_orderedCount E hE bid hb).mul hβ).aestronglyMeasurable (N+1:ℕ)
    exact ae_of_all _ (fun z => by
      change ‖orderedCount E bid z*β z‖≤(N+1:ℕ)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (orderedCount_bounds E bid z).1 (hbound z).1)]
      exact (mul_le_of_le_one_right (orderedCount_bounds E bid z).1 (hbound z).2).trans (orderedCount_bounds E bid z).2)
  have hp (z : X×(Fin (N+1) → X)) :
      (if equal z then 0 else orderedCount E bid z)=orderedCount E bid z-orderedCount E bid z*β z := by
    dsimp [β];split_ifs <;> ring
  simp_rw [hp]
  rw [integral_sub ho hloss]
  have hord := orderedCount_integral_lower (N:=N) μ E hE bid hb
  change (∫ z,orderedCount E bid z*β z
    ∂(μ.restrict E).prod (Measure.pi (fun _ : Fin (N+1) => μ)))≤_ at herr
  nlinarith only [hord,herr]

end FCAppendix.Affine.Tail04.OriginalActiveCrossingCarrier
