import FCAppendix.Affine.Uniform06.EntryConditionalRelative
import FCAppendix.Affine.LowBody.NoisyExpectedLoss

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySignFiber
open MeasureTheory ProbabilityTheory Set
open FCAppendix.Affine.LowBody
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.EntryUntilting
open FCAppendix.Affine.Uniform06.EntryRenewal
open FCAppendix.Affine.Uniform06.EntryParityRenewal
open scoped BigOperators

section FiniteFactor
variable {α β : Type*} [Fintype α] [Fintype β]

lemma iid_map_expect (C : FiniteLaw α) (f : α → β) (N : ℕ)
    (F : (Fin N → β) → ℝ) :
    (CommonList.iid (C.map f) N).expect F=
      (CommonList.iid C N).expect (fun ω => F (fun j => f (ω j))) := by
  induction N with
  | zero =>
    rw [CommonList.expect_iid_zero,CommonList.expect_iid_zero]
    congr 1
    funext j
    exact Fin.elim0 j
  | succ N ih =>
    rw [CommonList.expect_iid_succ,CommonList.expect_iid_succ,FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro a
    rw [ih]
    apply FiniteLaw.expect_congr
    intro ω
    congr 1
    funext j
    refine Fin.cases rfl (fun j => ?_) j
    rfl

lemma iid_prod_expect (P : FiniteLaw α) (Q : FiniteLaw β) (N : ℕ)
    (F : (Fin N → α × β) → ℝ) :
    (CommonList.iid (P.prod Q) N).expect F=
      (CommonList.iid P N).expect (fun x =>
        (CommonList.iid Q N).expect (fun y => F (fun j => (x j,y j)))) := by
  let e : ((Fin N → α) × (Fin N → β)) ≃ (Fin N → α × β) :=
    { toFun := fun p j => (p.1 j,p.2 j)
      invFun := fun p => (fun j => (p j).1,fun j => (p j).2)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro p; funext j; exact Prod.eta (p j) }
  unfold FiniteLaw.expect
  rw [← FiniteLaw.sum_equiv e
    (fun ω => (CommonList.iid (P.prod Q) N).mass ω*F ω),Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [e,CommonList.iid,FiniteLaw.prod,Finset.prod_mul_distrib]
  change ((∏ j, P.mass (x j))*(∏ j, Q.mass (y j)))*F (fun j => (x j,y j)) =
    (∏ j, P.mass (x j))*((∏ j, Q.mass (y j))*F (fun j => (x j,y j)))
  ring

end FiniteFactor

def fairSign : FiniteLaw Bool := IndependentCounts.bernoulli (1/2) (by norm_num) (by norm_num)

def tag (p : Bool × Bool) : Fin 4 := if p.1 then 0 else if p.2 then 2 else 3

theorem category_factor (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] :
    categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G=
      ((IndependentCounts.bernoulli t ht ht1).prod fairSign).map tag := by
  apply FiniteLaw.ext_expect
  intro f
  rw [categoryLaw_expect,FiniteLaw.expect_map,FiniteLaw.expect_prod]
  simp only [fairSign,IndependentCounts.expect_bernoulli]
  simp only [tag,Bool.false_eq_true,if_false,if_true]
  ring

theorem original_categories_mask_sign (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N : ℕ) (F : (Fin N → Fin 4) → ℝ) :
    (CommonList.iid (categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G) N).expect F=
      (CommonList.iid (IndependentCounts.bernoulli t ht ht1) N).expect (fun low =>
        (CommonList.iid fairSign N).expect (fun sign => F (fun j => tag (low j,sign j)))) := by
  rw [category_factor t ht ht1 G,iid_map_expect,iid_prod_expect]

def rawRowPoint (p : Fin 4 × ℝ) : RowRival := (p.1,if p.1=0 then p.2 else 0)

lemma measurable_rawRowPoint : Measurable rawRowPoint :=
  measurable_fst.prodMk (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_snd measurable_const)

lemma rawRowPoint_dirac_prod (G : Measure ℝ) [SFinite G] (k : Fin 4) :
    ((Measure.dirac k).prod G).map rawRowPoint=G.map (fun b => (k,if k=0 then b else 0)) := by
  rw [Measure.dirac_prod,Measure.map_map measurable_rawRowPoint
    (show Measurable (Prod.mk k : ℝ → Fin 4 × ℝ) from by fun_prop)]
  rfl

theorem rawRowPoint_law (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] :
    ((FiniteLaw.probabilityMeasure
      (categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G)).prod G).map rawRowPoint=
        rivalLaw t 0 (1-t) G := by
  have hC : FiniteLaw.probabilityMeasure
      (categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G)=
      ENNReal.ofReal t • Measure.dirac 0+
      ENNReal.ofReal ((1-t)/2) • Measure.dirac 2+
      ENNReal.ofReal ((1-t)/2) • Measure.dirac 3 := by
    unfold FiniteLaw.probabilityMeasure
    simp only [categoryLaw_mass]
    simp [Fin.sum_univ_succ,add_assoc]
  rw [hC,Measure.add_prod,Measure.add_prod,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ measurable_rawRowPoint,Measure.map_add _ _ measurable_rawRowPoint,
    Measure.map_smul,Measure.map_smul,Measure.map_smul]
  simp only [rawRowPoint_dirac_prod,ite_true]
  have h2 : (fun b : ℝ => ((2:Fin 4),if (2:Fin 4)=0 then b else 0))=fun _ => ((2:Fin 4),(0:ℝ)) := by
    funext b
    simp only [show (2 : Fin 4) ≠ 0 by decide,if_false]
  have h3 : (fun b : ℝ => ((3:Fin 4),if (3:Fin 4)=0 then b else 0))=fun _ => ((3:Fin 4),(0:ℝ)) := by
    funext b
    simp only [show (3 : Fin 4) ≠ 0 by decide,if_false]
  rw [h2,h3,Measure.map_const,Measure.map_const,measure_univ,one_smul,one_smul]
  simp [rivalLaw]

theorem rawRowProfile_law (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N : ℕ) :
    ((FiniteLaw.probabilityMeasure
      (CommonList.iid (categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G) N)).prod
      (Measure.pi fun _ : Fin N => G)).map
        (fun p : (Fin N → Fin 4) × (Fin N → ℝ) => fun j => rawRowPoint (p.1 j,p.2 j))=
      Measure.pi (fun _ : Fin N => rivalLaw t 0 (1-t) G) := by
  rw [probabilityMeasure_iid]
  let C := categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 4) ℝ (Fin N)
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin 4) ℝ (Fin N)
    (fun _ => FiniteLaw.probabilityMeasure C) (fun _ => G)).symm
  have hm : Measurable (fun p : Fin N → Fin 4 × ℝ => fun j => rawRowPoint (p j)) :=
    measurable_pi_lambda _ (fun j => measurable_rawRowPoint.comp (measurable_pi_apply j))
  calc
    _ = (((Measure.pi (fun _ : Fin N => FiniteLaw.probabilityMeasure C)).prod
      (Measure.pi fun _ : Fin N => G)).map e.symm).map
        (fun p : Fin N → Fin 4 × ℝ => fun j => rawRowPoint (p j)) := by
      rw [Measure.map_map hm hp.measurable]
      rfl
    _ = _ := by
      rw [hp.map_eq,Measure.pi_map_pi (fun _ => measurable_rawRowPoint.aemeasurable),
        rawRowPoint_law t ht ht1 G]

theorem integral_original_mask_sign (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (N : ℕ)
    (f : (Fin N → RowRival) → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : ∀ ω, |f ω| ≤ M) :
    (∫ ω, f ω ∂Measure.pi (fun _ : Fin N => rivalLaw t 0 (1-t) G))=
      (CommonList.iid (IndependentCounts.bernoulli t ht ht1) N).expect (fun low =>
        (CommonList.iid fairSign N).expect (fun sign =>
          ∫ B : Fin N → ℝ, f (fun j => rawRowPoint (tag (low j,sign j),B j))
            ∂Measure.pi (fun _ : Fin N => G))) := by
  let F : (Fin N → Fin 4) × (Fin N → ℝ) → (Fin N → RowRival) :=
    fun p j => rawRowPoint (p.1 j,p.2 j)
  have hm : Measurable F := measurable_pi_lambda _ (fun j =>
    measurable_rawRowPoint.comp (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))
  let C := categoryLaw t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) (by ring) G
  have hi : Integrable (fun p => f (F p))
      ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod (Measure.pi fun _ : Fin N => G)) :=
    Integrable.of_bound (hf.comp hm).aestronglyMeasurable M
      (ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using hM (F p))
  rw [← rawRowProfile_law t ht ht1 G N,integral_map hm.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi,integral_probabilityMeasure,original_categories_mask_sign]

def upperSet {N : ℕ} (low : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun j => low j=false)

def positiveCount {N : ℕ} (low sign : Fin N → Bool) : ℕ :=
  PiBinomial.count ({true} : Set Bool) (upperSet low) sign

lemma classCount_two {N : ℕ} (low sign : Fin N → Bool) :
    classCount 2 (patternRow (fun j => tag (low j,sign j)))=positiveCount low sign := by
  rw [positiveCount,PiBinomial.count_eq_sum]
  simp only [classCount,patternRow,upperSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases Bool.eq_false_or_eq_true (low j) with hL | hL <;>
    rcases Bool.eq_false_or_eq_true (sign j) with hS | hS <;> simp [tag,hL,hS]

lemma upper_counts_total {N : ℕ} (low sign : Fin N → Bool) :
    classCount 2 (patternRow (fun j => tag (low j,sign j)))+
      classCount 3 (patternRow (fun j => tag (low j,sign j)))=(upperSet low).card := by
  rw [classCount,classCount,← Finset.sum_add_distrib,upperSet,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases Bool.eq_false_or_eq_true (low j) with hL | hL <;>
    rcases Bool.eq_false_or_eq_true (sign j) with hS | hS <;> simp [patternRow,tag,hL,hS]

lemma classCount_three {N : ℕ} (low sign : Fin N → Bool) :
    classCount 3 (patternRow (fun j => tag (low j,sign j)))=
      (upperSet low).card-positiveCount low sign := by
  have ht := upper_counts_total low sign
  rw [classCount_two] at ht
  omega

lemma classCount_one {N : ℕ} (low sign : Fin N → Bool) :
    classCount 1 (patternRow (fun j => tag (low j,sign j)))=0 := by
  apply Finset.sum_eq_zero
  intro j _
  rcases Bool.eq_false_or_eq_true (low j) with hL | hL <;>
    rcases Bool.eq_false_or_eq_true (sign j) with hS | hS <;> simp [patternRow,tag,hL,hS]

def boundedPositiveCount {N : ℕ} (low sign : Fin N → Bool) : Fin ((upperSet low).card+1) :=
  ⟨positiveCount low sign,Nat.lt_succ_of_le (PiBinomial.count_le _ _ _)⟩

lemma fair_mass_true : (FiniteLaw.probabilityMeasure fairSign).real {true}=1/2 := by
  rw [Measure.real,FiniteLaw.probabilityMeasure_singleton,
    ENNReal.toReal_ofReal (fairSign.nonneg true)]
  norm_num [fairSign,IndependentCounts.bernoulli]

theorem upper_count_law {N : ℕ} (low : Fin N → Bool) :
    FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure (CommonList.iid fairSign N))
      (boundedPositiveCount low) (measurable_of_countable _)=
      IndependentCounts.binomial (upperSet low).card (1/2) (by norm_num) (by norm_num) := by
  apply FiniteLaw.ext
  intro r
  rw [FiniteLaw.ofMeasure_mass,probabilityMeasure_iid,PiBinomial.binomial_mass]
  have hset : {sign : Fin N → Bool | boundedPositiveCount low sign=r}=
      {sign : Fin N → Bool | PiBinomial.count ({true} : Set Bool) (upperSet low) sign=r.val} := by
    ext sign
    simp [boundedPositiveCount,positiveCount,Fin.ext_iff]
  rw [hset]
  change (Measure.pi fun _ : Fin N => fairSign.probabilityMeasure).real
    {sign | PiBinomial.count ({true} : Set Bool) (upperSet low) sign=r.val} = _
  rw [PiBinomial.measureReal_count_eq _ _ (measurableSet_singleton true),fair_mass_true]

theorem upper_count_expect {N : ℕ} (low : Fin N → Bool) (F : ℕ → ℝ) :
    (CommonList.iid fairSign N).expect (fun sign => F (positiveCount low sign))=
      ∑ c ∈ Finset.range ((upperSet low).card+1),
        PiBinomial.pmf (upperSet low).card (1/2) c*F c := by
  have he := FiniteLaw.expect_ofMeasure
    (FiniteLaw.probabilityMeasure (CommonList.iid fairSign N))
    (boundedPositiveCount low) (measurable_of_countable _) (fun c => F c.val)
  rw [upper_count_law,integral_probabilityMeasure] at he
  have he' : (IndependentCounts.binomial (upperSet low).card (1/2) (by norm_num)
      (by norm_num)).expect (fun c => F c.val) =
      (CommonList.iid fairSign N).expect (fun sign => F (positiveCount low sign)) := by
    convert! he using 1
  rw [← he',FiniteLaw.expect]
  simp only [PiBinomial.binomial_mass]
  rw [Fin.sum_univ_eq_sum_range (fun c => PiBinomial.pmf (upperSet low).card (1/2) c*F c)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem actual_sign_fiber_moment {N : ℕ} (low : Fin N → Bool)
    (w : Weights ι) (h : ι → ℝ) (k : ℕ) (s : ℝ) :
    (CommonList.iid fairSign N).expect (fun sign =>
      (pathLaw w (imbalance (upperSet low).card (positiveCount low sign)) ∅).expect
        (fun path => deficitMoment k (s-selectedSum h
          (imbalance (upperSet low).card (positiveCount low sign)) path)))=
      fairMoment w h (upperSet low).card k s := by
  exact upper_count_expect low (fun c => pathMoment w h k (imbalance (upperSet low).card c) ∅ s)

end FCAppendix.Affine.Uniform06.EntrySignFiber
