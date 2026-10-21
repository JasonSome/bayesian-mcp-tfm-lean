import FCAppendix.Affine.Hybrid.Native02.NativeActiveTransport
import FCAppendix.Affine.Hybrid.NativeFocalReindex
import FCAppendix.Affine.Hybrid.ActivePhysicalPattern

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open Existence.Distributional
open scoped BigOperators

def physicalRow (d U : ℝ) (u : UserDraw 2) : RowRival :=
  if u.1.2.bid ≤ d then (0, u.1.2.bid)
  else if u.1.2.bid ≤ U then (1, u.1.2.bid)
  else upperRow u.2

lemma measurable_physicalRow (d U : ℝ) : Measurable (physicalRow d U) := by
  have hb : Measurable (fun u : UserDraw 2 => u.1.2.bid) :=
    (measurable_bid 2).comp measurable_fst.snd
  exact Measurable.ite (measurableSet_le hb measurable_const)
    (measurable_const.prodMk hb)
    (Measurable.ite (measurableSet_le hb measurable_const)
      (measurable_const.prodMk hb)
      ((measurable_of_countable upperRow).comp measurable_snd))

lemma physicalRow_tag (d U : ℝ) (u : UserDraw 2) :
    (physicalRow d U u).1 = (collapseAction d U (u.1.2, u.2)).1 := by
  unfold physicalRow collapseAction
  split_ifs <;> rfl

def physicalRivalLaw (s a h : ℝ) (G B : Measure ℝ) : Measure RowRival :=
  ENNReal.ofReal s • G.map (fun b => ((0 : Fin 4), b)) +
    ENNReal.ofReal a • B.map (fun b => ((1 : Fin 4), b)) +
    ENNReal.ofReal (h/2) • Measure.dirac (2, 0) +
    ENNReal.ofReal (h/2) • Measure.dirac (3, 0)

lemma physicalRow_low_population (P : ProbabilityMeasure (ℝ × JointAction 2))
    (d U : ℝ) (hP : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), x.2.bid ≤ d) :
    ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (physicalRow d U) =
      ((P : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)).map
        (fun b => ((0 : Fin 4), b)) := by
  have hp := (measurePreserving_fst (μ := (P : Measure (ℝ × JointAction 2)))
    (ν := permLaw 2)).quasiMeasurePreserving.ae hP
  have he : ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (physicalRow d U) =
      ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (fun u : UserDraw 2 => ((0 : Fin 4), u.1.2.bid)) := by
    apply Measure.map_congr
    filter_upwards [hp] with u hu
    exact if_pos hu
  rw [he]
  have hb : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  have ht : Measurable (fun b : ℝ => ((0 : Fin 4), b)) :=
    measurable_const.prodMk measurable_id
  have hh := (Measure.map_map (ht.comp hb) measurable_fst
    (μ := (P : Measure (ℝ × JointAction 2)).prod (permLaw 2))).symm
  simpa only [Measure.map_fst_prod, measure_univ, one_smul, Function.comp_def,
    Measure.map_map ht hb] using hh

lemma physicalRow_active_population (P : ProbabilityMeasure (ℝ × JointAction 2))
    (d U : ℝ)
    (hP : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), d < x.2.bid ∧ x.2.bid ≤ U) :
    ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (physicalRow d U) =
      ((P : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)).map
        (fun b => ((1 : Fin 4), b)) := by
  have hp := (measurePreserving_fst (μ := (P : Measure (ℝ × JointAction 2)))
    (ν := permLaw 2)).quasiMeasurePreserving.ae hP
  have he : ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (physicalRow d U) =
      ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (fun u : UserDraw 2 => ((1 : Fin 4), u.1.2.bid)) := by
    apply Measure.map_congr
    filter_upwards [hp] with u hu
    simp only [physicalRow, if_neg (not_le.mpr hu.1), if_pos hu.2]
  rw [he]
  have hb : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  have ht : Measurable (fun b : ℝ => ((1 : Fin 4), b)) :=
    measurable_const.prodMk measurable_id
  have hh := (Measure.map_map (ht.comp hb) measurable_fst
    (μ := (P : Measure (ℝ × JointAction 2)).prod (permLaw 2))).symm
  simpa only [Measure.map_fst_prod, measure_univ, one_smul, Function.comp_def,
    Measure.map_map ht hb] using hh

lemma physicalRow_upper_population (P : ProbabilityMeasure (ℝ × JointAction 2))
    {d U : ℝ} (hdU : d ≤ U)
    (hP : ∀ᵐ x ∂(P : Measure (ℝ × JointAction 2)), U < x.2.bid) :
    ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (physicalRow d U) =
      ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (2, 0) +
        ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (3, 0) := by
  have hp := (measurePreserving_fst (μ := (P : Measure (ℝ × JointAction 2)))
    (ν := permLaw 2)).quasiMeasurePreserving.ae hP
  calc
    _ = ((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (fun u : UserDraw 2 => upperRow u.2) := by
      apply Measure.map_congr
      filter_upwards [hp] with u hu
      simp only [physicalRow, if_neg (not_le.mpr (hdU.trans_lt hu)),
        if_neg (not_le.mpr hu)]
    _ = (permLaw 2).map upperRow := by
      change (((P : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (upperRow ∘ (Prod.snd : UserDraw 2 → Equiv.Perm (Fin 2)))) = _
      rw [← Measure.map_map (measurable_of_countable upperRow) measurable_snd]
      simp only [Measure.map_snd_prod, measure_univ, one_smul]
    _ = _ := upperRow_law

theorem population_physical_row {d U : ℝ} (hdU : d ≤ U)
    (s a h : ℝ) (hh : 0 ≤ h) (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ d)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), d < x.2.bid ∧ x.2.bid ≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid) :
    ((populationJoint s a h PL PA PH).prod (permLaw 2)).map (physicalRow d U) =
      physicalRivalLaw s a h
        ((PL : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid))
        ((PA : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)) := by
  rw [populationJoint, Measure.add_prod, Measure.add_prod,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ (measurable_physicalRow d U),
    Measure.map_add _ _ (measurable_physicalRow d U)]
  simp only [Measure.map_smul]
  rw [physicalRow_low_population PL d U hL,
    physicalRow_active_population PA d U hA, physicalRow_upper_population PH hdU hH,
    smul_add, smul_smul, smul_smul]
  have hhalf : ENNReal.ofReal h * ENNReal.ofReal (1/2 : ℝ) = ENNReal.ofReal (h/2) := by
    rw [← ENNReal.ofReal_mul hh]
    congr 1
    ring
  rw [hhalf]
  exact (add_assoc _ _ _).symm

theorem native_population_physical_row {m c : ℕ} {d U : ℝ} (hdU : d ≤ U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h = 1)
    (PL PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ d)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)), d < x.2.bid ∧ x.2.bid ≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), U < x.2.bid)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    let P := populationLaw s a h hs ha hh hsum PL PA PH
    let Γ := PopulationGame.game m c P η hη0 hη1 U
    (userLaw Γ).map (physicalRow d U) = physicalRivalLaw s a h
      ((PL : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid))
      ((PA : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)) := by
  dsimp only
  rw [userLaw, PopulationGame.joint_law]
  exact population_physical_row hdU s a h hh PL PA PH hL hA hH

def physicalDeletedRow {N : ℕ} (d U : ℝ) (i : Fin (N+1))
    (z : UserProfile (N+1) 2) : Fin N → RowRival :=
  fun j => physicalRow d U (z (i.succAbove j))

lemma measurable_physicalDeletedRow {N : ℕ} (d U : ℝ) (i : Fin (N+1)) :
    Measurable (physicalDeletedRow d U i) :=
  measurable_pi_lambda _ (fun j => (measurable_physicalRow d U).comp
    (measurable_pi_apply (i.succAbove j)))

theorem deleted_physical_rival_rows_law {N c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame (N+1) 2 c Seed)
    (d U : ℝ) (i : Fin (N+1)) (ν : Measure RowRival)
    (hrow : (userLaw Γ).map (physicalRow d U) = ν) :
    (userProfileLaw Γ).map (physicalDeletedRow d U i) =
      Measure.pi (fun _ : Fin N => ν) :=
  deleted_rival_rows_law Γ i (physicalRow d U) (measurable_physicalRow d U) ν hrow

def physicalRowPoint (x : Fin 4 × (ℝ × ℝ)) : RowRival :=
  (x.1, if x.1 = 0 then x.2.1 else if x.1 = 1 then x.2.2 else 0)

lemma measurable_physicalRowPoint : Measurable physicalRowPoint :=
  measurable_fst.prodMk (Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const) measurable_snd.fst
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
      measurable_snd.snd measurable_const))

section Categorical
variable (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h = 1)
    (G B : Measure ℝ) [IsProbabilityMeasure G] [IsProbabilityMeasure B]
local notation "C" => categoryLaw s a h hs ha hh hsum G

lemma physical_category_probabilityMeasure_explicit :
    FiniteLaw.probabilityMeasure C =
      ENNReal.ofReal s • Measure.dirac 0 + ENNReal.ofReal a • Measure.dirac 1 +
        ENNReal.ofReal (h/2) • Measure.dirac 2 + ENNReal.ofReal (h/2) • Measure.dirac 3 := by
  unfold FiniteLaw.probabilityMeasure
  simp only [categoryLaw_mass]
  simp [Fin.sum_univ_succ]
  abel

lemma physicalRowPoint_dirac_prod (k : Fin 4) :
    ((Measure.dirac k).prod (G.prod B)).map physicalRowPoint =
      (G.prod B).map (fun x : ℝ × ℝ =>
        (k, if k = 0 then x.1 else if k = 1 then x.2 else 0)) := by
  rw [Measure.dirac_prod, Measure.map_map measurable_physicalRowPoint
    (show Measurable (Prod.mk k : ℝ × ℝ → Fin 4 × (ℝ × ℝ)) from
      measurable_const.prodMk measurable_id)]
  rfl

theorem physicalRowPoint_law :
    ((FiniteLaw.probabilityMeasure C).prod (G.prod B)).map physicalRowPoint =
      physicalRivalLaw s a h G B := by
  rw [physical_category_probabilityMeasure_explicit s a h hs ha hh hsum G]
  rw [Measure.add_prod, Measure.add_prod, Measure.add_prod,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.prod_smul_left, Measure.map_add _ _ measurable_physicalRowPoint,
    Measure.map_add _ _ measurable_physicalRowPoint,
    Measure.map_add _ _ measurable_physicalRowPoint]
  simp only [Measure.map_smul, physicalRowPoint_dirac_prod]
  have h0 : (G.prod B).map (fun x : ℝ × ℝ => ((0 : Fin 4), x.1)) =
      G.map (fun b => ((0 : Fin 4), b)) := by
    have ht : Measurable (fun b : ℝ => ((0 : Fin 4), b)) :=
      measurable_const.prodMk measurable_id
    rw [show (fun x : ℝ × ℝ => ((0 : Fin 4), x.1)) =
      (fun b : ℝ => ((0 : Fin 4), b)) ∘ Prod.fst from rfl,
      ← Measure.map_map ht measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  have h1 : (G.prod B).map (fun x : ℝ × ℝ => ((1 : Fin 4), x.2)) =
      B.map (fun b => ((1 : Fin 4), b)) := by
    have ht : Measurable (fun b : ℝ => ((1 : Fin 4), b)) :=
      measurable_const.prodMk measurable_id
    rw [show (fun x : ℝ × ℝ => ((1 : Fin 4), x.2)) =
      (fun b : ℝ => ((1 : Fin 4), b)) ∘ Prod.snd from rfl,
      ← Measure.map_map ht measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  norm_num only [Fin.reduceEq, if_true, if_false, show (1 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide]
  rw [h0, h1, Measure.map_const, Measure.map_const, measure_univ, one_smul, one_smul]
  rfl

include hs ha hh hsum in

lemma physicalRivalLaw_probability : IsProbabilityMeasure (physicalRivalLaw s a h G B) := by
  rw [← physicalRowPoint_law s a h hs ha hh hsum G B]
  exact Measure.isProbabilityMeasure_map measurable_physicalRowPoint.aemeasurable

lemma physicalPairedRowProfile_law (N : ℕ) :
    ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
      (Measure.pi (fun _ : Fin N => G.prod B))).map
        (fun p : (Fin N → Fin 4) × (Fin N → ℝ × ℝ) =>
          fun j => physicalRowPoint (p.1 j, p.2 j)) =
      Measure.pi (fun _ : Fin N => physicalRivalLaw s a h G B) := by
  rw [probabilityMeasure_iid]
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Fin 4) (ℝ × ℝ) (Fin N)
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin 4) (ℝ × ℝ) (Fin N)
    (fun _ => FiniteLaw.probabilityMeasure C) (fun _ => G.prod B)).symm
  have hm : Measurable (fun p : Fin N → Fin 4 × (ℝ × ℝ) =>
      fun j => physicalRowPoint (p j)) :=
    measurable_pi_lambda _ (fun j => measurable_physicalRowPoint.comp (measurable_pi_apply j))
  calc
    _ = (((Measure.pi (fun _ : Fin N => FiniteLaw.probabilityMeasure C)).prod
        (Measure.pi (fun _ : Fin N => G.prod B))).map e.symm).map
          (fun p : Fin N → Fin 4 × (ℝ × ℝ) => fun j => physicalRowPoint (p j)) := by
      rw [Measure.map_map hm hp.measurable]
      rfl
    _ = _ := by
      rw [hp.map_eq, Measure.pi_map_pi (fun _ => measurable_physicalRowPoint.aemeasurable),
        physicalRowPoint_law s a h hs ha hh hsum G B]

def physicalRowProfile (N : ℕ)
    (p : (Fin N → Fin 4) × ((Fin N → ℝ) × (Fin N → ℝ))) : Fin N → RowRival :=
  fun j => physicalRowPoint (p.1 j, p.2.1 j, p.2.2 j)

lemma measurable_physicalRowProfile (N : ℕ) : Measurable (physicalRowProfile N) :=
  measurable_pi_lambda _ (fun j => measurable_physicalRowPoint.comp
    (((measurable_pi_apply j).comp measurable_fst).prodMk
      (((measurable_pi_apply j).comp measurable_snd.fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd.snd))))

theorem physicalRowProfile_law (N : ℕ) :
    ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
      ((Measure.pi (fun _ : Fin N => G)).prod (Measure.pi (fun _ : Fin N => B)))).map
        (physicalRowProfile N) =
      Measure.pi (fun _ : Fin N => physicalRivalLaw s a h G B) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin N)
  have hp := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N)
    (fun _ => G) (fun _ => B)).symm
  let f : (Fin N → Fin 4) × (Fin N → ℝ × ℝ) → Fin N → RowRival :=
    fun p j => physicalRowPoint (p.1 j, p.2 j)
  have hf : Measurable f := measurable_pi_lambda _ (fun j =>
    measurable_physicalRowPoint.comp (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))
  have hj := ((MeasurePreserving.id
    (FiniteLaw.probabilityMeasure (CommonList.iid C N))).prod hp).map_eq
  calc
    _ = (((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
        ((Measure.pi (fun _ : Fin N => G)).prod (Measure.pi (fun _ : Fin N => B)))).map
          (Prod.map id e.symm)).map f := by
      rw [Measure.map_map hf (measurable_id.prodMap hp.measurable)]
      rfl
    _ = _ := by
      rw [hj]
      exact physicalPairedRowProfile_law s a h hs ha hh hsum G B N

theorem integral_physicalRowProfile (N : ℕ) (f : (Fin N → RowRival) → ℝ)
    (hf : Measurable f) (M : ℝ)
    (hM : ∀ᵐ p ∂(FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
      ((Measure.pi (fun _ : Fin N => G)).prod (Measure.pi (fun _ : Fin N => B))),
        |f (physicalRowProfile N p)| ≤ M) :
    (∫ r, f r ∂Measure.pi (fun _ : Fin N => physicalRivalLaw s a h G B)) =
      (CommonList.iid C N).expect (fun kind =>
        ∫ b : (Fin N → ℝ) × (Fin N → ℝ),
          f (fun j => physicalRowPoint (kind j, b.1 j, b.2 j))
          ∂(Measure.pi (fun _ : Fin N => G)).prod (Measure.pi (fun _ : Fin N => B))) := by
  have hm := measurable_physicalRowProfile N
  have hi : Integrable (fun p => f (physicalRowProfile N p))
      ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
        ((Measure.pi (fun _ : Fin N => G)).prod (Measure.pi (fun _ : Fin N => B)))) :=
    Integrable.of_bound (hf.comp hm).aestronglyMeasurable M
      (hM.mono (fun _ hp => by simpa only [Real.norm_eq_abs] using hp))
  rw [← physicalRowProfile_law s a h hs ha hh hsum G B N,
    integral_map hm.aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi, integral_probabilityMeasure]
  rfl

end Categorical

lemma physicalRow_lower_entry {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (u : UserDraw 2) (hgap : u.1.2.bid ≤ U ∨ R ≤ u.1.2.bid) :
    (if u.1.2.bid < R then some u.1.2.bid else none) =
      if (physicalRow d U u).1 = 0 ∨ (physicalRow d U u).1 = 1
      then some (physicalRow d U u).2 else none := by
  by_cases hd : u.1.2.bid ≤ d
  · simp [physicalRow, hd, (hd.trans hdU).trans_lt hUR]
  · by_cases hU : u.1.2.bid ≤ U
    · simp [physicalRow, hd, hU, hU.trans_lt hUR]
    · have hR : R ≤ u.1.2.bid := hgap.resolve_left hU
      by_cases hr : (0 : Fin 2) ∈ firstK u.2 1 <;>
        simp [physicalRow, hd, hU, not_lt.mpr hR, upperRow, hr]

lemma physicalRow_upper_entry {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R)
    (u : UserDraw 2)
    (hu : (u.1.2.bid < R ∧ u.1.2.routeCount = 2) ∨
      (R ≤ u.1.2.bid ∧ u.1.2.routeCount = 1))
    (hgap : u.1.2.bid ≤ U ∨ R ≤ u.1.2.bid) (j : Fin 2) :
    (R ≤ u.1.2.bid ∧ j ∈ firstK u.2 u.1.2.routeCount) ↔
      (physicalRow d U u).1 = NativeContinuation.upperTag j := by
  rcases hu with ⟨hb, hr⟩ | ⟨hb, hr⟩
  · have hU : u.1.2.bid ≤ U := hgap.resolve_right (not_le.mpr hb)
    by_cases hd : u.1.2.bid ≤ d
    · simp [physicalRow, hd, not_le.mpr hb,
        Ne.symm (NativeContinuation.upperTag_ne_zero j)]
    · simp [physicalRow, hd, hU, not_le.mpr hb,
        Ne.symm (NativeContinuation.upperTag_ne_one j)]
  · have hU : ¬ u.1.2.bid ≤ U := not_le.mpr (hUR.trans_le hb)
    have hd : ¬ u.1.2.bid ≤ d := fun h => hU (h.trans hdU)
    simp only [physicalRow, if_neg hd, if_neg hU, hr, hb, true_and]
    exact (NativeContinuation.upperRow_tag u.2 j).symm

lemma closedKind_upper_iff {m : ℕ} (R : ℝ) (z : UserProfile m 2) (i : Fin m) :
    closedKind R z i = 2 ↔ R ≤ (z i).1.2.bid := by
  by_cases hb : (z i).1.2.bid < R
  · simp [closedKind, hb, not_le.mpr hb]
  · simp [closedKind, hb, le_of_not_gt hb]

def physicalRowContext {N : ℕ} (b : ℝ) (r : Fin N → RowRival) :
    ClassifiedContext (N+1) :=
  (Fin.cons (some b) (fun j => if (r j).1 = 0 ∨ (r j).1 = 1 then some (r j).2 else none),
    classCount 2 r, classCount 3 r)

lemma measurable_physicalRowContext {N : ℕ} (b : ℝ) :
    Measurable (physicalRowContext (N := N) b) := by
  have hl : Measurable (fun r : Fin N → RowRival =>
      Fin.cons (α := fun _ => Option ℝ) (some b) (fun j => if (r j).1 = 0 ∨ (r j).1 = 1
        then some (r j).2 else none)) := by
    apply measurable_pi_lambda
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_const
    · exact Measurable.ite
        ((measurableSet_eq_fun (measurable_pi_apply j).fst measurable_const).union
          (measurableSet_eq_fun (measurable_pi_apply j).fst measurable_const))
        (measurable_some.comp (measurable_pi_apply j).snd) measurable_const
  have hc (k : Fin 4) : Measurable (fun r : Fin N → RowRival => classCount k r) := by
    unfold classCount
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_pi_apply j).fst measurable_const)
      measurable_const measurable_const
  exact hl.prodMk ((hc 2).prodMk (hc 3))

lemma actualClosedContext_reindex {m : ℕ} (e : Equiv.Perm (Fin m))
    (R : ℝ) (z : UserProfile m 2) :
    actualClosedContext R (z ∘ e) =
      NativeContinuation.reindexContext e (actualClosedContext R z) := by
  apply Prod.ext
  · funext i
    rfl
  · apply Prod.ext
    · change (∑ i : Fin m, if closedKind R (z ∘ e) i = 2 ∧
        (0 : Fin 2) ∈ (drawsRealization (z ∘ e)).recipients i then 1 else 0) = _
      exact Equiv.sum_comp e (fun i => if closedKind R z i = 2 ∧
        (0 : Fin 2) ∈ (drawsRealization z).recipients i then 1 else 0)
    · change (∑ i : Fin m, if closedKind R (z ∘ e) i = 2 ∧
        (1 : Fin 2) ∈ (drawsRealization (z ∘ e)).recipients i then 1 else 0) = _
      exact Equiv.sum_comp e (fun i => if closedKind R z i = 2 ∧
        (1 : Fin 2) ∈ (drawsRealization z).recipients i then 1 else 0)

theorem actualClosedContext_eq_physicalRow_zero {N : ℕ} {d U R : ℝ}
    (hdU : d ≤ U) (hUR : U < R) (z : UserProfile (N+1) 2)
    (hz : z ∈ closedProfiles (N+1) R)
    (hgap : ∀ k, (z k).1.2.bid ≤ U ∨ R ≤ (z k).1.2.bid)
    (hf : (z 0).1.2.bid ≤ U) :
    actualClosedContext R z =
      physicalRowContext (z 0).1.2.bid (physicalDeletedRow d U 0 z) := by
  have hzero (j : Fin N) : (0 : Fin (N+1)).succAbove j = j.succ := by simp
  have hu (j : Fin 2) :
      TaggedLocal.upperAt (closedKind R z) (drawsRealization z) j =
        classCount (NativeContinuation.upperTag j) (physicalDeletedRow d U 0 z) := by
    have hterm (k : Fin (N+1)) :
        (closedKind R z k = 2 ∧ j ∈ (drawsRealization z).recipients k) ↔
          (physicalRow d U (z k)).1 = NativeContinuation.upperTag j := by
      rw [closedKind_upper_iff]
      exact physicalRow_upper_entry hdU hUR (z k) (hz k) (hgap k) j
    have hf0 : ¬ (physicalRow d U (z 0)).1 = NativeContinuation.upperTag j := by
      intro hh
      have hR := ((physicalRow_upper_entry hdU hUR (z 0) (hz 0) (hgap 0) j).mpr hh).1
      exact (not_le.mpr (hf.trans_lt hUR)) hR
    unfold TaggedLocal.upperAt
    simp_rw [hterm]
    rw [Fin.sum_univ_succ]
    simp only [if_neg hf0, zero_add]
    unfold classCount
    apply Finset.sum_congr rfl
    intro k _
    simp only [physicalDeletedRow, hzero]
  apply Prod.ext
  · change lowerPart R (observe (drawsRealization z) 0) = _
    rw [lowerPart_observe z hz 0]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [physicalRowContext, hf.trans_lt hUR]
    · simpa only [physicalRowContext, Fin.cons_succ, physicalDeletedRow,
        hzero] using physicalRow_lower_entry hdU hUR (z j.succ) (hgap j.succ)
  · exact Prod.ext (by simpa only [actualClosedContext, physicalRowContext, show NativeContinuation.upperTag (0 : Fin 2) = (2 : Fin 4) from rfl] using hu 0)
      (by simpa only [actualClosedContext, physicalRowContext, show NativeContinuation.upperTag (1 : Fin 2) = (3 : Fin 4) from rfl] using hu 1)

def reindexedPhysicalContext {N : ℕ} (i : Fin (N+1)) (b : ℝ)
    (r : Fin N → RowRival) : ClassifiedContext (N+1) :=
  NativeContinuation.reindexContext (NativeContinuation.focalIndex i).symm
    (physicalRowContext b r)

lemma measurable_reindexedPhysicalContext {N : ℕ} (i : Fin (N+1)) (b : ℝ) :
    Measurable (reindexedPhysicalContext (N := N) i b) := by
  have hm := measurable_physicalRowContext (N := N) b
  exact (measurable_pi_lambda _ (fun j =>
    (measurable_pi_apply ((NativeContinuation.focalIndex i).symm j)).comp hm.fst)).prodMk hm.snd

theorem actualClosedContext_eq_physicalRow {N : ℕ} {d U R : ℝ}
    (hdU : d ≤ U) (hUR : U < R) (z : UserProfile (N+1) 2)
    (hz : z ∈ closedProfiles (N+1) R)
    (hgap : ∀ k, (z k).1.2.bid ≤ U ∨ R ≤ (z k).1.2.bid)
    (i : Fin (N+1)) (hf : (z i).1.2.bid ≤ U) :
    actualClosedContext R z =
      reindexedPhysicalContext i (z i).1.2.bid (physicalDeletedRow d U i z) := by
  let e := NativeContinuation.focalIndex i
  have he := actualClosedContext_eq_physicalRow_zero hdU hUR (z ∘ e)
    (fun k => hz (e k)) (fun k => hgap (e k))
    (by simpa only [e, Function.comp_apply, NativeContinuation.focalIndex_zero] using hf)
  rw [actualClosedContext_reindex] at he
  have hr : physicalDeletedRow d U 0 (z ∘ e) = physicalDeletedRow d U i z := by
    funext j
    simp [physicalDeletedRow, e]
  simp only [Function.comp_apply, e, NativeContinuation.focalIndex_zero, hr] at he
  have hh := congrArg (NativeContinuation.reindexContext e.symm) he
  simpa only [NativeContinuation.reindexContext, reindexedPhysicalContext,
    Function.comp_def, Equiv.apply_symm_apply, e] using hh

theorem insertedLowerContext_eq_physicalRow {N : ℕ} {d U R : ℝ}
    (hdU : d ≤ U) (hUR : U < R) (i : Fin (N+1)) (act : JointAction 2)
    (hb : act.bid ≤ U) (hk : act.routeCount = 2)
    (z : UserProfile (N+1) 2) (hz : z ∈ closedProfiles (N+1) R)
    (hgap : ∀ k, (z k).1.2.bid ≤ U ∨ R ≤ (z k).1.2.bid) :
    insertedLowerContext R i act z =
      reindexedPhysicalContext i act.bid (physicalDeletedRow d U i z) := by
  have hi := insertedLowerProfile_mem i act (hb.trans_lt hUR) hk z hz
  have hg : ∀ k, ((insertedLowerProfile i act z) k).1.2.bid ≤ U ∨
      R ≤ ((insertedLowerProfile i act z) k).1.2.bid := by
    intro k
    by_cases hki : k = i
    · subst k
      left
      simpa [insertedLowerProfile] using hb
    · simpa only [insertedLowerProfile, Function.update_of_ne hki] using hgap k
  rw [insertedLowerContext_eq_actual i act (hb.trans_lt hUR) hk z hz,
    actualClosedContext_eq_physicalRow hdU hUR (insertedLowerProfile i act z) hi hg i
      (by simpa [insertedLowerProfile] using hb)]
  have hr : physicalDeletedRow d U i (insertedLowerProfile i act z) =
      physicalDeletedRow d U i z := by
    funext j
    simp only [physicalDeletedRow, insertedLowerProfile,
      Function.update_of_ne (Fin.succAbove_ne i j)]
  rw [hr]
  congr 1
  simp only [insertedLowerProfile, Function.update_self]

lemma profile_noGap_support {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (U R : ℝ)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid) :
    ∀ᵐ z ∂userProfileLaw Γ, ∀ k : Fin m,
      (z k).1.2.bid ≤ U ∨ R ≤ (z k).1.2.bid := by
  have hu : ∀ᵐ u ∂userLaw Γ, u.1.2.bid ≤ U ∨ R ≤ u.1.2.bid :=
    (measurePreserving_fst (μ := Γ.F ⊗ₘ Γ.σ) (ν := permLaw 2)).quasiMeasurePreserving.ae hgap
  exact ae_all_iff.mpr (fun k =>
    (measurePreserving_eval (fun _ : Fin m => userLaw Γ) k).quasiMeasurePreserving.ae hu)

lemma measurable_privateContextLaw_expect {m c : ℕ} (C : ContextPolicy m c unitInterval)
    (i : Fin m) (f : Fin 3 → ℝ) :
    Measurable (fun X => (privateContextLaw C X i).expect f) := by
  have he (X : ClassifiedContext m) : (privateContextLaw C X i).expect f =
      (1-privateAcceptance C 0 X i)*(1-privateAcceptance C 1 X i)*f 0 +
      (privateAcceptance C 0 X i*(1-privateAcceptance C 1 X i) +
        (1-privateAcceptance C 0 X i)*privateAcceptance C 1 X i)*f 1 +
      privateAcceptance C 0 X i*privateAcceptance C 1 X i*f 2 := by
    have hh := privateContextLaw_masses C X i
    dsimp only at hh
    change (∑ k : Fin 3, (privateContextLaw C X i).mass k * f k) = _
    rw [Fin.sum_univ_three, hh.1, hh.2.1, hh.2.2]
  simp_rw [he]
  have h0 := measurable_privateAcceptance C 0 i
  have h1 := measurable_privateAcceptance C 1 i
  fun_prop

theorem closed_broadcast_count_physicalRows {N c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R) (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (ν : Measure RowRival) (hrow : (userLaw Γ).map (physicalRow d U) = ν)
    (i : Fin (N+1)) (act : JointAction 2) (hb : act.bid ≤ U)
    (hk : act.routeCount = 2) (f : Fin 3 → ℝ) :
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect f =
      ∫ r, (privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect f
        ∂Measure.pi (fun _ : Fin N => ν) := by
  rw [closed_broadcast_count_expectation C Γ hseed hfull i act (hb.trans_lt hUR) hk]
  calc
    _ = ∫ z, (privateContextLaw C (reindexedPhysicalContext i act.bid
        (physicalDeletedRow d U i z)) i).expect f ∂userProfileLaw Γ := by
      apply integral_congr_ae
      filter_upwards [hfull, profile_noGap_support Γ U R hgap] with z hz hzgap
      rw [insertedLowerContext_eq_physicalRow hdU hUR i act hb hk z hz hzgap]
    _ = _ := by
      rw [← deleted_physical_rival_rows_law Γ d U i ν hrow]
      exact (integral_map (measurable_physicalDeletedRow d U i).aemeasurable
        ((measurable_privateContextLaw_expect C i f).comp
          (measurable_reindexedPhysicalContext i act.bid)).aestronglyMeasurable).symm

theorem closed_singleton_payoff_physicalRows {N c : ℕ}
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d ≤ U) (hUR : U < R) (hg : Γ.g = 0)
    (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (ν : Measure RowRival) (hrow : (userLaw Γ).map (physicalRow d U) = ν)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid ≤ U)
    (hk : act.routeCount = 1) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act =
      ∫ r, (privateContextLaw C (reindexedPhysicalContext i act.bid r) i).expect
        (fun k => ((v-act.bid)/2)*(k.val : ℝ)) ∂Measure.pi (fun _ : Fin N => ν) := by
  let broad := NativeLowIncentives.broadcast act.bid act.bid_nonneg
  have hl := closed_broadcast_count_physicalRows C Γ hdU hUR hseed hfull hgap ν hrow
    i broad hb rfl (fun k => (k.val : ℝ))
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome broad).load =
    ∫ r, (privateContextLaw C (reindexedPhysicalContext i act.bid r) i).load
      ∂Measure.pi (fun _ : Fin N => ν) at hl
  rw [load_eq_mean _ (by norm_num : 0 < 2),
    show broad.routeCount = 2 from rfl, Nat.cast_ofNat] at hl
  simp_rw [FiniteLaw.expect_const_mul]
  rw [integral_const_mul, singleton_payoff _ (by norm_num : 0 < 2) i act hk v]
  change (v-Γ.g-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid = _
  change (v-Γ.g-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid =
    ((v-act.bid)/2)*(∫ r, (privateContextLaw C (reindexedPhysicalContext i act.bid r) i).load ∂Measure.pi (fun _ : Fin N => ν))
  rw [hg, ← hl]
  change (v-0-act.bid)*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid =
    ((v-act.bid)/2)*(2*meanAcceptProb (ClosedPolicy.nativeGame C Γ R) i act.bid)
  ring

end FCAppendix.Affine.Hybrid.Native02
