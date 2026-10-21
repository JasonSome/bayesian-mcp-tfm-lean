import FCAppendix.Affine.Hybrid.PopulationRows
import FCAppendix.Affine.Hybrid.CategoryFibers

noncomputable section
namespace FCAppendix.Affine.Tail04.Observable
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open FCAppendix.Affine.Hybrid
open scoped BigOperators

structure Regions where
  d : ℝ
  R : ℝ
  Rp : ℝ
  U : ℝ
  H : ℝ
  d_nonneg : 0 ≤ d
  d_lt_R : d < R
  R_le_Rp : R ≤ Rp
  Rp_lt_one : Rp < 1
  one_le_U : 1 ≤ U
  U_lt_H : U < H

namespace Regions
variable (E : Regions)

lemma d_lt_one : E.d < 1 :=
  (E.d_lt_R.trans_le E.R_le_Rp).trans E.Rp_lt_one

lemma d_lt_H : E.d < E.H :=
  (E.d_lt_one.trans_le E.one_le_U).trans E.U_lt_H

lemma Rp_lt_H : E.Rp < E.H :=
  (E.Rp_lt_one.trans_le E.one_le_U).trans E.U_lt_H

def privateBids : Set ℝ := Icc E.R E.Rp ∪ Ici E.H

lemma measurableSet_privateBids : MeasurableSet E.privateBids :=
  measurableSet_Icc.union measurableSet_Ici

lemma private_above_low {b : ℝ} (hb : b ∈ E.privateBids) : E.d < b := by
  rcases hb with hb | hb
  · exact E.d_lt_R.trans_le hb.1
  · exact E.d_lt_H.trans_le hb

def role (b : ℝ) : Fin 4 :=
  if b ≤ E.d then 0 else if b ∈ Icc E.R E.Rp then 1
  else if E.H ≤ b then 3 else 2

lemma measurable_role : Measurable E.role := by
  unfold role
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Icc measurable_const
      (Measurable.ite measurableSet_Ici measurable_const measurable_const))

lemma role_low {b : ℝ} (hb : b ≤ E.d) : E.role b = 0 := by
  simp [role, hb]

lemma role_partial {b : ℝ} (hb : b ∈ Icc E.R E.Rp) : E.role b = 1 := by
  have hd : ¬ b ≤ E.d := not_le.mpr (E.d_lt_R.trans_le hb.1)
  simp [role, hd, hb]

lemma role_active {b : ℝ} (hb : b ∈ Icc (1 : ℝ) E.U) : E.role b = 2 := by
  have hd : ¬ b ≤ E.d := not_le.mpr (E.d_lt_one.trans_le hb.1)
  have hp : b ∉ Icc E.R E.Rp := by
    intro h; linarith [E.Rp_lt_one, hb.1, h.2]
  have hh : ¬ E.H ≤ b := not_le.mpr (hb.2.trans_lt E.U_lt_H)
  simp [role, hd, hp, hh]

lemma role_upper {b : ℝ} (hb : E.H ≤ b) : E.role b = 3 := by
  have hd : ¬ b ≤ E.d := not_le.mpr (E.d_lt_H.trans_le hb)
  have hp : b ∉ Icc E.R E.Rp := by
    intro h; linarith [E.Rp_lt_H, hb, h.2]
  simp [role, hd, hp, hb]

lemma role_at_upper_floor : E.role E.H = 3 := E.role_upper le_rfl

lemma role_unused {b : ℝ} (hU : E.U < b) (hH : b < E.H) : E.role b = 2 := by
  have hd : ¬ b ≤ E.d := not_le.mpr
    ((E.d_lt_one.trans_le E.one_le_U).trans hU)
  have hp : b ∉ Icc E.R E.Rp := by
    intro h; linarith [E.Rp_lt_one, E.one_le_U, hU, h.2]
  simp [role, hd, hp, not_le.mpr hH]

lemma role_private_iff (b : ℝ) :
    (E.role b = 1 ∨ E.role b = 3) ↔ b ∈ E.privateBids := by
  by_cases hl : b ≤ E.d
  · have hn : b ∉ E.privateBids := fun hp => not_lt_of_ge hl (E.private_above_low hp)
    simp [role, hl, hn]
  · by_cases hp : b ∈ Icc E.R E.Rp
    · simp [role, hl, hp, privateBids]
    · by_cases hh : E.H ≤ b <;> simp [role, hl, hp, hh, privateBids]

def lowActions : Set (JointAction 2) := {a | a.bid ≤ E.d}
def commonActions : Set (JointAction 2) := {a | E.d < a.bid ∧ a.bid ∉ E.privateBids}
def privateActions : Set (JointAction 2) := {a | a.bid ∈ E.privateBids}

lemma measurableSet_lowActions : MeasurableSet E.lowActions :=
  measurableSet_le (measurable_bid 2) measurable_const

lemma measurableSet_privateActions : MeasurableSet E.privateActions :=
  (measurable_bid 2) E.measurableSet_privateBids

lemma measurableSet_commonActions : MeasurableSet E.commonActions :=
  (measurableSet_lt measurable_const (measurable_bid 2)).inter
    E.measurableSet_privateActions.compl

lemma action_partition (μ : Measure (JointAction 2)) :
    μ.restrict E.lowActions + μ.restrict E.commonActions + μ.restrict E.privateActions = μ := by
  have hd : Disjoint E.lowActions E.commonActions := by
    apply Set.disjoint_left.mpr
    intro a hl hc
    exact not_lt_of_ge hl hc.1
  have hu : E.lowActions ∪ E.commonActions = E.privateActionsᶜ := by
    ext a
    change (a.bid ≤ E.d ∨ (E.d < a.bid ∧ a.bid ∉ E.privateBids)) ↔
      a.bid ∉ E.privateBids
    constructor
    · rintro (hl | hc)
      · exact fun hp => not_lt_of_ge hl (E.private_above_low hp)
      · exact hc.2
    · intro hn
      by_cases hl : a.bid ≤ E.d
      · exact Or.inl hl
      · exact Or.inr ⟨lt_of_not_ge hl, hn⟩
  rw [← Measure.restrict_union hd E.measurableSet_commonActions, hu]
  simpa only [compl_compl] using
    (Measure.restrict_add_restrict_compl (μ := μ) E.measurableSet_privateActions.compl)

def collapse (x : JointAction 2 × Equiv.Perm (Fin 2)) : LowBody.RowRival :=
  if x.1.bid ≤ E.d then (0, x.1.bid)
  else if x.1.bid ∈ E.privateBids then upperRow x.2 else (1, 0)

lemma measurable_collapse : Measurable E.collapse := by
  unfold collapse
  exact Measurable.ite
    (measurableSet_le ((measurable_bid 2).comp measurable_fst) measurable_const)
    (measurable_const.prodMk ((measurable_bid 2).comp measurable_fst))
    (Measurable.ite
      (((measurable_bid 2).comp measurable_fst) E.measurableSet_privateBids)
      ((measurable_of_countable upperRow).comp measurable_snd) measurable_const)

theorem collapse_law (μ : Measure (JointAction 2)) [IsProbabilityMeasure μ] :
    (μ.prod (permLaw 2)).map E.collapse =
      (((μ.restrict E.lowActions).map (fun a : JointAction 2 => a.bid)).map
        (fun b => ((0 : Fin 4), b))) +
      μ E.commonActions • Measure.dirac (1, 0) +
      (μ E.privateActions * ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (2, 0) +
      (μ E.privateActions * ENNReal.ofReal (1 / 2 : ℝ)) • Measure.dirac (3, 0) := by
  let μ₀ := μ.restrict E.lowActions
  let μ₁ := μ.restrict E.commonActions
  let μ₂ := μ.restrict E.privateActions
  have hμ : μ = μ₀ + μ₁ + μ₂ := (E.action_partition μ).symm
  have hlaw₀ : (μ₀.prod (permLaw 2)).map E.collapse =
      (μ₀.map (fun a => a.bid)).map (fun b => ((0 : Fin 4), b)) := by
    have heq : (μ₀.prod (permLaw 2)).map E.collapse =
        (μ₀.prod (permLaw 2)).map (fun x => ((0 : Fin 4), x.1.bid)) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ := μ₀) (ν := permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem E.measurableSet_lowActions : ∀ᵐ a ∂μ₀, a ∈ E.lowActions)
      exact hh.mono (fun x hx => if_pos hx)
    rw [heq]
    have hm : Measurable (fun a : JointAction 2 => ((0 : Fin 4), a.bid)) :=
      measurable_const.prodMk (measurable_bid 2)
    change (μ₀.prod (permLaw 2)).map
      ((fun a : JointAction 2 => ((0 : Fin 4), a.bid)) ∘ Prod.fst) = _
    rw [← Measure.map_map hm measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
    exact (Measure.map_map (measurable_const.prodMk measurable_id) (measurable_bid 2)).symm
  have hlaw₁ : (μ₁.prod (permLaw 2)).map E.collapse =
      μ E.commonActions • Measure.dirac (1, 0) := by
    have heq : (μ₁.prod (permLaw 2)).map E.collapse =
        (μ₁.prod (permLaw 2)).map (fun _ => ((1 : Fin 4), (0 : ℝ))) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ := μ₁) (ν := permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem E.measurableSet_commonActions : ∀ᵐ a ∂μ₁, a ∈ E.commonActions)
      exact hh.mono (fun x hx => by
        simp only [collapse, if_neg (not_le.mpr hx.1), if_neg hx.2])
    have ht : (μ₁.prod (permLaw 2)) univ = μ₁ univ := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ (μ := permLaw 2), mul_one]
    rw [heq, Measure.map_const, ht]
    simp only [μ₁, Measure.restrict_apply_univ]
  have hlaw₂ : (μ₂.prod (permLaw 2)).map E.collapse =
      μ E.privateActions • ((permLaw 2).map upperRow) := by
    have heq : (μ₂.prod (permLaw 2)).map E.collapse =
        (μ₂.prod (permLaw 2)).map (upperRow ∘ Prod.snd) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ := μ₂) (ν := permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem E.measurableSet_privateActions : ∀ᵐ a ∂μ₂, a ∈ E.privateActions)
      exact hh.mono (fun x hx => by
        simp only [collapse, if_neg (not_le.mpr (E.private_above_low hx)), if_pos (show x.1.bid ∈ E.privateBids from hx),
          Function.comp_apply])
    rw [heq, ← Measure.map_map (measurable_of_countable upperRow) measurable_snd,
      Measure.map_snd_prod, Measure.map_smul]
    simp only [μ₂, Measure.restrict_apply_univ]
  calc
    _ = ((μ₀ + μ₁ + μ₂).prod (permLaw 2)).map E.collapse := by rw [← hμ]
    _ = _ := by
      rw [Measure.add_prod, Measure.add_prod,
        Measure.map_add _ _ E.measurable_collapse,
        Measure.map_add _ _ E.measurable_collapse,
        hlaw₀, hlaw₁, hlaw₂, upperRow_law, smul_add, smul_smul, smul_smul]
      simp only [add_assoc, μ₀]

theorem collapse_eq_rivalLaw (μ : Measure (JointAction 2)) [IsProbabilityMeasure μ] :
    (μ.prod (permLaw 2)).map E.collapse =
      LowBody.rivalLaw (μ.real E.lowActions) (μ.real E.commonActions)
        (μ.real E.privateActions) ((cond μ E.lowActions).map (fun a => a.bid)) := by
  rw [E.collapse_law μ, LowBody.rivalLaw]
  have hl : ENNReal.ofReal (μ.real E.lowActions) •
      (((cond μ E.lowActions).map (fun a => a.bid)).map (fun b => ((0 : Fin 4), b))) =
      (((μ.restrict E.lowActions).map (fun a => a.bid)).map
        (fun b => ((0 : Fin 4), b))) := by
    rw [ofReal_measureReal, ← Measure.map_smul, ← Measure.map_smul, measure_smul_cond]
  have hh : ENNReal.ofReal (μ.real E.privateActions / 2) =
      μ E.privateActions * ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [show μ.real E.privateActions / 2 = μ.real E.privateActions * (1 / 2) by ring,
      ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal]
  rw [hl, ofReal_measureReal, hh]

def nativeRow {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (_Γ : FiniteGame m 2 c Seed) (x : UserDraw 2) : LowBody.RowRival :=
  E.collapse (x.1.2, x.2)

lemma measurable_nativeRow {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) : Measurable (E.nativeRow Γ) :=
  E.measurable_collapse.comp (measurable_fst.snd.prodMk measurable_snd)

theorem native_row_law {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) :
    (userLaw Γ).map (E.nativeRow Γ) =
      LowBody.rivalLaw ((nativeActionLaw Γ).real E.lowActions)
        ((nativeActionLaw Γ).real E.commonActions)
        ((nativeActionLaw Γ).real E.privateActions)
        ((cond (nativeActionLaw Γ) E.lowActions).map (fun a => a.bid)) := by
  have hm : Measurable (fun x : UserDraw 2 => (x.1.2, x.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hmap : (userLaw Γ).map (fun x : UserDraw 2 => (x.1.2, x.2)) =
      (nativeActionLaw Γ).prod (permLaw 2) := by
    have h := (Measure.map_prod_map (Γ.F ⊗ₘ Γ.σ) (permLaw 2)
      measurable_snd measurable_id).symm
    rw [Measure.map_id] at h
    exact h
  calc
    _ = ((userLaw Γ).map (fun x : UserDraw 2 => (x.1.2, x.2))).map E.collapse :=
      (Measure.map_map E.measurable_collapse hm).symm
    _ = _ := by rw [hmap]; exact E.collapse_eq_rivalLaw (nativeActionLaw Γ)

theorem native_deleted_rivals {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame (N + 1) 2 c Seed) (i : Fin (N + 1)) :
    (userProfileLaw Γ).map (fun x (j : Fin N) => E.nativeRow Γ (x (i.succAbove j))) =
      Measure.pi (fun _ : Fin N =>
        LowBody.rivalLaw ((nativeActionLaw Γ).real E.lowActions)
          ((nativeActionLaw Γ).real E.commonActions)
          ((nativeActionLaw Γ).real E.privateActions)
          ((cond (nativeActionLaw Γ) E.lowActions).map (fun a => a.bid))) :=
  deleted_rival_rows_law Γ i (E.nativeRow Γ) (E.measurable_nativeRow Γ) _
    (E.native_row_law Γ)

def markedTag (x : UserDraw 2) : Fin 6 :=
  if x.1.2.bid ≤ E.d then 0
  else if x.1.2.bid ∈ Icc E.R E.Rp then
    if (0 : Fin 2) ∈ firstK x.2 1 then 2 else 3
  else if E.H ≤ x.1.2.bid then
    if (0 : Fin 2) ∈ firstK x.2 1 then 4 else 5
  else 1

lemma measurable_markedTag : Measurable E.markedTag := by
  have hb : Measurable (fun x : UserDraw 2 => x.1.2.bid) :=
    (measurable_bid 2).comp measurable_fst.snd
  have hp : MeasurableSet {x : UserDraw 2 | (0 : Fin 2) ∈ firstK x.2 1} :=
    measurable_snd ((Set.to_countable {p : Equiv.Perm (Fin 2) |
      (0 : Fin 2) ∈ firstK p 1}).measurableSet)
  unfold markedTag
  exact Measurable.ite (measurableSet_le hb measurable_const) measurable_const
    (Measurable.ite (hb measurableSet_Icc)
      (Measurable.ite hp measurable_const measurable_const)
      (Measurable.ite (measurableSet_le measurable_const hb)
        (Measurable.ite hp measurable_const measurable_const) measurable_const))

def coarseTag (x : UserDraw 2) : Fin 4 := (E.collapse (x.1.2, x.2)).1

lemma measurable_coarseTag : Measurable E.coarseTag :=
  (E.measurable_collapse.comp (measurable_fst.snd.prodMk measurable_snd)).fst

theorem native_conditioned_private_partition {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed) (k : Fin m → Fin 4) :
    cond (userProfileLaw Γ) (categoryFiber E.coarseTag k) =
      Measure.pi (fun i : Fin m => cond (userLaw Γ) (E.coarseTag ⁻¹' {k i})) :=
  native_conditional_categoryFiber Γ E.coarseTag E.measurable_coarseTag k

theorem native_conditioned_marked_partition {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed) (k : Fin m → Fin 6) :
    cond (userProfileLaw Γ) (categoryFiber E.markedTag k) =
      Measure.pi (fun i : Fin m => cond (userLaw Γ) (E.markedTag ⁻¹' {k i})) :=
  native_conditional_categoryFiber Γ E.markedTag E.measurable_markedTag k

theorem native_private_partition_mass {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed) (k : Fin m → Fin 4) :
    (userProfileLaw Γ) (categoryFiber E.coarseTag k) =
      ∏ i, (userLaw Γ) (E.coarseTag ⁻¹' {k i}) :=
  categoryFiber_mass (userLaw Γ) E.coarseTag k

end Regions
end FCAppendix.Affine.Tail04.Observable
