import FCAppendix.Affine.Hybrid.NativeSeed
import FCAppendix.Affine.LowBody.Rows

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Game Set
open scoped BigOperators

def upperRow (τ : Equiv.Perm (Fin 2)) : LowBody.RowRival :=
  if (0 : Fin 2) ∈ firstK τ 1 then (2,0) else (3,0)

lemma upperRow_law : (permLaw 2).map upperRow =
    ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (2,0)+
      ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (3,0) := by
  classical
  let P : Set (Equiv.Perm (Fin 2)) := {τ | (0 : Fin 2) ∈ firstK τ 1}
  have hP : MeasurableSet P := (Set.to_countable P).measurableSet
  have hhalf : permLaw 2 P = ENNReal.ofReal (1/2 : ℝ) := by
    rw [←ofReal_measureReal]
    congr 1
    simpa only [P,Nat.cast_one,Nat.cast_ofNat] using permLaw_mem_firstK 2 1 (by omega) (by omega) 0
  have hcomp : permLaw 2 Pᶜ = ENNReal.ofReal (1/2 : ℝ) := by
    rw [measure_compl hP (measure_ne_top _ _),measure_univ,hhalf]
    rw [←ENNReal.ofReal_one,←ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have hsplit := Measure.restrict_add_restrict_compl (μ:=permLaw 2) hP
  have hm : Measurable upperRow := measurable_of_countable _
  calc
    _ = ((permLaw 2).restrict P+(permLaw 2).restrict Pᶜ).map upperRow :=
      congrArg (fun μ : Measure (Equiv.Perm (Fin 2))=>μ.map upperRow) hsplit.symm
    _ = _ := by
      rw [Measure.map_add _ _ hm]
      have h₀ : ((permLaw 2).restrict P).map upperRow=
          ((permLaw 2).restrict P).map (fun _=>((2:Fin 4),(0:ℝ))) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hP] with τ hτ
        exact if_pos hτ
      have h₁ : ((permLaw 2).restrict Pᶜ).map upperRow=
          ((permLaw 2).restrict Pᶜ).map (fun _=>((3:Fin 4),(0:ℝ))) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hP.compl] with τ hτ
        exact if_neg hτ
      rw [h₀,h₁,Measure.map_const,Measure.map_const,
        Measure.restrict_apply_univ,Measure.restrict_apply_univ,hhalf,hcomp]

def collapseAction (d U : ℝ) (x : JointAction 2 × Equiv.Perm (Fin 2)) : LowBody.RowRival :=
  if x.1.bid≤d then (0,x.1.bid) else if x.1.bid≤U then (1,0) else upperRow x.2

lemma measurable_collapseAction (d U : ℝ) : Measurable (collapseAction d U) := by
  unfold collapseAction
  exact Measurable.ite (measurableSet_le ((measurable_bid 2).comp measurable_fst) measurable_const)
    (measurable_const.prodMk ((measurable_bid 2).comp measurable_fst))
    (Measurable.ite (measurableSet_le ((measurable_bid 2).comp measurable_fst) measurable_const)
      measurable_const ((measurable_of_countable upperRow).comp measurable_snd))

def actionLow (d : ℝ) : Set (JointAction 2) := {a | a.bid≤d}
def actionActive (d U : ℝ) : Set (JointAction 2) := {a | d<a.bid ∧ a.bid≤U}
def actionUpper (U : ℝ) : Set (JointAction 2) := {a | U<a.bid}

lemma measurableSet_actionLow (d : ℝ) : MeasurableSet (actionLow d) :=
  measurableSet_le (measurable_bid 2) measurable_const
lemma measurableSet_actionActive (d U : ℝ) : MeasurableSet (actionActive d U) :=
  (measurableSet_lt measurable_const (measurable_bid 2)).inter
    (measurableSet_le (measurable_bid 2) measurable_const)
lemma measurableSet_actionUpper (U : ℝ) : MeasurableSet (actionUpper U) :=
  measurableSet_lt measurable_const (measurable_bid 2)

lemma action_restrict_partition (μ : Measure (JointAction 2)) {d U : ℝ} (hdU : d≤U) :
    μ.restrict (actionLow d)+μ.restrict (actionActive d U)+μ.restrict (actionUpper U)=μ := by
  have hlo : actionLow d ∪ actionActive d U={a : JointAction 2 | a.bid≤U} := by
    ext a
    simp only [actionLow,actionActive,mem_union,mem_setOf_eq]
    constructor
    · rintro (hl | ⟨_,hu⟩)
      · exact hl.trans hdU
      · exact hu
    · intro hu
      by_cases hl : a.bid≤d
      · exact Or.inl hl
      · exact Or.inr ⟨lt_of_not_ge hl,hu⟩
  have hd : Disjoint (actionLow d) (actionActive d U) := by
    apply Set.disjoint_left.mpr
    intro a hlow hact
    exact not_lt_of_ge hlow hact.1
  rw [←Measure.restrict_union hd (measurableSet_actionActive d U),hlo]
  simpa only [actionUpper,compl_setOf,not_le] using
    (Measure.restrict_add_restrict_compl (μ:=μ)
      (measurableSet_le (measurable_bid 2) (measurable_const : Measurable (fun _ : JointAction 2=>U))))

theorem collapseAction_law (μ : Measure (JointAction 2)) [IsProbabilityMeasure μ]
    {d U : ℝ} (hdU : d≤U) :
    (μ.prod (permLaw 2)).map (collapseAction d U)=
      (((μ.restrict (actionLow d)).map (fun a : JointAction 2=>a.bid)).map (fun b=>((0:Fin 4),b)))+
      μ (actionActive d U) • Measure.dirac (1,0)+
      (μ (actionUpper U)*ENNReal.ofReal (1/2 : ℝ)) • Measure.dirac (2,0)+
      (μ (actionUpper U)*ENNReal.ofReal (1/2 : ℝ)) • Measure.dirac (3,0) := by
  let μ₀:=μ.restrict (actionLow d)
  let μ₁:=μ.restrict (actionActive d U)
  let μ₂:=μ.restrict (actionUpper U)
  have hμ : μ=μ₀+μ₁+μ₂ := (action_restrict_partition μ hdU).symm
  have hlaw₀ : (μ₀.prod (permLaw 2)).map (collapseAction d U)=
      (μ₀.map (fun a=>a.bid)).map (fun b=>((0:Fin 4),b)) := by
    have heq : (μ₀.prod (permLaw 2)).map (collapseAction d U)=
        (μ₀.prod (permLaw 2)).map (fun x=>((0:Fin 4),x.1.bid)) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ:=μ₀) (ν:=permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem (measurableSet_actionLow d) : ∀ᵐa ∂μ₀,a∈actionLow d)
      exact hh.mono (fun x hx=>if_pos hx)
    rw [heq]
    have hm : Measurable (fun a : JointAction 2=>((0:Fin 4),a.bid)) :=
      measurable_const.prodMk (measurable_bid 2)
    change (μ₀.prod (permLaw 2)).map ((fun a : JointAction 2=>((0:Fin 4),a.bid)) ∘ Prod.fst)=_
    rw [←Measure.map_map hm measurable_fst,Measure.map_fst_prod,measure_univ,one_smul]
    exact (Measure.map_map
      (show Measurable (fun b : ℝ=>((0:Fin 4),b)) from measurable_const.prodMk measurable_id)
      (measurable_bid 2)).symm
  have hlaw₁ : (μ₁.prod (permLaw 2)).map (collapseAction d U)=
      μ (actionActive d U) • Measure.dirac (1,0) := by
    have heq : (μ₁.prod (permLaw 2)).map (collapseAction d U)=
        (μ₁.prod (permLaw 2)).map (fun _=>((1:Fin 4),(0:ℝ))) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ:=μ₁) (ν:=permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem (measurableSet_actionActive d U) : ∀ᵐa ∂μ₁,a∈actionActive d U)
      exact hh.mono (fun x hx=>by simp only [collapseAction,if_neg (not_le.mpr hx.1),if_pos hx.2])
    have ht : (μ₁.prod (permLaw 2)) Set.univ=μ₁ Set.univ := by
      rw [←Set.univ_prod_univ,Measure.prod_prod,measure_univ (μ:=permLaw 2),mul_one]
    rw [heq,Measure.map_const,ht]
    simp only [μ₁,Measure.restrict_apply_univ]
  have hlaw₂ : (μ₂.prod (permLaw 2)).map (collapseAction d U)=
      μ (actionUpper U) • ((permLaw 2).map upperRow) := by
    have heq : (μ₂.prod (permLaw 2)).map (collapseAction d U)=
        (μ₂.prod (permLaw 2)).map (upperRow ∘ Prod.snd) := by
      apply Measure.map_congr
      have hh := (measurePreserving_fst (μ:=μ₂) (ν:=permLaw 2)).quasiMeasurePreserving.ae
        (ae_restrict_mem (measurableSet_actionUpper U) : ∀ᵐa ∂μ₂,a∈actionUpper U)
      exact hh.mono (fun x hx=>by
        change U<x.1.bid at hx
        simp only [collapseAction,if_neg (not_le.mpr (hdU.trans_lt hx)),if_neg (not_le.mpr hx),
          Function.comp_apply])
    rw [heq,←Measure.map_map (measurable_of_countable upperRow) measurable_snd,
      Measure.map_snd_prod,Measure.map_smul]
    simp only [μ₂,Measure.restrict_apply_univ]
  calc
    _ = ((μ₀+μ₁+μ₂).prod (permLaw 2)).map (collapseAction d U) := by rw [←hμ]
    _ = _ := by
      rw [Measure.add_prod,Measure.add_prod,
        Measure.map_add _ _ (measurable_collapseAction d U),
        Measure.map_add _ _ (measurable_collapseAction d U),hlaw₀,hlaw₁,hlaw₂,
        upperRow_law,smul_add,smul_smul,smul_smul]
      simp only [add_assoc,μ₀]

lemma measure_smul_cond {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) : μ S • cond μ S=μ.restrict S := by
  by_cases hzero : μ S=0
  · rw [hzero,zero_smul,Measure.restrict_zero_set hzero]
  · unfold ProbabilityTheory.cond
    rw [smul_smul,ENNReal.mul_inv_cancel hzero (measure_ne_top μ S),one_smul]

theorem collapseAction_eq_rivalLaw (μ : Measure (JointAction 2)) [IsProbabilityMeasure μ]
    {d U : ℝ} (hdU : d≤U) :
    (μ.prod (permLaw 2)).map (collapseAction d U)=
      LowBody.rivalLaw (μ.real (actionLow d)) (μ.real (actionActive d U))
        (μ.real (actionUpper U)) ((cond μ (actionLow d)).map (fun a=>a.bid)) := by
  rw [collapseAction_law μ hdU,LowBody.rivalLaw]
  have hlow : ENNReal.ofReal (μ.real (actionLow d)) •
      (((cond μ (actionLow d)).map (fun a=>a.bid)).map (fun b=>((0:Fin 4),b)))=
      (((μ.restrict (actionLow d)).map (fun a=>a.bid)).map (fun b=>((0:Fin 4),b))) := by
    rw [ofReal_measureReal,←Measure.map_smul,←Measure.map_smul,measure_smul_cond]
  have hupper : ENNReal.ofReal (μ.real (actionUpper U)/2)=
      μ (actionUpper U)*ENNReal.ofReal (1/2 : ℝ) := by
    rw [show μ.real (actionUpper U)/2=μ.real (actionUpper U)*(1/2) by ring,
      ENNReal.ofReal_mul (measureReal_nonneg),ofReal_measureReal]
  rw [hlow,ofReal_measureReal,hupper]

def nativeActionLaw {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : Bayes.FiniteGame m 2 c Seed) : Measure (JointAction 2) :=
  (Γ.F ⊗ₘ Γ.σ).map Prod.snd

instance nativeActionLaw_probability {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : Bayes.FiniteGame m 2 c Seed) : IsProbabilityMeasure (nativeActionLaw Γ) :=
  Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

def nativeRowRival {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (_Γ : Bayes.FiniteGame m 2 c Seed) (d U : ℝ) (x : Bayes.UserDraw 2) : LowBody.RowRival :=
  collapseAction d U (x.1.2,x.2)

lemma measurable_nativeRowRival {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : Bayes.FiniteGame m 2 c Seed) (d U : ℝ) : Measurable (nativeRowRival Γ d U) :=
  (measurable_collapseAction d U).comp (measurable_fst.snd.prodMk measurable_snd)

theorem nativeRowRival_law {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : Bayes.FiniteGame m 2 c Seed) {d U : ℝ} (hdU : d≤U) :
    (Bayes.userLaw Γ).map (nativeRowRival Γ d U)=
      LowBody.rivalLaw ((nativeActionLaw Γ).real (actionLow d))
        ((nativeActionLaw Γ).real (actionActive d U))
        ((nativeActionLaw Γ).real (actionUpper U))
        ((cond (nativeActionLaw Γ) (actionLow d)).map (fun a=>a.bid)) := by
  have hm : Measurable (fun x : Bayes.UserDraw 2=>(x.1.2,x.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hmap : (Bayes.userLaw Γ).map (fun x : Bayes.UserDraw 2=>(x.1.2,x.2))=
      (nativeActionLaw Γ).prod (permLaw 2) :=
    by
    have h := (Measure.map_prod_map (Γ.F ⊗ₘ Γ.σ) (permLaw 2) measurable_snd measurable_id).symm
    rw [Measure.map_id] at h
    convert h using 1 <;> rfl
  calc
    _ = ((Bayes.userLaw Γ).map (fun x : Bayes.UserDraw 2=>(x.1.2,x.2))).map
        (collapseAction d U) := (Measure.map_map (measurable_collapseAction d U) hm).symm
    _ = _ := by rw [hmap]; exact collapseAction_eq_rivalLaw (nativeActionLaw Γ) hdU

theorem native_deleted_rivals_law {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : Bayes.FiniteGame (N+1) 2 c Seed) (i : Fin (N+1)) {d U : ℝ} (hdU : d≤U) :
    (Bayes.userProfileLaw Γ).map
      (fun x (j : Fin N)=>nativeRowRival Γ d U (x (i.succAbove j)))=
      Measure.pi (fun _ : Fin N=>
        LowBody.rivalLaw ((nativeActionLaw Γ).real (actionLow d))
          ((nativeActionLaw Γ).real (actionActive d U))
          ((nativeActionLaw Γ).real (actionUpper U))
          ((cond (nativeActionLaw Γ) (actionLow d)).map (fun a=>a.bid))) := by
  let delete : Bayes.UserProfile (N+1) 2 → (Fin N → Bayes.UserDraw 2) :=
    fun x j=>x (i.succAbove j)
  have hp : MeasurePreserving delete (Bayes.userProfileLaw Γ)
      (Measure.pi (fun _ : Fin N=>Bayes.userLaw Γ)) :=
    (measurePreserving_snd (μ:=Bayes.userLaw Γ)
      (ν:=Measure.pi (fun _ : Fin N=>Bayes.userLaw Γ))).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>Bayes.userLaw Γ) i)
  have hm : Measurable (fun x : Fin N → Bayes.UserDraw 2=>
      fun j=>nativeRowRival Γ d U (x j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_nativeRowRival Γ d U).comp (measurable_pi_apply j))
  calc
    _ = ((Bayes.userProfileLaw Γ).map delete).map
        (fun x : Fin N → Bayes.UserDraw 2=>fun j=>nativeRowRival Γ d U (x j)) :=
      (Measure.map_map hm hp.measurable).symm
    _ = _ := by
      rw [hp.map_eq,Measure.pi_map_pi (fun _=>(measurable_nativeRowRival Γ d U).aemeasurable),
        nativeRowRival_law Γ hdU]

end FCAppendix.Affine.Hybrid
