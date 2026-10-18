import FCAppendix.Exclusive.PrimitiveConstruction
import FCAppendix.Exclusive.NarrowExistenceGameScore

noncomputable section
namespace FCAppendix.Bayes.ExclusiveConstruction
open MeasureTheory ProbabilityTheory Game Set Filter

theorem bernoulliMeasure_ennreal (h : unitInterval) :
    bernoulliMeasure true false h =
      ENNReal.ofReal (h : ℝ) • Measure.dirac true+
        ENNReal.ofReal (1-(h : ℝ)) • Measure.dirac false := by
  rw [bernoulliMeasure_def, ← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  simp only [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
    unitInterval.coe_symm_eq]

theorem map_bernoulli_prod {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (h : unitInterval) (nu : Measure X) [SFinite nu]
    {f : Bool × X → Y} (hf : Measurable f) :
    ((bernoulliMeasure true false h).prod nu).map f =
      ENNReal.ofReal (h : ℝ) • nu.map (fun x => f (true,x))+
        ENNReal.ofReal (1-(h : ℝ)) • nu.map (fun x => f (false,x)) := by
  rw [bernoulliMeasure_ennreal, Measure.add_prod, Measure.prod_smul_left,
    Measure.prod_smul_left, Measure.map_add _ _ hf, Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left, Measure.map_map hf measurable_prodMk_left]
  rfl

theorem pureAction_map_twoBand (n : ℕ) (h : unitInterval)
    (high low : Measure ℝ) [IsProbabilityMeasure high] [IsProbabilityMeasure low]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (hhigh : ∀ᵐ v ∂high, v ∈ E) (hlow : ∀ᵐ v ∂low, v ∉ E) :
    (twoBandLaw h high low).map (pureAction n E b) =
      ENNReal.ofReal (h : ℝ) • high.map
        (fun v => (⟨max (b v) 0, le_max_right _ _, n, le_rfl⟩ : JointAction n))+
      ENNReal.ofReal (1-(h : ℝ)) • Measure.dirac (Interim.abstain n) := by
  rw [twoBandLaw_map h high low (measurable_pureAction n hE hb)]
  congr 1
  · congr 1
    apply Measure.map_congr
    filter_upwards [hhigh] with v hv
    simp only [pureAction, if_pos hv]
  · have he : low.map (pureAction n E b) = low.map (fun _ => Interim.abstain n) := by
      apply Measure.map_congr
      filter_upwards [hlow] with v hv
      simp only [pureAction, if_neg hv]
    rw [he, Measure.map_const, measure_univ, one_smul]

def flagAction {X : Type*} (n : ℕ) (b : X → ℝ) (x : Bool × X) : JointAction n :=
  if x.1 then ⟨max (b x.2) 0, le_max_right _ _, n, le_rfl⟩ else Interim.abstain n

theorem measurable_flagAction {X : Type*} [MeasurableSpace X]
    (n : ℕ) {b : X → ℝ} (hb : Measurable b) : Measurable (flagAction n b) := by
  unfold flagAction
  apply Measurable.ite (measurable_fst (measurableSet_singleton true)) _ measurable_const
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction, MeasurableSpace.comap_comp]
  exact (((hb.comp measurable_snd).max measurable_const).prodMk measurable_const).comap_le

theorem pureAction_law_eq_flag_law (n : ℕ) (h : unitInterval)
    (high low : Measure ℝ) [IsProbabilityMeasure high] [IsProbabilityMeasure low]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (hhigh : ∀ᵐ v ∂high, v ∈ E) (hlow : ∀ᵐ v ∂low, v ∉ E) :
    (twoBandLaw h high low).map (pureAction n E b) =
      ((bernoulliMeasure true false h).prod high).map (flagAction n b) := by
  rw [pureAction_map_twoBand n h high low E hE b hb hhigh hlow,
    map_bernoulli_prod h high (measurable_flagAction n hb)]
  simp only [flagAction, Bool.false_eq_true, if_false, if_true, Measure.map_const,
    measure_univ, one_smul]

theorem pureAction_scaled_law_eq_flag_law
    (n : ℕ) (h : unitInterval) {eps : ℝ} (H : ℝ)
    (nu : Measure (Icc (1-eps) (1+eps))) [IsProbabilityMeasure nu]
    (low : Measure ℝ) [IsProbabilityMeasure low]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (hhigh : ∀ᵐ v ∂scaledHighLaw H nu, v ∈ E) (hlow : ∀ᵐ v ∂low, v ∉ E) :
    (twoBandLaw h (scaledHighLaw H nu) low).map (pureAction n E b) =
      (Exclusive.Narrow.Existence.sampleLaw h nu).map
        (flagAction n (fun v : Icc (1-eps) (1+eps) => b (H*(v : ℝ)))) := by
  rw [pureAction_law_eq_flag_law n h (scaledHighLaw H nu) low E hE b hb hhigh hlow]
  have hp : MeasurePreserving
      (Prod.map id (fun v : Icc (1-eps) (1+eps) => H*(v : ℝ)))
      ((bernoulliMeasure true false h).prod nu)
      ((bernoulliMeasure true false h).prod (scaledHighLaw H nu)) :=
    (MeasurePreserving.id _).prod ⟨measurable_highScale eps H, rfl⟩
  rw [← hp.map_eq, Measure.map_map (measurable_flagAction n hb) hp.measurable]
  rfl

theorem game_user_action_law {m n c : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (policy : LocalPolicy m c unitInterval)
    (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)) :
    (userLaw (game m n c F E hE b hb A G g hg policy hpolicy)).map
      (fun d => d.1.2) = F.map (pureAction n E b) := by
  let Γ := game m n c F E hE b hb A G g hg policy hpolicy
  change (userLaw Γ).map (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst]
  have hp : (userLaw Γ).map Prod.fst = (Γ).F ⊗ₘ (Γ).σ :=
    (measurePreserving_fst (μ := (Γ).F ⊗ₘ (Γ).σ) (ν := permLaw n)).map_eq
  rw [hp, value_action_law hE hb A G g hg policy hpolicy]
  exact Measure.map_map measurable_snd
    ((measurable_id).prodMk (measurable_pureAction n hE hb))

theorem game_profile_action_law {m n c : ℕ} (F : Measure ℝ) [IsProbabilityMeasure F]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (policy : LocalPolicy m c unitInterval)
    (hpolicy : Measurable (fun x : LocalList m × unitInterval => (policy x.1 x.2).val)) :
    (userProfileLaw (game m n c F E hE b hb A G g hg policy hpolicy)).map
      (fun d i => (d i).1.2) =
      Measure.pi (fun _ : Fin m => F.map (pureAction n E b)) := by
  let Γ := game m n c F E hE b hb A G g hg policy hpolicy
  have hm : (userProfileLaw Γ).map (fun d i => (d i).1.2) =
      Measure.pi (fun _ : Fin m => (userLaw Γ).map (fun d => d.1.2)) :=
    Measure.pi_map_pi (fun _ => (measurable_snd.comp measurable_fst).aemeasurable)
  rw [hm]
  congr 1
  funext j
  exact game_user_action_law F E hE b hb A G g hg policy hpolicy

theorem rival_projection_measurePreserving {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] {m : ℕ} (i : Fin (m+1)) :
    MeasurePreserving (fun d : Fin (m+1) → X => fun j => d (i.succAbove j))
      (Measure.pi (fun _ : Fin (m+1) => mu))
      (Measure.pi (fun _ : Fin m => mu)) := by
  exact (measurePreserving_snd (μ := mu) (ν := Measure.pi (fun _ : Fin m => mu))).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => mu) i)

theorem game_rival_action_law_eq_flag_law
    {m n c : ℕ} (i : Fin (m+1)) (h : unitInterval) {eps : ℝ} (H : ℝ)
    (nu : Measure (Icc (1-eps) (1+eps))) [IsProbabilityMeasure nu]
    (low : Measure ℝ) [IsProbabilityMeasure low]
    (E : Set ℝ) (hE : MeasurableSet E) (b : ℝ → ℝ) (hb : Measurable b)
    (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)
    (policy : LocalPolicy (m+1) c unitInterval)
    (hpolicy : Measurable (fun x : LocalList (m+1) × unitInterval => (policy x.1 x.2).val))
    (hhigh : ∀ᵐ v ∂scaledHighLaw H nu, v ∈ E) (hlow : ∀ᵐ v ∂low, v ∉ E) :
    (userProfileLaw (game (m+1) n c (twoBandLaw h (scaledHighLaw H nu) low)
      E hE b hb A G g hg policy hpolicy)).map
        (fun d j => (d (i.succAbove j)).1.2) =
      (Exclusive.Narrow.Existence.iidRivalLaw m h nu).map
        (fun omega j => flagAction n
          (fun v : Icc (1-eps) (1+eps) => b (H*(v : ℝ))) (omega j)) := by
  let F := twoBandLaw h (scaledHighLaw H nu) low
  let Γ := game (m+1) n c F E hE b hb A G g hg policy hpolicy
  let f : UserDraw n → JointAction n := fun d => d.1.2
  let s := flagAction n (fun v : Icc (1-eps) (1+eps) => b (H*(v : ℝ)))
  have hf : Measurable f := measurable_snd.comp measurable_fst
  have hs : Measurable s := measurable_flagAction n (hb.comp (measurable_highScale eps H))
  have hproj := rival_projection_measurePreserving (userLaw Γ) i
  have hActions : (userLaw Γ).map f =
      (Exclusive.Narrow.Existence.sampleLaw h nu).map s :=
    (game_user_action_law F E hE b hb A G g hg policy hpolicy).trans
      (pureAction_scaled_law_eq_flag_law n h H nu low E hE b hb hhigh hlow)
  have hleft : (userProfileLaw Γ).map (fun d j => f (d (i.succAbove j))) =
      Measure.pi (fun _ : Fin m => (userLaw Γ).map f) := by
    have hm := Measure.pi_map_pi (fun _ : Fin m => hf.aemeasurable)
      (μ := fun _ : Fin m => userLaw Γ)
    rw [← hproj.map_eq] at hm
    exact (Measure.map_map (measurable_pi_lambda _ fun j =>
      hf.comp (measurable_pi_apply j)) hproj.measurable).symm.trans hm
  change (userProfileLaw Γ).map (fun d j => f (d (i.succAbove j))) = _
  rw [hleft]
  simp_rw [hActions]
  exact (Measure.pi_map_pi (fun _ : Fin m => hs.aemeasurable)).symm

end FCAppendix.Bayes.ExclusiveConstruction
