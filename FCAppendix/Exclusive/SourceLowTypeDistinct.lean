import FCAppendix.Exclusive.SourceLowTypeCountTail
import FCAppendix.Exclusive.SourceLowTypeRejection

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence ExclusiveConstruction
open scoped BigOperators

variable {m n c : ℕ} {Seed V : Type*} [MeasurableSpace Seed] [MeasurableSpace V]

theorem ae_iid_pairwise_distinct (nu : Measure V) [IsProbabilityMeasure nu]
    [NullSingletonClass nu] [MeasurableEq V] :
    ∀ᵐ v ∂Measure.pi (fun _ : Fin m => nu), Function.Injective v := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · subst j
    exact Eventually.of_forall fun _ _ => rfl
  · have hdiag : ∀ᵐ z ∂nu.prod nu, z.1 ≠ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
      exact Eventually.of_forall fun x => (nu.ae_ne x).mono fun _ h => Ne.symm h
    have hind := (iIndepFun_pi (μ := fun _ : Fin m => nu)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hij
    have hmap := hind.map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin m => nu) i).map_eq,
      (measurePreserving_eval (fun _ : Fin m => nu) j).map_eq] at hmap
    have hpres : MeasurePreserving
        (fun v : Fin m → V => (v i,v j)) (Measure.pi fun _ : Fin m => nu) (nu.prod nu) :=
      ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),hmap⟩
    exact (hpres.quasiMeasurePreserving.ae hdiag).mono fun _ h he => (h he).elim

def DistinctActiveActions (a : Fin m → JointAction n) : Prop :=
  ∀ j l, j ≠ l → (a j).routeCount ≠ 0 → (a l).routeCount ≠ 0 → (a j).bid ≠ (a l).bid

theorem measurableSet_distinctActiveActions :
    MeasurableSet {a : Fin m → JointAction n | DistinctActiveActions a} := by
  classical
  unfold DistinctActiveActions
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  have hj : Measurable (fun a : Fin m → JointAction n => (a j).routeCount) :=
    (measurable_routeCount n).comp (measurable_pi_apply j)
  have hl : Measurable (fun a : Fin m → JointAction n => (a l).routeCount) :=
    (measurable_routeCount n).comp (measurable_pi_apply l)
  have hbj : Measurable (fun a : Fin m → JointAction n => (a j).bid) :=
    (measurable_bid n).comp (measurable_pi_apply j)
  have hbl : Measurable (fun a : Fin m → JointAction n => (a l).bid) :=
    (measurable_bid n).comp (measurable_pi_apply l)
  have hb := measurableSet_eq_fun hbj hbl
  convert (measurableSet_eq_fun hj measurable_const).union
    ((measurableSet_eq_fun hl measurable_const).union hb.compl) using 1
  ext a
  simp only [mem_setOf_eq,mem_union,mem_compl_iff]
  tauto

theorem ae_flag_distinct_active (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] [NullSingletonClass nu] [MeasurableEq V]
    (b : V → ℝ) (hpos : ∀ v, 0 < b v) (hinj : Function.Injective b) :
    ∀ᵐ omega ∂iidRivalLaw m h nu,
      DistinctActiveActions (fun j => flagAction n b (omega j)) := by
  have hpres : MeasurePreserving (fun omega : RivalProfile m V => fun j => (omega j).2)
      (iidRivalLaw m h nu) (Measure.pi fun _ : Fin m => nu) :=
    measurePreserving_pi (fun _ : Fin m => Exclusive.Narrow.Existence.sampleLaw h nu) (fun _ : Fin m => nu)
      (fun _ => measurePreserving_snd (μ := bernoulliMeasure true false h) (ν := nu))
  filter_upwards [hpres.quasiMeasurePreserving.ae (ae_iid_pairwise_distinct (m := m) nu)]
    with omega hd
  intro j l hjl hj hl he
  have hbj : (omega j).1 = true := by
    cases hh : (omega j).1 <;> simp [flagAction,hh,Interim.abstain] at hj ⊢
  have hbl : (omega l).1 = true := by
    cases hh : (omega l).1 <;> simp [flagAction,hh,Interim.abstain] at hl ⊢
  have he' : b (omega j).2 = b (omega l).2 := by
    simpa only [flagAction,hbj,hbl,if_true,max_eq_left (hpos _).le] using he
  exact hjl (hd (hinj he'))

theorem ae_actual_activeRivals_distinct (Γ : FiniteGame (m+1) n c Seed)
    (i : Fin (m+1)) (h : unitInterval) (nu : Measure V)
    [IsProbabilityMeasure nu] [NullSingletonClass nu] [MeasurableEq V]
    (b : V → ℝ) (hb : Measurable b) (hpos : ∀ v, 0 < b v) (hinj : Function.Injective b)
    (hActions : (userProfileLaw Γ).map (fun d j => (d (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction n b (omega j))) :
    ∀ᵐ d ∂userProfileLaw Γ,
      Set.InjOn (fun j => (d j).1.2.bid) (activeRivals i d) := by
  have hp : Measurable (fun d : UserProfile (m+1) n => fun j : Fin m =>
      (d (i.succAbove j)).1.2) := measurable_pi_lambda _ fun j =>
    measurable_snd.comp (measurable_fst.comp (measurable_pi_apply (i.succAbove j)))
  have hf : Measurable (fun omega : RivalProfile m V => fun j => flagAction n b (omega j)) :=
    measurable_pi_lambda _ fun j => (measurable_flagAction n hb).comp (measurable_pi_apply j)
  have hgood : ∀ᵐ a ∂(userProfileLaw Γ).map
      (fun d j => (d (i.succAbove j)).1.2), DistinctActiveActions a := by
    rw [hActions]
    exact (ae_map_iff hf.aemeasurable measurableSet_distinctActiveActions).mpr
      (ae_flag_distinct_active h nu b hpos hinj)
  filter_upwards [(ae_map_iff hp.aemeasurable measurableSet_distinctActiveActions).mp hgood]
    with d hd
  intro j hj l hl he
  by_contra hjl
  obtain ⟨j',rfl⟩ := Fin.exists_succAbove_eq ((mem_activeRivals i j d).mp hj).1
  obtain ⟨l',rfl⟩ := Fin.exists_succAbove_eq ((mem_activeRivals i l d).mp hl).1
  exact hd j' l' (by intro h; exact hjl (congrArg i.succAbove h))
    ((mem_activeRivals i _ d).mp hj).2 ((mem_activeRivals i _ d).mp hl).2 he

end FCAppendix.Bayes.ExclusiveSource
