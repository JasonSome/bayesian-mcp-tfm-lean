import FCAppendix.Exclusive.SourceLowTypeDistinct
import FCAppendix.Exclusive.SourceLowTypePrice

noncomputable section
namespace FCAppendix.Bayes.ExclusiveSource
open MeasureTheory ProbabilityTheory Game Exclusive ExclusiveNarrow Set Filter
open Exclusive.Narrow.Existence ExclusiveConstruction

variable {m n c : ℕ} {Seed V : Type*} [MeasurableSpace Seed] [MeasurableSpace V]

def BandActions (lower upper : ℝ) (a : Fin m → JointAction n) : Prop :=
  ∀ j, (a j).routeCount = 0 ∨ ((a j).routeCount = n ∧ (a j).bid ∈ Icc lower upper)

theorem measurableSet_bandActions (lower upper : ℝ) :
    MeasurableSet {a : Fin m → JointAction n | BandActions lower upper a} := by
  unfold BandActions
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  have hk : Measurable (fun a : Fin m → JointAction n => (a j).routeCount) :=
    (measurable_routeCount n).comp (measurable_pi_apply j)
  have hb : Measurable (fun a : Fin m → JointAction n => (a j).bid) :=
    (measurable_bid n).comp (measurable_pi_apply j)
  exact (measurableSet_eq_fun hk measurable_const).union
    ((measurableSet_eq_fun hk measurable_const).inter (hb measurableSet_Icc))

theorem ae_actual_bandRivals (Γ : FiniteGame (m+1) n c Seed)
    (i : Fin (m+1)) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (b : V → ℝ) (hb : Measurable b) {lower upper : ℝ} (hlo : 0 < lower)
    (hband : ∀ v, b v ∈ Icc lower upper)
    (hActions : (userProfileLaw Γ).map (fun d j => (d (i.succAbove j)).1.2) =
      (iidRivalLaw m h nu).map (fun omega j => flagAction n b (omega j))) :
    ∀ᵐ d ∂userProfileLaw Γ, BandRivals lower upper i d := by
  have hp : Measurable (fun d : UserProfile (m+1) n => fun j : Fin m =>
      (d (i.succAbove j)).1.2) := measurable_pi_lambda _ fun j =>
    measurable_snd.comp (measurable_fst.comp (measurable_pi_apply (i.succAbove j)))
  have hf : Measurable (fun omega : RivalProfile m V => fun j => flagAction n b (omega j)) :=
    measurable_pi_lambda _ fun j => (measurable_flagAction n hb).comp (measurable_pi_apply j)
  have hgood : ∀ᵐ a ∂(userProfileLaw Γ).map
      (fun d j => (d (i.succAbove j)).1.2), BandActions lower upper a := by
    rw [hActions]
    apply (ae_map_iff hf.aemeasurable (measurableSet_bandActions lower upper)).mpr
    apply Eventually.of_forall
    intro omega j
    cases hh : (omega j).1
    · exact Or.inl (by simp [flagAction,hh,Interim.abstain])
    · have hbpos : 0 < b (omega j).2 := hlo.trans_le (hband _).1
      exact Or.inr ⟨by simp [flagAction,hh],by simpa [flagAction,hh,max_eq_left hbpos.le]
        using (hband (omega j).2)⟩
  filter_upwards [(ae_map_iff hp.aemeasurable (measurableSet_bandActions lower upper)).mp hgood]
    with d hd
  intro j hji
  obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hji
  exact hd k

end FCAppendix.Bayes.ExclusiveSource
