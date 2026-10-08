import FCAppendix.Game.JointMeasurability
import FCAppendix.Probability.Resample

namespace FCAppendix.Bayes

open MeasureTheory ProbabilityTheory Game
open scoped ProbabilityTheory

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def playedCount (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ω : Background m n Seed) : Fin (n + 1) :=
  boundedCount (drawsRealization ω.1) Γ.policy ω.2 i

def insertDraw (i : Fin m) (p : UserDraw n × Background m n Seed) : Background m n Seed :=
  (Function.update p.2.1 i p.1, p.2.2)

def playFromDeviation (i : Fin m)
    (p : (ℝ × JointAction n) × Sample m n Seed) : Background m n Seed :=
  insertDraw i ((p.1, p.2.2), p.2.1)

theorem insertDraw_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (insertDraw (Seed := Seed) i)
      ((userLaw Γ).prod (backgroundLaw Γ)) (backgroundLaw Γ) := by
  have hu : MeasurePreserving (fun p : UserDraw n × (Fin m → UserDraw n) =>
      Function.update p.2 i p.1)
      ((userLaw Γ).prod (Measure.pi fun _ : Fin m => userLaw Γ))
      (Measure.pi fun _ : Fin m => userLaw Γ) :=
    ⟨Resample.measurable_update_pair i, Resample.map_update_eq (userLaw Γ) i⟩
  exact (hu.prod (MeasurePreserving.id (Measure.pi fun _ : Fin n => Γ.seedLaw))).comp
    (measurePreserving_prodAssoc (userLaw Γ) (Measure.pi fun _ : Fin m => userLaw Γ)
      (Measure.pi fun _ : Fin n => Γ.seedLaw)).symm

theorem playFromDeviation_measurePreserving (Γ : FiniteGame m n c Seed) (i : Fin m) :
    MeasurePreserving (playFromDeviation (Seed := Seed) i)
      ((Γ.F ⊗ₘ Γ.σ).prod (sampleLaw Γ)) (backgroundLaw Γ) := by
  have hs := (MeasurePreserving.id (Γ.F ⊗ₘ Γ.σ)).prod
    (Measure.measurePreserving_swap (μ := backgroundLaw Γ) (ν := permLaw n))
  have ha := (measurePreserving_prodAssoc (Γ.F ⊗ₘ Γ.σ) (permLaw n)
    (backgroundLaw Γ)).symm
  exact (insertDraw_measurePreserving Γ i).comp (ha.comp hs)

omit [MeasurableSpace Seed] in
theorem observe_insertDraw (i : Fin m) (p : UserDraw n × Background m n Seed) (j : Fin n) :
    observe (drawsRealization (insertDraw i p).1) j =
      observe (deviated i p.1.1.2 (p.2, p.1.2)) j := by
  classical
  funext l
  by_cases hl : l = i
  · subst l
    simp [observe, drawsRealization, insertDraw, deviated_recipients_self,
      deviated_bid_self]
  · simp [observe, drawsRealization, insertDraw, Function.update_of_ne hl,
      deviated_recipients_other i l hl, deviated_bid_other i l hl]

theorem playedCount_insertDraw (Γ : FiniteGame m n c Seed) (i : Fin m)
    (p : UserDraw n × Background m n Seed) :
    playedCount Γ i (insertDraw i p) = focalCount Γ i p.1.1.2 (p.2, p.1.2) := by
  apply Fin.ext
  change inclusionCount _ _ _ _ = inclusionCount _ _ _ _
  have halloc (j : Fin n) :
      allocation (drawsRealization (insertDraw i p).1) Γ.policy (insertDraw i p).2 j =
        allocation (deviated i p.1.1.2 (p.2, p.1.2)) Γ.policy p.2.2 j :=
    congrArg (fun ℓ => (Γ.policy j ℓ (p.2.2 j)).val) (observe_insertDraw i p j)
  simp only [inclusionCount_eq_sum, halloc]

theorem playedCount_eq_focalCount (Γ : FiniteGame m n c Seed) (i : Fin m)
    (ω : Background m n Seed) :
    playedCount Γ i ω = focalCount Γ i (ω.1 i).1.2 (ω, (ω.1 i).2) := by
  have h := playedCount_insertDraw Γ i (ω.1 i, ω)
  simpa [insertDraw, Function.update_eq_self] using h

theorem measurable_playedCount (Γ : FiniteGame m n c Seed) (i : Fin m) :
    Measurable (playedCount Γ i) := by
  have hd : Measurable (fun ω : Background m n Seed => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have h := (measurable_focalCount_joint Γ i).comp
    ((measurable_snd.comp (measurable_fst.comp hd)).prodMk
      (measurable_id.prodMk (measurable_snd.comp hd)))
  change Measurable (fun ω : Background m n Seed =>
    focalCount Γ i (ω.1 i).1.2 (ω, (ω.1 i).2)) at h
  simpa only [← playedCount_eq_focalCount] using h

theorem ae_played_of_ae_deviation (Γ : FiniteGame m n c Seed) (i : Fin m)
    (P : (ℝ × JointAction n) → Fin (n + 1) → Prop)
    (hP : MeasurableSet {p : (ℝ × JointAction n) × Fin (n + 1) | P p.1 p.2})
    (h : ∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), ∀ᵐ ω ∂(sampleLaw Γ), P x (focalCount Γ i x.2 ω)) :
    ∀ᵐ ω ∂(backgroundLaw Γ), P (ω.1 i).1 (playedCount Γ i ω) := by
  have harg : Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
      (p.1.2, p.2)) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have hm := (measurable_focalCount_joint Γ i).comp harg
  change Measurable (fun p : (ℝ × JointAction n) × Sample m n Seed =>
    focalCount Γ i p.1.2 p.2) at hm
  have hp := (Measure.ae_prod_iff_ae_ae ((measurable_fst.prodMk hm) hP)).mpr h
  have hplayed : MeasurableSet {ω : Background m n Seed |
      P (ω.1 i).1 (playedCount Γ i ω)} :=
    ((measurable_fst.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      (measurable_playedCount Γ i)) hP
  have hpres := playFromDeviation_measurePreserving Γ i
  rw [← hpres.map_eq]
  apply (ae_map_iff hpres.measurable.aemeasurable hplayed).mpr
  filter_upwards [hp] with p hp
  have hv : ((playFromDeviation i p).1 i).1 = p.1 := by
    simp only [playFromDeviation, insertDraw, Function.update_self]
  have hk := playedCount_insertDraw Γ i ((p.1, p.2.2), p.2.1)
  rw [hv]
  change P p.1 (playedCount Γ i (insertDraw i ((p.1, p.2.2), p.2.1)))
  rw [hk]
  exact hp

end FCAppendix.Bayes
