import FCAppendix.Game.UniformRoutes
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Constructions.Pi

namespace FCAppendix
namespace Game

open MeasureTheory ProbabilityTheory
open scoped BigOperators

instance instMeasurableSpacePerm (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance (n : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

instance instMeasurableSpaceFinset (α : Type*) : MeasurableSpace (Finset α) := ⊤

instance (α : Type*) : DiscreteMeasurableSpace (Finset α) := ⟨fun _ => trivial⟩

instance instMeasurableSpaceJointAction (n : ℕ) : MeasurableSpace (JointAction n) :=
  MeasurableSpace.comap (fun a : JointAction n => (a.bid, a.routeCount)) inferInstance

instance instMeasurableSpaceOption (α : Type*) [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  MeasurableSpace.map some ‹MeasurableSpace α›

theorem measurable_bid (n : ℕ) : Measurable (fun a : JointAction n => a.bid) :=
  measurable_fst.comp (comap_measurable (fun a : JointAction n => (a.bid, a.routeCount)))

theorem measurable_routeCount (n : ℕ) :
    Measurable (fun a : JointAction n => a.routeCount) :=
  measurable_snd.comp (comap_measurable (fun a : JointAction n => (a.bid, a.routeCount)))

theorem measurable_some {α : Type*} [MeasurableSpace α] :
    Measurable (some : α → Option α) := fun _ hs => hs

theorem measurable_option_ite {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {P : Set Ω} (hP : MeasurableSet P) {f : Ω → α} (hf : Measurable f) [DecidablePred (· ∈ P)] :
    Measurable (fun ω => if ω ∈ P then some (f ω) else (none : Option α)) := by
  intro S hS
  have hS' : MeasurableSet (some ⁻¹' S) := hS
  have hset : (fun ω => if ω ∈ P then some (f ω) else (none : Option α)) ⁻¹' S =
      (P ∩ f ⁻¹' (some ⁻¹' S)) ∪ (Pᶜ ∩ {_ω | (none : Option α) ∈ S}) := by
    ext ω
    by_cases h : ω ∈ P <;> simp [h]
  rw [hset]
  refine (hP.inter (hf hS')).union (hP.compl.inter ?_)
  by_cases hn : (none : Option α) ∈ S
  · simp [hn]
  · simp [hn]

noncomputable def firstK {n : ℕ} (τ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (τ j).val < k)

theorem mem_firstK {n : ℕ} (τ : Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) :
    j ∈ firstK τ k ↔ (τ j).val < k := by
  simp [firstK]

theorem firstK_mono {n : ℕ} (τ : Equiv.Perm (Fin n)) {k k' : ℕ} (h : k ≤ k') :
    firstK τ k ⊆ firstK τ k' := by
  intro j hj
  rw [mem_firstK] at hj ⊢
  omega

theorem card_firstK {n : ℕ} (τ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (firstK τ k).card = k := by
  classical
  have himage : firstK τ k = (Finset.univ.filter (fun r : Fin n => r.val < k)).map
      τ.symm.toEmbedding := by
    ext j
    simp only [mem_firstK, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · intro h
      exact ⟨τ j, h, by simp⟩
    · rintro ⟨r, hr, rfl⟩
      simpa using hr
  rw [himage, Finset.card_map]
  have : (Finset.univ.filter (fun r : Fin n => r.val < k)) =
      (Finset.range k).attachFin (fun r hr => by
        have := Finset.mem_range.mp hr
        omega) := by
    ext r
    simp
  rw [this, Finset.card_attachFin, Finset.card_range]

noncomputable def permLaw (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  uniformOn Set.univ

instance (n : ℕ) : IsProbabilityMeasure (permLaw n) := by
  unfold permLaw
  exact isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

theorem permLaw_real_filter (n : ℕ) (p : Equiv.Perm (Fin n) → Prop) [DecidablePred p] :
    (permLaw n).real {τ | p τ} =
      ((Finset.univ.filter p).card : ℝ) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  classical
  have hset : {τ | p τ} = ((Finset.univ.filter p : Finset (Equiv.Perm (Fin n))) :
      Set (Equiv.Perm (Fin n))) := by
    ext τ
    simp
  unfold permLaw
  rw [Measure.real, uniformOn_univ, hset, Measure.count_apply_finset, ENNReal.toReal_div]
  simp

theorem permLaw_mem_firstK (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) (j : Fin n) :
    (permLaw n).real {τ | j ∈ firstK τ k} = (k : ℝ) / n := by
  classical

  have hsym : ∀ j l : Fin n,
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => j ∈ firstK τ k)).card =
      (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => l ∈ firstK τ k)).card := by
    intro j l
    apply Finset.card_nbij' (fun τ => τ * Equiv.swap j l) (fun τ => τ * Equiv.swap j l)
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        mem_firstK, Equiv.Perm.mul_apply, Equiv.swap_apply_right] at hτ ⊢
      exact hτ
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        mem_firstK, Equiv.Perm.mul_apply, Equiv.swap_apply_left] at hτ ⊢
      exact hτ
    · intro τ _
      simp [mul_assoc]
    · intro τ _
      simp [mul_assoc]

  have hsum : ∑ l : Fin n,
      ((Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => l ∈ firstK τ k)).card : ℝ) =
      k * Fintype.card (Equiv.Perm (Fin n)) := by
    have h1 : ∀ l : Fin n,
        ((Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => l ∈ firstK τ k)).card : ℝ) =
        ∑ τ : Equiv.Perm (Fin n), (if l ∈ firstK τ k then (1 : ℝ) else 0) := by
      intro l
      rw [Finset.sum_boole]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ τ : Equiv.Perm (Fin n),
        (∑ l : Fin n, (if l ∈ firstK τ k then (1 : ℝ) else 0)) = k := by
      intro τ
      rw [sum_membership_real, card_firstK τ k hk]
    simp_rw [h2]
    simp [mul_comm]
  have hall : ∑ l : Fin n,
      ((Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => l ∈ firstK τ k)).card : ℝ) =
      n * (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => j ∈ firstK τ k)).card := by
    rw [Finset.sum_congr rfl (fun l _ => by rw [hsym l j])]
    simp
  rw [hall] at hsum
  rw [permLaw_real_filter]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hcR : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  linarith

end Game
end FCAppendix
