import FCAppendix.Affine.Tail04.ObservableRoles

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory ProbabilityTheory Set Game Bayes
open FCAppendix.Affine.Hybrid
open scoped BigOperators

theorem private_mark_given_route {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (P U : Set X) (T : Set Y) (hP : MeasurableSet P) (hT : MeasurableSet T)
    (hUP : U ⊆ P) (hPm : 0 < μ.real P) (hTm : 0 < ν.real T) :
    (cond (μ.prod ν) (P ×ˢ T)).real (U ×ˢ (univ : Set Y)) = μ.real U / μ.real P := by
  have hinter : (P ×ˢ T) ∩ (U ×ˢ (univ : Set Y)) = U ×ˢ T := by
    ext x
    simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hUP h.1, h.2⟩, h.1⟩⟩
  have h := congrArg ENNReal.toReal
    (ProbabilityTheory.cond_mul_eq_inter (s := P ×ˢ T) (hP.prod hT)
      (U ×ˢ (univ : Set Y)) (μ.prod ν))
  rw [hinter] at h
  simp only [ENNReal.toReal_mul, Measure.prod_prod] at h
  have hcancel :
      (cond (μ.prod ν) (P ×ˢ T)).real (U ×ˢ (univ : Set Y)) * μ.real P = μ.real U := by
    apply mul_right_cancel₀ hTm.ne'
    simpa only [measureReal_def, mul_assoc] using h
  exact (eq_div_iff hPm.ne').2 hcancel

def oneRouteEvent (j : Fin 2) : Set (Equiv.Perm (Fin 2)) :=
  {τ | j ∈ firstK τ 1}

lemma measurableSet_oneRouteEvent (j : Fin 2) : MeasurableSet (oneRouteEvent j) :=
  (Set.to_countable _).measurableSet

lemma original_fair_route_mass (j : Fin 2) :
    (permLaw 2).real (oneRouteEvent j) = 1 / 2 := by
  simpa only [oneRouteEvent, Nat.cast_one, Nat.cast_ofNat] using
    permLaw_mem_firstK 2 1 (by omega) (by omega) j

namespace Observable.Regions
variable (E : Observable.Regions)

def privateJointEvent : Set (ℝ × JointAction 2) := {x | x.2.bid ∈ E.privateBids}
def upperJointEvent : Set (ℝ × JointAction 2) := {x | E.H ≤ x.2.bid}

lemma measurableSet_privateJointEvent : MeasurableSet E.privateJointEvent :=
  ((measurable_bid 2).comp measurable_snd) E.measurableSet_privateBids

lemma measurableSet_upperJointEvent : MeasurableSet E.upperJointEvent :=
  measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)

lemma upperJointEvent_subset : E.upperJointEvent ⊆ E.privateJointEvent := by
  intro x hx
  exact Or.inr hx

theorem native_private_mark_share {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (hP : 0 < (Γ.F ⊗ₘ Γ.σ).real E.privateJointEvent) :
    (cond (userLaw Γ) (E.privateJointEvent ×ˢ oneRouteEvent j)).real
      (E.upperJointEvent ×ˢ (univ : Set (Equiv.Perm (Fin 2)))) =
      (Γ.F ⊗ₘ Γ.σ).real E.upperJointEvent /
        (Γ.F ⊗ₘ Γ.σ).real E.privateJointEvent := by
  exact private_mark_given_route (Γ.F ⊗ₘ Γ.σ) (permLaw 2)
    E.privateJointEvent E.upperJointEvent (oneRouteEvent j)
    E.measurableSet_privateJointEvent (measurableSet_oneRouteEvent j)
    E.upperJointEvent_subset hP (by rw [original_fair_route_mass]; norm_num)

theorem native_private_mark_share_of_masses {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (h hm : ℝ) (hh : 0 < h) (hhm : 0 ≤ hm)
    (hprivate : (Γ.F ⊗ₘ Γ.σ).real E.privateJointEvent = h + hm)
    (hupper : (Γ.F ⊗ₘ Γ.σ).real E.upperJointEvent = hm) :
    (cond (userLaw Γ) (E.privateJointEvent ×ˢ oneRouteEvent j)).real
      (E.upperJointEvent ×ˢ (univ : Set (Equiv.Perm (Fin 2)))) = hm / (h + hm) := by
  rw [E.native_private_mark_share Γ j (by rw [hprivate]; positivity), hprivate, hupper]

end Observable.Regions

theorem upper_any_union_bound {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    (ν : FiniteLaw Ω) (upper : ι → Ω → Prop) (π : ℝ)
    (hmarg : ∀ i, ν.prob (upper i) ≤ π) :
    ν.prob (fun ω => ∃ i, upper i ω) ≤ (Fintype.card ι : ℝ) * π := by
  classical
  rw [FiniteLaw.prob_eq_expect]
  calc
    ν.expect (fun ω => if ∃ i, upper i ω then 1 else 0) ≤
        ν.expect (fun ω => ∑ i, if upper i ω then 1 else 0) := by
      apply ν.expect_mono
      intro ω
      by_cases h : ∃ i, upper i ω
      · obtain ⟨i, hi⟩ := h
        rw [if_pos (show ∃ i,upper i ω from ⟨i,hi⟩)]
        have hsingle := Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
            (show (0 : ℝ) ≤ if upper j ω then 1 else 0 by split <;> norm_num))
          (Finset.mem_univ i)
        simpa only [if_pos hi] using hsingle
      · simp only [if_neg h]
        exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    _ = ∑ i, ν.prob (upper i) := by
      rw [FiniteLaw.expect_finset_sum]
      simp only [← FiniteLaw.prob_eq_expect]
    _ ≤ ∑ _i : ι, π := Finset.sum_le_sum (fun i _ => hmarg i)
    _ = (Fintype.card ι : ℝ) * π := by simp

end FCAppendix.Affine.Tail04
