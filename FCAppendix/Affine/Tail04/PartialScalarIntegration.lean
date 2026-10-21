import FCAppendix.Affine.Tail04.NativePartialTerminal
import FCAppendix.Affine.Tail04.PrivateComposition

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialScalarIntegration
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeCountCoordinates NativePrivatePosterior NativePartialExperiment
open scoped BigOperators

def gated (a : Bool×Bool) (τ : Equiv.Perm (Fin 2)) : Fin 3 :=
  boolPairCount ((if (0:Fin 2)∈firstK τ 1 then a.1 else false),
    (if (1:Fin 2)∈firstK τ 1 then a.2 else false))

lemma gated_payoff (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (v b : ℝ)
    (a : Bool×Bool) (τ : Equiv.Perm (Fin 2)) :
    userPayoff v b 0 (Schedule.affine 2 η hη0 hη1).charge (Schedule.once 2).charge
      (gated a τ).val=
      (if (0:Fin 2)∈firstK τ 1 then (v-b)*(if a.1 then 1 else 0) else 0)+
      (if (1:Fin 2)∈firstK τ 1 then (v-b)*(if a.2 then 1 else 0) else 0) := by
  have h01 : ((0:Fin 2)∉firstK τ 1)↔(1:Fin 2)∈firstK τ 1 :=
    singleton_missing_iff_other τ 0
  rcases a with ⟨a0,a1⟩
  cases a0 <;> cases a1 <;> by_cases h0 : (0:Fin 2)∈firstK τ 1
  all_goals
    have h1 : ((1:Fin 2)∈firstK τ 1)↔¬((0:Fin 2)∈firstK τ 1) := h01.symm
    simp only [gated,boolPairCount,h1,h0,not_true_eq_false,not_false_eq_true,
      ite_true,ite_false,Bool.false_eq_true,Schedule.affine,Schedule.once,
      userPayoff,successIndicator]
    norm_num

lemma integral_fair_indicator (j : Fin 2) (x : ℝ) :
    (∫ τ : Equiv.Perm (Fin 2),(if j∈firstK τ 1 then x else 0) ∂permLaw 2)=(1/2:ℝ)*x := by
  have he : (fun τ : Equiv.Perm (Fin 2) => if j∈firstK τ 1 then x else 0)=
      (oneRouteEvent j).indicator (fun _ => x) := by
    funext τ
    simp only [Set.indicator,oneRouteEvent,Set.mem_setOf_eq]
  rw [he]
  rw [integral_indicator_const x (measurableSet_oneRouteEvent j),smul_eq_mul,
    original_fair_route_mass j]

theorem fair_route_payoff (η : ℝ) (hη0 : 0≤ η) (hη1 : η≤1) (v b : ℝ) (a : Bool×Bool) :
    (∫ τ : Equiv.Perm (Fin 2),userPayoff v b 0
      (Schedule.affine 2 η hη0 hη1).charge (Schedule.once 2).charge (gated a τ).val ∂permLaw 2)=
      (1/2:ℝ)*((v-b)*(if a.1 then 1 else 0))+
      (1/2:ℝ)*((v-b)*(if a.2 then 1 else 0)) := by
  simp_rw [gated_payoff]
  have hi (j : Fin 2) (x : ℝ) : Integrable
      (fun τ : Equiv.Perm (Fin 2) => if j∈firstK τ 1 then x else 0) (permLaw 2) := by
    have h := (integrable_const x : Integrable (fun _ : Equiv.Perm (Fin 2) => x) (permLaw 2)).indicator
      (measurableSet_oneRouteEvent j)
    convert! h using 1
    funext τ
    simp only [Set.indicator,oneRouteEvent,Set.mem_setOf_eq]
  erw [integral_add (hi 0 _) (hi 1 _),integral_fair_indicator,integral_fair_indicator]

lemma indicator_surplus_bound {R V : ℝ} (hR : 0≤ R) (v : ℝ) (b : Icc R V) (a : Bool) :
    |(v-b)*(if a then (1:ℝ) else 0)|≤|v|+V := by
  cases a
  · simp only [Bool.false_eq_true,ite_false,mul_zero,abs_zero]
    linarith [abs_nonneg v,hR.trans b.2.1,b.2.2]
  · simp only [ite_true,mul_one]
    exact (abs_sub v b).trans (by rw [abs_of_nonneg (hR.trans b.2.1)];linarith [b.2.2])

lemma integrable_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (f : Y→ℝ) (h : X→ Y)
    (hf : Measurable f) (hh : Measurable h) (C : ℝ) (hC : ∀ y,‖f y‖≤ C) :
    Integrable (f ∘ h) μ :=
  Integrable.of_bound (hf.comp hh).aestronglyMeasurable C (ae_of_all _ fun x => hC (h x))

end FCAppendix.Affine.Tail04.PartialScalarIntegration
