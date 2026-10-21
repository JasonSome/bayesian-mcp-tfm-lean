import FCAppendix.Affine.Hybrid.CategoryFibers
import FCAppendix.AppendixRepair.TailReceipts

noncomputable section
namespace FCAppendix.Appendix08.Tail
open MeasureTheory ProbabilityTheory Set Game Bayes Filter Topology Classical Affine Affine.Hybrid
open scoped BigOperators

def tailRoutedTag (chi : ℝ→ Fin 3) (x : UserDraw 2) : Fin 4 :=
  if chi x.1.2.bid=0 then 0 else if chi x.1.2.bid=1 then 1
  else if (0:Fin 2)∈firstK x.2 x.1.2.routeCount then 2 else 3

theorem measurable_tailRoutedTag (chi : ℝ→ Fin 3) (hchi : Measurable chi) :
    Measurable (tailRoutedTag chi) := by
  have hb : Measurable (fun x : UserDraw 2=>x.1.2.bid) :=
    (measurable_bid 2).comp measurable_fst.snd
  have hc : Measurable (fun x : UserDraw 2=>chi x.1.2.bid) := hchi.comp hb
  have hr : Measurable (fun x : UserDraw 2=>(x.2,x.1.2.routeCount)) :=
    measurable_snd.prodMk ((measurable_routeCount 2).comp measurable_fst.snd)
  unfold tailRoutedTag
  apply Measurable.ite (measurableSet_eq_fun hc measurable_const) measurable_const
  apply Measurable.ite (measurableSet_eq_fun hc measurable_const) measurable_const
  exact Measurable.ite
    ((measurableSet_mem_firstK (0:Fin 2)).preimage hr) measurable_const measurable_const

theorem tail_native_private_fiber {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (chi : ℝ→ Fin 3) (hchi : Measurable chi)
    (assignment : Fin m→ Fin 4) :
    cond (userProfileLaw Gamma) (categoryFiber (tailRoutedTag chi) assignment)=
      Measure.pi (fun i : Fin m=>
        cond (userLaw Gamma) ((tailRoutedTag chi) ⁻¹' {assignment i})) := by
  exact native_conditional_categoryFiber Gamma (tailRoutedTag chi)
    (measurable_tailRoutedTag chi hchi) assignment

theorem tail_native_private_fiber_mass {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame m 2 c Seed) (chi : ℝ→ Fin 3)
    (assignment : Fin m→ Fin 4) :
    (userProfileLaw Gamma) (categoryFiber (tailRoutedTag chi) assignment)=
      ∏i : Fin m,(userLaw Gamma) ((tailRoutedTag chi) ⁻¹' {assignment i}) := by
  exact categoryFiber_mass (userLaw Gamma) (tailRoutedTag chi) assignment

theorem tail_private_mark_share {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (privateSet upper : Set X)
    (hprivate : MeasurableSet privateSet) (_hupper : MeasurableSet upper)
    {h epsilon : ℝ} (hh : 0< h) (he : 0≤ epsilon)
    (hprivateMass : mu privateSet=ENNReal.ofReal ((h+epsilon)/2))
    (hupperMass : mu (privateSet∩upper)=ENNReal.ofReal (epsilon/2)) :
    ((cond mu privateSet) upper).toReal=epsilon/(h+epsilon) := by
  rw [cond_apply hprivate,hprivateMass,hupperMass]
  rw [ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : 0≤(h+epsilon)/2),
    ENNReal.toReal_ofReal (by positivity : 0≤ epsilon/2)]
  have hd : h+epsilon≠0 := ne_of_gt (by positivity)
  field_simp [hd]

theorem tail_private_share_small {C h x : ℝ}
    (hC : 0≤ C) (hh : 0< h) (hx : 0< x) (hlarge : 100*C≤ h*x) :
    x*(C/x^2)/(h+C/x^2)≤ 1/100 := by
  have hx2 : 0< x^2 := sq_pos_of_pos hx
  have he : 0≤ C/x^2 := div_nonneg hC hx2.le
  have hden : 0< h+C/x^2 := by positivity
  apply (div_le_iff₀ hden).2
  have hc : 100*(x*(C/x^2))≤ h := by
    apply (mul_le_mul_iff_left₀ hx2).mp
    calc
      100*(x*(C/x^2))*x^2=100*C*x := by
        field_simp [ne_of_gt hx]
      _≤(h*x)*x := mul_le_mul_of_nonneg_right hlarge hx.le
      _=h*x^2 := by ring
  nlinarith

theorem eventually_tail_private_share_small (C h : ℝ) (hC : 0≤ C) (hh : 0< h) :
    ∀ᶠm : ℕ in atTop,
      (m:ℝ)*(C/(m:ℝ)^2)/(h+C/(m:ℝ)^2)≤ 1/100 := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max (1:ℝ) (100*C/h))
  filter_upwards [eventually_ge_atTop M] with m hm
  have hmm : (M:ℝ)≤ m := by exact_mod_cast hm
  have hx : 0<(m:ℝ) := by linarith [le_max_left (1:ℝ) (100*C/h)]
  have hlarge : 100*C≤ h*(m:ℝ) := by
    have hbound : 100*C/h≤(m:ℝ) :=
      (le_max_right (1:ℝ) (100*C/h)).trans (hM.le.trans hmm)
    have hh' := (div_le_iff₀ hh).mp hbound
    nlinarith
  exact tail_private_share_small hC hh hx hlarge

end FCAppendix.Appendix08.Tail
