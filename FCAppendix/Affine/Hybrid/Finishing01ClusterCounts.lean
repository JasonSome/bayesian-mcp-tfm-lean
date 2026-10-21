import FCAppendix.Affine.Hybrid.Finishing01Definitions
import FCAppendix.Affine.Hybrid.FavoredCountCoefficient

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open scoped BigOperators
open Affine.LowBody

def activePatternPure {N : ℕ} (xi L U : ℝ) (c : ℕ) (z : ℝ)
    (kind : Fin N → Fin 4) : Prop :=
  ¬activePatternGuarded xi L U c z kind ∧
    (activePatternTemplate c kind).residual₀ ≠
      (activePatternTemplate c kind).residual₁

lemma activePattern_equal_full_lower_of_close {N c : ℕ} {rho a h delta : ℝ}
    (kind : Fin N → Fin 4)
    (hcap : |(c:ℝ)-(N+1:ℕ)*rho| ≤ (N+1:ℕ)*delta)
    (ha : |(Fintype.card (ActivePatternIndex kind):ℝ)-(N+1:ℕ)*a| ≤
      (N+1:ℕ)*delta)
    (h0 : |(activePatternUpper kind 0:ℝ)-(N+1:ℕ)*(h/2)| ≤ (N+1:ℕ)*delta)
    (h1 : |(activePatternUpper kind 1:ℝ)-(N+1:ℕ)*(h/2)| ≤ (N+1:ℕ)*delta)
    (hlo : 2*delta < rho-h/2) (hhi : 3*delta < a+h/2-rho)
    (heq : activePatternCapacity c kind 0 = activePatternCapacity c kind 1) :
    (activePatternTemplate c kind).residual₀ =
      (activePatternTemplate c kind).residual₁ := by
  have hi := active_residuals_interior_of_close (M:=N+1) (by omega)
    hcap ha h0 h1 hlo hhi
  have hu : activePatternUpper kind 0 = activePatternUpper kind 1 :=
    hi.2.2.2.2.2.2.mp heq
  simp only [activePatternTemplate,hu]

lemma activePatternCountException_mono {N : ℕ} (C : FiniteLaw (Fin 4))
    {delta epsilon : ℝ} (hle : delta ≤ epsilon) (kind : Fin N → Fin 4) :
    activePatternCountException C epsilon kind → activePatternCountException C delta kind := by
  rintro ⟨k,hk⟩
  exact ⟨k,(mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)).trans hk⟩

def doubleActivePrefix : Fin 2 → Fin 4 := fun _ => 1

lemma categoryCount_cons_active {N : ℕ} (k : Fin 4) (row : Fin N → Fin 4) :
    categoryCount k (Fin.cons (1:Fin 4) row) =
      (if (1:Fin 4)=k then 1 else 0)+categoryCount k row := by
  exact categoryCount_cons k 1 row

lemma activePatternCountException_cons {N : ℕ} (C : FiniteLaw (Fin 4))
    (delta : ℝ) (row : Fin N → Fin 4) :
    activePatternCountException C delta (Fin.cons (1:Fin 4) row) ↔
      ∃k : Fin 4,(N+2:ℕ)*delta ≤
        |(categoryCount k doubleActivePrefix:ℝ)+(categoryCount k row:ℝ)-
          (N+2:ℕ)*C.mass k| := by
  have hprefix (k : Fin 4) : categoryCount k activeFocalPrefix+
      categoryCount k (Fin.cons (1:Fin 4) row) =
      categoryCount k doubleActivePrefix+categoryCount k row := by
    rw [categoryCount_cons_active]
    have h1 : categoryCount k activeFocalPrefix = (if (1:Fin 4)=k then 1 else 0) := by
      unfold categoryCount LowBody.hitCount activeFocalPrefix
      rw [Fin.sum_univ_one]
      split_ifs <;> rfl
    have h2 : categoryCount k doubleActivePrefix =
        (if (1:Fin 4)=k then 1 else 0)+(if (1:Fin 4)=k then 1 else 0) := by
      unfold categoryCount LowBody.hitCount doubleActivePrefix
      rw [Fin.sum_univ_two]
      split_ifs <;> rfl
    rw [h1,h2]
    omega
  unfold activePatternCountException
  apply exists_congr
  intro k
  have hsize : N+1+1=N+2 := by omega
  rw [hsize,←Nat.cast_add,hprefix]
  simp only [Nat.cast_add]

namespace Finish01.Primitives
variable (P : Primitives)

theorem eventual_count_good_guarded_or_equal (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃delta : ℝ,0<delta ∧ delta<P.s ∧
      ∀ᶠN : ℕ in atTop,∀ kind : Fin N → Fin 4,
      ¬activePatternCountException P.categories delta kind →
        activePatternGuarded P.xi P.L P.U (c (N+1)) P.z kind ∨
          (activePatternTemplate (c (N+1)) kind).residual₀=
            (activePatternTemplate (c (N+1)) kind).residual₁ := by
  obtain ⟨dg,deq,hdg,hdgs,hdeq,hguard⟩ :=
    exists_eventual_activePattern_guard_bound P.s P.a P.h P.rho P.z P.xi P.L P.U
      P.s_pos P.a_pos P.h_pos P.mass P.z_nonneg P.z_lt_one P.xi_pos P.xi_lt_one
      P.L_pos P.L_lt_U.le P.rho_lower P.rho_upper P.qbar_pos P.qbar_lt_one
      P.box_lower P.box_upper c hc
  let delta := min dg (min ((P.rho-P.h/2)/4) ((P.a+P.h/2-P.rho)/6))
  have hd : 0<delta := lt_min hdg (lt_min (by linarith [P.rho_lower])
    (by linarith [P.rho_upper]))
  have hdg' : delta≤ dg := min_le_left _ _
  have hlo : 2*delta<P.rho-P.h/2 := by
    have h : delta ≤ (P.rho-P.h/2)/4 :=
      (min_le_right dg _).trans (min_le_left _ _)
    change delta≤(P.rho-P.h/2)/4 at h
    linarith [P.rho_lower]
  have hhi : 3*delta<P.a+P.h/2-P.rho := by
    have h : delta ≤ (P.a+P.h/2-P.rho)/6 :=
      (min_le_right dg _).trans (min_le_right _ _)
    change delta≤(P.a+P.h/2-P.rho)/6 at h
    linarith [P.rho_upper]
  have hcapN : ∀ᶠN : ℕ in atTop,
      |(c (N+1):ℝ)/(N+1:ℕ)-P.rho|<delta := by
    simpa only [Real.dist_eq,Function.comp_def] using
      (Metric.tendsto_nhds.mp (hc.comp (tendsto_add_atTop_nat 1))) delta hd
  refine ⟨delta,hd,hdg'.trans_lt hdgs,?_⟩
  filter_upwards [hguard,hcapN] with N hN hcapFrac
  intro kind hgood
  have hgoodg : ¬activePatternCountException P.categories dg kind :=
    fun h => hgood (activePatternCountException_mono P.categories hdg' kind h)
  have hpoint := (hN (Measure.dirac (0:ℝ)) inferInstance).1 kind hgoodg
  rcases hpoint with heq|hg
  · right
    have hm : (0:ℝ)<(N+1:ℕ) := by positivity
    have hcap : |(c (N+1):ℝ)-(N+1:ℕ)*P.rho|≤(N+1:ℕ)*delta := by
      have he : (c (N+1):ℝ)/(N+1:ℕ)-P.rho=
          ((c (N+1):ℝ)-(N+1:ℕ)*P.rho)/(N+1:ℕ) := by field_simp
      rw [he,abs_div,abs_of_pos hm] at hcapFrac
      simpa only [mul_comm] using ((div_lt_iff₀ hm).mp hcapFrac).le
    have hclose (k : Fin 4) :
        |(fullCategoryCount activeFocalPrefix kind k:ℝ)-(N+1:ℕ)*P.categories.mass k|≤
          (N+1:ℕ)*delta := by
      have h := (lt_of_not_ge (fun h => hgood ⟨k,h⟩)).le
      simpa only [fullCategoryCount,Nat.cast_add] using h
    apply activePattern_equal_full_lower_of_close kind hcap
      (rho:=P.rho) (a:=P.a) (h:=P.h) (delta:=delta)
    · simpa [activePattern_count_active,Primitives.categories,
        LowBody.categoryLaw_mass] using hclose 1
    · have hh := hclose 2
      rw [show fullCategoryCount activeFocalPrefix kind 2=activePatternUpper kind 0 from
        activePattern_count_upper kind 0] at hh
      simpa [Primitives.categories,LowBody.categoryLaw_mass] using hh
    · have hh := hclose 3
      rw [show fullCategoryCount activeFocalPrefix kind 3=activePatternUpper kind 1 from
        activePattern_count_upper kind 1] at hh
      simpa [Primitives.categories,LowBody.categoryLaw_mass] using hh
    · exact hlo
    · exact hhi
    · exact heq
  · exact Or.inl hg

theorem two_prefix_actual_guard_region (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃delta : ℝ,0<delta ∧ delta<P.s ∧ ∀ᶠN : ℕ in atTop,
      (∀ row : Fin N→ Fin 4,
        ¬(∃k : Fin 4,(N+2:ℕ)*delta≤
          |(categoryCount k doubleActivePrefix:ℝ)+(categoryCount k row:ℝ)-
            (N+2:ℕ)*P.categories.mass k|) →
        activePatternGuarded P.xi P.L P.U (c (N+2)) P.z (Fin.cons (1:Fin 4) row) ∨
          (activePatternTemplate (c (N+2)) (Fin.cons (1:Fin 4) row)).residual₀=
            (activePatternTemplate (c (N+2)) (Fin.cons (1:Fin 4) row)).residual₁) ∧
      (CommonList.iid P.categories N).prob (fun row =>
        ∃k : Fin 4,(N+2:ℕ)*delta≤
          |(categoryCount k doubleActivePrefix:ℝ)+(categoryCount k row:ℝ)-
            (N+2:ℕ)*P.categories.mass k|)≤
        8*Real.exp (-(N:ℝ)*delta^2/2) := by
  obtain ⟨delta,hd,hds,hgood⟩ := P.eventual_count_good_guarded_or_equal c hc
  have hgood2 := (tendsto_add_atTop_nat 1).eventually hgood
  have hn : Tendsto (fun N : ℕ => (N:ℝ)*delta/2) atTop atTop := by
    convert! (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hd)) using 1
    funext N
    ring
  have hprefix : ∀ᶠN : ℕ in atTop,(2:ℝ)≤(N:ℝ)*delta/2 := hn.eventually_ge_atTop 2
  refine ⟨delta,hd,hds,?_⟩
  filter_upwards [hgood2,hprefix] with N hN hpr
  constructor
  · intro row hrow
    have hactual : ¬activePatternCountException P.categories delta (Fin.cons (1:Fin 4) row) :=
      fun h => hrow ((activePatternCountException_cons P.categories delta row).mp h)
    simpa only [show N+1+1=N+2 by omega] using hN (Fin.cons (1:Fin 4) row) hactual
  · simpa only [Nat.cast_ofNat] using
      forced_fractional_count_exception_le P.categories doubleActivePrefix N hd.le hpr

theorem eventually_pure_branch_rate (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃delta : ℝ,0<delta ∧ ∀ᶠN : ℕ in atTop,
      (CommonList.iid P.categories N).prob (fun row =>
        activePatternPure P.xi P.L P.U (c (N+2)) P.z (Fin.cons (1:Fin 4) row)) ≤
          8*Real.exp (-(N:ℝ)*delta^2/2) := by
  obtain ⟨delta,hd,hds,hgood⟩ := P.eventual_count_good_guarded_or_equal c hc
  have hgood2 := (tendsto_add_atTop_nat 1).eventually hgood
  have hn : Tendsto (fun N : ℕ => (N:ℝ)*delta/2) atTop atTop := by
    convert! (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hd)) using 1
    funext N
    ring
  have hprefix : ∀ᶠN : ℕ in atTop,(2:ℝ)≤(N:ℝ)*delta/2 := hn.eventually_ge_atTop 2
  refine ⟨delta,hd,?_⟩
  filter_upwards [hgood2,hprefix] with N hN hpr
  apply le_trans ?_ (forced_fractional_count_exception_le P.categories
    doubleActivePrefix N hd.le (by simpa using hpr))
  apply FiniteLaw.prob_mono
  intro row hpure
  apply (activePatternCountException_cons P.categories delta row).mp
  by_contra hnot
  have h := hN (Fin.cons (1:Fin 4) row) hnot
  rcases h with hguard|hequal
  · exact hpure.1 (by simpa only [Nat.add_assoc] using hguard)
  · exact hpure.2 (by simpa only [Nat.add_assoc] using hequal)

theorem eventually_pure_branch_rate_one (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∃delta : ℝ,0<delta ∧ ∀ᶠN : ℕ in atTop,
      (CommonList.iid P.categories N).prob (fun kind =>
        activePatternPure P.xi P.L P.U (c (N+1)) P.z kind) ≤
          8*Real.exp (-(N:ℝ)*delta^2/2) := by
  obtain ⟨delta,hd,hds,hgood⟩ := P.eventual_count_good_guarded_or_equal c hc
  have hn : Tendsto (fun N : ℕ => (N:ℝ)*delta/2) atTop atTop := by
    convert! (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hd)) using 1
    funext N
    ring
  have hprefix : ∀ᶠN : ℕ in atTop,(1:ℝ)≤(N:ℝ)*delta/2 := hn.eventually_ge_atTop 1
  refine ⟨delta,hd,?_⟩
  filter_upwards [hgood,hprefix] with N hN hpr
  apply le_trans ?_ (forced_fractional_count_exception_le P.categories
    activeFocalPrefix N hd.le (by simpa using hpr))
  apply FiniteLaw.prob_mono
  intro kind hpure
  change activePatternCountException P.categories delta kind
  by_contra hnot
  rcases hN kind hnot with hguard|hequal
  · exact hpure.1 hguard
  · exact hpure.2 hequal

theorem eventually_guarded_probability_half (c : ℕ → ℕ)
    (hc : Tendsto (fun M => (c M:ℝ)/(M:ℝ)) atTop (𝓝 P.rho)) :
    ∀ᶠN : ℕ in atTop,
      (1:ℝ)/2≤(CommonList.iid P.categories N).prob
        (activePatternGuarded P.xi P.L P.U (c (N+1)) P.z) := by
  obtain ⟨d,deq,hd,hds,hdeq,hbound⟩ :=
    exists_eventual_activePattern_guard_bound P.s P.a P.h P.rho P.z P.xi P.L P.U
      P.s_pos P.a_pos P.h_pos P.mass P.z_nonneg P.z_lt_one P.xi_pos P.xi_lt_one
      P.L_pos P.L_lt_U.le P.rho_lower P.rho_upper P.qbar_pos P.qbar_lt_one
      P.box_lower P.box_upper c hc
  have hsmall := (activeGuardExceptionError_tendsto_zero P.h_pos hd hdeq).eventually_lt_const
    (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hbound,hsmall] with N hN hsmallN
  have h := (hN (Measure.dirac (0:ℝ)) inferInstance).2
  change (CommonList.iid P.categories N).prob
    (fun kind => ¬activePatternGuarded P.xi P.L P.U (c (N+1)) P.z kind)≤ _ at h
  have hcomp := (CommonList.iid P.categories N).prob_compl
    (activePatternGuarded P.xi P.L P.U (c (N+1)) P.z)
  linarith

end Finish01.Primitives
end FCAppendix.Affine.Hybrid
