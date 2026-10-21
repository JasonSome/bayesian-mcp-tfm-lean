import FCAppendix.Affine.Hybrid.Native02.FullContextRows
import FCAppendix.Affine.Hybrid.Native02.SourceRowPayoff
import FCAppendix.Affine.Hybrid.SourceUniformMenus
import FCAppendix.Affine.Hybrid.ActivePatternCountBounds
import FCAppendix.Affine.Hybrid.Native02.CountsFromPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
namespace FullContext

open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical Filter Topology
open scoped BigOperators

variable {N m c : ℕ}

lemma finite_menu_error {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (good : Ω → Prop) (f : Ω → ℝ) (target B eps : ℝ)
    (heps : 0 ≤ eps) (hB : ∀ k, |f k| ≤ B) (htarget : |target| ≤ B)
    (hgood : ∀ k, good k → |f k-target| ≤ eps) :
    |P.expect f-target| ≤ eps+2*B*P.prob (fun k => ¬good k) := by
  have hd (k : Ω) : |f k-target| ≤ eps+2*B*(if ¬good k then (1:ℝ) else 0) := by
    by_cases hg : good k
    · simpa only [not_not, hg, not_true_eq_false, if_false, mul_zero, add_zero]
        using hgood k hg
    · have h := (abs_sub (f k) target).trans (add_le_add (hB k) htarget)
      simpa only [if_pos hg, mul_one] using h.trans (by linarith)
  calc
    |P.expect f-target| = |P.expect (fun k => f k-target)| := by
      rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
    _ ≤ P.expect (fun k => |f k-target|) := P.abs_expect_le _
    _ ≤ P.expect (fun k => eps+2*B*(if ¬good k then (1:ℝ) else 0)) := P.expect_mono hd
    _ = _ := by
      rw [FiniteLaw.expect_add, FiniteLaw.expect_const, FiniteLaw.expect_const_mul]
      rw [FiniteLaw.prob_eq_expect]

lemma abs_realizedPayoff_two {eta : ℝ} (heta : |eta| ≤ 1)
    (v b : ℝ) (k : Fin 3) : |realizedPayoff eta v b k.val| ≤ |v|+2*|b| := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · simpa [realizedPayoff] using add_nonneg (abs_nonneg v)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg b))
  · simpa [realizedPayoff] using
      (abs_sub v b).trans (by linarith [abs_nonneg b])
  · have h : |v-b*(1+eta)| ≤ |v|+2*|b| := by
      calc
        _ ≤ |v|+|b| *|1+eta| := by simpa only [abs_mul] using abs_sub v (b*(1+eta))
        _ ≤ |v|+|b| *2 := add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (show |1+eta| ≤ 2 from
            (abs_add_le 1 eta).trans (by simpa only [abs_one] using (show 1+|eta| ≤ 2 by linarith)))
            (abs_nonneg b))
        _ = _ := by ring
    convert! h using 1
    norm_num [realizedPayoff]

lemma abs_singletonCountPayoff_two (v b : ℝ) (k : Fin 3) :
    |((v-b)/2)*(k.val:ℝ)| ≤ |v|+|b| := by
  have hk : (k.val:ℝ) ≤ 2 := by exact_mod_cast (show k.val≤2 by omega)
  have hk0 : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
  calc
    _ = |v-b|/2*(k.val:ℝ) := by rw [abs_mul, abs_div, abs_of_nonneg hk0]; norm_num
    _ ≤ |v-b|/2*2 := mul_le_mul_of_nonneg_left hk (div_nonneg (abs_nonneg _) (by norm_num))
    _ = |v-b| := by ring
    _ ≤ _ := abs_sub v b

lemma abs_private_broadcast_menu (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) {eta : ℝ} (heta : |eta| ≤ 1) (v b : ℝ) :
    |(privateContextLaw C X i).expect (fun k => realizedPayoff eta v b k.val)| ≤
      |v|+2*|b| :=
  abs_finite_expect_le_of_support _ _ _ (fun k _ => abs_realizedPayoff_two heta v b k)

lemma abs_private_singleton_menu (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (v b : ℝ) :
    |(privateContextLaw C X i).expect (fun k => ((v-b)/2)*(k.val:ℝ))| ≤ |v|+|b| :=
  abs_finite_expect_le_of_support _ _ _ (fun k _ => abs_singletonCountPayoff_two v b k)

def patternBroadcastMenu (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ) (eta v b : ℝ)
    (kind : Fin N → Fin 4) : ℝ :=
  ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
    (privateContextLaw C
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
        (fun k => realizedPayoff eta v b k.val)
    ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B)

def patternSingletonMenu (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ) (v b : ℝ)
    (kind : Fin N → Fin 4) : ℝ :=
  ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
    (privateContextLaw C
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
        (fun k => ((v-b)/2)*(k.val:ℝ))
    ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B)

lemma abs_patternBroadcastMenu (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    {eta : ℝ} (heta : |eta| ≤ 1) (v b : ℝ) (kind : Fin N → Fin 4) :
    |patternBroadcastMenu C e μ B eta v b kind| ≤ |v|+2*|b| := by
  unfold patternBroadcastMenu
  have hlow (active : Fin N → ℝ) :
      |∫ low : Fin N → ℝ,
        (privateContextLaw C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
            (fun k => realizedPayoff eta v b k.val) ∂Measure.pi (fun _ : Fin N => μ)| ≤
          |v|+2*|b| := by
    have h := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin N => μ))
      (C := |v|+2*|b|)
      (f := fun low : Fin N → ℝ => (privateContextLaw C
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
          (fun k => realizedPayoff eta v b k.val))
      (ae_of_all _ (fun low => by
        simpa only [Real.norm_eq_abs] using abs_private_broadcast_menu C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0) heta v b))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin N => B))
    (C := |v|+2*|b|)
    (f := fun active : Fin N → ℝ => ∫ low : Fin N → ℝ,
      (privateContextLaw C (NativeContinuation.reindexContext e
        (sourceRowContext kind low active b)) (e.symm 0)).expect
          (fun k => realizedPayoff eta v b k.val) ∂Measure.pi (fun _ : Fin N => μ))
    (ae_of_all _ (fun active => by
      simpa only [Real.norm_eq_abs] using hlow active))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

lemma abs_patternSingletonMenu (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (v b : ℝ) (kind : Fin N → Fin 4) :
    |patternSingletonMenu C e μ B v b kind| ≤ |v|+|b| := by
  unfold patternSingletonMenu
  have hlow (active : Fin N → ℝ) :
      |∫ low : Fin N → ℝ,
        (privateContextLaw C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
            (fun k => ((v-b)/2)*(k.val:ℝ)) ∂Measure.pi (fun _ : Fin N => μ)| ≤
          |v|+|b| := by
    have h := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin N => μ))
      (C := |v|+|b|)
      (f := fun low : Fin N → ℝ => (privateContextLaw C
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).expect
          (fun k => ((v-b)/2)*(k.val:ℝ)))
      (ae_of_all _ (fun low => by
        simpa only [Real.norm_eq_abs] using abs_private_singleton_menu C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0) v b))
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin N => B))
    (C := |v|+|b|)
    (f := fun active : Fin N → ℝ => ∫ low : Fin N → ℝ,
      (privateContextLaw C (NativeContinuation.reindexContext e
        (sourceRowContext kind low active b)) (e.symm 0)).expect
          (fun k => ((v-b)/2)*(k.val:ℝ)) ∂Measure.pi (fun _ : Fin N => μ))
    (ae_of_all _ (fun active => by
      simpa only [Real.norm_eq_abs] using hlow active))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

lemma abs_independentTwo {eta q : ℝ} (heta : |eta| ≤ 1) (hq : q ∈ Icc (0:ℝ) 1)
    (v b : ℝ) : |independentTwo eta v b q| ≤ |v|+2*|b| := by
  have hq0 := hq.1
  have hq1 := hq.2
  have hq2 : 0 ≤ q^2 ∧ q^2 ≤ 1 := ⟨sq_nonneg q, by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]⟩
  have hs : 0 ≤ 2*q-q^2 ∧ 2*q-q^2 ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (q-1)]
  have he : independentTwo eta v b q = (v-b)*(2*q-q^2)-eta*b*q^2 := by
    unfold independentTwo
    ring
  rw [he]
  calc
    _ ≤ |v-b| *|2*q-q^2|+|eta| *|b| *|q^2| := by
      convert! (abs_sub ((v-b)*(2*q-q^2)) (eta*b*q^2)) using 1
      rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (|v|+|b|)*1+1*|b| *1 := by
      rw [abs_of_nonneg hs.1, abs_of_nonneg hq2.1]
      apply add_le_add
      · exact mul_le_mul (abs_sub v b) hs.2 hs.1 (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right heta (abs_nonneg b)) hq2.2
          hq2.1 (by positivity)
    _ = _ := by ring

lemma abs_limiting_broadcast_menu {eta z q : ℝ} (heta : |eta| ≤ 1)
    (hz : z ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) (v b : ℝ) :
    |z*(v-b)+(1-z)*independentTwo eta v b q| ≤ |v|+2*|b| := by
  calc
    _ ≤ z*|v-b|+(1-z)*|independentTwo eta v b q| := by
      simpa only [abs_mul, abs_of_nonneg hz.1, abs_of_nonneg (sub_nonneg.mpr hz.2)] using
        abs_add_le (z*(v-b)) ((1-z)*independentTwo eta v b q)
    _ ≤ z*(|v|+2*|b|)+(1-z)*(|v|+2*|b|) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left ((abs_sub v b).trans (by linarith [abs_nonneg b])) hz.1)
        (mul_le_mul_of_nonneg_left (abs_independentTwo heta hq v b) (sub_nonneg.mpr hz.2))
    _ = _ := by ring

lemma abs_limiting_singleton_menu {z q : ℝ}
    (hz : z ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) (v b : ℝ) :
    |(z/2+(1-z)*q)*(v-b)| ≤ |v|+|b| := by
  have hz0 := hz.1
  have hz1 := hz.2
  have hq0 := hq.1
  have hq1 := hq.2
  have hp : 0 ≤ z/2+(1-z)*q ∧ z/2+(1-z)*q ≤ 1 := by
    constructor
    · positivity
    · nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (sub_nonneg.mpr hq.2)]
  calc
    _ = (z/2+(1-z)*q)*|v-b| := by rw [abs_mul, abs_of_nonneg hp.1]
    _ ≤ 1*(|v|+|b|) := mul_le_mul hp.2 (abs_sub v b) (abs_nonneg _) (by norm_num)
    _ = _ := one_mul _

lemma sourceOwnerPayoff_roles {xi L U : ℝ} (z : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (hg : activePatternGuarded xi L U c z kind)
    (eta v : ℝ) (b : ActivePatternIndex kind → ℝ) (i : ActivePatternIndex kind) :
    sourceOwnerPayoff xi eta v b (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) i =
    sourceOwnerPayoff xi eta v b (activePatternResidual c z kind)
      (activePatternQuota z kind+activePatternGap c kind) (activePatternQuota z kind) i := by
  have hs := activePatternOwner_sum_of_ne c z kind hg.2.1
  have hbig : (activePatternQuota z kind+activePatternGap c kind)+activePatternQuota z kind =
      activePatternOwner c z kind 0+activePatternOwner c z kind 1 := by omega
  rw [sourceOwnerPayoff_eq_favored _ _ _ _ _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2.1.le,
    sourceOwnerPayoff_eq_favored _ _ _ _ _ _ _ _ hg.1
      (by simpa only [hbig] using hg.2.2.1) (by simpa only [hbig] using hg.2.2.2.1.le), hbig]

lemma sourceSingletonPayoff_roles {xi L U : ℝ} (z : ℝ) (c : ℕ)
    (kind : Fin N → Fin 4) (hg : activePatternGuarded xi L U c z kind)
    (v : ℝ) (b : ActivePatternIndex kind → ℝ) (i : ActivePatternIndex kind) :
    sourceSingletonPayoff xi v b (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) i =
    sourceSingletonPayoff xi v b (activePatternResidual c z kind)
      (activePatternQuota z kind+activePatternGap c kind) (activePatternQuota z kind) i := by
  have hs := activePatternOwner_sum_of_ne c z kind hg.2.1
  have hbig : (activePatternQuota z kind+activePatternGap c kind)+activePatternQuota z kind =
      activePatternOwner c z kind 0+activePatternOwner c z kind 1 := by omega
  rw [sourceSingletonPayoff_eq_favored _ _ _ _ _ _ _ hg.1 hg.2.2.1 hg.2.2.2.1.le,
    sourceSingletonPayoff_eq_favored _ _ _ _ _ _ _ hg.1
      (by simpa only [hbig] using hg.2.2.1) (by simpa only [hbig] using hg.2.2.2.1.le), hbig]

theorem exists_eventual_pattern_menu_bounds (s a h rho z xi eta L U W : ℝ)
    (hs : 0 ≤ s) (ha : 0 < a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hxi : 0 < xi) (hxi1 : xi < 1)
    (hL : 0 < L) (hLU : L ≤ U) (hW : 0 ≤ W)
    (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (B : Measure ℝ) [IsProbabilityMeasure B], (∀ᵐ x ∂B, x ∈ Icc L U) →
      ∀ kind : Fin N → Fin 4,
      activePatternGuarded xi L U (capacityFamily (N+1)) z kind →
      ¬activePatternCountException (categoryLaw s a h hs ha.le hh hsum B) delta kind →
      ∀ b ∈ Icc L U, ∀ v : ℝ, |v| ≤ W →
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) b
      |(∫ x : ActivePatternIndex kind → ℝ,
        sourceOwnerPayoff xi eta v (Function.update x (activePatternFocal kind) b)
          (activePatternResidual (capacityFamily (N+1)) z kind)
          (activePatternOwner (capacityFamily (N+1)) z kind 0)
          (activePatternOwner (capacityFamily (N+1)) z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => B))-
          (z*(v-b)+(1-z)*independentTwo eta v b q)| < eps ∧
      |(∫ x : ActivePatternIndex kind → ℝ,
        sourceSingletonPayoff xi v (Function.update x (activePatternFocal kind) b)
          (activePatternResidual (capacityFamily (N+1)) z kind)
          (activePatternOwner (capacityFamily (N+1)) z kind 0)
          (activePatternOwner (capacityFamily (N+1)) z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => B))-
          ((z/2+(1-z)*q)*(v-b))| < eps := by
  obtain ⟨delta, hdelta, hmenus⟩ := exists_eventual_uniform_typical_menus
    a h rho z xi eta L U W ha hz0 hz1 hxi hxi1 hL hLU hW hlower hupper
    hq0 hq1 hboxlo hboxhi capacityFamily hc eps heps
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hmenus] with N hN
  intro B _ hB kind hg hgood b hb v hv
  let C := categoryLaw s a h hs ha.le hh hsum B
  have hclose (k : Fin 4) :
      |(fullCategoryCount activeFocalPrefix kind k : ℝ)-(N+1:ℕ)*C.mass k| <
        (N+1:ℕ)*delta := by
    have h := lt_of_not_ge (fun hk => hgood ⟨k, hk⟩)
    simpa only [fullCategoryCount, Nat.cast_add] using h
  have hA : |(Fintype.card (ActivePatternIndex kind):ℝ)-(N+1:ℕ)*a| ≤
      (N+1:ℕ)*delta := by
    have ht := (hclose 1).le
    simpa [C, categoryLaw_mass, activePattern_count_active] using ht
  have hH₀ : |(activePatternUpper kind 0:ℝ)-(N+1:ℕ)*(h/2)| ≤ (N+1:ℕ)*delta := by
    have ht := (hclose 2).le
    rw [show fullCategoryCount activeFocalPrefix kind 2 = activePatternUpper kind 0 from activePattern_count_upper kind 0] at ht
    simpa [C, categoryLaw_mass] using ht
  have hH₁ : |(activePatternUpper kind 1:ℝ)-(N+1:ℕ)*(h/2)| ≤ (N+1:ℕ)*delta := by
    have ht := (hclose 3).le
    rw [show fullCategoryCount activeFocalPrefix kind 3 = activePatternUpper kind 1 from activePattern_count_upper kind 1] at ht
    simpa [C, categoryLaw_mass] using ht
  have hcap (j : Fin 2) : activeResidual (capacityFamily (N+1))
      (Fintype.card (ActivePatternIndex kind)) (activePatternUpper kind j) =
        activePatternCapacity (capacityFamily (N+1)) kind j := rfl
  have hm := hN (Fintype.card (ActivePatternIndex kind))
    (activePatternUpper kind 0) (activePatternUpper kind 1) hA hH₀ hH₁
  dsimp only at hm
  rw [hcap 0, hcap 1] at hm
  have hh' := hm hg.2.1 (ActivePatternIndex kind) rfl (activePatternFocal kind) B hB b hb v hv
  simp_rw [sourceOwnerPayoff_roles z (capacityFamily (N+1)) kind hg,
    sourceSingletonPayoff_roles z (capacityFamily (N+1)) kind hg]
  exact hh'

def fullMenuCountError (h delta deltaGuard deltaEq : ℝ) (N : ℕ) : ℝ :=
  8*Real.exp (-(N:ℝ)*delta^2/2)+activeGuardExceptionError h deltaGuard deltaEq N

lemma fullMenuCountError_tendsto_zero {h delta deltaGuard deltaEq : ℝ}
    (hh : 0 < h) (hd : 0 < delta) (hg : 0 < deltaGuard) (he : 0 < deltaEq) :
    Tendsto (fullMenuCountError h delta deltaGuard deltaEq) atTop (nhds 0) := by
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hn.const_mul_atTop (by positivity : 0 < delta^2/2))
  have hc : Tendsto (fun N : ℕ => 8*Real.exp (-(N:ℝ)*delta^2/2)) atTop (nhds 0) := by
    convert! hx.const_mul 8 using 1
    · funext N
      congr 2
      ring
    · ring
  convert! hc.add (activeGuardExceptionError_tendsto_zero hh hg he) using 1
  simp only [add_zero]

theorem exists_eventual_full_menu_count_bound (s a h rho z xi L U : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hxi : 0 < xi) (hxi1 : xi < 1)
    (hL : 0 < L) (hLU : L ≤ U) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ deltaGuard deltaEq : ℝ, 0 < deltaGuard ∧ 0 < deltaEq ∧
      ∀ᶠ N : ℕ in atTop, ∀ (B : Measure ℝ) [IsProbabilityMeasure B],
      let C := categoryLaw s a h hs.le ha.le hh.le hsum B
      (CommonList.iid C N).prob (fun kind =>
        ¬(activePatternGuarded xi L U (capacityFamily (N+1)) z kind ∧
          ¬activePatternCountException C delta kind)) ≤
        fullMenuCountError h delta deltaGuard deltaEq N := by
  obtain ⟨dg, de, hdg, _hdgs, hde, hguard⟩ := exists_eventual_activePattern_guard_bound
    s a h rho z xi L U hs ha hh hsum hz0 hz1 hxi hxi1 hL hLU hlower hupper
    hq0 hq1 hboxlo hboxhi capacityFamily hc
  have hn : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hprefix : ∀ᶠ N : ℕ in atTop, (1:ℝ) ≤ (N:ℝ)*delta/2 := by
    have ht : Tendsto (fun N : ℕ => (N:ℝ)*delta/2) atTop atTop := by
      convert! hn.const_mul_atTop (half_pos hdelta) using 1
      funext N
      ring
    exact ht.eventually_ge_atTop 1
  refine ⟨dg, de, hdg, hde, ?_⟩
  filter_upwards [hguard, hprefix] with N hNg hNp
  intro B _
  let C := categoryLaw s a h hs.le ha.le hh.le hsum B
  let P := CommonList.iid C N
  have hg := (hNg B inferInstance).2
  have hd := forced_fractional_count_exception_le C activeFocalPrefix N hdelta.le
    (by simpa only [Nat.cast_one] using hNp)
  have he : (fun kind : Fin N → Fin 4 =>
      ¬(activePatternGuarded xi L U (capacityFamily (N+1)) z kind ∧
        ¬activePatternCountException C delta kind)) =
      fun kind => activePatternCountException C delta kind ∨
        ¬activePatternGuarded xi L U (capacityFamily (N+1)) z kind := by
    funext kind
    exact propext (by tauto)
  change P.prob (fun kind => ¬(activePatternGuarded xi L U (capacityFamily (N+1)) z kind ∧
    ¬activePatternCountException C delta kind)) ≤ _
  rw [he]
  exact (P.prob_union_le _ _).trans (add_le_add hd hg)

theorem integral_physicalRows_eq_patternMenus (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (C : ContextPolicy (N+1) c unitInterval) (i : Fin (N+1)) (b : ℝ)
    (f : Fin 3 → ℝ) (K : ℝ) (hK : ∀ k, |f k| ≤ K) :
    (∫ r : Fin N → RowRival,
      (privateContextLaw C (reindexedPhysicalContext i b r) i).expect f
      ∂Measure.pi (fun _ : Fin N => physicalRivalLaw s a h μ B)) =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum μ) N).expect (fun kind =>
        ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
          (privateContextLaw C (NativeContinuation.reindexContext
            (NativeContinuation.focalIndex i).symm (sourceRowContext kind low active b)) i).expect f
          ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B)) := by
  let F := fun r : Fin N → RowRival =>
    (privateContextLaw C (reindexedPhysicalContext i b r) i).expect f
  have hF : Measurable F := (measurable_privateContextLaw_expect C i f).comp
    (measurable_reindexedPhysicalContext i b)
  have hbound (r : Fin N → RowRival) : |F r| ≤ K :=
    abs_finite_expect_le_of_support _ _ K (fun k _ => hK k)
  rw [integral_physicalRowProfile s a h hs ha hh hsum μ B N F hF K
    (ae_of_all _ (fun p => hbound _))]
  apply FiniteLaw.expect_congr
  intro kind
  let E := fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
    F (fun j => physicalRowPoint (kind j, p.1 j, p.2 j))
  have hE : Measurable E := hF.comp (measurable_pi_lambda _ (fun j =>
    measurable_physicalRowPoint.comp (measurable_const.prodMk
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)))))
  have hi : Integrable E ((Measure.pi (fun _ : Fin N => μ)).prod
      (Measure.pi (fun _ : Fin N => B))) := Integrable.of_bound hE.aestronglyMeasurable K
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hbound _))
  rw [integral_prod_symm E hi]
  rfl

lemma affine_userPayoff_eq_realized (eta : ℝ) (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (v b : ℝ) (k : Fin 3) (G : ℕ → ℝ) :
    userPayoff v b 0 (Schedule.affine 2 eta heta0 heta1).charge G k.val =
      realizedPayoff eta v b k.val := by
  fin_cases k <;> simp [userPayoff, successIndicator, Schedule.affine, realizedPayoff]

theorem closed_broadcast_payoff_fullRows
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {eta d U R : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hg : Γ.g = 0) (hA : Γ.A = Schedule.affine 2 eta heta0 heta1)
    (hdU : d ≤ U) (hUR : U < R) (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U) = physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid ≤ U)
    (hk : act.routeCount = 2) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum B) N).expect
        (patternBroadcastMenu C (NativeContinuation.focalIndex i).symm μ B eta v act.bid) := by
  have heta : |eta| ≤ 1 := by rw [abs_of_nonneg heta0]; exact heta1
  change ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).expect
    (fun k => userPayoff v act.bid Γ.g Γ.A.charge Γ.G.charge k.val) = _
  simp_rw [hg, hA, affine_userPayoff_eq_realized]
  rw [closed_broadcast_count_physicalRows C Γ hdU hUR hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i act hb hk]
  rw [integral_physicalRows_eq_patternMenus s a h hs ha hh hsum μ B C i act.bid
    (fun k => realizedPayoff eta v act.bid k.val) (|v|+2*|act.bid|)
      (abs_realizedPayoff_two heta v act.bid)]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum μ B]
  apply FiniteLaw.expect_congr
  intro kind
  simp only [patternBroadcastMenu, Equiv.symm_symm, NativeContinuation.focalIndex_zero]

theorem closed_singleton_payoff_fullRows
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hg : Γ.g = 0) (hdU : d ≤ U) (hUR : U < R)
    (hseed : Γ.seedLaw = volume)
    (hfull : ∀ᵐ z ∂userProfileLaw Γ, z ∈ closedProfiles (N+1) R)
    (hgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U) = physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (v : ℝ) (act : JointAction 2) (hb : act.bid ≤ U)
    (hk : act.routeCount = 1) :
    (problem (ClosedPolicy.nativeGame C Γ R) i).payoff v act =
      (CommonList.iid (categoryLaw s a h hs ha hh hsum B) N).expect
        (patternSingletonMenu C (NativeContinuation.focalIndex i).symm μ B v act.bid) := by
  rw [closed_singleton_payoff_physicalRows C Γ hdU hUR hg hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i v act hb hk]
  rw [integral_physicalRows_eq_patternMenus s a h hs ha hh hsum μ B C i act.bid
    (fun k => ((v-act.bid)/2)*(k.val:ℝ)) (|v|+|act.bid|)
      (abs_singletonCountPayoff_two v act.bid)]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum μ B]
  apply FiniteLaw.expect_congr
  intro kind
  simp only [patternSingletonMenu, Equiv.symm_symm, NativeContinuation.focalIndex_zero]

theorem patternBroadcastMenu_guarded {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀ b, μ {b}=0) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d)
    (hB : ∀ᵐ b ∂B, b ∈ Icc L U)
    (kind : Fin N → Fin 4) (eta v b : ℝ) (hb : b ∈ Icc L U)
    (hguard : activePatternGuarded xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    patternBroadcastMenu (contextPolicy hxi hxi1 d L U z c μ) e μ B eta v b kind =
      ∫ x : ActivePatternIndex kind → ℝ,
        sourceOwnerPayoff xi eta v (Function.update x (activePatternFocal kind) b)
          (activePatternResidual c z kind) (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => B) := by
  have hvec : ∀ᵐ active : Fin N → ℝ ∂Measure.pi (fun _ : Fin N => B),
      ∀ j, active j ∈ Icc L U :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => B) j).quasiMeasurePreserving.ae hB)
  unfold patternBroadcastMenu
  calc
    _ = ∫ active : Fin N → ℝ,
        sourceOwnerPayoff xi eta v
          (activePhysicalActiveBids kind (v, b, (fun _ => 0), active))
          (activePatternResidual c z kind) (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : Fin N => B) := by
      apply integral_congr_ae
      filter_upwards [hvec] with active ha
      exact sourceRow_private_payoff_guarded hxi hxi1 z c μ hnoatoms hd hL hgap hμ
        kind active eta v b ha hb hguard e
    _ = _ := integral_physicalActiveBids B kind v b _
      (measurable_sourceOwnerPayoff xi eta v _ _ _ _)

theorem patternSingletonMenu_guarded {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀ b, μ {b}=0) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d)
    (hB : ∀ᵐ b ∂B, b ∈ Icc L U)
    (kind : Fin N → Fin 4) (v b : ℝ) (hb : b ∈ Icc L U)
    (hguard : activePatternGuarded xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    patternSingletonMenu (contextPolicy hxi hxi1 d L U z c μ) e μ B v b kind =
      ∫ x : ActivePatternIndex kind → ℝ,
        sourceSingletonPayoff xi v (Function.update x (activePatternFocal kind) b)
          (activePatternResidual c z kind) (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : ActivePatternIndex kind => B) := by
  have hvec : ∀ᵐ active : Fin N → ℝ ∂Measure.pi (fun _ : Fin N => B),
      ∀ j, active j ∈ Icc L U :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => B) j).quasiMeasurePreserving.ae hB)
  unfold patternSingletonMenu
  calc
    _ = ∫ active : Fin N → ℝ,
        sourceSingletonPayoff xi v
          (activePhysicalActiveBids kind (v, b, (fun _ => 0), active))
          (activePatternResidual c z kind) (activePatternOwner c z kind 0)
          (activePatternOwner c z kind 1) (activePatternFocal kind)
        ∂Measure.pi (fun _ : Fin N => B) := by
      apply integral_congr_ae
      filter_upwards [hvec] with active ha
      exact sourceRow_private_singleton_guarded hxi hxi1 z c μ hnoatoms hd hL hgap hμ
        kind active v b ha hb hguard e
    _ = _ := integral_physicalActiveBids B kind v b _
      (measurable_sourceSingletonPayoff xi v _ _ _ _)

theorem eventually_native_fullrow_menus (s a h rho z xi eta d L U W : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hxi : 0 < xi) (hxi1 : xi < 1)
    (heta : |eta| ≤ 1) (hd : 0 ≤ d) (hL : 0 < L) (hLU : L ≤ U) (hW : 0 ≤ W)
    (hgap : d < (1-xi)*L) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b, μ {b}=0) → (∀ᵐ b ∂μ, b ∈ Icc 0 d) → (∀ᵐ b ∂B, b ∈ Icc L U) →
      ∀ (e : Equiv.Perm (Fin (N+1))) (b : ℝ), b ∈ Icc L U →
      ∀ v : ℝ, |v| ≤ W →
      let C := contextPolicy (m := N+1) hxi hxi1 d L U z (capacityFamily (N+1)) μ
      let P := CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) b
      |P.expect (patternBroadcastMenu C e μ B eta v b)-
        (z*(v-b)+(1-z)*independentTwo eta v b q)| < eps ∧
      |P.expect (patternSingletonMenu C e μ B v b)-
        ((z/2+(1-z)*q)*(v-b))| < eps := by
  obtain ⟨delta, hdelta, hmenus⟩ := exists_eventual_pattern_menu_bounds
    s a h rho z xi eta L U W hs.le ha hh.le hsum hz0 hz1 hxi hxi1 hL hLU hW
    hlower hupper hq0 hq1 hboxlo hboxhi capacityFamily hc (eps/2) (half_pos heps)
  obtain ⟨dg, de, hdg, hde, hcount⟩ := exists_eventual_full_menu_count_bound
    s a h rho z xi L U hs ha hh hsum hz0 hz1 hxi hxi1 hL hLU hlower hupper
    hq0 hq1 hboxlo hboxhi capacityFamily hc delta hdelta
  let K := W+2*U
  have hU : 0 < U := hL.trans_le hLU
  have hK : 0 < K := by dsimp [K]; positivity
  have ht : Tendsto (fun N => 2*K*fullMenuCountError h delta dg de N) atTop (nhds 0) := by
    simpa only [mul_zero] using (fullMenuCountError_tendsto_zero hh hdelta hdg hde).const_mul (2*K)
  have hsmall : ∀ᶠ N : ℕ in atTop, 2*K*fullMenuCountError h delta dg de N < eps/2 :=
    ht.eventually (Iio_mem_nhds (half_pos heps))
  filter_upwards [hmenus, hcount, hsmall] with N hNm hNc hNs
  intro μ B _ _ hnoatoms hμ hB e b hb v hv
  dsimp only
  let C := contextPolicy (m := N+1) hxi hxi1 d L U z (capacityFamily (N+1)) μ
  let Cat := categoryLaw s a h hs.le ha.le hh.le hsum B
  let P := CommonList.iid Cat N
  let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) b
  let good := fun kind : Fin N → Fin 4 =>
    activePatternGuarded xi L U (capacityFamily (N+1)) z kind ∧
      ¬activePatternCountException Cat delta kind
  have hprob : P.prob (fun kind => ¬good kind) ≤ fullMenuCountError h delta dg de N := hNc B
  have hq : q ∈ Icc (0:ℝ) 1 := exposure_mem_of_mean_factor B hxi hxi1 hL hB hb
    (by have ht := mul_lt_mul_of_pos_left hq1 hxi; linarith) hboxlo hboxhi
  have hbid : |b| ≤ U := by rw [abs_of_pos (hL.trans_le hb.1)]; exact hb.2
  have hBrow (kind : Fin N → Fin 4) : |patternBroadcastMenu C e μ B eta v b kind| ≤ K :=
    (abs_patternBroadcastMenu C e μ B heta v b kind).trans (by dsimp [K]; linarith)
  have hSrow (kind : Fin N → Fin 4) : |patternSingletonMenu C e μ B v b kind| ≤ K :=
    (abs_patternSingletonMenu C e μ B v b kind).trans (by dsimp [K]; linarith)
  have hBt : |z*(v-b)+(1-z)*independentTwo eta v b q| ≤ K :=
    (abs_limiting_broadcast_menu heta ⟨hz0, hz1.le⟩ hq v b).trans (by dsimp [K]; linarith)
  have hSt : |(z/2+(1-z)*q)*(v-b)| ≤ K :=
    (abs_limiting_singleton_menu ⟨hz0, hz1.le⟩ hq v b).trans (by dsimp [K]; linarith)
  have hgoodB (kind : Fin N → Fin 4) (hk : good kind) :
      |patternBroadcastMenu C e μ B eta v b kind-
        (z*(v-b)+(1-z)*independentTwo eta v b q)| ≤ eps/2 := by
    rw [patternBroadcastMenu_guarded hxi hxi1 z (capacityFamily (N+1)) μ B
      hnoatoms hd hL hgap hμ hB kind eta v b hb hk.1 e]
    exact (hNm B hB kind hk.1 hk.2 b hb v hv).1.le
  have hgoodS (kind : Fin N → Fin 4) (hk : good kind) :
      |patternSingletonMenu C e μ B v b kind-((z/2+(1-z)*q)*(v-b))| ≤ eps/2 := by
    rw [patternSingletonMenu_guarded hxi hxi1 z (capacityFamily (N+1)) μ B
      hnoatoms hd hL hgap hμ hB kind v b hb hk.1 e]
    exact (hNm B hB kind hk.1 hk.2 b hb v hv).2.le
  have htail : eps/2+2*K*P.prob (fun kind => ¬good kind) < eps := by
    have hm := mul_le_mul_of_nonneg_left hprob (by positivity : 0 ≤ 2*K)
    linarith
  exact ⟨(finite_menu_error P good _ _ K (eps/2) (half_pos heps).le hBrow hBt hgoodB).trans_lt htail,
    (finite_menu_error P good _ _ K (eps/2) (half_pos heps).le hSrow hSt hgoodS).trans_lt htail⟩

theorem eventually_original_game_boxed_menus (s a h rho z xi eta d L U R W : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hxi : 0 < xi) (hxi1 : xi < 1)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hd : 0 ≤ d) (hL : 0 < L) (hLU : L ≤ U) (hUR : U < R) (hW : 0 ≤ W)
    (hgap : d < (1-xi)*L) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b, μ {b}=0) → (∀ᵐ b ∂μ, b ∈ Icc 0 d) → (∀ᵐ b ∂B, b ∈ Icc L U) →
      ∀ Γ : FiniteGame (N+1) 2 (capacityFamily (N+1)) unitInterval,
      Γ.g=0 → Γ.A=Schedule.affine 2 eta heta0 heta1 → Γ.seedLaw=volume →
      (∀ᵐ x ∂userProfileLaw Γ, x ∈ closedProfiles (N+1) R) →
      (∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid) →
      (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B →
      ∀ (i : Fin (N+1)) (act : JointAction 2), act.bid ∈ Icc L U →
      ∀ v : ℝ, |v| ≤ W →
      let G := ClosedPolicy.nativeGame
        (contextPolicy hxi hxi1 d L U z (capacityFamily (N+1)) μ) Γ R
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) act.bid
      (act.routeCount=2 → |(problem G i).payoff v act-
        (z*(v-act.bid)+(1-z)*independentTwo eta v act.bid q)| < eps) ∧
      (act.routeCount=1 → |(problem G i).payoff v act-
        ((z/2+(1-z)*q)*(v-act.bid))| < eps) := by
  have heta : |eta| ≤ 1 := by rw [abs_of_nonneg heta0]; exact heta1
  have hm := eventually_native_fullrow_menus s a h rho z xi eta d L U W
    hs ha hh hsum hz0 hz1 hxi hxi1 heta hd hL hLU hW hgap hlower hupper
    hq0 hq1 hboxlo hboxhi capacityFamily hc eps heps
  have hdU : d ≤ U := (hgap.trans (by nlinarith [mul_pos hxi hL])).le.trans hLU
  filter_upwards [hm] with N hN
  intro μ B _ _ hatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb v hv
  let C := contextPolicy (m := N+1) hxi hxi1 d L U z (capacityFamily (N+1)) μ
  have ht := hN μ B hatoms hμ hB (NativeContinuation.focalIndex i).symm act.bid hb v hv
  constructor
  · intro hk
    rw [closed_broadcast_payoff_fullRows C Γ heta0 heta1 hg hA hdU hUR hseed hfull hpopgap
      s a h hs.le ha.le hh.le hsum μ B hrow i v act hb.2 hk]
    exact ht.1
  · intro hk
    rw [closed_singleton_payoff_fullRows C Γ hg hdU hUR hseed hfull hpopgap
      s a h hs.le ha.le hh.le hsum μ B hrow i v act hb.2 hk]
    exact ht.2

theorem eventually_original_game_boxed_count_masses (s a h rho z xi eta d L U R : ℝ)
    (hs : 0 < s) (ha : 0 < a) (hh : 0 < h) (hsum : s+a+h=1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) (hxi : 0 < xi) (hxi1 : xi < 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hd : 0 ≤ d) (hL : 0 < L) (hLU : L ≤ U) (hUR : U < R)
    (hgap : d < (1-xi)*L) (hlower : h/2 < rho) (hupper : rho < a+h/2)
    (hq0 : 0 < sourceExposure a h rho z) (hq1 : sourceExposure a h rho z < 1)
    (hboxlo : (1-xi)*U < (1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U < L)
    (capacityFamily : ℕ → ℕ)
    (hc : Tendsto (fun M => (capacityFamily M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀ b, μ {b}=0) → (∀ᵐ b ∂μ, b ∈ Icc 0 d) → (∀ᵐ b ∂B, b ∈ Icc L U) →
      ∀ Γ : FiniteGame (N+1) 2 (capacityFamily (N+1)) unitInterval,
      Γ.g=0 → Γ.A=Schedule.affine 2 eta heta.le heta1 → Γ.seedLaw=volume →
      (∀ᵐ x ∂userProfileLaw Γ, x ∈ closedProfiles (N+1) R) →
      (∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid) →
      (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B →
      ∀ (i : Fin (N+1)) (act : JointAction 2), act.bid ∈ Icc L U → act.routeCount=2 →
      let G := ClosedPolicy.nativeGame
        (contextPolicy hxi hxi1 d L U z (capacityFamily (N+1)) μ) Γ R
      let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) act.bid
      ∃ (hq0' : 0 ≤ q) (hq1' : q ≤ 1), ∀ r : Fin 3,
        |((problem G i).outcome act).mass r-
          (activeLimitLaw z q hz0 hz1.le hq0' hq1').mass r| < eps := by
  let K := countTestErrorConstant eta L
  have hK : 0 < K := by dsimp [K, countTestErrorConstant]; positivity
  let tau := eps/(K+1)
  have htau : 0 < tau := div_pos heps (by positivity)
  have hm := eventually_original_game_boxed_menus s a h rho z xi eta d L U R 1
    hs ha hh hsum hz0 hz1 hxi hxi1 heta.le heta1 hd hL hLU hUR (by norm_num)
    hgap hlower hupper hq0 hq1 hboxlo hboxhi capacityFamily hc tau htau
  filter_upwards [hm] with N hN
  intro μ B _ _ hatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb hk
  dsimp only
  let G := ClosedPolicy.nativeGame
    (contextPolicy hxi hxi1 d L U z (capacityFamily (N+1)) μ) Γ R
  let q := exposure xi ((1-xi*sourceExposure a h rho z)/reciprocalMean B) act.bid
  have hq : q ∈ Icc (0:ℝ) 1 := exposure_mem_of_mean_factor B hxi hxi1 hL hB hb
    (by have ht := mul_lt_mul_of_pos_left hq1 hxi; linarith) hboxlo hboxhi
  let Q := activeLimitLaw z q hz0 hz1.le hq.1 hq.2
  have hzero := (hN μ B hatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb
    0 (by norm_num)).1 hk
  have hone := (hN μ B hatoms hμ hB Γ hg hA hseed hfull hpopgap hrow i act hb
    1 (by norm_num)).1 hk
  have hu (v : ℝ) : Q.utility v act.bid 0
      (Schedule.affine 2 eta heta.le heta1) (Schedule.once 2) =
      z*(v-act.bid)+(1-z)*independentTwo eta v act.bid q :=
    activeLimitLaw_utility z q eta v act.bid hz0 hz1.le hq.1 hq.2 heta.le heta1
  have ht := native_count_mass_error_of_two_payoff_tests G i eta L tau
    heta heta1 hL htau.le hA hg act hb.1 Q
    (by simpa only [hu] using hzero.le) (by simpa only [hu] using hone.le)
  refine ⟨hq.1, hq.2, fun r => (ht r).trans_lt ?_⟩
  change K*tau < eps
  have he : (K+1)*tau = eps := by dsimp [tau]; field_simp
  nlinarith

end FullContext
end FCAppendix.Affine.Hybrid.Native02
