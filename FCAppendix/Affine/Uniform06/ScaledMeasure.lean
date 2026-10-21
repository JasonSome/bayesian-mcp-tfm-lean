import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic

noncomputable section

namespace FCAppendix.Affine.Uniform06.ScaledMeasure

open Set MeasureTheory Filter
open scoped Topology BigOperators

def scaledSet (κ : ℝ) (A : Set ℝ) : Set ℝ := (fun x => κ*x) '' A

def scaledRankMeasure (κ : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  Measure.map (fun b => b/κ) μ

theorem scaledSet_eq_preimage_div {κ : ℝ} (hκ : κ ≠ 0) (A : Set ℝ) :
    scaledSet κ A = (fun x => x/κ) ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa [mul_div_cancel_left₀ _ hκ] using hx
  · intro hy
    refine ⟨y/κ,hy,?_⟩
    field_simp [hκ]

theorem measurableSet_scaled {κ : ℝ} (hκ : κ ≠ 0) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (scaledSet κ A) := by
  rw [scaledSet_eq_preimage_div hκ]
  exact hA.preimage (by fun_prop)

theorem scaledRankMeasure_apply {κ : ℝ} (hκ : κ ≠ 0)
    (μ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    scaledRankMeasure κ μ A = μ (scaledSet κ A) := by
  unfold scaledRankMeasure
  rw [Measure.map_apply (by fun_prop) hA,scaledSet_eq_preimage_div hκ]

theorem scaledRankMeasure_real_apply {κ : ℝ} (hκ : κ ≠ 0)
    (μ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (scaledRankMeasure κ μ).real A = μ.real (scaledSet κ A) := by
  unfold Measure.real
  rw [scaledRankMeasure_apply hκ μ hA]

theorem scaledSet_one (A : Set ℝ) : scaledSet 1 A = A := by
  ext x
  simp [scaledSet]

theorem scaledSet_mul (κ scale : ℝ) (A : Set ℝ) :
    scaledSet κ (scaledSet scale A) = scaledSet (κ*scale) A := by
  ext y
  constructor
  · rintro ⟨x,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z,hz,by ring⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨scale*z,⟨z,hz,rfl⟩,by ring⟩

theorem volume_map_div {κ : ℝ} (hκ : 0 < κ) :
    Measure.map (fun x : ℝ => x/κ) volume = ENNReal.ofReal κ • volume := by
  have h := Real.map_volume_mul_left (inv_ne_zero hκ.ne')
  simpa only [inv_inv,abs_of_pos hκ,div_eq_mul_inv,mul_comm] using h

theorem volume_scaled {κ : ℝ} (hκ : 0 < κ) {A : Set ℝ}
    (hA : MeasurableSet A) :
    volume (scaledSet κ A) = ENNReal.ofReal κ * volume A := by
  rw [scaledSet_eq_preimage_div hκ.ne',
    ← Measure.map_apply (by fun_prop) hA,volume_map_div hκ]
  simp [Measure.smul_apply,smul_eq_mul]

theorem integral_scaledSet {κ : ℝ} (hκ : 0 < κ)
    {A : Set ℝ} (hA : MeasurableSet A) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ x in scaledSet κ A, f x) = κ*(∫ x in A, f (κ*x)) := by
  let g : ℝ → ℝ := A.indicator (fun x => f (κ*x))
  have hg : Measurable g := by
    exact (hf.comp (by fun_prop)).indicator hA
  have hi := integral_map_of_stronglyMeasurable
    (μ := (volume : Measure ℝ)) (φ := fun x : ℝ => x/κ)
    (by fun_prop) hg.stronglyMeasurable
  have hcomp : (fun x : ℝ => g (x/κ)) = (scaledSet κ A).indicator f := by
    funext x
    have hx : x/κ ∈ A ↔ x ∈ scaledSet κ A := by
      rw [scaledSet_eq_preimage_div hκ.ne']
      rfl
    by_cases ha : x/κ ∈ A
    · have hs : x ∈ scaledSet κ A := hx.mp ha
      simp only [g,Set.indicator_of_mem ha,Set.indicator_of_mem hs]
      congr 1
      field_simp [hκ.ne']
    · have hs : x ∉ scaledSet κ A := fun h => ha (hx.mpr h)
      simp only [g,Set.indicator_of_notMem ha,Set.indicator_of_notMem hs]
  rw [volume_map_div hκ,integral_smul_measure,ENNReal.toReal_ofReal hκ.le,
    smul_eq_mul,hcomp,integral_indicator (measurableSet_scaled hκ.ne' hA)] at hi
  simpa only [g,integral_indicator hA] using hi.symm

def rentWeight (m b : ℝ) : ℝ := 1+1/(m*b)

theorem scaled_rentWeight_algebra {κ : ℝ} (hκ : κ ≠ 0) (m b : ℝ) :
    κ*rentWeight m (κ*b) = κ+1/(m*b) := by
  unfold rentWeight
  by_cases hm : m = 0
  · simp [hm]
  by_cases hb : b = 0
  · simp [hb]
  field_simp [hκ,hm,hb]

theorem scaled_rentWeight_integral {κ : ℝ} (hκ : 0 < κ)
    (m : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x in scaledSet κ A, rentWeight m x) =
      ∫ x in A, κ+1/(m*x) := by
  rw [integral_scaledSet hκ hA (show Measurable (rentWeight m) by
    unfold rentWeight
    fun_prop)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (scaled_rentWeight_algebra hκ.ne' m)

theorem scaled_power_rentWeight_integral {κ : ℝ} (hκ : 0 < κ)
    (m : ℝ) (j : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x in scaledSet (κ^j) A, rentWeight m x) =
      ∫ x in A, κ^j+1/(m*x) :=
  scaled_rentWeight_integral (pow_pos hκ j) m hA

theorem scaled_positive_interval {κ B : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {A : Set ℝ} (hA : A ⊆ Ioc 0 B) : scaledSet κ A ⊆ Ioc 0 B := by
  rintro y ⟨x,hx,rfl⟩
  have h := hA hx
  refine ⟨mul_pos hκ0 h.1,?_⟩
  calc
    κ*x ≤ 1*x := mul_le_mul_of_nonneg_right hκ1 h.1.le
    _ ≤ B := by simpa using h.2

theorem bounded_forward_contraction_nonpos (u : ℕ → ℝ) {ε K : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hb : ∀ n, u n ≤ K)
    (hc : ∀ n, u n ≤ ε*u (n+1)) : ∀ n, u n ≤ 0 := by
  let R : Set ℝ := Set.range u
  have hne : R.Nonempty := ⟨u 0,⟨0,rfl⟩⟩
  have hbd : BddAbove R := ⟨K,by rintro z ⟨n,rfl⟩; exact hb n⟩
  let M : ℝ := sSup R
  have hle (n : ℕ) : u n ≤ M := le_csSup hbd ⟨n,rfl⟩
  have hM : M ≤ ε*M := by
    apply csSup_le hne
    rintro z ⟨n,rfl⟩
    exact (hc n).trans (mul_le_mul_of_nonneg_left (hle (n+1)) hε0)
  have hM0 : M ≤ 0 := by
    by_contra h
    have hp := mul_pos (sub_pos.mpr hε1) (lt_of_not_ge h)
    nlinarith
  exact fun n => (hle n).trans hM0

theorem scaled_recurrence_bound (u : ℕ → ℝ) {ε κ C a b K : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hub : ∀ n, u n ≤ K)
    (hc : ∀ n, u n ≤ C*(κ^n*a+b)+ε*u (n+1)) :
    u 0 ≤ C*(a/(1-ε*κ)+b/(1-ε)) := by
  have hεk : ε*κ < 1 :=
    (mul_le_mul_of_nonneg_left hκ1 hε0).trans_lt (by simpa using hε1)
  have hden₁ : 0 < 1-ε*κ := sub_pos.mpr hεk
  have hden₂ : 0 < 1-ε := sub_pos.mpr hε1
  let v : ℕ → ℝ := fun n => C*(κ^n*a/(1-ε*κ)+b/(1-ε))
  have hv0 (n : ℕ) : 0 ≤ v n := by dsimp [v]; positivity
  have hvrec (n : ℕ) : v n = C*(κ^n*a+b)+ε*v (n+1) := by
    dsimp [v]
    rw [pow_succ]
    field_simp [hden₁.ne',hden₂.ne']
    ring
  have hbound (n : ℕ) : u n-v n ≤ K := by linarith [hub n,hv0 n]
  have hcontract (n : ℕ) : u n-v n ≤ ε*(u (n+1)-v (n+1)) := by
    rw [hvrec]
    linarith [hc n]
  have hz := bounded_forward_contraction_nonpos (fun n => u n-v n)
    hε0 hε1 hbound hcontract 0
  simpa [v] using (show u 0 ≤ v 0 by linarith)

theorem scaled_mass_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (κ : ℝ) (A : Set ℝ) (j : ℕ) :
    μ.real (scaledSet (κ^j) A) ≤ μ.real univ :=
  measureReal_mono (subset_univ _)

theorem local_ac_of_scaled_null_contraction
    (μ : Measure ℝ) [IsFiniteMeasure μ] {κ ε B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hc : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioc 0 B → volume A = 0 →
      μ.real A ≤ ε*μ.real (scaledSet κ A)) :
    μ.restrict (Ioc 0 B) ≪ volume := by
  let T : Set ℝ → Set ℝ := scaledSet κ
  have hz : ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioc 0 B →
      volume A = 0 → μ A = 0 := by
    intro A hA hAB hAv
    let An : ℕ → Set ℝ := fun n => (T^[n]) A
    have hAn (n : ℕ) : MeasurableSet (An n) ∧
        An n ⊆ Ioc 0 B ∧ volume (An n) = 0 := by
      induction n with
      | zero => simpa [An] using And.intro hA (And.intro hAB hAv)
      | succ n ih =>
        have he : An (n+1) = scaledSet κ (An n) := by
          simp [An,Function.iterate_succ_apply',T]
        rw [he]
        refine ⟨measurableSet_scaled hκ0.ne' ih.1,
          scaled_positive_interval hκ0 hκ1 ih.2.1,?_⟩
        rw [volume_scaled hκ0 ih.1,ih.2.2,mul_zero]
    have hu (n : ℕ) : μ.real (An n) ≤ μ.real univ :=
      measureReal_mono (subset_univ _)
    have hr (n : ℕ) : μ.real (An n) ≤ ε*μ.real (An (n+1)) := by
      have he : An (n+1) = scaledSet κ (An n) := by
        simp [An,Function.iterate_succ_apply',T]
      rw [he]
      exact hc (An n) (hAn n).1 (hAn n).2.1 (hAn n).2.2
    have hm := bounded_forward_contraction_nonpos (fun n => μ.real (An n))
      hε0 hε1 hu hr 0
    have hreal : μ.real A = 0 := by
      simpa [An] using le_antisymm hm (show 0 ≤ μ.real (An 0) from measureReal_nonneg)
    exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp hreal
  intro A hA
  obtain ⟨C,hAC,hCm,hCv⟩ := exists_measurable_superset_of_null hA
  have hCi : MeasurableSet (C ∩ Ioc 0 B) := hCm.inter measurableSet_Ioc
  have hCi0 : volume (C ∩ Ioc 0 B) = 0 := measure_mono_null inter_subset_left hCv
  have hμCi := hz (C ∩ Ioc 0 B) hCi inter_subset_right hCi0
  apply le_antisymm _ bot_le
  calc
    (μ.restrict (Ioc 0 B)) A ≤ (μ.restrict (Ioc 0 B)) C := measure_mono hAC
    _ = μ (C ∩ Ioc 0 B) := Measure.restrict_apply hCm
    _ = 0 := hμCi

theorem density_supersolution_identity {ε κ C m b : ℝ}
    (h₁ : 1-ε*κ ≠ 0) (h₂ : 1-ε ≠ 0) (hm : m ≠ 0) (hb : b ≠ 0)
    (hκ : κ ≠ 0) :
    C*(1/(1-ε*κ)+1/((1-ε)*m*b)) =
      C*(1+1/(m*b))+ε*κ*C*(1/(1-ε*κ)+1/((1-ε)*m*(κ*b))) := by
  field_simp [h₁,h₂,hm,hb,hκ]
  ring

theorem reciprocal_integrableOn {m a B : ℝ} (hm : 0 < m) (ha : 0 < a)
    {A : Set ℝ} (hA : A ⊆ Icc a B) :
    IntegrableOn (fun x : ℝ => 1/(m*x)) A := by
  have hf : ContinuousOn (fun x : ℝ => 1/(m*x)) (Icc a B) := by
    exact continuousOn_const.div (continuous_const.mul continuous_id).continuousOn
      (fun x hx => mul_ne_zero hm.ne' (ha.trans_le hx.1).ne')
  exact hf.integrableOn_Icc.mono_set hA

theorem integrated_density_bound
    (μ : Measure ℝ) [IsFiniteMeasure μ] {κ ε C m B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hC : 0 ≤ C) (hm : 0 < m)
    (hc : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ,
      MeasurableSet A → A ⊆ Icc a B →
      μ.real A ≤ C*(∫ x in A, rentWeight m x)+ε*μ.real (scaledSet κ A))
    {a : ℝ} (ha : 0 < a) {A : Set ℝ}
    (hAm : MeasurableSet A) (hA : A ⊆ Icc a B) :
    μ.real A ≤ C*(volume.real A/(1-ε*κ)+
      (∫ x in A, 1/(m*x))/(1-ε)) := by
  let An : ℕ → Set ℝ := fun n => scaledSet (κ^n) A
  have hAnm (n : ℕ) : MeasurableSet (An n) :=
    measurableSet_scaled (pow_pos hκ0 n).ne' hAm
  have hAn (n : ℕ) : An n ⊆ Icc (κ^n*a) B := by
    rintro x ⟨y,hy,rfl⟩
    have hyp := hA hy
    refine ⟨mul_le_mul_of_nonneg_left hyp.1 (pow_nonneg hκ0.le n),?_⟩
    have hpower : κ^n ≤ 1 := pow_le_one₀ hκ0.le hκ1
    calc
      κ^n*y ≤ 1*y := mul_le_mul_of_nonneg_right hpower (ha.le.trans hyp.1)
      _ ≤ B := by simpa using hyp.2
  have hrecip := reciprocal_integrableOn hm ha hA
  have hcost (n : ℕ) :
      (∫ x in An n, rentWeight m x) =
        κ^n*volume.real A+(∫ x in A, 1/(m*x)) := by
    rw [scaled_power_rentWeight_integral hκ0 m n hAm]
    have hconst : IntegrableOn (fun _ : ℝ => κ^n) A :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ => κ^n) (Icc a B)).integrableOn_Icc.mono_set hA
    rw [integral_add hconst hrecip,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
  have hub (n : ℕ) : μ.real (An n) ≤ μ.real univ :=
    measureReal_mono (subset_univ _)
  have hnext (n : ℕ) : scaledSet κ (An n) = An (n+1) := by
    dsimp [An]
    rw [scaledSet_mul,pow_succ]
    congr 1
    ring
  have hrec (n : ℕ) : μ.real (An n) ≤
      C*(κ^n*volume.real A+(∫ x in A, 1/(m*x)))+ε*μ.real (An (n+1)) := by
    have h := hc (κ^n*a) (mul_pos (pow_pos hκ0 n) ha) (An n) (hAnm n) (hAn n)
    rwa [hcost n,hnext n] at h
  have hnonneg : 0 ≤ ∫ x in A, 1/(m*x) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hAm] with x hx
    exact one_div_nonneg.mpr (mul_nonneg hm.le (ha.le.trans (hA hx).1))
  have hres := scaled_recurrence_bound (fun n => μ.real (An n))
    hε0 hε1 hκ0.le hκ1 hC (show 0 ≤ volume.real A from measureReal_nonneg)
    hnonneg hub hrec
  simpa only [An,pow_zero,scaledSet_one] using hres

theorem local_ac_of_compact_null_contraction
    (μ : Measure ℝ) [IsFiniteMeasure μ] {κ ε B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hc : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Ioc a B → volume A=0 → μ.real A ≤ ε*μ.real (scaledSet κ A)) :
    μ.restrict (Ioc 0 B) ≪ volume := by
  have hcompact : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ, MeasurableSet A →
      A ⊆ Ioc a B → volume A=0 → μ A=0 := by
    intro a ha A hAm hA hnull
    let An : ℕ → Set ℝ := fun n => scaledSet (κ^n) A
    have hmeas (n : ℕ) : MeasurableSet (An n) :=
      measurableSet_scaled (pow_pos hκ0 n).ne' hAm
    have hsubset (n : ℕ) : An n ⊆ Ioc (κ^n*a) B := by
      rintro x ⟨y,hy,rfl⟩
      have hyp := hA hy
      constructor
      · exact mul_lt_mul_of_pos_left hyp.1 (pow_pos hκ0 n)
      · have hpower : κ^n ≤ 1 := pow_le_one₀ hκ0.le hκ1
        exact (mul_le_mul_of_nonneg_right hpower (ha.le.trans hyp.1.le)).trans
          (by simpa using hyp.2)
    have hzero (n : ℕ) : volume (An n)=0 := by
      change volume (scaledSet (κ^n) A)=0
      rw [volume_scaled (pow_pos hκ0 n) hAm,hnull,mul_zero]
    have hnext (n : ℕ) : scaledSet κ (An n)=An (n+1) := by
      dsimp only [An]
      rw [scaledSet_mul,pow_succ]
      congr 1
      ring
    have hrec (n : ℕ) : μ.real (An n) ≤ ε*μ.real (An (n+1)) := by
      rw [← hnext n]
      exact hc (κ^n*a) (mul_pos (pow_pos hκ0 n) ha) (An n)
        (hmeas n) (hsubset n) (hzero n)
    have hbound (n : ℕ) : μ.real (An n) ≤ μ.real univ :=
      measureReal_mono (subset_univ _)
    have hh := bounded_forward_contraction_nonpos (fun n => μ.real (An n))
      hε0 hε1 hbound hrec 0
    have hreal : μ.real A=0 := by
      simpa only [An,pow_zero,scaledSet_one] using
        le_antisymm hh (show 0 ≤ μ.real (An 0) from measureReal_nonneg)
    exact (measureReal_eq_zero_iff (measure_ne_top μ A)).mp hreal
  intro A hA
  obtain ⟨C,hAC,hCm,hCv⟩ := exists_measurable_superset_of_null hA
  let Cn : ℕ → Set ℝ := fun n => C ∩ Ioc (1/((n:ℝ)+1)) B
  have hCn (n : ℕ) : μ (Cn n)=0 := by
    apply hcompact (1/((n:ℝ)+1)) (by positivity) (Cn n)
      (hCm.inter measurableSet_Ioc) inter_subset_right
    exact measure_mono_null inter_subset_left hCv
  have hcover : C ∩ Ioc 0 B ⊆ ⋃ n : ℕ, Cn n := by
    rintro x ⟨hxC,hx0,hxB⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (1/x)
    have hn0 : 0 < (n:ℝ)+1 := by positivity
    have hsmall : 1/((n:ℝ)+1) < x := by
      apply (div_lt_iff₀ hn0).mpr
      have hh := (div_lt_iff₀ hx0).mp hn
      nlinarith
    exact mem_iUnion.mpr ⟨n,hxC,hsmall,hxB⟩
  have hμC : μ (C ∩ Ioc 0 B)=0 :=
    measure_mono_null hcover (measure_iUnion_null hCn)
  apply le_antisymm _ bot_le
  calc
    (μ.restrict (Ioc 0 B)) A ≤ (μ.restrict (Ioc 0 B)) C := measure_mono hAC
    _ = μ (C ∩ Ioc 0 B) := Measure.restrict_apply hCm
    _ = 0 := hμC

theorem local_ac_of_weighted_Borel_contraction
    (μ : Measure ℝ) [IsFiniteMeasure μ] {κ ε C m B : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (hc : ∀ a : ℝ, 0 < a → ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc a B →
      μ.real A ≤ C*(∫ x in A, rentWeight m x)+ε*μ.real (scaledSet κ A)) :
    μ.restrict (Ioc 0 B) ≪ volume := by
  apply local_ac_of_compact_null_contraction μ hκ0 hκ1 hε0 hε1
  intro a ha A hAm hAB hnull
  have hh := hc a ha A hAm (fun x hx => ⟨(hAB hx).1.le,(hAB hx).2⟩)
  have hz : volume.restrict A=0 := Measure.restrict_eq_zero.mpr hnull
  rw [hz,integral_zero_measure,mul_zero,zero_add] at hh
  exact hh

end FCAppendix.Affine.Uniform06.ScaledMeasure
