import FCAppendix.Affine.Uniform06.LiteralExperiment
import FCAppendix.Probability.EmpiricalConcentration

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.RivalGood

open Set MeasureTheory Filter Topology LowBody
open FCAppendix.Affine.ClippedResidual
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {κ : Type*} [Fintype κ]

def empirical (f : κ → Ω → ℝ) (N : ℕ) (ω : Fin N → Ω) (k : κ) : ℝ :=
  (∑ j, f k (ω j))/(N:ℝ)

def good (μ : Measure Ω) (f : κ → Ω → ℝ) (N : ℕ) (ε : ℝ) :
    Set (Fin N → Ω) :=
  {ω | ∀ k, |empirical f N ω k-∫ x, f k x ∂μ| < ε}

theorem measurable_good (μ : Measure Ω) (f : κ → Ω → ℝ)
    (hf : ∀ k, Measurable (f k)) (N : ℕ) (ε : ℝ) :
    MeasurableSet (good μ f N ε) := by
  classical
  have he : good μ f N ε=⋂ k, {ω | |empirical f N ω k-∫ x, f k x ∂μ| < ε} := by
    ext ω
    simp [good]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  have hm : Measurable (fun ω : Fin N → Ω => empirical f N ω k) := by
    unfold empirical
    exact (Finset.measurable_sum Finset.univ
      (fun j _ => (hf k).comp (measurable_pi_apply j))).div_const _
  exact measurableSet_lt ((hm.sub_const _).abs) measurable_const

theorem good_complement_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : κ → Ω → ℝ) (hf : ∀ k, AEMeasurable (f k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, f k x ∈ Icc (0:ℝ) 1)
    (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi (fun _ : Fin N => μ)).real (good μ f N ε)ᶜ ≤
      2*(Fintype.card κ:ℝ)*Real.exp (-2*(N:ℝ)*ε^2) := by
  classical
  let E : κ → Set (Fin N → Ω) := fun k =>
    {ω | ε ≤ |empirical f N ω k-∫ x, f k x ∂μ|}
  have he : (good μ f N ε)ᶜ=⋃ k, E k := by
    ext ω
    simp [good,E,not_forall,not_lt]
  rw [he]
  calc
    _ ≤ ∑ k, (Measure.pi (fun _ : Fin N => μ)).real (E k) :=
      measureReal_iUnion_fintype_le E
    _ ≤ ∑ _k : κ, 2*Real.exp (-2*(N:ℝ)*ε^2) := by
      apply Finset.sum_le_sum
      intro k _
      exact FCAppendix.Probability.iid_empiricalMean_two_sided_le
        μ (hf k) (hb k) N hN hε
    _ = _ := by simp [mul_comm,mul_left_comm,mul_assoc]

theorem integral_unit_bounds (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEMeasurable f μ)
    (hb : ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1) :
    (∫ x, f x ∂μ) ∈ Icc (0:ℝ) 1 := by
  have hi : Integrable f μ := by
    apply (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    exact hb.mono fun _ hx => by simpa [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ hx => hx.1),?_⟩
  simpa using integral_mono_ae hi (integrable_const (1:ℝ)) (hb.mono fun _ hx => hx.2)

omit [Fintype κ] in

theorem insertions_error {N r m : ℕ} (hsize : N+r=m)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : κ → Ω → ℝ} (hf : ∀ k, AEMeasurable (f k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, f k x ∈ Icc (0:ℝ) 1)
    {ε : ℝ} (hε : 0 ≤ ε) {ω : Fin N → Ω}
    (hgood : ω ∈ good μ f N ε) (hN : 0 < N)
    (marks : Fin r → κ → ℝ) (hmarks : ∀ j k, marks j k ∈ Icc (0:ℝ) 1) :
    ∀ k, |(∑ j, f k (ω j))+(∑ j, marks j k)-(m:ℝ)*(∫ x, f k x ∂μ)| ≤
      ε*(m:ℝ)+(r:ℝ) := by
  intro k
  let a := ∫ x, f k x ∂μ
  have ha : a ∈ Icc (0:ℝ) 1 := integral_unit_bounds μ (hf k) (hb k)
  have hreal : (N:ℝ)+(r:ℝ)=m := by exact_mod_cast hsize
  have he : |(∑ j, f k (ω j))-(N:ℝ)*a| < ε*(N:ℝ) := by
    have hg := hgood k
    change |(∑ j, f k (ω j))/(N:ℝ)-a| < ε at hg
    have hrew : (∑ j, f k (ω j))/(N:ℝ)-a=
        ((∑ j, f k (ω j))-(N:ℝ)*a)/(N:ℝ) := by
      field_simp [Nat.cast_ne_zero.mpr hN.ne']
    rw [hrew,abs_div] at hg
    rw [abs_of_pos (show (0:ℝ)<N from Nat.cast_pos.mpr hN)] at hg
    exact (div_lt_iff₀ (Nat.cast_pos.mpr hN)).mp hg
  have hm : |(∑ j, marks j k)-(r:ℝ)*a| ≤ (r:ℝ) := by
    have hsum : (∑ j, marks j k)-(r:ℝ)*a=∑ j, (marks j k-a) := by
      simp [Finset.sum_sub_distrib]
    rw [hsum]
    calc
      _ ≤ ∑ j, |marks j k-a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin r, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_le]
        constructor <;> linarith [(hmarks j k).1,(hmarks j k).2,ha.1,ha.2]
      _ = (r:ℝ) := by simp
  have hsplit : (∑ j, f k (ω j))+(∑ j, marks j k)-(m:ℝ)*a=
      ((∑ j, f k (ω j))-(N:ℝ)*a)+((∑ j, marks j k)-(r:ℝ)*a) := by
    rw [← hreal]
    ring
  rw [hsplit]
  have hNm : (N:ℝ) ≤ m := by exact_mod_cast (by omega : N ≤ m)
  exact (abs_add_le _ _).trans ((add_le_add he.le hm).trans
    (by linarith only [mul_le_mul_of_nonneg_left hNm hε]))

def tag (j : Fin 4) (x : RowRival) : ℝ := if x.1=j then 1 else 0
def lowerTest (f : ℝ → ℝ) (x : RowRival) : ℝ := if x.1=0 then f x.2 else 0

def statistics (ξ L a r d z h lo U : ℝ) : Fin 9 → RowRival → ℝ :=
  ![tag 0,tag 2,tag 3,
    lowerTest (exposure ξ (L-a)),lowerTest (exposure ξ (L+a)),
    lowerTest (FiniteGuards.eligibility ξ L r),lowerTest (PrefixRoot.psi d z),
    lowerTest (fun b => if b ≤ h then 1 else 0),
    lowerTest (fun b => if b ∈ Icc lo U then 1 else 0)]

theorem measurable_tag (j : Fin 4) : Measurable (tag j) := by
  unfold tag
  exact measurable_const.piecewise (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const

theorem measurable_lowerTest {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (lowerTest f) := by
  unfold lowerTest
  exact (hf.comp measurable_snd).piecewise
    (measurableSet_eq_fun measurable_fst measurable_const) measurable_const

theorem statistics_measurable (ξ L a r d z h lo U : ℝ) :
    ∀ k, Measurable (statistics ξ L a r d z h lo U k) := by
  intro k
  fin_cases k
  · exact measurable_tag 0
  · exact measurable_tag 2
  · exact measurable_tag 3
  · apply measurable_lowerTest
    unfold exposure
    fun_prop
  · apply measurable_lowerTest
    unfold exposure
    fun_prop
  · apply measurable_lowerTest
    unfold FiniteGuards.eligibility FiniteGuards.clip01 exposure
    fun_prop
  · apply measurable_lowerTest
    unfold PrefixRoot.psi
    fun_prop
  · exact measurable_lowerTest (measurable_const.piecewise measurableSet_Iic measurable_const)
  · exact measurable_lowerTest (measurable_const.piecewise measurableSet_Icc measurable_const)

theorem lowerTest_unit {f : ℝ → ℝ} (hf : ∀ b, f b ∈ Icc (0:ℝ) 1) (x : RowRival) :
    lowerTest f x ∈ Icc (0:ℝ) 1 := by
  unfold lowerTest
  split_ifs
  · exact hf _
  · norm_num

theorem statistics_unit {ξ L a r d z h lo U : ℝ}
    (hξ : 0 < ξ) (hlo : 0 < L-a) (hhi : 0 < L+a) (hd : 0 < d) :
    ∀ k x, statistics ξ L a r d z h lo U k x ∈ Icc (0:ℝ) 1 := by
  intro k x
  fin_cases k
  · dsimp [statistics,tag]; split_ifs <;> norm_num
  · dsimp [statistics,tag]; split_ifs <;> norm_num
  · dsimp [statistics,tag]; split_ifs <;> norm_num
  · exact lowerTest_unit (fun b => ⟨exposure_nonneg hξ hlo,exposure_le_one _ _ _⟩) x
  · exact lowerTest_unit (fun b => ⟨exposure_nonneg hξ hhi,exposure_le_one _ _ _⟩) x
  · exact lowerTest_unit (FiniteGuards.eligibility_bounds _ _ _) x
  · exact lowerTest_unit (fun _ => PrefixRoot.psi_bounds hd) x
  · change lowerTest (fun b => if b ≤ h then (1:ℝ) else 0) x ∈ Icc (0:ℝ) 1
    apply lowerTest_unit _ x
    intro b
    split_ifs <;> norm_num
  · change lowerTest (fun b => if b ∈ Icc lo U then (1:ℝ) else 0) x ∈ Icc (0:ℝ) 1
    apply lowerTest_unit _ x
    intro b
    split_ifs <;> norm_num

theorem source_good_complement (i : Uniform07.Row)
    (G : Measure (ℝ × ℝ)) [IsProbabilityMeasure G]
    {ξ L a r d z h lo U : ℝ} (hξ : 0 < ξ)
    (hlo : 0 < L-a) (hhi : 0 < L+a) (hd : 0 < d)
    {m marks : ℕ} (hN : 0 < m-1-marks) {ε : ℝ} (hε : 0 ≤ ε) :
    let μ := rivalLaw (Uniform07.cutoff i) 0 (1-Uniform07.cutoff i) (G.map Prod.snd)
    let f := statistics ξ L a r d z h lo U
    (Measure.pi (fun _ : Fin (m-1-marks) => μ)).real
      (good μ f (m-1-marks) ε)ᶜ ≤
      18*Real.exp (-2*(m-1-marks:ℕ)*ε^2) := by
  letI : IsProbabilityMeasure (G.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  letI : IsProbabilityMeasure
      (rivalLaw (Uniform07.cutoff i) 0 (1-Uniform07.cutoff i) (G.map Prod.snd)) :=
    rivalLaw_isProbability _ _ _ (Uniform07.cutoff_pos i).le (le_refl 0)
      (sub_nonneg.mpr (Uniform07.cutoff_lt_one i).le) (by ring) _
  have hh := good_complement_le
    (rivalLaw (Uniform07.cutoff i) 0 (1-Uniform07.cutoff i) (G.map Prod.snd))
    (statistics ξ L a r d z h lo U)
    (fun k => (statistics_measurable ξ L a r d z h lo U k).aemeasurable)
    (fun k => Eventually.of_forall fun x => statistics_unit hξ hlo hhi hd k x)
    (m-1-marks) hN hε
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, show (2:ℝ)*9=18 by norm_num] at hh
  exact hh

theorem residual_of_counts {m c low upper : ℕ} {t ρ h ε : ℝ}
    (hcap : |(c:ℝ)-(m:ℝ)*ρ| ≤ 1)
    (hlow : |(low:ℝ)-(m:ℝ)*t| ≤ ε)
    (hupper : |(upper:ℝ)-(m:ℝ)*h| ≤ ε)
    (hpos : ε+1 < (m:ℝ)*(ρ-h))
    (hroom : 2*ε+1 ≤ (m:ℝ)*(t-(ρ-h))) :
    min low (c-upper)=c-upper ∧ upper < c ∧
      |((min low (c-upper):ℕ):ℝ)-(m:ℝ)*(ρ-h)| ≤ ε+1 := by
  have hc := abs_le.mp hcap
  have hl := abs_le.mp hlow
  have hu := abs_le.mp hupper
  have hucR : (upper:ℝ) < c := by nlinarith
  have huc : upper < c := by exact_mod_cast hucR
  have hclR : (c:ℝ)-(upper:ℝ) ≤ low := by nlinarith
  have hcl : c-upper ≤ low := by
    have hh : ((c-upper:ℕ):ℝ) ≤ (low:ℝ) := by
      simpa only [Nat.cast_sub huc.le] using hclR
    exact_mod_cast hh
  refine ⟨min_eq_right hcl,huc,?_⟩
  rw [min_eq_right hcl,Nat.cast_sub huc.le,abs_le]
  constructor <;> nlinarith

theorem residual_gap_le {d0 d1 : ℕ} {v ε : ℝ}
    (h0 : |(d0:ℝ)-v| ≤ ε) (h1 : |(d1:ℝ)-v| ≤ ε) :
    |((min d0 d1:ℕ):ℝ)-v| ≤ ε ∧
    |((max d0 d1:ℕ):ℝ)-v| ≤ ε ∧
    ((max d0 d1-min d0 d1:ℕ):ℝ) ≤ 2*ε := by
  have he : min d0 d1 ≤ max d0 d1 := min_le_max
  rw [Nat.cast_sub he]
  rcases le_total d0 d1 with hd | hd
  · simp only [min_eq_left hd,max_eq_right hd]
    refine ⟨h0,h1,?_⟩
    linarith [(abs_le.mp h0).1,(abs_le.mp h1).2]
  · simp only [min_eq_right hd,max_eq_left hd]
    refine ⟨h1,h0,?_⟩
    linarith [(abs_le.mp h1).1,(abs_le.mp h0).2]

theorem four_slacks {d0 d1 : ℕ} {m v ε γ w Hlo Hhi W Ψ : ℝ}
    (h0 : |(d0:ℝ)-v*m| ≤ ε) (h1 : |(d1:ℝ)-v*m| ≤ ε)
    (hlo : (v+γ)*m-ε ≤ Hlo) (hhi : Hhi ≤ (v-γ)*m+ε)
    (hW : w*m-ε ≤ W) (hΨ : 3*v*m-ε ≤ Ψ)
    (ownLo ownHi ownW ownΨ : ℝ)
    (hoLo : 0 ≤ ownLo) (hoHi : ownHi ≤ 1)
    (hoW : 0 ≤ ownW) (hoΨ : 0 ≤ ownΨ) :
    γ*m-2*ε ≤ Hlo+ownLo-(max d0 d1:ℕ) ∧
    γ*m-2*ε-1 ≤ (min d0 d1:ℕ)-(Hhi+ownHi) ∧
    w*m-3*ε ≤ W+ownW-(max d0 d1-min d0 d1:ℕ) ∧
    v*m-3*ε ≤ Ψ+ownΨ-(d0:ℝ)-d1 := by
  have hr := residual_gap_le h0 h1
  have hs := abs_le.mp hr.1
  have hlarge := abs_le.mp hr.2.1
  have h0' := abs_le.mp h0
  have h1' := abs_le.mp h1
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [hr.2.2]

theorem alpha_eq_one_of_inner {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M)
    (seeded : Prop) [Decidable seeded] (hseed : seeded) (s : Fin 5 → ℝ)
    (hs : ∀ k, 2*ε*M ≤ s k) : FiniteGuards.alpha ε M seeded s=1 := by
  unfold FiniteGuards.alpha
  rw [if_pos hseed]
  apply Finset.prod_eq_one
  intro k _
  apply FiniteGuards.clip01_one
  change 1 ≤ (s k-ε*M)/(2*ε*M-ε*M)
  apply (le_div_iff₀ (by nlinarith [mul_pos hε hM])).mpr
  linarith [hs k]

theorem actual_guard_one {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : LiteralExperiment.GuardData) (T : PureTemplate ι)
    (b : ι → ℝ) (hε : 0 < g.margin) (hM : 0 < g.population)
    (hseed : LiteralExperiment.seeded g T b)
    (hs : ∀ k, 2*g.margin*g.population ≤ LiteralExperiment.slackVector ξ g T b k) :
    LiteralExperiment.guardAlpha ξ g T b=1 := by
  classical
  exact alpha_eq_one_of_inner hε hM _ hseed _ hs

end FCAppendix.Affine.Uniform06.RivalGood
