import FCAppendix.Affine.Uniform06.ClosedSupportIC
import FCAppendix.Affine.Uniform06.ScaledMeasure

noncomputable section
namespace FCAppendix.Affine.Uniform06.ICAbsorption

open MeasureTheory Set Filter Topology
open Rank ScaledMeasure SupportIntervalDomination

theorem finite_IC_absorb
    {η r A B L W a b v Sa Sb Da Db u z : ℝ}
    (hη : 0 ≤ η) (hr : 0 < r) (hA : 0 < A) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (_hW : 0 ≤ W) (ha : 0 < a) (hab : a ≤ b)
    (hb2 : b ≤ 2*a) (hsmall : b-a ≤ r*a/2)
    (hrent : r*a ≤ v-a) (hu : 0 ≤ u) (hz : 0 ≤ z)
    (hIC : payoff η v b Sb Db ≤ payoff η v a Sa Da)
    (hS : A*u ≤ Sb-Sa) (hD : Db-Da ≤ B*(u+z)+L*(b-a)/a)
    (hlevel : Sa+η*Da ≤ W) (habsorb : 0 < r*A/2-2*η*B) :
    u ≤ (W+2*η*L)/(a*(r*A/2-2*η*B))*(b-a)+
      (2*η*B/(r*A/2-2*η*B))*z := by
  let d := r*A/2-2*η*B
  have hd : 0 < d := habsorb
  have hb : 0 < b := ha.trans_le hab
  have hstep : 0 ≤ b-a := sub_nonneg.mpr hab
  have hvb : r*a/2 ≤ v-b := by linarith
  have hva0 : 0 ≤ v-b := (by positivity : 0 ≤ r*a/2).trans hvb
  have hS0 : 0 ≤ Sb-Sa := (mul_nonneg hA.le hu).trans hS
  have hlower : (r*a/2)*(A*u) ≤ (v-b)*(Sb-Sa) :=
    mul_le_mul hvb hS (mul_nonneg hA.le hu) hva0
  have hi := IC_increment_upper hIC
  have hcost := mul_le_mul_of_nonneg_left hlevel hstep
  have hdup := mul_le_mul_of_nonneg_left hD (mul_nonneg hη hb.le)
  have hBfactor : η*b*B*(u+z) ≤ 2*η*a*B*(u+z) := by
    have hh := mul_le_mul_of_nonneg_right hb2
      (show 0 ≤ η*B*(u+z) by positivity)
    nlinarith
  have hLfactor : η*b*(L*(b-a)/a) ≤ 2*η*L*(b-a) := by
    have hba : b/a ≤ 2 := (div_le_iff₀ ha).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_right hba (show 0 ≤ η*L*(b-a) by positivity)
    convert! hh using 1
    · field_simp [ha.ne']
    · ring
  have hfinal : a*d*u ≤ (W+2*η*L)*(b-a)+2*η*a*B*z := by
    dsimp only [d]
    nlinarith
  have hquot : u ≤ ((W+2*η*L)*(b-a)+2*η*a*B*z)/(a*d) :=
    (le_div_iff₀ (mul_pos ha hd)).mpr (by nlinarith)
  convert! hquot using 1
  dsimp only [d]
  field_simp [ha.ne',habsorb.ne']

theorem absorption_coefficient_bounds
    {η r A B : ℝ} (hη : 0 ≤ η) (_hr : 0 < r) (_hA : 0 < A)
    (hB : 0 ≤ B) (hsmall : 8*η*B < r*A) :
    0 < r*A/2-2*η*B ∧
      0 ≤ 2*η*B/(r*A/2-2*η*B) ∧
        2*η*B/(r*A/2-2*η*B) < 1 := by
  have hnon : 0 ≤ η*B := mul_nonneg hη hB
  have hd : 0 < r*A/2-2*η*B := by nlinarith
  refine ⟨hd,by positivity,?_⟩
  apply (div_lt_one hd).mpr
  nlinarith

theorem scaledSet_Ioc {κ a b : ℝ} (hκ : 0 < κ) :
    scaledSet κ (Ioc a b)=Ioc (κ*a) (κ*b) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨mul_lt_mul_of_pos_left hy.1 hκ,mul_le_mul_of_nonneg_left hy.2 hκ.le⟩
  · intro hx
    refine ⟨x/κ,⟨?_,?_⟩,?_⟩
    · exact (lt_div_iff₀ hκ).mpr (by nlinarith [hx.1])
    · exact (div_le_iff₀ hκ).mpr (by nlinarith [hx.2])
    · field_simp [hκ.ne']

theorem scaledRankMeasure_atomless (μ : Measure ℝ)
    (hatom : ∀ x : ℝ, μ {x}=0) {κ : ℝ} (hκ : κ ≠ 0) (x : ℝ) :
    scaledRankMeasure κ μ {x}=0 := by
  rw [scaledRankMeasure_apply hκ μ (measurableSet_singleton x)]
  simpa only [scaledSet,Set.image_singleton] using hatom (κ*x)

def comparisonMeasure (μ : Measure ℝ) (κ C ε lo hi : ℝ) : Measure ℝ :=
  ENNReal.ofReal C • volume.restrict (Ioc lo hi)+
    ENNReal.ofReal ε • scaledRankMeasure κ μ

theorem comparisonMeasure_atomless (μ : Measure ℝ)
    (hatom : ∀ x : ℝ, μ {x}=0) {κ : ℝ} (hκ : κ ≠ 0)
    (C ε lo hi x : ℝ) : comparisonMeasure μ κ C ε lo hi {x}=0 := by
  rw [comparisonMeasure,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    scaledRankMeasure_atomless μ hatom hκ x,
    restricted_singleton_null volume (fun x => measure_singleton x) (Ioc lo hi) x]
  simp

theorem comparisonMeasure_interval (μ : Measure ℝ) [IsFiniteMeasure μ]
    {κ C ε lo hi a b : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) (hab : a ≤ b) :
    (comparisonMeasure μ κ C ε lo hi).real (Ioc a b)=
      C*(b-a)+ε*μ.real (Ioc (κ*a) (κ*b)) := by
  have hsub : Ioc a b ⊆ Ioc lo hi :=
    fun x hx => ⟨ha.1.trans_lt hx.1,hx.2.trans hb.2⟩
  letI : IsFiniteMeasure (ENNReal.ofReal C • volume.restrict (Ioc lo hi)) :=
    (volume.restrict (Ioc lo hi)).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (scaledRankMeasure κ μ) := by
    unfold scaledRankMeasure
    infer_instance
  letI : IsFiniteMeasure (ENNReal.ofReal ε • scaledRankMeasure κ μ) :=
    (scaledRankMeasure κ μ).smul_finite ENNReal.ofReal_ne_top
  have hfin₀ : (ENNReal.ofReal C • volume.restrict (Ioc lo hi)) (Ioc a b) ≠ ⊤ :=
    measure_ne_top _ _
  have hfin₁ : (ENNReal.ofReal ε • scaledRankMeasure κ μ) (Ioc a b) ≠ ⊤ :=
    measure_ne_top _ _
  rw [comparisonMeasure,measureReal_add_apply hfin₀ hfin₁]
  simp only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal hε]
  rw [Measure.restrict_apply measurableSet_Ioc,inter_eq_left.mpr hsub,
    Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    scaledRankMeasure_apply hκ.ne' μ measurableSet_Ioc,scaledSet_Ioc hκ]

theorem Borel_contraction_of_anchored_intervals
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hatom : ∀ x : ℝ, μ {x}=0) {κ C ε lo hi δ : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hanchor : ∀ a ∈ μ.support, ∀ b : ℝ,
      a ∈ Icc lo hi → b ∈ Icc lo hi → a ≤ b → b-a ≤ δ →
        μ.real (Ioc a b) ≤ C*(b-a)+ε*μ.real (Ioc (κ*a) (κ*b))) :
    ∀ A : Set ℝ, MeasurableSet A → A ⊆ Ioc lo hi →
      μ.real A ≤ C*volume.real A+ε*μ.real (scaledSet κ A) := by
  let ν := comparisonMeasure μ κ C ε lo hi
  letI : IsFiniteMeasure (ENNReal.ofReal C • volume.restrict (Ioc lo hi)) :=
    (volume.restrict (Ioc lo hi)).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure (scaledRankMeasure κ μ) := by
    unfold scaledRankMeasure
    infer_instance
  letI : IsFiniteMeasure (ENNReal.ofReal ε • scaledRankMeasure κ μ) :=
    (scaledRankMeasure κ μ).smul_finite ENNReal.ofReal_ne_top
  letI : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure
    (ENNReal.ofReal C • volume.restrict (Ioc lo hi)+ENNReal.ofReal ε • scaledRankMeasure κ μ))
  have hνatom : ∀ x : ℝ, ν {x}=0 := comparisonMeasure_atomless μ hatom hκ.ne' C ε lo hi
  have hdom : μ.restrict (Ioc lo hi) ≤ ν.restrict (Ioc lo hi) := by
    apply measure_restrict_le_of_local_support_bounds μ ν Measure.isClosed_support
      Measure.support_mem_ae hatom hνatom hδ
    intro a ha b haI hbI hab hs
    rw [comparisonMeasure_interval μ hκ hC hε haI hbI hab]
    exact hanchor a ha b haI hbI hab hs
  intro A hAm hA
  have hh := Measure.le_iff'.mp hdom A
  rw [Measure.restrict_apply hAm,Measure.restrict_apply hAm,
    inter_eq_left.mpr hA] at hh
  have hr := ENNReal.toReal_mono (measure_ne_top ν A) hh
  change μ.real A ≤ ν.real A at hr
  dsimp only [ν] at hr
  rw [comparisonMeasure,measureReal_add_apply (measure_ne_top _ _) (measure_ne_top _ _)] at hr
  simp only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC,ENNReal.toReal_ofReal hε] at hr
  rw [Measure.restrict_apply hAm,inter_eq_left.mpr hA,
    scaledRankMeasure_apply hκ.ne' μ hAm] at hr
  exact hr

end FCAppendix.Affine.Uniform06.ICAbsorption
