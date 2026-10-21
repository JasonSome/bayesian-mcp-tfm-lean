import FCAppendix.Existence.R01PayOnceSmallBid

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open Set Filter Topology MeasureTheory ProbabilityTheory

section OpenMass
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace.MetrizableSpace X] [BorelSpace X]

theorem eventually_open_mass_gt (ν : ℕ → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (O : Set X) (hO : IsOpen O)
    (r : ℝ) (hr : 0 ≤ r) (hrO : r < (ν₀ : Measure X).real O) :
    ∀ᶠ j in atTop, r < (ν j : Measure X).real O := by
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hν hO
  have hr' : ENNReal.ofReal r < (ν₀ : Measure X) O := by
    exact (ENNReal.ofReal_lt_iff_lt_toReal hr (measure_ne_top _ _)).mpr hrO
  have he : ∀ᶠ j in atTop, ENNReal.ofReal r < (ν j : Measure X) O :=
    eventually_lt_of_lt_liminf (hr'.trans_le hp)
  filter_upwards [he] with j hj
  exact (ENNReal.ofReal_lt_iff_lt_toReal hr (measure_ne_top _ _)).mp hj
end OpenMass

section ActiveZero
variable {W : ℝ}

def nearActive (a t : ℝ) : Set (Value W × FloorAction 0 W) :=
  {z | a ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 ≤ t}

def nearActiveOpen (a t : ℝ) : Set (Value W × FloorAction 0 W) :=
  {z | a / 2 < z.1.1 ∧ present z.2 = true ∧ bid z.2 < t}

theorem isOpen_nearActiveOpen (a t : ℝ) : IsOpen (nearActiveOpen (W := W) a t) := by
  have hw : IsOpen {z : Value W × FloorAction 0 W | a / 2 < z.1.1} :=
    isOpen_lt continuous_const
    (continuous_subtype_val.comp continuous_fst)
  have hb : IsOpen {z : Value W × FloorAction 0 W | bid z.2 < t} :=
    isOpen_lt (continuous_bid.comp continuous_snd) continuous_const
  have ha : IsOpen {z : Value W × FloorAction 0 W | present z.2 = true} :=
    (isOpen_discrete {true}).preimage (continuous_present.comp continuous_snd)
  exact hw.inter (ha.inter hb)

theorem active_zero_subset_open (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    {z : Value W × FloorAction 0 W |
      a ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0} ⊆ nearActiveOpen a t := by
  rintro z ⟨hz, hp, hb⟩
  exact ⟨by linarith, hp, by simpa [hb] using ht⟩

theorem nearActiveOpen_subset (a t : ℝ) :
    nearActiveOpen (W := W) a t ⊆ nearActive (a / 2) t := by
  rintro z ⟨hw, hp, hb⟩
  exact ⟨hw.le, hp, hb.le⟩

theorem no_positive_active_zero_of_power_bound
    (ν : ℕ → ProbabilityMeasure (Value W × FloorAction 0 W))
    (ν₀ : ProbabilityMeasure (Value W × FloorAction 0 W))
    (hν : Tendsto ν atTop (𝓝 ν₀)) (k : ℕ) (_hk : 0 < k)
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ → ℝ) (hC : ∀ a, 0 < a → 0 ≤ C a)
    (hbound : ∀ a, 0 < a → ∀ t, 0 < t → t < δ →
      ∀ᶠ j in atTop, ((ν j : Measure (Value W × FloorAction 0 W)).real (nearActive a t)) ^ k ≤ C a * t) :
    (ν₀ : Measure (Value W × FloorAction 0 W))
      {z | 0 < z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0} = 0 := by
  have hcut : ∀ a, 0 < a →
      (ν₀ : Measure (Value W × FloorAction 0 W))
        {z | a ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0} = 0 := by
    intro a ha
    let S : Set (Value W × FloorAction 0 W) :=
      {z | a ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0}
    by_contra hmass
    let r := (ν₀ : Measure (Value W × FloorAction 0 W)).real S / 2
    have hr : 0 < r := by
      dsimp [r, Measure.real]
      exact div_pos (ENNReal.toReal_pos hmass (measure_ne_top _ _)) (by norm_num)
    have hCp : 0 ≤ C (a / 2) := hC _ (by linarith)
    let t := min (δ / 2) (r ^ k / (2 * (C (a / 2) + 1)))
    have ht : 0 < t := lt_min (by linarith) (by positivity)
    have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
    have hsmall : C (a / 2) * t < r ^ k := by
      have ht₂ : t ≤ r ^ k / (2 * (C (a / 2) + 1)) := min_le_right _ _
      have hden : 0 < 2 * (C (a / 2) + 1) := by positivity
      have hh := (le_div_iff₀ hden).mp ht₂
      have hp : 0 < r ^ k := pow_pos hr k
      nlinarith
    have hSO := active_zero_subset_open (W := W) a t ha ht
    have hmassle : (ν₀ : Measure (Value W × FloorAction 0 W)).real S ≤
        (ν₀ : Measure (Value W × FloorAction 0 W)).real (nearActiveOpen a t) :=
      measureReal_mono hSO
    have hrO : r < (ν₀ : Measure (Value W × FloorAction 0 W)).real (nearActiveOpen a t) := by
      dsimp [r] at hr ⊢
      linarith
    have he := eventually_open_mass_gt ν ν₀ hν _ (isOpen_nearActiveOpen a t) r hr.le hrO
    have hb := hbound (a / 2) (by linarith) t ht htδ
    obtain ⟨j, hj, hbj⟩ := (he.and hb).exists
    have hmj : (ν j : Measure (Value W × FloorAction 0 W)).real (nearActiveOpen a t) ≤
        (ν j : Measure (Value W × FloorAction 0 W)).real (nearActive (a / 2) t) :=
      measureReal_mono (nearActiveOpen_subset a t)
    have hpj := pow_le_pow_left₀ hr.le (hj.le.trans hmj) k
    linarith
  let a : ℕ → ℝ := fun j => 1 / (j + 1 : ℕ)
  have ha : ∀ j, 0 < a j := by intro j; dsimp [a]; positivity
  have hcover : {z : Value W × FloorAction 0 W |
      0 < z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0} ⊆
        ⋃ j : ℕ, {z | a j ≤ z.1.1 ∧ present z.2 = true ∧ bid z.2 = 0} := by
    rintro z ⟨hw, hp, hb⟩
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / z.1.1)
    refine mem_iUnion.mpr ⟨j, ?_, hp, hb⟩
    dsimp [a]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j + 1 : ℕ))).mpr
    have hh := (div_lt_iff₀ hw).mp hj
    push_cast
    nlinarith
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro j
  exact hcut (a j) (ha j)
end ActiveZero
end FCAppendix.Existence.PayOnceBounded
