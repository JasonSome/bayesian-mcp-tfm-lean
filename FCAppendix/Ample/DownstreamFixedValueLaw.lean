import FCAppendix.Ample.DownstreamBidTiers

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace FCAppendix.Ample.DownstreamNormalizationCore

universe u v

theorem antitone_measure_tendsto_zero
    {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hMeas : ∀ n, MeasurableSet (s n))
    (hAnti : Antitone s) (hNull : μ (⋂ n, s n) = 0) :
    Tendsto (fun n => μ (s n)) atTop (𝓝 0) := by
  have hraw : Tendsto (fun n => μ (s n)) atTop (𝓝 (μ (⋂ n, s n))) := by
    exact tendsto_measure_iInter_atTop (fun n => (hMeas n).nullMeasurableSet)
      hAnti ⟨0, measure_ne_top μ _⟩
  simpa only [hNull] using hraw

def closedValueTail (ell : ℝ) (n : ℕ) : Set ℝ :=
  Iic (ell + 1 / ((n : ℝ) + 1)) ∪ Ici (ell + ((n : ℝ) + 1))

theorem closedValueTail_measurable (ell : ℝ) (n : ℕ) :
    MeasurableSet (closedValueTail ell n) :=
  measurableSet_Iic.union measurableSet_Ici

theorem closedValueTail_antitone (ell : ℝ) :
    Antitone (closedValueTail ell) := by
  intro i j hij x hx
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hrec : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
    apply (div_le_div_iff₀ hj hi).2
    nlinarith
  change x ≤ ell + 1 / ((j : ℝ) + 1) ∨ ell + ((j : ℝ) + 1) ≤ x at hx
  change x ≤ ell + 1 / ((i : ℝ) + 1) ∨ ell + ((i : ℝ) + 1) ≤ x
  rcases hx with hx | hx
  · left
    linarith
  · right
    linarith

theorem closedValueTail_iInter (ell : ℝ) :
    (⋂ n, closedValueTail ell n) = Iic ell := by
  ext x
  constructor
  · intro hx
    change x ≤ ell
    by_contra hn
    have hgap : 0 < x - ell := sub_pos.mpr (lt_of_not_ge hn)
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / (x - ell)) (x - ell))
    have hNlow : 1 / (x - ell) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hN
    have hNhigh : x - ell < (N : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hN
    have hNp : 0 < (N : ℝ) + 1 := by positivity
    have hmul : 1 < ((N : ℝ) + 1) * (x - ell) := by
      have hlt : 1 / (x - ell) < (N : ℝ) + 1 := by linarith
      exact (div_lt_iff₀ hgap).mp hlt
    have hinv : 1 / ((N : ℝ) + 1) < x - ell := by
      apply (div_lt_iff₀ hNp).2
      nlinarith
    have hmem := mem_iInter.mp hx N
    change x ≤ ell + 1 / ((N : ℝ) + 1) ∨ ell + ((N : ℝ) + 1) ≤ x at hmem
    rcases hmem with hmem | hmem <;> linarith
  · intro hx
    apply mem_iInter.mpr
    intro n
    change x ≤ ell + 1 / ((n : ℝ) + 1) ∨ ell + ((n : ℝ) + 1) ≤ x
    left
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    change x ≤ ell at hx
    linarith

section FixedLaw

variable {Ω : ℕ → Type u} [∀ m, MeasurableSpace (Ω m)]

theorem fixed_law_apply
    (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ν : Measure ℝ)
    (hV : ∀ m, Measurable (V m))
    (hLaw : ∀ m, (μ m).map (V m) = ν)
    (s : Set ℝ) (hs : MeasurableSet s) (m : ℕ) :
    μ m ((V m) ⁻¹' s) = ν s := by
  rw [← hLaw m, Measure.map_apply (hV m) hs]

theorem compactContainment_fixed_law
    (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hV : ∀ m, Measurable (V m))
    (hLaw : ∀ m, (μ m).map (V m) = ν)
    {ell : ℝ} (hNull : ν (Iic ell) = 0) :
    CompactContainment μ V ell := by
  intro η hη
  have hInter : ν (⋂ n, closedValueTail ell n) = 0 := by
    rw [closedValueTail_iInter, hNull]
  have hLim := antitone_measure_tendsto_zero ν (closedValueTail ell)
    (closedValueTail_measurable ell) (closedValueTail_antitone ell) hInter
  have hηE : (0 : ℝ≥0∞) < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  obtain ⟨N, hN⟩ := (hLim.eventually (eventually_lt_nhds hηE)).exists
  let r : ℝ := (N : ℝ) + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := by
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    dsimp [r]
    linarith
  have hinv : 1 / r ≤ 1 := (div_le_one hr).2 hr1
  refine ⟨ell + 1 / r, ell + r, ?_, ?_, ?_⟩
  · have := one_div_pos.mpr hr
    linarith
  · linarith
  · intro m
    calc
      μ m {ω | V m ω < ell + 1 / r ∨ ell + r < V m ω}
          ≤ μ m ((V m) ⁻¹' closedValueTail ell N) := by
        apply measure_mono
        intro ω hω
        change V m ω ≤ ell + 1 / ((N : ℝ) + 1) ∨
          ell + ((N : ℝ) + 1) ≤ V m ω
        rcases hω with hω | hω
        · exact Or.inl (le_of_lt hω)
        · exact Or.inr (le_of_lt hω)
      _ = ν (closedValueTail ell N) :=
        fixed_law_apply μ V ν hV hLaw _ (closedValueTail_measurable ell N) m
      _ < ENNReal.ofReal η := hN

theorem positive_band_fixed_law
    (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hV : ∀ m, Measurable (V m))
    (hLaw : ∀ m, (μ m).map (V m) = ν)
    {a : ℝ} (hpos : 0 < ν (Iic a)) :
    ∃ β : ℝ, 0 < β ∧
      ∀ m, ENNReal.ofReal β ≤ μ m {ω | V m ω ≤ a} := by
  have hfin : ν (Iic a) ≠ ∞ := measure_ne_top ν _
  have hβ : 0 < (ν (Iic a)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hpos) hfin
  refine ⟨(ν (Iic a)).toReal, hβ, ?_⟩
  intro m
  rw [ENNReal.ofReal_toReal hfin]
  change ν (Iic a) ≤ μ m ((V m) ⁻¹' Iic a)
  exact le_of_eq (fixed_law_apply μ V ν hV hLaw _ measurableSet_Iic m).symm

structure ActiveEndpointLaw
    (μ : (m : ℕ) → Measure (Ω m))
    (V : (m : ℕ) → Ω m → ℝ) (ν : Measure ℝ) (ell : ℝ) : Prop where
  value_measurable : ∀ m, Measurable (V m)
  value_law : ∀ m, (μ m).map (V m) = ν
  nonpositive_null : ν (Iic 0) = 0
  below_endpoint_null : ν (Iio ell) = 0
  lower_bands : ∀ a : ℝ, ell < a → 0 < ν (Iic a)

theorem ActiveEndpointLaw.positiveLowerBands
    {μ : (m : ℕ) → Measure (Ω m)}
    {V : (m : ℕ) → Ω m → ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {ell : ℝ} (h : ActiveEndpointLaw μ V ν ell) :
    PositiveLowerBands μ V ell := by
  intro a ha
  exact positive_band_fixed_law μ V ν h.value_measurable h.value_law
    (h.lower_bands a ha)

theorem upper_value_tail_small (ν : Measure ℝ) [IsFiniteMeasure ν]
    (ell : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℝ, ell ≤ b ∧ ν (Ioi b) < ENNReal.ofReal η := by
  have hInter : (⋂ n : ℕ, Ici (n : ℝ)) = (∅ : Set ℝ) := by
    ext x
    simp only [mem_iInter, mem_Ici, mem_empty_iff_false]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact (not_le_of_gt hn) (h n)
    · exact False.elim
  have hAnti : Antitone (fun n : ℕ => Ici (n : ℝ)) := by
    intro i j hij x hx
    have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact le_trans hijR hx
  have hNull : ν (⋂ n : ℕ, Ici (n : ℝ)) = 0 := by
    rw [hInter, measure_empty]
  have hLim := antitone_measure_tendsto_zero ν
    (fun n : ℕ => Ici (n : ℝ)) (fun _ => measurableSet_Ici) hAnti hNull
  have hηE : (0 : ℝ≥0∞) < ENNReal.ofReal η := ENNReal.ofReal_pos.mpr hη
  obtain ⟨N, hN⟩ := (hLim.eventually (eventually_lt_nhds hηE)).exists
  refine ⟨max ell (N : ℝ), le_max_left _ _, ?_⟩
  apply lt_of_le_of_lt _ hN
  apply measure_mono
  intro x hx
  exact le_trans (le_max_right _ _) (le_of_lt (show max ell (N : ℝ) < x from hx))

variable {A : ℕ → Type v}

theorem random_deficit_normalization_fixedLaw
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {ell z : ℝ} (hell : 0 ≤ ell) (hz : ell < z)
    (hLaw : ActiveEndpointLaw μ V ν ell)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hUp : Request02UsedFailure μ M f chosen z) :
    ProbZero μ (fun m ω => f m (V m ω) / f m z - 1) := by
  have hPoint : ∀ w : ℝ, ell < w →
      Tendsto (fun m => f m w / f m z) atTop (𝓝 1) :=
    fun w hw => pointwise_deficit_normalization μ M f V chosen
      hell hz hE hBest hLaw.positiveLowerBands hUp hw
  by_cases hEnd : ν (Iic ell) = 0
  · exact random_deficit_normalization μ V f hell
      (fun m => envelope_monotone (hE m)) hUp.scale_pos hPoint
      (compactContainment_fixed_law μ V ν hLaw.value_measurable hLaw.value_law hEnd)
  · have hEndPos : 0 < ν (Iic ell) := pos_iff_ne_zero.mpr hEnd
    have hBand := positive_band_fixed_law μ V ν
      hLaw.value_measurable hLaw.value_law hEndPos
    have hPointEll : Tendsto (fun m => f m ell / f m z) atTop (𝓝 1) := by
      apply pointwise_deficit_normalization_of_band μ M f V chosen
        hell (lt_of_le_of_lt hell hz) hE hBest hUp
      simpa only [min_eq_left (le_of_lt hz)] using hBand
    intro ε hε η hη
    obtain ⟨b, hb, htail⟩ := upper_value_tail_small ν ell hη
    have hPointB : Tendsto (fun m => f m b / f m z) atTop (𝓝 1) := by
      rcases lt_or_eq_of_le hb with hlt | heq
      · exact hPoint b hlt
      · simpa only [← heq] using hPointEll
    filter_upwards [uniform_between_normalized_points f hell hb
      (fun m => envelope_monotone (hE m)) hUp.scale_pos
      hPointEll hPointB hε] with m hm
    have hsub : {ω | ε < |f m (V m ω) / f m z - 1|} ⊆
        {ω | V m ω < ell} ∪ {ω | b < V m ω} := by
      intro ω hω
      by_cases hlow : V m ω < ell
      · exact Or.inl hlow
      by_cases hhigh : b < V m ω
      · exact Or.inr hhigh
      have hgood := hm (V m ω) ⟨le_of_not_gt hlow, le_of_not_gt hhigh⟩
      exact False.elim ((not_lt_of_ge (le_of_lt hgood)) hω)
    have hlowLaw : μ m {ω | V m ω < ell} = ν (Iio ell) :=
      fixed_law_apply μ V ν hLaw.value_measurable hLaw.value_law _ measurableSet_Iio m
    have hhighLaw : μ m {ω | b < V m ω} = ν (Ioi b) :=
      fixed_law_apply μ V ν hLaw.value_measurable hLaw.value_law _ measurableSet_Ioi m
    calc
      μ m {ω | ε < |f m (V m ω) / f m z - 1|}
          ≤ μ m ({ω | V m ω < ell} ∪ {ω | b < V m ω}) := measure_mono hsub
      _ ≤ μ m {ω | V m ω < ell} + μ m {ω | b < V m ω} := measure_union_le _ _
      _ = ν (Iio ell) + ν (Ioi b) := by rw [hlowLaw, hhighLaw]
      _ = ν (Ioi b) := by rw [hLaw.below_endpoint_null, zero_add]
      _ < ENNReal.ofReal η := htail

theorem normalized_bid_fixedLaw
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K B S : (m : ℕ) → Ω m → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {ell z : ℝ} (hell : 0 ≤ ell) (hz : ell < z)
    (hLaw : ActiveEndpointLaw μ V ν ell)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hUp : Request02UsedFailure μ M f chosen z)
    (hAcceptance : ProbZero μ (fun m ω => S m ω / K m ω - 1))
    (hActual : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ K m ω ∧ 0 ≤ B m ω ∧ 0 ≤ S m ω ∧ S m ω ≤ K m ω ∧
        (M m).payment (chosen m ω) = B m ω * S m ω) :
    ProbZero μ (fun m ω => K m ω * B m ω / f m z - 1) := by
  have hF := random_deficit_normalization_fixedLaw μ M f V chosen ν
    hell hz hLaw hE hBest hUp
  have hCompact0 := compactContainment_fixed_law μ V ν
    hLaw.value_measurable hLaw.value_law hLaw.nonpositive_null
  have hY := probZero_value_mul μ V
    (fun m ω => (M m).failure (chosen m ω) / f m z)
    hCompact0 hUp.failure_small
  apply probZero_bid_of_identity μ
    (fun m ω => K m ω * B m ω / f m z)
    (fun m ω => V m ω * ((M m).failure (chosen m ω) / f m z))
    (fun m ω => S m ω / K m ω)
    (fun m ω => f m (V m ω) / f m z)
    hF hY hAcceptance
  intro m
  filter_upwards [hBest m, hActual m] with ω hω hA
  have hC := hUp.scale_pos m
  have hratio : S m ω / K m ω ≤ 1 := by
    by_cases hk : K m ω = 0
    · simp [hk]
    · have hkpos : 0 < K m ω := lt_of_le_of_ne hA.1 (Ne.symm hk)
      exact (div_le_one hkpos).2 hA.2.2.2.1
  refine ⟨div_nonneg (mul_nonneg hA.1 hA.2.1) (le_of_lt hC),
    mul_nonneg hω.1
      (div_nonneg ((M m).failure_nonneg _) (le_of_lt hC)), hratio, ?_⟩
  apply payment_normalization_identity hA.2.2.1 hA.2.2.2.1 hC
  rw [bestReply_touches (hE m) hω.1 hω.2, hA.2.2.2.2]

theorem normalized_charge_fixedLaw_of_upstream
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K E S : (m : ℕ) → Ω m → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {ell z : ℝ} (hell : 0 ≤ ell) (hz : ell < z)
    (hLaw : ActiveEndpointLaw μ V ν ell)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hUp : Request02NormalizationInput μ M f chosen K S z)
    (hNoRoute : ∀ m, ∀ᵐ ω ∂μ m,
      K m ω = 0 → (M m).failure (chosen m ω) = 1)
    (hActual : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ K m ω ∧ 0 ≤ E m ω ∧ 0 ≤ S m ω ∧ S m ω ≤ K m ω ∧
        (M m).payment (chosen m ω) = E m ω * S m ω) :
    ProbZero μ (fun m ω => K m ω * E m ω / f m z - 1) := by
  have hK : ∀ m, ∀ᵐ ω ∂μ m, 0 ≤ K m ω :=
    fun m => (hActual m).mono (fun _ h => h.1)
  have hAcc := acceptance_probZero_of_upstream μ M f chosen K S hUp hK hNoRoute
  exact normalized_bid_fixedLaw μ M f V chosen K E S ν hell hz hLaw hE hBest
    hUp.toRequest02UsedFailure hAcc hActual

theorem normalized_raw_bid_fixedLaw_of_upstream
    (μ : (m : ℕ) → Measure (Ω m))
    (M : (m : ℕ) → AffineMenu (A m))
    (f : ℕ → ℝ → ℝ)
    (V : (m : ℕ) → Ω m → ℝ)
    (chosen : (m : ℕ) → Ω m → A m)
    (K B S : (m : ℕ) → Ω m → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    {a ell z : ℝ} (ha : 0 < a) (hell : 0 ≤ ell) (hz : ell < z)
    (hLaw : ActiveEndpointLaw μ V ν ell)
    (hE : ∀ m, IsEnvelope (M m) (f m))
    (hBest : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ V m ω ∧ IsBestReply (M m) (V m ω) (chosen m ω))
    (hUp : Request02NormalizationInput μ M f chosen K S z)
    (hNoRoute : ∀ m, ∀ᵐ ω ∂μ m,
      K m ω = 0 → (M m).failure (chosen m ω) = 1)
    (hActual : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ K m ω ∧ 0 ≤ B m ω ∧ 0 ≤ S m ω ∧ S m ω ≤ K m ω ∧
        (M m).payment (chosen m ω) = (a * B m ω) * S m ω) :
    ProbZero μ (fun m ω => a * (K m ω * B m ω) / f m z - 1) := by
  have hEff : ∀ m, ∀ᵐ ω ∂μ m,
      0 ≤ K m ω ∧ 0 ≤ a * B m ω ∧ 0 ≤ S m ω ∧ S m ω ≤ K m ω ∧
        (M m).payment (chosen m ω) = (a * B m ω) * S m ω := by
    intro m
    filter_upwards [hActual m] with ω hω
    exact ⟨hω.1, mul_nonneg (le_of_lt ha) hω.2.1,
      hω.2.2.1, hω.2.2.2.1, hω.2.2.2.2⟩
  have h := normalized_charge_fixedLaw_of_upstream μ M f V chosen
    K (fun m ω => a * B m ω) S ν hell hz hLaw hE hBest hUp hNoRoute hEff
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end FixedLaw
end FCAppendix.Ample.DownstreamNormalizationCore
