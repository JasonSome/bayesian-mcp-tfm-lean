import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.Representation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

lemma continuous_cdf_of_singletons (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnoatoms : ∀ x : ℝ, mu {x} = 0) : Continuous (cdf mu : ℝ → ℝ) := by
  apply continuous_iff_continuousAt.2
  intro x
  have hzero : ENNReal.ofReal (cdf mu x-Function.leftLim (cdf mu) x) = 0 := by
    rw [← (cdf mu).measure_singleton, measure_cdf, hnoatoms]
  have hle := ENNReal.ofReal_eq_zero.1 hzero
  have hleftlim : Function.leftLim (cdf mu) x = cdf mu x :=
    le_antisymm ((cdf mu).mono.leftLim_le le_rfl) (by linarith)
  have hleft : ContinuousWithinAt (cdf mu) (Iio x) x :=
    (Monotone.continuousWithinAt_Iio_iff_leftLim_eq (cdf mu).mono).2 hleftlim
  have hboth := hleft.union ((cdf mu).right_continuous x)
  have hcover : Iio x ∪ Ici x = (univ : Set ℝ) := by
    ext y
    simp only [mem_union, mem_Iio, mem_Ici, mem_univ, iff_true]
    exact lt_or_ge y x
  rw [hcover] at hboth
  exact (continuousWithinAt_univ _ _).1 hboth

lemma cdf_hits_interior (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hcont : Continuous (cdf mu : ℝ → ℝ)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ, cdf mu x = t := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot mu).eventually (eventually_lt_nhds ht.1)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop mu).eventually (eventually_gt_nhds ht.2)).exists
  have hab : a ≤ b := by
    by_contra! h
    have := (cdf mu).mono h.le
    linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨ha.le, hb.le⟩
  exact ⟨x, hx⟩

lemma cdf_sublevel_real (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hcont : Continuous (cdf mu : ℝ → ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    mu.real {x | cdf mu x ≤ t} = t := by
  by_cases ht1 : t = 1
  · subst t
    have he : {x | cdf mu x ≤ (1 : ℝ)} = univ := by
      ext x
      simp [cdf_le_one]
    simp [he]
  have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro eps heps
    by_cases hb : t+eps < 1
    · obtain ⟨y, hy⟩ := cdf_hits_interior mu hcont ⟨by linarith [ht.1], hb⟩
      have hs : {x | cdf mu x ≤ t} ⊆ Iic y := by
        intro x hx
        by_contra! hxy
        have := (cdf mu).mono (le_of_lt (lt_of_not_ge hxy))
        change cdf mu x ≤ t at hx
        linarith
      calc
        mu.real {x | cdf mu x ≤ t} ≤ mu.real (Iic y) := measureReal_mono hs
        _ = t+eps := by rw [← cdf_eq_real, hy]
    · exact (measureReal_le_one (μ := mu) (s := {x | cdf mu x ≤ t})).trans (by linarith)
  · by_cases ht0 : t = 0
    · subst t
      exact measureReal_nonneg
    · obtain ⟨y, hy⟩ := cdf_hits_interior mu hcont ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht1'⟩
      have hs : Iic y ⊆ {x | cdf mu x ≤ t} := by
        intro x hx
        exact ((cdf mu).mono hx).trans hy.le
      calc
        t = mu.real (Iic y) := by rw [← cdf_eq_real, hy]
        _ ≤ mu.real {x | cdf mu x ≤ t} := measureReal_mono hs

def cdfUnit (mu : Measure ℝ) (x : ℝ) : unitInterval :=
  ⟨cdf mu x, cdf_nonneg mu x, cdf_le_one mu x⟩

lemma measurable_cdfUnit (mu : Measure ℝ) : Measurable (cdfUnit mu) :=
  show Measurable (fun x => (⟨cdf mu x, cdf_nonneg mu x, cdf_le_one mu x⟩ : unitInterval)) from
    (cdf mu).mono.measurable.subtype_mk

lemma map_cdfUnit (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnoatoms : ∀ x : ℝ, mu {x} = 0) :
    mu.map (cdfUnit mu) = (volume : Measure unitInterval) := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (measurable_cdfUnit mu) measurableSet_Iic, unitInterval.volume_Iic]
  have he : cdfUnit mu ⁻¹' Iic t = {x | cdf mu x ≤ (t : ℝ)} := rfl
  rw [he]
  calc
    mu {x | cdf mu x ≤ (t : ℝ)} =
        ENNReal.ofReal (mu.real {x | cdf mu x ≤ (t : ℝ)}) :=
      (ENNReal.ofReal_toReal (measure_ne_top mu _)).symm
    _ = ENNReal.ofReal (t : ℝ) := by
      rw [cdf_sublevel_real mu (continuous_cdf_of_singletons mu hnoatoms) t.property]

def minBid : (n : ℕ) → (Fin (n+1) → ℝ) → ℝ
  | 0, b => b 0
  | n+1, b => min (b 0) (minBid n (fun i => b i.succ))

lemma continuous_minBid (n : ℕ) : Continuous (minBid n) := by
  induction n with
  | zero => exact continuous_apply 0
  | succ n ih =>
    exact (continuous_apply 0).min (ih.comp (continuous_pi fun i => continuous_apply i.succ))

lemma lt_minBid_iff (n : ℕ) (b : Fin (n+1) → ℝ) (t : ℝ) :
    t < minBid n b ↔ ∀ i, t < b i := by
  induction n with
  | zero => simp [minBid, Fin.forall_fin_one]
  | succ n ih =>
    simp only [minBid, lt_min_iff, ih, Fin.forall_fin_succ]

lemma minBid_is_coordinate (n : ℕ) (b : Fin (n+1) → ℝ) :
    ∃ i, minBid n b = b i := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨i, hi⟩ := ih (fun i => b i.succ)
    by_cases h : b 0 ≤ minBid n (fun i => b i.succ)
    · exact ⟨0, by simp [minBid, min_eq_left h]⟩
    · exact ⟨i.succ, by rw [minBid, min_eq_right (le_of_not_ge h), hi]⟩

def lowVectorLaw (mu : Measure ℝ) (n : ℕ) : Measure (Fin (n+1) → ℝ) :=
  Measure.pi (fun _ : Fin (n+1) => mu)

instance lowVectorLaw_isProbability (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    IsProbabilityMeasure (lowVectorLaw mu n) := by
  unfold lowVectorLaw
  infer_instance

def minimumLaw (mu : Measure ℝ) (n : ℕ) : Measure ℝ :=
  (lowVectorLaw mu n).map (minBid n)

instance minimumLaw_isProbability (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) :
    IsProbabilityMeasure (minimumLaw mu n) :=
  Measure.isProbabilityMeasure_map (continuous_minBid n).measurable.aemeasurable

lemma minimumLaw_singletons (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnoatoms : ∀ x : ℝ, mu {x} = 0) (n : ℕ) (t : ℝ) :
    minimumLaw mu n {t} = 0 := by
  rw [minimumLaw, Measure.map_apply (continuous_minBid n).measurable (measurableSet_singleton t)]
  have hs : minBid n ⁻¹' {t} ⊆ ⋃ i : Fin (n+1), {b | b i = t} := by
    intro b hb
    obtain ⟨i, hi⟩ := minBid_is_coordinate n b
    refine mem_iUnion.2 ⟨i, ?_⟩
    change b i = t
    exact hi.symm.trans hb
  apply measure_mono_null hs
  apply measure_iUnion_null
  intro i
  have he := (measurePreserving_eval (fun _ : Fin (n+1) => mu) i).map_eq
  have he' := congrArg (fun nu : Measure ℝ => nu {t}) he
  rw [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton t), hnoatoms] at he'
  exact he'

lemma minimumLaw_cdf (mu : Measure ℝ) [IsProbabilityMeasure mu] (n : ℕ) (t : ℝ) :
    cdf (minimumLaw mu n) t = 1-(1-cdf mu t)^(n+1) := by
  have htail : minimumLaw mu n (Ioi t) = (mu (Ioi t))^(n+1) := by
    rw [minimumLaw, Measure.map_apply (continuous_minBid n).measurable measurableSet_Ioi]
    have he : minBid n ⁻¹' Ioi t = pi univ (fun _ : Fin (n+1) => Ioi t) := by
      ext b
      simp [lt_minBid_iff, Set.mem_pi]
    rw [he, lowVectorLaw, Measure.pi_pi]
    simp
  have htail_mu : mu (Ioi t) = ENNReal.ofReal (1-cdf mu t) := by
    calc
      mu (Ioi t) = (cdf mu).measure (Ioi t) := by rw [measure_cdf]
      _ = _ := (cdf mu).measure_Ioi (tendsto_cdf_atTop mu) t
  have htail_min : minimumLaw mu n (Ioi t) = ENNReal.ofReal (1-cdf (minimumLaw mu n) t) := by
    calc
      minimumLaw mu n (Ioi t) = (cdf (minimumLaw mu n)).measure (Ioi t) := by rw [measure_cdf]
      _ = _ := (cdf (minimumLaw mu n)).measure_Ioi (tendsto_cdf_atTop (minimumLaw mu n)) t
  rw [htail_mu, htail_min] at htail
  have hr := congrArg ENNReal.toReal htail
  simp only [ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (cdf_le_one mu t)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (cdf_le_one (minimumLaw mu n) t))] at hr
  linarith

def conditionalMinimumSeed (mu : Measure ℝ) (n : ℕ) (b : Fin (n+1) → ℝ) : unitInterval :=
  cdfUnit (minimumLaw mu n) (minBid n b)

lemma conditionalMinimumSeed_formula (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (n : ℕ) (b : Fin (n+1) → ℝ) :
    (conditionalMinimumSeed mu n b : ℝ) = 1-(1-cdf mu (minBid n b))^(n+1) :=
  minimumLaw_cdf mu n _

lemma measurable_conditionalMinimumSeed (mu : Measure ℝ) (n : ℕ) :
    Measurable (conditionalMinimumSeed mu n) :=
  (measurable_cdfUnit _).comp (continuous_minBid n).measurable

lemma conditionalMinimumSeed_uniform (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnoatoms : ∀ x : ℝ, mu {x} = 0) (n : ℕ) :
    (lowVectorLaw mu n).map (conditionalMinimumSeed mu n) =
      (volume : Measure unitInterval) := by
  change (lowVectorLaw mu n).map ((cdfUnit (minimumLaw mu n)) ∘ minBid n) = _
  rw [← Measure.map_map (measurable_cdfUnit _) (continuous_minBid n).measurable]
  exact map_cdfUnit (minimumLaw mu n) (minimumLaw_singletons mu hnoatoms n)

lemma conditionalMinimumSeed_joint {X : Type*} [MeasurableSpace X]
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hnoatoms : ∀ x : ℝ, mu {x} = 0) (n : ℕ)
    (nu : Measure X) [IsProbabilityMeasure nu] :
    ((lowVectorLaw mu n).prod nu).map
      (fun bx => (conditionalMinimumSeed mu n bx.1, bx.2)) =
        (volume : Measure unitInterval).prod nu := by
  calc
    _ = ((lowVectorLaw mu n).map (conditionalMinimumSeed mu n)).prod (nu.map id) :=
      (Measure.map_prod_map (lowVectorLaw mu n) nu (measurable_conditionalMinimumSeed mu n) measurable_id).symm
    _ = _ := by rw [conditionalMinimumSeed_uniform mu hnoatoms n, Measure.map_id]

theorem exists_independent_uniform_streams :
    ∃ f : unitInterval → (ℕ → unitInterval), Measurable f ∧
      (volume : Measure unitInterval).map f =
        Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval)) :=
  Measure.exists_measurable_map_eq _

def optionalSeed (mu : Measure ℝ) : (n : ℕ) → (Fin n → ℝ) → Option unitInterval
  | 0, _ => none
  | n+1, b => some (conditionalMinimumSeed mu n b)

@[simp] lemma optionalSeed_zero (mu : Measure ℝ) (b : Fin 0 → ℝ) :
    optionalSeed mu 0 b = none := rfl

lemma reconstruct_other_upper {m low active upperHere upperThere : ℕ}
    (hpartition : low+active+upperHere+upperThere = m) :
    m-low-active-upperHere = upperThere := by omega

def realizedPayoff (eta v b : ℝ) (K : ℕ) : ℝ :=
  if K = 0 then 0 else v-b*(1+eta*((K:ℝ)-1))

lemma rejected_seed_user_invariance (eta v b b' : ℝ) {K K' : ℕ}
    (hK : K = 0) (hK' : K' = 0) :
    realizedPayoff eta v b K = realizedPayoff eta v b' K' := by
  simp [realizedPayoff, hK, hK']

end FCAppendix.Affine.Hybrid
