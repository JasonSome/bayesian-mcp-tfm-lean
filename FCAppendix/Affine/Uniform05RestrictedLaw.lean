import FCAppendix.Affine.Uniform05LawRoots

noncomputable section
namespace FCAppendix.Affine.Uniform05
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

def lowerValueMeasure (i : Row) : Measure ℝ :=
  ENNReal.ofReal (1/t i) • volume.restrict (Icc (0 : ℝ) (t i))

lemma lowerValueMeasure_isProbability (i : Row) :
    IsProbabilityMeasure (lowerValueMeasure i) := by
  constructor
  have ht := t_pos i
  simp only [lowerValueMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel ht.ne']
  norm_num

instance lowerValueMeasure_probability (i : Row) :
    IsProbabilityMeasure (lowerValueMeasure i) := lowerValueMeasure_isProbability i

lemma lowerValueMeasure_singleton (i : Row) (a : ℝ) :
    lowerValueMeasure i {a} = 0 := by
  have hnull : volume ({a} ∩ Icc (0 : ℝ) (t i)) = 0 :=
    measure_mono_null inter_subset_left (measure_singleton a)
  simp only [lowerValueMeasure, Measure.smul_apply,
    Measure.restrict_apply (measurableSet_singleton a), hnull, smul_zero]

lemma lowerValueMeasure_ae_mem (i : Row) :
    ∀ᵐ v ∂lowerValueMeasure i, v ∈ Icc (0 : ℝ) (t i) := by
  exact Measure.ae_smul_measure (ae_restrict_mem (μ := volume) measurableSet_Icc) _

lemma lowerValueMeasure_positive (i : Row) :
    ∀ᵐ v ∂lowerValueMeasure i, 0 < v := by
  have hzero : ∀ᵐ v ∂lowerValueMeasure i, v ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (lowerValueMeasure_singleton i 0)
  filter_upwards [lowerValueMeasure_ae_mem i, hzero] with v hv hn
  exact lt_of_le_of_ne hv.1 (Ne.symm hn)

def RestrictedPair (i : Row) (p : ℝ × Bid i) : Prop :=
  p.1 ∈ Icc (0 : ℝ) (t i) ∧ floorBid i p.1 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ p.1

lemma restrictedPair_measurable (i : Row) : MeasurableSet {p | RestrictedPair i p} := by
  unfold RestrictedPair
  exact (measurableSet_Icc.preimage measurable_fst).inter
    ((measurableSet_le ((continuous_floor i).measurable.comp measurable_fst)
      (measurable_subtype_coe.comp measurable_snd)).inter
      (measurableSet_le (measurable_subtype_coe.comp measurable_snd) measurable_fst))

abbrev RestrictedLaw (i : Row) :=
  {G : ProbabilityMeasure (ℝ × Bid i) //
    (G : Measure (ℝ × Bid i)).map Prod.fst = lowerValueMeasure i ∧
    ∀ᵐ p ∂(G : Measure (ℝ × Bid i)), RestrictedPair i p}

namespace RestrictedLaw

variable {i : Row}

def bidLaw (G : RestrictedLaw i) : ProbabilityMeasure (Bid i) :=
  G.1.map measurable_snd.aemeasurable

lemma bidLaw_coe (G : RestrictedLaw i) :
    (G.bidLaw : Measure (Bid i)) = (G.1 : Measure (ℝ × Bid i)).map Prod.snd := rfl

lemma continuous_bidLaw : Continuous (bidLaw (i := i)) := by
  exact (ProbabilityMeasure.continuous_map continuous_snd).comp continuous_subtype_val

lemma integral_bidLaw (G : RestrictedLaw i) {f : Bid i → ℝ}
    (hf : AEStronglyMeasurable f (G.bidLaw : Measure (Bid i))) :
    (∫ b, f b ∂(G.bidLaw : Measure (Bid i))) =
      ∫ p, f p.2 ∂(G.1 : Measure (ℝ × Bid i)) := by
  exact integral_map measurable_snd.aemeasurable hf

lemma value_singleton_mass (G : RestrictedLaw i) (a : ℝ) :
    (G.1 : Measure (ℝ × Bid i)) {p | p.1 = a} = 0 := by
  change (G.1 : Measure (ℝ × Bid i)) (Prod.fst ⁻¹' {a}) = 0
  rw [← Measure.map_apply measurable_fst (measurableSet_singleton a), G.2.1]
  exact lowerValueMeasure_singleton i a

lemma value_positive (G : RestrictedLaw i) :
    ∀ᵐ p ∂(G.1 : Measure (ℝ × Bid i)), 0 < p.1 := by
  apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ioi).mp
  rw [G.2.1]
  exact lowerValueMeasure_positive i

lemma value_interval_mass (G : RestrictedLaw i) {a b : ℝ}
    (ha : 0 ≤ a) (_hab : a ≤ b) (hb : b ≤ 1) :
    (G.1 : Measure (ℝ × Bid i)) {p | a*t i < p.1 ∧ p.1 ≤ b*t i} =
      ENNReal.ofReal (b-a) := by
  have ht := t_pos i
  have hsub : Ioc (a*t i) (b*t i) ⊆ Icc (0 : ℝ) (t i) := by
    intro v hv
    exact ⟨(mul_nonneg ha ht.le).trans hv.1.le,
      hv.2.trans (by nlinarith)⟩
  change (G.1 : Measure (ℝ × Bid i)) (Prod.fst ⁻¹' Ioc (a*t i) (b*t i)) = _
  rw [← Measure.map_apply measurable_fst measurableSet_Ioc, G.2.1]
  simp only [lowerValueMeasure, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hsub, Real.volume_Ioc]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp [ht.ne']

lemma value_interval_real (G : RestrictedLaw i) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (G.1 : Measure (ℝ × Bid i)).real {p | a*t i < p.1 ∧ p.1 ≤ b*t i} = b-a := by
  rw [measureReal_def, value_interval_mass G ha hab hb, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

end RestrictedLaw

def floorPanelLeft (j : Fin 10) : ℝ := 4/5+((j : ℕ) : ℝ)/50

def floorPanelRight (j : Fin 10) : ℝ := floorPanelLeft j+1/50

def floorPanelHeight (i : Row) (j : Fin 10) : ℝ :=
  (1-(54/100)/(chi*(floorPanelLeft j-1/200)))/xi i

def floorPanel (i : Row) (j : Fin 10) : Set (ℝ × Bid i) :=
  {p | floorPanelLeft j*t i < p.1 ∧ p.1 ≤ floorPanelRight j*t i}

lemma floorPanel_endpoints (j : Fin 10) :
    4/5 ≤ floorPanelLeft j ∧ floorPanelLeft j < floorPanelRight j ∧
      floorPanelRight j ≤ 1 := by
  fin_cases j <;> norm_num [floorPanelLeft, floorPanelRight]

lemma floorPanel_height_range (i : Row) (j : Fin 10) :
    0 ≤ floorPanelHeight i j ∧ floorPanelHeight i j ≤ 1 := by
  cases i <;> fin_cases j <;> norm_num [floorPanelHeight, floorPanelLeft, chi, xi, eta]

lemma floorPanel_measurable (i : Row) (j : Fin 10) : MeasurableSet (floorPanel i j) :=
  measurableSet_Ioc.preimage measurable_fst

lemma floorPanel_disjoint (i : Row) {j k : Fin 10} (hjk : j ≠ k) :
    Disjoint (floorPanel i j) (floorPanel i k) := by
  rw [Set.disjoint_left]
  intro p hpj hpk
  have ht := t_pos i
  have hn : (j : ℕ) ≠ (k : ℕ) := fun he => hjk (Fin.ext he)
  rcases lt_or_gt_of_ne hn with h | h
  · have hr : (j : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hcut : floorPanelRight j ≤ floorPanelLeft k := by
      dsimp [floorPanelRight, floorPanelLeft]
      norm_num only [Nat.cast_add, Nat.cast_one] at hr ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcut ht.le
    exact (not_lt_of_ge (hpj.2.trans hmul)) hpk.1
  · have hr : (k : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    have hcut : floorPanelRight k ≤ floorPanelLeft j := by
      dsimp [floorPanelRight, floorPanelLeft]
      norm_num only [Nat.cast_add, Nat.cast_one] at hr ⊢
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcut ht.le
    exact (not_lt_of_ge (hpk.2.trans hmul)) hpj.1

lemma panel_bottom_exposure (i : Row) (j : Fin 10) :
    exposure (xi i) ((54 : ℝ)/100*t i)
      (chi*(floorPanelLeft j-1/200)*t i) = floorPanelHeight i j := by
  have ht := t_pos i
  have hb : (54 : ℝ)/100 < chi*(floorPanelLeft j-1/200) := by
    fin_cases j <;> norm_num [floorPanelLeft, chi]
  have hg : (1-xi i)*(chi*(floorPanelLeft j-1/200)) ≤ (54 : ℝ)/100 := by
    cases i <;> fin_cases j <;> norm_num [floorPanelLeft, chi, xi, eta]
  have hg' : (1-xi i)*(chi*(floorPanelLeft j-1/200)*t i) ≤ (54 : ℝ)/100*t i := by
    convert! mul_le_mul_of_nonneg_right hg ht.le using 1; ring
  rw [exposure_of_between (xi_range i).1 (demandLo_pos i)
    (mul_lt_mul_of_pos_right hb ht) hg']
  unfold floorPanelHeight
  have hden : chi*(floorPanelLeft j-1/200) ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 54/100) hb)
  field_simp [ht.ne', hden, (xi_range i).1.ne']

lemma floorPanel_lower (i : Row) {p : ℝ × Bid i} (hp : RestrictedPair i p)
    (j : Fin 10) (hj : p ∈ floorPanel i j) :
    floorPanelHeight i j ≤ exposure (xi i) ((54 : ℝ)/100*t i) (p.2 : ℝ) := by
  have ht := t_pos i
  have hz : zc i ≤ (4/5)*t i := by
    cases i <;> dsimp [zc, lambda, x] <;> nlinarith
  have hy := (floorPanel_endpoints j).1
  have hv : zc i ≤ p.1 :=
    hz.trans ((mul_le_mul_of_nonneg_right hy ht.le).trans hj.1.le)
  have hfloor := floor_full i ht hv
  have hv0 : v0 i ≤ p.1 := by
    have h₁ : (4/5)*t i ≤ p.1 :=
      (mul_le_mul_of_nonneg_right hy ht.le).trans hj.1.le
    dsimp [v0]
    linarith
  have hpmin : chi*(floorPanelLeft j-1/200)*t i ≤ (p.2 : ℝ) := by
    have hlf := hp.2.1
    rw [hfloor, max_eq_right (sub_nonneg.mpr hv0)] at hlf
    have hc : 0 < chi := by norm_num [chi]
    have hm := mul_le_mul_of_nonneg_left hj.1.le hc.le
    dsimp [v0] at hlf
    nlinarith
  rw [← panel_bottom_exposure i j]
  exact exposure_monotone_bid (xi_range i).1 (demandLo_pos i) hpmin

def floorStep (i : Row) (p : ℝ × Bid i) : ℝ :=
  ∑ j : Fin 10, (floorPanel i j).indicator (fun _ => floorPanelHeight i j) p

lemma floorStep_lower (i : Row) {p : ℝ × Bid i} (hp : RestrictedPair i p) :
    floorStep i p ≤ exposure (xi i) ((54 : ℝ)/100*t i) (p.2 : ℝ) := by
  classical
  by_cases hex : ∃ j, p ∈ floorPanel i j
  · obtain ⟨j,hj⟩ := hex
    have he : floorStep i p = floorPanelHeight i j := by
      unfold floorStep
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hj _
      · intro k _ hkj
        have hk : p ∉ floorPanel i k := fun hpk =>
          Set.disjoint_left.mp (floorPanel_disjoint i hkj) hpk hj
        exact Set.indicator_of_notMem hk _
      · simp
    rw [he]
    exact floorPanel_lower i hp j hj
  · have he : floorStep i p = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact Set.indicator_of_notMem (fun hj => hex ⟨j,hj⟩) _
    rw [he]
    exact exposure_nonneg (xi_range i).1 (demandLo_pos i)

lemma integrable_floorStep (i : Row) (G : RestrictedLaw i) :
    Integrable (floorStep i) (G.1 : Measure (ℝ × Bid i)) := by
  apply integrable_finsetSum
  intro j _
  exact (integrable_const _).indicator (floorPanel_measurable i j)

lemma integral_floorStep (i : Row) (G : RestrictedLaw i) :
    (∫ p, floorStep i p ∂(G.1 : Measure (ℝ × Bid i))) =
      (∑ j : Fin 10, floorPanelHeight i j)/50 := by
  unfold floorStep
  rw [integral_finsetSum _ (fun j _ =>
    (integrable_const (floorPanelHeight i j)).indicator (floorPanel_measurable i j))]
  have he : ∀ j : Fin 10,
      (∫ p, (floorPanel i j).indicator (fun _ => floorPanelHeight i j) p
        ∂(G.1 : Measure (ℝ × Bid i))) = floorPanelHeight i j/50 := by
    intro j
    have h := floorPanel_endpoints j
    have hm := G.value_interval_real
      (show 0 ≤ floorPanelLeft j by linarith [h.1]) h.2.1.le h.2.2
    rw [integral_indicator (floorPanel_measurable i j)]
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
    change (G.1 : Measure (ℝ × Bid i)).real (floorPanel i j)*floorPanelHeight i j = _
    rw [show (G.1 : Measure (ℝ × Bid i)).real (floorPanel i j) =
      floorPanelRight j-floorPanelLeft j from hm]
    unfold floorPanelRight
    ring
  simp_rw [he]
  rw [Finset.sum_div]

lemma floorStep_strict_guard (i : Row) :
    requiredDemand i < (∑ j : Fin 10, floorPanelHeight i j)/50 := by
  have hr := requiredDemand_lt_coarse_upper i
  have hrat : demandUpper i < (∑ j : Fin 10, floorPanelHeight i j)/50 := by
    cases i <;>
      norm_num [floorPanelHeight, floorPanelLeft, chi, xi, eta, demandUpper,
        Fin.sum_univ_succ]
  exact hr.trans hrat

theorem restrictedLaw_demand_guard (i : Row) (G : RestrictedLaw i) :
    requiredDemand i < lawDemand i G.bidLaw ((54 : ℝ)/100*t i) := by
  have hf := integrable_lawDemand i G.bidLaw (demandLo_pos i)
  rw [lawDemand, G.integral_bidLaw hf.aestronglyMeasurable]
  have hig : Integrable
      (fun p : ℝ × Bid i => exposure (xi i) ((54 : ℝ)/100*t i) (p.2 : ℝ))
      (G.1 : Measure (ℝ × Bid i)) := by
    apply integrable_of_unit_bounds
    · exact ((continuous_exposure (xi_range i).1 (demandLo_pos i)).comp
        (continuous_subtype_val.comp continuous_snd)).measurable
    · exact fun _ => exposure_nonneg (xi_range i).1 (demandLo_pos i)
    · exact fun _ => exposure_le_one _ _ _
  have hle := integral_mono_ae (integrable_floorStep i G) hig
    (G.2.2.mono fun p hp => floorStep_lower i hp)
  rw [integral_floorStep] at hle
  exact (floorStep_strict_guard i).trans_le hle

lemma restrictedPair_fullFloor_bid (i : Row) {p : ℝ × Bid i}
    (hp : RestrictedPair i p) (hv : fullFloorCut*t i < p.1) :
    (54 : ℝ)/100*t i ≤ (p.2 : ℝ) := by
  have ht := t_pos i
  have hz : zc i ≤ fullFloorCut*t i := by
    cases i <;> dsimp [zc, lambda, x, fullFloorCut] <;> nlinarith
  have hfull := floor_full i ht (hz.trans hv.le)
  have hc : 0 < chi := by norm_num [chi]
  have hcut : chi*(fullFloorCut*t i-v0 i) = (54 : ℝ)/100*t i := by
    unfold chi fullFloorCut v0
    ring
  rw [← hcut]
  calc
    chi*(fullFloorCut*t i-v0 i) ≤ chi*(p.1-v0 i) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hv.le _) hc.le
    _ ≤ chi*max 0 (p.1-v0 i) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
    _ = floorBid i p.1 := hfull.symm
    _ ≤ (p.2 : ℝ) := hp.2.1

lemma rejection_at_fullFloor (i : Row) :
    rejectionExposure (rejectionScale i) ((52 : ℝ)/100*t i) ((54 : ℝ)/100*t i) =
      (20 : ℝ)/21 := by
  have ht := t_pos i
  have hd : 0 ≤ (54 : ℝ)/100*t i-(52 : ℝ)/100*t i := by nlinarith
  rw [rejectionExposure, max_eq_right hd]
  unfold rejectionScale
  field_simp [ht.ne']; ring

theorem restrictedLaw_rejection_guard (i : Row) (G : RestrictedLaw i) :
    3*requiredDemand i < lawRejection i G.bidLaw ((52 : ℝ)/100*t i) := by
  let A : Set (ℝ × Bid i) := {p | fullFloorCut*t i < p.1 ∧ p.1 ≤ t i}
  have hA : MeasurableSet A := measurableSet_Ioc.preimage measurable_fst
  have hm : (G.1 : Measure (ℝ × Bid i)).real A = 1-fullFloorCut := by
    simpa [A] using G.value_interval_real
      (a := fullFloorCut) (b := 1) (by norm_num [fullFloorCut])
      (by norm_num [fullFloorCut]) le_rfl
  have hf := integrable_lawRejection i G.bidLaw ((52 : ℝ)/100*t i)
  rw [lawRejection, G.integral_bidLaw hf.aestronglyMeasurable]
  have hi : Integrable
      (fun p : ℝ × Bid i => rejectionExposure (rejectionScale i)
        ((52 : ℝ)/100*t i) (p.2 : ℝ)) (G.1 : Measure (ℝ × Bid i)) := by
    apply integrable_of_unit_bounds
    · exact ((continuous_rejectionExposure (rejectionScale_pos i)).comp
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))).measurable
    · exact fun _ => rejectionExposure_nonneg (rejectionScale_pos i)
    · exact fun _ => rejectionExposure_le_one (rejectionScale_pos i)
  have hpoint : ∀ᵐ p ∂(G.1 : Measure (ℝ × Bid i)),
      A.indicator (fun _ => (20 : ℝ)/21) p ≤
      rejectionExposure (rejectionScale i) ((52 : ℝ)/100*t i) (p.2 : ℝ) := by
    filter_upwards [G.2.2] with p hp
    by_cases hv : p ∈ A
    · rw [Set.indicator_of_mem hv, ← rejection_at_fullFloor i]
      exact rejectionExposure_monotone_bid (rejectionScale_pos i)
        (restrictedPair_fullFloor_bid i hp hv.1)
    · rw [Set.indicator_of_notMem hv]
      exact rejectionExposure_nonneg (rejectionScale_pos i)
  have hh := integral_mono_ae ((integrable_const ((20 : ℝ)/21)).indicator hA) hi hpoint
  rw [integral_indicator hA] at hh
  simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hh
  change (G.1 : Measure (ℝ × Bid i)).real A*((20 : ℝ)/21) ≤ _ at hh
  rw [hm] at hh
  have hn := (numerical_seed_rejection_guard i).2.2
  norm_num only at hn
  exact hn.trans_le hh

namespace RestrictedLaw

variable {i : Row}

def rootDomain (G : RestrictedLaw i) : RootDomain i :=
  ⟨G.bidLaw, restrictedLaw_demand_guard i G, restrictedLaw_rejection_guard i G⟩

lemma continuous_rootDomain : Continuous (rootDomain (i := i)) :=
  continuous_bidLaw.subtype_mk _

def multiplier (G : RestrictedLaw i) : ℝ := lawMultiplier i G.rootDomain

def rejectionRoot (G : RestrictedLaw i) : ℝ := lawRejectionRoot i G.rootDomain

lemma multiplier_equation (G : RestrictedLaw i) :
    lawDemand i G.bidLaw G.multiplier = requiredDemand i :=
  (lawMultiplier_spec i G.rootDomain).2

lemma rejectionRoot_equation (G : RestrictedLaw i) :
    lawRejection i G.bidLaw G.rejectionRoot = 3*requiredDemand i :=
  (lawRejectionRoot_spec i G.rootDomain).2

lemma multiplier_guards (G : RestrictedLaw i) :
    (54 : ℝ)/100*t i < G.multiplier ∧
    G.multiplier ≤ (1-xi i*requiredDemand i)*cap i ∧
    G.multiplier < cap i ∧ kappa i*cap i < G.multiplier :=
  ⟨(lawMultiplier_strict_bounds i G.rootDomain).1,
    lawMultiplier_upper i G.rootDomain,
    (lawMultiplier_strict_bounds i G.rootDomain).2,
    lawMultiplier_receipt_guard i G.rootDomain⟩

lemma rejectionRoot_guards (G : RestrictedLaw i) :
    (52 : ℝ)/100*t i < G.rejectionRoot ∧ G.rejectionRoot < cap i :=
  lawRejectionRoot_strict_bounds i G.rootDomain

lemma continuous_multiplier : Continuous (multiplier (i := i)) :=
  (continuous_lawMultiplier i).comp continuous_rootDomain

lemma continuous_rejectionRoot : Continuous (rejectionRoot (i := i)) :=
  (continuous_lawRejectionRoot i).comp continuous_rootDomain

theorem constructed_roots (G : RestrictedLaw i) :
    lawDemand i G.bidLaw G.multiplier = requiredDemand i ∧
    lawRejection i G.bidLaw G.rejectionRoot = 3*requiredDemand i ∧
    (54 : ℝ)/100*t i < G.multiplier ∧
    G.multiplier ≤ (1-xi i*requiredDemand i)*cap i ∧
    kappa i*cap i < G.multiplier ∧
    (52 : ℝ)/100*t i < G.rejectionRoot ∧ G.rejectionRoot < cap i := by
  exact ⟨G.multiplier_equation, G.rejectionRoot_equation,
    G.multiplier_guards.1, G.multiplier_guards.2.1,
    G.multiplier_guards.2.2.2, G.rejectionRoot_guards.1, G.rejectionRoot_guards.2⟩

lemma multiplier_unique (G : RestrictedLaw i) {z : ℝ}
    (hz : 0 < z) (heq : lawDemand i G.bidLaw z = requiredDemand i) :
    z = G.multiplier :=
  lawMultiplier_unique i G.rootDomain hz heq

lemma rejectionRoot_unique (G : RestrictedLaw i) {z : ℝ}
    (heq : lawRejection i G.bidLaw z = 3*requiredDemand i) :
    z = G.rejectionRoot :=
  lawRejectionRoot_unique i G.rootDomain heq

lemma multiplier_distance_bound (G H : RestrictedLaw i)
    (hnear : requiredDemand i/2 ≤ lawDemand i G.bidLaw H.multiplier) :
    |G.multiplier-H.multiplier| ≤
      2*|lawDemand i G.bidLaw H.multiplier-requiredDemand i| /
        ((1/(xi i*cap i))*requiredDemand i) :=
  lawMultiplier_distance_bound i G.rootDomain H.rootDomain hnear

lemma rejectionRoot_distance_bound (G H : RestrictedLaw i)
    (hnear : (3*requiredDemand i)/2 ≤ lawRejection i G.bidLaw H.rejectionRoot) :
    |G.rejectionRoot-H.rejectionRoot| ≤
      2*|lawRejection i G.bidLaw H.rejectionRoot-3*requiredDemand i| /
        ((rejectionScale i/(rejectionScale i+cap i)^2)*(3*requiredDemand i)) :=
  lawRejectionRoot_distance_bound i G.rootDomain H.rootDomain hnear

end RestrictedLaw
end FCAppendix.Affine.Uniform05
