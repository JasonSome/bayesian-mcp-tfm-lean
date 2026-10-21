import FCAppendix.Affine.TaggedLocalInformation

noncomputable section
namespace FCAppendix.Appendix08.Information
open MeasureTheory Game Set
open scoped BigOperators

structure Classifier where
  label : ℝ → Fin 3
  measurable_label : Measurable label

def tag (C : Classifier) : Option ℝ → Fin 4
  | none => 3
  | some b => (C.label b).castSucc

theorem measurable_tag (C : Classifier) : Measurable (tag C) := by
  intro S hS
  change MeasurableSet ((fun b : ℝ => (C.label b).castSucc) ⁻¹' S)
  exact ((measurable_of_countable (fun k : Fin 3 => k.castSucc)).comp
    C.measurable_label) hS

def Correct {m : ℕ} (C : Classifier) (kind : Fin m → Fin 3)
    (x : Realization m 2) : Prop :=
  ∀ i, C.label (x.action i).bid = kind i

abbrev Routes {m : ℕ} (kind : Fin m → Fin 3) (x : Realization m 2) : Prop :=
  Affine.TaggedLocal.ClassRoutes kind x

abbrev countKind {m : ℕ} (kind : Fin m → Fin 3) (k : Fin 3) : ℕ :=
  Affine.TaggedLocal.countKind kind k

abbrev privateAt {m : ℕ} (kind : Fin m → Fin 3)
    (x : Realization m 2) (j : Fin 2) : ℕ :=
  Affine.TaggedLocal.upperAt kind x j

def localCount {m : ℕ} (C : Classifier) (L : LocalList m) (k : Fin 4) : ℕ :=
  ∑ i : Fin m, if tag C (L i) = k then 1 else 0

theorem measurable_localCount {m : ℕ} (C : Classifier) (k : Fin 4) :
    Measurable (fun L : LocalList m => localCount C L k) := by
  classical
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag C).comp (measurable_pi_apply i))
      measurable_const) measurable_const measurable_const

def part {m : ℕ} (C : Classifier) (k : Fin 4) (L : LocalList m) : LocalList m :=
  fun i => if tag C (L i) = k then L i else none

theorem measurable_part {m : ℕ} (C : Classifier) (k : Fin 4) :
    Measurable (part (m := m) C k) := by
  apply measurable_pi_iff.mpr
  intro i
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_tag C).comp (measurable_pi_apply i))
      measurable_const) (measurable_pi_apply i) measurable_const

theorem counts_partition {m : ℕ} (kind : Fin m → Fin 3)
    (x : Realization m 2) (hr : Routes kind x) :
    countKind kind 0 + countKind kind 1 + privateAt kind x 0 + privateAt kind x 1 = m :=
  Affine.TaggedLocal.counts_partition kind x hr

theorem local_counts_correct {m : ℕ} (C : Classifier) (kind : Fin m → Fin 3)
    (x : Realization m 2) (hc : Correct C kind x) (hr : Routes kind x) (j : Fin 2) :
    localCount C (observe x j) 0 = countKind kind 0 ∧
    localCount C (observe x j) 1 = countKind kind 1 ∧
    localCount C (observe x j) 2 = privateAt kind x j := by
  classical
  have hterm (i : Fin m) :
      (if tag C (observe x j i) = 0 then 1 else 0) =
        (if kind i = 0 then 1 else 0) ∧
      (if tag C (observe x j i) = 1 then 1 else 0) =
        (if kind i = 1 then 1 else 0) ∧
      (if tag C (observe x j i) = 2 then 1 else 0) =
        (if kind i = 2 ∧ j ∈ x.recipients i then 1 else 0) := by
    rcases hk : kind i with ⟨k, hklt⟩
    interval_cases k
    · have hrec := hr.1 i (by simp [hk])
      simp [observe, hrec, tag, hc i, hk]
    · have hrec := hr.1 i (by simp [hk])
      simp [observe, hrec, tag, hc i, hk]
    · by_cases hj : j ∈ x.recipients i
      · simp [observe, hj, tag, hc i, hk]
      · simp [observe, hj, tag]
  exact ⟨Finset.sum_congr rfl (fun i _ => (hterm i).1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.1),
    Finset.sum_congr rfl (fun i _ => (hterm i).2.2)⟩

theorem broadcast_part_observe {m : ℕ} (C : Classifier) (kind : Fin m → Fin 3)
    (x : Realization m 2) (hc : Correct C kind x) (hr : Routes kind x)
    (k : Fin 3) (hk : k ≠ 2) (j : Fin 2) :
    part C k.castSucc (observe x j) =
      fun i => if kind i = k then some (x.action i).bid else none := by
  classical
  funext i
  by_cases hi : kind i = k
  · have hrec := hr.1 i (by simpa only [hi] using hk)
    simp [part, observe, hrec, tag, hc i, hi]
  · by_cases hj : j ∈ x.recipients i
    · simp [part, observe, hj, tag, hc i, hi]
    · have hnone : (3 : Fin 4) ≠ k.castSucc := by
        intro heq
        have hv := congrArg Fin.val heq
        have hh := k.isLt
        simp only [Fin.val_castSucc] at hv
        omega
      simp [part, observe, hj, tag, hnone, hi]

theorem common_broadcast_parts {m : ℕ} (C : Classifier) (kind : Fin m → Fin 3)
    (x : Realization m 2) (hc : Correct C kind x) (hr : Routes kind x) (j l : Fin 2) :
    part C 0 (observe x j) = part C 0 (observe x l) ∧
    part C 1 (observe x j) = part C 1 (observe x l) := by
  constructor
  · simpa using (broadcast_part_observe C kind x hc hr 0 (by decide) j).trans
      (broadcast_part_observe C kind x hc hr 0 (by decide) l).symm
  · simpa using (broadcast_part_observe C kind x hc hr 1 (by decide) j).trans
      (broadcast_part_observe C kind x hc hr 1 (by decide) l).symm

def other (j : Fin 2) : Fin 2 := if j = 0 then 1 else 0

theorem reconstruct_other_private {m : ℕ} (C : Classifier) (kind : Fin m → Fin 3)
    (x : Realization m 2) (hc : Correct C kind x) (hr : Routes kind x) (j : Fin 2) :
    privateAt kind x (other j) =
      m - localCount C (observe x j) 0 - localCount C (observe x j) 1 -
        localCount C (observe x j) 2 := by
  obtain ⟨hl, ha, hh⟩ := local_counts_correct C kind x hc hr j
  rw [hl, ha, hh]
  have hp := counts_partition kind x hr
  fin_cases j <;> norm_num [other] at * <;> omega

def ownResidual {m : ℕ} (C : Classifier) (c : ℕ) (L : LocalList m) : ℕ :=
  min (localCount C L 0) (c - localCount C L 1 - localCount C L 2)

def otherResidual {m : ℕ} (C : Classifier) (c : ℕ) (L : LocalList m) : ℕ :=
  min (localCount C L 0)
    (c - localCount C L 1 - (m - localCount C L 0 - localCount C L 1 - localCount C L 2))

theorem measurable_ownResidual {m : ℕ} (C : Classifier) (c : ℕ) :
    Measurable (ownResidual (m := m) C c) := by
  exact (measurable_of_countable (fun z : ℕ × (ℕ × ℕ) => min z.1 (c-z.2.1-z.2.2))).comp
    ((measurable_localCount C 0).prodMk
      ((measurable_localCount C 1).prodMk (measurable_localCount C 2)))

theorem measurable_otherResidual {m : ℕ} (C : Classifier) (c : ℕ) :
    Measurable (otherResidual (m := m) C c) := by
  exact (measurable_of_countable
    (fun z : ℕ × (ℕ × ℕ) => min z.1 (c-z.2.1-(m-z.1-z.2.1-z.2.2)))).comp
    ((measurable_localCount C 0).prodMk
      ((measurable_localCount C 1).prodMk (measurable_localCount C 2)))

theorem residuals_correct {m : ℕ} (C : Classifier) (c : ℕ) (kind : Fin m → Fin 3)
    (x : Realization m 2) (hc : Correct C kind x) (hr : Routes kind x) (j : Fin 2) :
    ownResidual C c (observe x j) =
      min (countKind kind 0) (c-countKind kind 1-privateAt kind x j) ∧
    otherResidual C c (observe x j) =
      min (countKind kind 0) (c-countKind kind 1-privateAt kind x (other j)) := by
  obtain ⟨hl, ha, hh⟩ := local_counts_correct C kind x hc hr j
  constructor
  · simp only [ownResidual, hl, ha, hh]
  · unfold otherResidual
    rw [←reconstruct_other_private C kind x hc hr j, hl, ha]

def SameLowObservation {m : ℕ} (C D : Classifier)
    (x y : Realization m 2) : Prop :=
  (∀ i, x.recipients i = y.recipients i) ∧
  (∀ i, C.label (x.action i).bid = D.label (y.action i).bid) ∧
  (∀ i, C.label (x.action i).bid = 0 → (x.action i).bid = (y.action i).bid)

theorem same_observed_tags {m : ℕ} (C D : Classifier)
    (x y : Realization m 2) (h : SameLowObservation C D x y) (j : Fin 2) (i : Fin m) :
    tag C (observe x j i) = tag D (observe y j i) := by
  by_cases hi : j ∈ x.recipients i
  · have hy : j ∈ y.recipients i := by simpa only [←h.1 i] using hi
    simp only [observe, if_pos hi, if_pos hy, tag, h.2.1 i]
  · have hy : j ∉ y.recipients i := by simpa only [←h.1 i] using hi
    simp only [observe, if_neg hi, if_neg hy, tag]

theorem same_observed_counts {m : ℕ} (C D : Classifier)
    (x y : Realization m 2) (h : SameLowObservation C D x y) (j : Fin 2) (k : Fin 4) :
    localCount C (observe x j) k = localCount D (observe y j) k := by
  unfold localCount
  apply Finset.sum_congr rfl
  intro i _
  rw [same_observed_tags C D x y h j i]

theorem same_observed_low_list {m : ℕ} (C D : Classifier)
    (x y : Realization m 2) (h : SameLowObservation C D x y) (j : Fin 2) :
    part C 0 (observe x j) = part D 0 (observe y j) := by
  classical
  funext i
  have ht := same_observed_tags C D x y h j i
  by_cases hi : j ∈ x.recipients i
  · have hy : j ∈ y.recipients i := by simpa only [←h.1 i] using hi
    by_cases hk : C.label (x.action i).bid = 0
    · have hb := h.2.2 i hk
      have hk' : D.label (y.action i).bid = 0 := (h.2.1 i).symm.trans hk
      have hc' : C.label (y.action i).bid = 0 := by rw [←hb]; exact hk
      simp [part, observe, hi, hy, tag, hk', hc', hb]
    · have hk' : D.label (y.action i).bid ≠ 0 := by
        intro hh
        exact hk ((h.2.1 i).trans hh)
      simp [part, observe, hi, hy, tag, hk, hk']
  · have hy : j ∉ y.recipients i := by simpa only [←h.1 i] using hi
    simp [part, observe, hi, hy, tag]

theorem same_decoded_low_data {m : ℕ} (C D : Classifier) (c : ℕ)
    (x y : Realization m 2) (h : SameLowObservation C D x y) (j : Fin 2) :
    part C 0 (observe x j) = part D 0 (observe y j) ∧
    ownResidual C c (observe x j) = ownResidual D c (observe y j) ∧
    otherResidual C c (observe x j) = otherResidual D c (observe y j) := by
  refine ⟨same_observed_low_list C D x y h j, ?_, ?_⟩
  · simp only [ownResidual, same_observed_counts C D x y h j]
  · simp only [otherResidual, same_observed_counts C D x y h j]

theorem ae_information {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (C : Classifier) (c : ℕ) (kind : Ω → Fin m → Fin 3)
    (x : Ω → Realization m 2)
    (h : ∀ᵐω ∂μ, Correct C (kind ω) (x ω) ∧ Routes (kind ω) (x ω)) :
    ∀ᵐω ∂μ, ∀j : Fin 2,
      localCount C (observe (x ω) j) 0 = countKind (kind ω) 0 ∧
      localCount C (observe (x ω) j) 1 = countKind (kind ω) 1 ∧
      localCount C (observe (x ω) j) 2 = privateAt (kind ω) (x ω) j ∧
      otherResidual C c (observe (x ω) j) =
        min (countKind (kind ω) 0)
          (c-countKind (kind ω) 1-privateAt (kind ω) (x ω) (other j)) := by
  filter_upwards [h] with ω hω
  intro j
  obtain ⟨hl, ha, hh⟩ := local_counts_correct C (kind ω) (x ω) hω.1 hω.2 j
  exact ⟨hl, ha, hh, (residuals_correct C c (kind ω) (x ω) hω.1 hω.2 j).2⟩

theorem posterior_residual {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (ν : Measure Ω) (C : Classifier) (c : ℕ) (j : Fin 2) (L : LocalList m)
    (kind : Ω → Fin m → Fin 3) (x : Ω → Realization m 2)
    (h : ∀ᵐω ∂ν, Correct C (kind ω) (x ω) ∧ Routes (kind ω) (x ω) ∧ observe (x ω) j = L) :
    ∀ᵐω ∂ν,
      min (countKind (kind ω) 0)
        (c-countKind (kind ω) 1-privateAt (kind ω) (x ω) (other j)) =
      otherResidual C c L := by
  filter_upwards [h] with ω hω
  have hr := (residuals_correct C c (kind ω) (x ω) hω.1 hω.2.1 j).2
  rw [hω.2.2] at hr
  exact hr.symm

def intervalClassifier (d L U : ℝ) : Classifier where
  label b := if b ≤ d then 0 else if b ∈ Icc L U then 1 else 2
  measurable_label := Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Icc measurable_const measurable_const)

def privateUnion (R P U : ℝ) : Set ℝ := Icc R P ∪ Ioi U

theorem measurableSet_privateUnion (R P U : ℝ) : MeasurableSet (privateUnion R P U) :=
  measurableSet_Icc.union measurableSet_Ioi

theorem intervalClassifier_low {d L U b : ℝ} (hb : b ≤ d) :
    (intervalClassifier d L U).label b = 0 := by
  simp [intervalClassifier, hb]

theorem intervalClassifier_active {d L U b : ℝ} (hdL : d < L) (hb : b ∈ Icc L U) :
    (intervalClassifier d L U).label b = 1 := by
  have hbd : ¬ b ≤ d := not_le.mpr (hdL.trans_le hb.1)
  simp [intervalClassifier, hbd, hb.1, hb.2]

theorem intervalClassifier_private {d R P L U b : ℝ}
    (hdR : d < R) (hRP : R ≤ P) (hPL : P < L) (hLU : L ≤ U)
    (hb : b ∈ privateUnion R P U) :
    (intervalClassifier d L U).label b = 2 := by
  rcases hb with hb | hb
  · have hbd : ¬ b ≤ d := not_le.mpr (hdR.trans_le hb.1)
    have hba : b ∉ Icc L U := fun hx => (not_le.mpr hPL) (hx.1.trans hb.2)
    simp only [intervalClassifier, if_neg hbd, if_neg hba]
  · have hbd : ¬ b ≤ d := by
      have hdU : d < U := ((hdR.trans_le hRP).trans hPL).trans_le hLU
      exact not_le.mpr (hdU.trans hb)
    have hba : b ∉ Icc L U := fun hx => (not_le.mpr hb) hx.2
    simp only [intervalClassifier, if_neg hbd, if_neg hba]

theorem intervalClassifier_correct {m : ℕ} (kind : Fin m → Fin 3)
    (x : Realization m 2) {d R P L U : ℝ}
    (hdR : d < R) (hRP : R ≤ P) (hPL : P < L) (hLU : L ≤ U)
    (hboxes : ∀ i,
      (kind i = 0 → (x.action i).bid ≤ d) ∧
      (kind i = 1 → (x.action i).bid ∈ Icc L U) ∧
      (kind i = 2 → (x.action i).bid ∈ privateUnion R P U)) :
    Correct (intervalClassifier d L U) kind x := by
  intro i
  rcases hk : kind i with ⟨k, hklt⟩
  interval_cases k
  · exact intervalClassifier_low ((hboxes i).1 (by simp [hk]))
  · exact intervalClassifier_active ((hdR.trans_le hRP).trans hPL)
      ((hboxes i).2.1 (by simp [hk]))
  · exact intervalClassifier_private hdR hRP hPL hLU
      ((hboxes i).2.2 (by simp [hk]))

theorem upperFloor_subset_privateUnion {R P U Rm : ℝ} (hUR : U < Rm) :
    Ici Rm ⊆ privateUnion R P U := by
  intro b hb
  exact Or.inr (hUR.trans_le hb)

theorem measurable_market_classifier (d L : ℝ) (U : ℕ → ℝ) (m : ℕ) :
    Measurable (intervalClassifier d L (U m)).label :=
  (intervalClassifier d L (U m)).measurable_label

def thresholdClassifier (d U : ℝ) : Classifier where
  label b := if b ≤ d then 0 else if b ≤ U then 1 else 2
  measurable_label := Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

theorem threshold_tag_eq (d U : ℝ) (b : Option ℝ) :
    tag (thresholdClassifier d U) b = Affine.TaggedLocal.tag d U b := by
  cases b with
  | none => rfl
  | some b =>
      by_cases hd : b ≤ d
      · simp [tag, thresholdClassifier, Affine.TaggedLocal.tag, hd]
      · by_cases hU : b ≤ U
        · simp [tag, thresholdClassifier, Affine.TaggedLocal.tag, hd, hU]
        · simp [tag, thresholdClassifier, Affine.TaggedLocal.tag, hd, hU]

theorem threshold_correct {m : ℕ} (kind : Fin m → Fin 3)
    (x : Realization m 2) {d U : ℝ} (hdU : d ≤ U)
    (hb : Affine.TaggedLocal.BidBoxes kind x d U) :
    Correct (thresholdClassifier d U) kind x := by
  intro i
  have ht := Affine.TaggedLocal.tag_of_boxes hdU hb i
  rw [←threshold_tag_eq d U (some (x.action i).bid)] at ht
  change ((thresholdClassifier d U).label (x.action i).bid).castSucc = (kind i).castSucc at ht
  apply Fin.ext
  exact congrArg (fun q : Fin 4 => q.val) ht

theorem threshold_counts_eq {m : ℕ} (d U : ℝ) (L : LocalList m) (k : Fin 4) :
    localCount (thresholdClassifier d U) L k = Affine.TaggedLocal.localCount d U L k := by
  unfold localCount Affine.TaggedLocal.localCount
  apply Finset.sum_congr rfl
  intro i _
  rw [threshold_tag_eq]

theorem threshold_low_part_eq {m : ℕ} (d U : ℝ) (L : LocalList m) :
    part (thresholdClassifier d U) 0 L = Affine.TaggedLocal.lowList d U L := by
  funext i
  simp only [part, Affine.TaggedLocal.lowList, threshold_tag_eq]

end FCAppendix.Appendix08.Information
