import FCAppendix.Affine.Tail04.LocalCoordinates
import FCAppendix.Affine.Tail04.LowResidualCompletion
import FCAppendix.Proposer.LotterySupport

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon
open LocalCoordinates SortedCoordinates JoinedHighPolicy

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

abbrev PublicInput (m N : ℕ) (U : ℝ) :=
  LocalList m × (TypicalGuard.BidBox N U × (ℕ×ℕ))

abbrev Seed := unitInterval × unitInterval

def seedLaw : Measure Seed := (volume : Measure unitInterval).prod volume
instance seedLaw_probability : IsProbabilityMeasure seedLaw := by
  unfold seedLaw
  infer_instance

structure Data (m c : ℕ) where
  E : Observable.Regions
  ξ : ℝ
  width : ℝ
  π : ℝ
  xi_pos : 0< ξ
  xi_lt_one : ξ<1
  width_pos : 0< width
  pi_nonneg : 0≤ π
  rare_upper : (1-ξ)*E.U+ξ*E.U*((m:ℝ)*π)≤ E.R
  duplicate_below_active : (1-ξ)*E.U<1
  originalPrivateRow : (H : Fin (m+1)) → ProbabilityMeasure (Row H.val E.R E.Rp E.H)
  any_upper : ∀ H, (AtypicalOriginalPosterior.markLaw (originalPrivateRow H : Measure (Row H.val E.R E.Rp E.H))).prob
    AtypicalOriginalPosterior.anyUpper ≤ (H.val:ℝ)*π
  publicChoice : ∀ N, PublicInput m N E.U → Scenario N × unitInterval
  publicChoice_measurable : ∀ N, Measurable (publicChoice N)

namespace Data
variable {m c : ℕ} (D : Data m c)

def marksLaw (H : Fin (m+1)) : FiniteLaw (Marks H.val) :=
  AtypicalOriginalPosterior.markLaw (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H))

def signalLaw (H : Fin (m+1)) : WeakProbability.Law (Signal H.val D.E.R D.E.Rp) :=
  ⟨(D.originalPrivateRow H).map continuous_signal.measurable.aemeasurable⟩

lemma signalLaw_exact (H : Fin (m+1)) :
    (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H)).map signal=WeakProbability.toMeasure (D.signalLaw H) := by
  rfl

lemma marksLaw_exact (H : Fin (m+1)) :
    (D.originalPrivateRow H : Measure (Row H.val D.E.R D.E.Rp D.E.H)).map (fun row => marks (signal row))=
      FiniteLaw.probabilityMeasure (D.marksLaw H) :=
  (FiniteLaw.probabilityMeasure_ofMeasure _ _ AtypicalOriginalPosterior.continuous_rowMarks.measurable).symm

lemma rare_upper_at (H : Fin (m+1)) :
    (1-D.ξ)*D.E.U+D.ξ*D.E.U*((H.val:ℝ)*D.π)≤ D.E.R := by
  have hH : (H.val:ℝ)≤(m:ℝ) := by exact_mod_cast (show H.val≤ m by omega)
  have hU : 0≤ D.E.U := (by norm_num : (0:ℝ)≤1).trans D.E.one_le_U
  exact (add_le_add (le_refl ((1-D.ξ)*D.E.U)) (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hH D.pi_nonneg) (mul_nonneg D.xi_pos.le hU))).trans D.rare_upper

def equalSampler (N : ℕ) (H : Fin (m+1)) :
    (Parameters N H.val D.E.R D.E.Rp D.E.U × Row H.val D.E.R D.E.Rp D.E.H) →
      unitInterval → Finset (Target N H.val) :=
  AllCountHighPolicy.equalSample N H.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ (D.E.d_nonneg.trans D.E.d_lt_R.le)
    (D.E.Rp_lt_one.le.trans D.E.one_le_U) D.E.U_lt_H
    (((by norm_num : (0:ℝ)<1).trans_le D.E.one_le_U).trans D.E.U_lt_H)

def zeroSampler (N : ℕ) (H0 H1 : Fin (m+1)) :
    (Parameters N H0.val D.E.R D.E.Rp D.E.U × Row H0.val D.E.R D.E.Rp D.E.H) →
      unitInterval → Finset (Target N H0.val) :=
  if H0=H1 then D.equalSampler N H0
  else unequal0 N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width
    (D.marksLaw H0) (D.marksLaw H1)

def oneSampler (N : ℕ) (H0 H1 : Fin (m+1)) :
    (Parameters N H0.val D.E.R D.E.Rp D.E.U × Row H1.val D.E.R D.E.Rp D.E.H) →
      unitInterval → Finset (Target N H1.val) := by
  by_cases he : H0=H1
  · subst H1
    exact D.equalSampler N H0
  · exact unequal1 N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width
      (D.marksLaw H0) (D.marksLaw H1)

lemma zeroSampler_unequal (N : ℕ) (H0 H1 : Fin (m+1)) (h : H0≠H1) :
    D.zeroSampler N H0 H1=unequal0 N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
      D.width (D.marksLaw H0) (D.marksLaw H1) := by simp [zeroSampler,h]

lemma oneSampler_unequal (N : ℕ) (H0 H1 : Fin (m+1)) (h : H0≠H1) :
    D.oneSampler N H0 H1=unequal1 N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
      D.width (D.marksLaw H0) (D.marksLaw H1) := by simp [oneSampler,h]

lemma zeroSampler_equal (N : ℕ) (H : Fin (m+1)) :
    D.zeroSampler N H H=D.equalSampler N H := by simp [zeroSampler]

lemma oneSampler_equal (N : ℕ) (H : Fin (m+1)) :
    D.oneSampler N H H=D.equalSampler N H := by simp [oneSampler]

lemma equalSampler_measurable (N : ℕ) (H : Fin (m+1)) :
    Measurable (Function.uncurry (D.equalSampler N H)) :=
  AllCountHighPolicy.equal_measurable N H.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ (D.E.d_nonneg.trans D.E.d_lt_R.le)
    (D.E.Rp_lt_one.le.trans D.E.one_le_U) D.E.U_lt_H
    (((by norm_num : (0:ℝ)<1).trans_le D.E.one_le_U).trans D.E.U_lt_H)

lemma zeroSampler_measurable (N : ℕ) (H0 H1 : Fin (m+1)) :
    Measurable (Function.uncurry (D.zeroSampler N H0 H1)) := by
  by_cases he : H0=H1
  · subst H1
    rw [D.zeroSampler_equal]
    exact D.equalSampler_measurable N H0
  · rw [D.zeroSampler_unequal N H0 H1 he]
    exact measurable_unequal0 _ _ _ _ _ _ _ _ _ _ _ _

lemma oneSampler_measurable (N : ℕ) (H0 H1 : Fin (m+1)) :
    Measurable (Function.uncurry (D.oneSampler N H0 H1)) := by
  by_cases he : H0=H1
  · subst H1
    rw [D.oneSampler_equal]
    exact D.equalSampler_measurable N H0
  · rw [D.oneSampler_unequal N H0 H1 he]
    exact measurable_unequal1 _ _ _ _ _ _ _ _ _ _ _ _

lemma equalSampler_capacity (N : ℕ) (H : Fin (m+1))
    (p : Parameters N H.val D.E.R D.E.Rp D.E.U) (row : Row H.val D.E.R D.E.Rp D.E.H)
    (u : unitInterval) : (D.equalSampler N H (p,row) u).card≤ c :=
  AllCountHighPolicy.equal_capacity N H.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
    ⟨D.xi_pos.le,D.xi_lt_one.le⟩ (D.E.d_nonneg.trans D.E.d_lt_R.le)
    (D.E.Rp_lt_one.le.trans D.E.one_le_U) D.E.U_lt_H
    (((by norm_num : (0:ℝ)<1).trans_le D.E.one_le_U).trans D.E.U_lt_H) p row u

lemma zeroSampler_capacity (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (row : Row H0.val D.E.R D.E.Rp D.E.H)
    (u : unitInterval) : (D.zeroSampler N H0 H1 (p,row) u).card≤ c := by
  by_cases he : H0=H1
  · subst H1
    rw [D.zeroSampler_equal]
    exact D.equalSampler_capacity N H0 p row u
  · rw [D.zeroSampler_unequal N H0 H1 he]
    exact unequal0_capacity _ _ _ _ _ _ _ _ _ _ _ _ D.xi_pos D.xi_lt_one.le D.width_pos p row u

lemma oneSampler_capacity (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (row : Row H1.val D.E.R D.E.Rp D.E.H)
    (u : unitInterval) : (D.oneSampler N H0 H1 (p,row) u).card≤ c := by
  by_cases he : H0=H1
  · subst H1
    rw [D.oneSampler_equal]
    exact D.equalSampler_capacity N H0 p row u
  · rw [D.oneSampler_unequal N H0 H1 he]
    exact unequal1_capacity _ _ _ _ _ _ _ _ _ _ _ _ D.xi_pos D.xi_lt_one.le D.width_pos p row u

lemma original_row_compatibility (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (hp : p.2.1=D.signalLaw H0) :
    AllCountHighPolicy.OriginalRowCompatibility N H0.val H1.val D.E.R D.E.Rp D.E.H D.E.U
      (D.marksLaw H0) (D.marksLaw H1) p (D.originalPrivateRow H0) (D.originalPrivateRow H1) := by
  by_cases hh : H0.val=H1.val
  · have he : H0=H1 := Fin.ext hh
    subst H1
    simp only [AllCountHighPolicy.OriginalRowCompatibility,hp]
    refine ⟨D.signalLaw_exact H0,?_⟩
    convert! D.signalLaw_exact H0 using 1
  · simp only [AllCountHighPolicy.OriginalRowCompatibility,dif_neg hh]
    exact ⟨D.marksLaw_exact H0,D.marksLaw_exact H1⟩

theorem original_high_optimal (N : ℕ) (H0 H1 : Fin (m+1))
    (p : Parameters N H0.val D.E.R D.E.Rp D.E.U) (hp : p.2.1=D.signalLaw H0) :
    (∀ row u, Finite.Optimal c
      (receipt (publicBids p)
        (fun i => LocalSamplerMean.mean (D.oneSampler N H0 H1) p (D.originalPrivateRow H1) (Sum.inl i)) D.ξ row)
      (D.zeroSampler N H0 H1 (p,row) u)) ∧
    (∀ row u, Finite.Optimal c
      (receipt (publicBids p)
        (fun i => LocalSamplerMean.mean (D.zeroSampler N H0 H1) p (D.originalPrivateRow H0) (Sum.inl i)) D.ξ row)
      (D.oneSampler N H0 H1 (p,row) u)) :=
by
  by_cases he : H0=H1
  · subst H1
    rw [D.zeroSampler_equal,D.oneSampler_equal]
    have hl : (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)).map signal=WeakProbability.toMeasure p.2.1 := by
      rw [hp]
      exact D.signalLaw_exact H0
    have ho := AllCountHighPolicy.equal_original_optimal N H0.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H
      ⟨D.xi_pos.le,D.xi_lt_one.le⟩ (D.E.d_nonneg.trans D.E.d_lt_R.le)
      (D.E.Rp_lt_one.le.trans D.E.one_le_U) D.E.U_lt_H
      (((by norm_num : (0:ℝ)<1).trans_le D.E.one_le_U).trans D.E.U_lt_H)
      p (D.originalPrivateRow H0 : Measure (Row H0.val D.E.R D.E.Rp D.E.H)) hl
    exact ⟨ho,ho⟩
  · rw [D.zeroSampler_unequal N H0 H1 he,D.oneSampler_unequal N H0 H1 he]
    exact ⟨unequal0_optimal N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width D.π
      (D.marksLaw H0) (D.marksLaw H1) D.xi_pos D.xi_lt_one.le D.E.one_le_U
      D.width_pos D.pi_nonneg (D.E.d_nonneg.trans_lt D.E.d_lt_R) D.E.R_le_Rp D.E.Rp_lt_one D.E.U_lt_H
      (D.rare_upper_at H1) D.duplicate_below_active (D.any_upper H1)
      p (D.originalPrivateRow H1) (D.marksLaw_exact H1),
      unequal1_optimal N H0.val H1.val c D.ξ D.E.U D.E.R D.E.Rp D.E.H D.width D.π
      (D.marksLaw H0) (D.marksLaw H1) D.xi_pos D.xi_lt_one.le D.E.one_le_U
      D.width_pos D.pi_nonneg (D.E.d_nonneg.trans_lt D.E.d_lt_R) D.E.R_le_Rp D.E.Rp_lt_one D.E.U_lt_H
      (D.rare_upper_at H0) D.duplicate_below_active (D.any_upper H0)
      p (D.originalPrivateRow H0) (D.marksLaw_exact H0)⟩

def finiteCount (_D : Data m c) (P : Finset (Fin m)) : Fin (m+1) :=
  ⟨P.card,by have h:=Finset.card_le_univ P;simp only [Fintype.card_fin] at h;omega⟩

def parameter (A : Finset (Fin m)) (H0 H1 : Fin (m+1)) (L : LocalList m) :
    Parameters A.card H0.val D.E.R D.E.Rp D.E.U :=
  let b := LocalCoordinates.activeBids D.E A L
  let q := D.publicChoice A.card (D.E.roleList 0 L,(b,(H0.val,H1.val)))
  ((q.1,b),(D.signalLaw H0,q.2))

lemma parameter_measurable (A : Finset (Fin m)) (H0 H1 : Fin (m+1)) :
    Measurable (D.parameter A H0 H1) := by
  let input : LocalList m → PublicInput m A.card D.E.U := fun L =>
    (D.E.roleList 0 L,(LocalCoordinates.activeBids D.E A L,(H0.val,H1.val)))
  have hi : Measurable input := (D.E.measurable_roleList 0).prodMk
    ((LocalCoordinates.measurable_activeBids D.E A).prodMk measurable_const)
  have hq := (D.publicChoice_measurable A.card).comp hi
  exact (hq.fst.prodMk (LocalCoordinates.measurable_activeBids D.E A)).prodMk
    (measurable_const.prodMk hq.snd)

lemma parameter_signal (A : Finset (Fin m)) (H0 H1 : Fin (m+1)) (L : LocalList m) :
    (D.parameter A H0 H1 L).2.1=D.signalLaw H0 := rfl

def highAtKey (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (u : unitInterval) : Finset (Fin m) :=
  if hAP : Disjoint K.1.1 K.1.2 then
    if j=0 then
      transport K.1.1 K.1.2 hAP (bidVector L) (privateKey D.E L)
        (D.zeroSampler K.1.1.card (D.finiteCount K.1.2) K.2
          (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L,privateRow D.E K.1.2 L) u)
    else
      transport K.1.1 K.1.2 hAP (bidVector L) (privateKey D.E L)
        (D.oneSampler K.1.1.card K.2 (D.finiteCount K.1.2)
          (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L,privateRow D.E K.1.2 L) u)
  else ∅

lemma highAtKey_measurable (j : Fin 2) (K : LocalCoordinates.Key m) :
    Measurable (Function.uncurry (D.highAtKey j K)) := by
  change Measurable (fun z : LocalList m × unitInterval => D.highAtKey j K z.1 z.2)
  by_cases hd : Disjoint K.1.1 K.1.2
  · by_cases hj : j=0
    · simp only [highAtKey,dif_pos hd,if_pos hj]
      apply measurable_transport K.1.1 K.1.2 hd
        (fun z : LocalList m×unitInterval => bidVector z.1)
        (fun z => privateKey D.E z.1)
        (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
        (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst))
      exact (D.zeroSampler_measurable K.1.1.card (D.finiteCount K.1.2) K.2).comp
        ((((D.parameter_measurable K.1.1 (D.finiteCount K.1.2) K.2).comp measurable_fst).prodMk
          ((measurable_privateRow D.E K.1.2).comp measurable_fst)).prodMk measurable_snd)
    · simp only [highAtKey,dif_pos hd,if_neg hj]
      apply measurable_transport K.1.1 K.1.2 hd
        (fun z : LocalList m×unitInterval => bidVector z.1)
        (fun z => privateKey D.E z.1)
        (fun i => (measurable_pi_apply i).comp (measurable_bidVector.comp measurable_fst))
        (fun i => (measurable_pi_apply i).comp ((measurable_privateKey D.E).comp measurable_fst))
      exact (D.oneSampler_measurable K.1.1.card K.2 (D.finiteCount K.1.2)).comp
        ((((D.parameter_measurable K.1.1 K.2 (D.finiteCount K.1.2)).comp measurable_fst).prodMk
          ((measurable_privateRow D.E K.1.2).comp measurable_fst)).prodMk measurable_snd)
  · simpa only [highAtKey,dif_neg hd] using
      (measurable_const : Measurable (fun _ : LocalList m×unitInterval => (∅ : Finset (Fin m))))

lemma highAtKey_capacity (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (u : unitInterval) : (D.highAtKey j K L u).card≤ c := by
  unfold highAtKey
  split_ifs with hd hj
  · rw [transport_card]
    convert! D.zeroSampler_capacity K.1.1.card
      (D.finiteCount K.1.2) K.2 (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L)
      (privateRow D.E K.1.2 L) u using 1
  · rw [transport_card]
    convert! D.oneSampler_capacity K.1.1.card
      K.2 (D.finiteCount K.1.2) (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L)
      (privateRow D.E K.1.2 L) u using 1
  · simp

lemma highAtKey_subset (j : Fin 2) (K : LocalCoordinates.Key m) (L : LocalList m)
    (u : unitInterval) : D.highAtKey j K L u⊆K.1.1∪K.1.2 := by
  unfold highAtKey
  split_ifs <;> first | exact transport_subset _ _ _ _ _ _ | exact Finset.empty_subset _

def high (j : Fin 2) (L : LocalList m) (u : unitInterval) : Finset (Fin m) :=
  D.highAtKey j (LocalCoordinates.key D.E L) L u

lemma high_measurable (j : Fin 2) : Measurable (Function.uncurry (D.high j)) := by
  have h : Measurable (fun z : LocalCoordinates.Key m×(LocalList m×unitInterval) =>
      D.highAtKey j z.1 z.2.1 z.2.2) :=
    measurable_from_prod_countable_right (D.highAtKey_measurable j)
  exact h.comp (((measurable_key D.E).comp measurable_fst).prodMk measurable_id)

lemma high_capacity (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    (D.high j L u).card≤ c := D.highAtKey_capacity j _ L u

lemma high_subset (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    D.high j L u⊆ids D.E 1 L∪ids D.E 2 L := D.highAtKey_subset j _ L u

lemma high_card_le_count (j : Fin 2) (L : LocalList m) (u : unitInterval) :
    (D.high j L u).card≤ D.E.localCount L 1+D.E.localCount L 2 := by
  calc
    _ ≤ (ids D.E 1 L∪ids D.E 2 L).card := Finset.card_le_card (D.high_subset j L u)
    _ = _ := by rw [Finset.card_union_of_disjoint (ids_disjoint D.E (by decide) L),ids_card,ids_card]

lemma high_present (j : Fin 2) (L : LocalList m) (u : unitInterval) (i : Fin m)
    (hi : i∈D.high j L u) : L i≠none := by
  rcases Finset.mem_union.mp (D.high_subset j L u hi) with hi | hi
  · exact ids_present D.E 1 (by decide) L i hi
  · exact ids_present D.E 2 (by decide) L i hi

def selection (j : Fin 2) (L : LocalList m) (u : Seed) : Finset (Fin m) :=
  D.high j L u.1 ∪ Observable.Regions.lowSelect D.E
    D.ξ D.xi_pos D.xi_lt_one c j L u.2

lemma selection_capacity (j : Fin 2) (L : LocalList m) (u : Seed) :
    (D.selection j L u).card≤ c := by
  have hh := D.high_capacity j L u.1
  have hn := D.high_card_le_count j L u.1
  have hl := (Observable.Regions.lowSelect_feasible D.E
    D.ξ D.xi_pos D.xi_lt_one c j L u.2).1
  have hu := Finset.card_union_le (D.high j L u.1)
    (Observable.Regions.lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j L u.2)
  change (D.high j L u.1 ∪ Observable.Regions.lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j L u.2).card ≤ c
  omega

lemma selection_present (j : Fin 2) (L : LocalList m) (u : Seed) (i : Fin m)
    (hi : i∈D.selection j L u) : L i≠none := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact D.high_present j L u.1 i hi
  · exact (Observable.Regions.lowSelect_present D.E
      D.ξ D.xi_pos D.xi_lt_one c j L u.2 i hi).1

def policy (j : Fin 2) : LocalPolicy m c Seed :=
  fun L u => ⟨D.selection j L u,D.selection_capacity j L u,D.selection_present j L u⟩

lemma policy_measurable (j : Fin 2) :
    Measurable (fun z : LocalList m×Seed => (D.policy j z.1 z.2).val) := by
  change Measurable (fun z : LocalList m × Seed =>
    D.high j z.1 z.2.1 ∪ Observable.Regions.lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j z.1 z.2.2)
  have hh := (D.high_measurable j).comp
    (show Measurable (fun z : LocalList m × Seed => (z.1,z.2.1)) from
      measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hl := (Observable.Regions.measurable_lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j).comp
    (show Measurable (fun z : LocalList m × Seed => (z.1,z.2.2)) from
      measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h := (measurable_of_countable (fun z : Finset (Fin m) × Finset (Fin m) => z.1∪z.2)).comp
    (hh.prodMk hl)
  simpa only [Function.comp_def,Function.uncurry] using h

lemma high_low_disjoint (j : Fin 2) (L : LocalList m) (u : Seed) :
    Disjoint (D.high j L u.1)
      (Observable.Regions.lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j L u.2) := by
  apply Finset.disjoint_left.mpr
  intro i hi hl
  have ht := (Observable.Regions.lowSelect_present D.E
    D.ξ D.xi_pos D.xi_lt_one c j L u.2 i hl).2
  rcases Finset.mem_union.mp (D.high_subset j L u.1 hi) with hi | hi <;>
    have hh := (Finset.mem_filter.mp hi).2 <;> simp_all

lemma policy_low_iff (j : Fin 2) (L : LocalList m) (u : Seed) (i : Fin m)
    (hi : D.E.localTag (L i)=0) :
    i∈(D.policy j L u).val ↔
      i∈Observable.Regions.lowSelect D.E D.ξ D.xi_pos D.xi_lt_one c j L u.2 := by
  have hh : i∉D.high j L u.1 := by
    intro h
    rcases Finset.mem_union.mp (D.high_subset j L u.1 h) with h | h <;>
      have ht := (Finset.mem_filter.mp h).2 <;> simp_all
  simp [policy,selection,hh]

lemma policy_high_iff (j : Fin 2) (L : LocalList m) (u : Seed) (i : Fin m)
    (hi : D.E.localTag (L i)≠0) : i∈(D.policy j L u).val ↔ i∈D.high j L u.1 := by
  have hl : i∉Observable.Regions.lowSelect D.E
      D.ξ D.xi_pos D.xi_lt_one c j L u.2 := by
    intro h
    exact hi (Observable.Regions.lowSelect_present D.E
      D.ξ D.xi_pos D.xi_lt_one c j L u.2 i h).2
  simp [policy,selection,hl]

end Data
end FCAppendix.Affine.Tail04.NativeLocalPolicy
