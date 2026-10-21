import FCAppendix.Affine.Tail04.NativeHighReceipts

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon LocalCoordinates SortedCoordinates JoinedHighPolicy
open FCAppendix.Affine.Hybrid
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : NativeLocalPolicy.Data m c)

lemma lowAcceptance_bounds (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) :
    NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c j X i∈Icc (0:ℝ) 1 := by
  have hm : Measurable (fun u : unitInterval =>
      if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X u then (1:ℝ) else 0) :=
    (measurable_of_countable (fun S : Finset (Fin m) => if i∈S then (1:ℝ) else 0)).comp
      ((NativeExactLow.measurable_select D.ξ D.xi_pos D.xi_lt_one c j).comp
        (measurable_const.prodMk measurable_id))
  have hi : Integrable (fun u : unitInterval =>
      if i∈NativeExactLow.select D.ξ D.xi_pos D.xi_lt_one c j X u then (1:ℝ) else 0) volume :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun u => by split_ifs <;> norm_num)
  constructor
  · exact integral_nonneg (fun u => by dsimp only; split_ifs <;> norm_num)
  · calc
      _ ≤ ∫ _u : unitInterval,(1:ℝ) ∂volume :=
        integral_mono_ae hi (integrable_const _) (ae_of_all _ fun u => by dsimp only; split_ifs <;> norm_num)
      _ = 1 := by simp

def lowReceipt (j : Fin 2) (L : LocalList m) : Fin m → ℝ :=
  NativeExactLow.receipt D.ξ D.xi_pos D.xi_lt_one c j
    (Observable.Regions.lowContext D.E j L)

lemma lowReceipt_zero (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : D.E.localTag (L i)≠0) : D.lowReceipt j L i=0 := by
  simp [lowReceipt,NativeExactLow.receipt,
    Observable.Regions.lowContext,Observable.Regions.context,
    Observable.Regions.roleList,hi,entryBid]

lemma lowReceipt_bounds (j : Fin 2) (L : LocalList m) (hL : NonnegativeList L) (i : Fin m) :
    D.lowReceipt j L i∈Icc (0:ℝ) D.E.d := by
  let X := Observable.Regions.lowContext D.E j L
  have hX := Observable.Regions.lowContext_nonnegative D.E j L hL
  have hp := D.lowAcceptance_bounds (otherProposer j) X i
  have hb : entryBid (X.1 i)≤ D.E.d := by
    change entryBid (D.E.roleList 0 L i)≤ D.E.d
    by_cases ht : D.E.localTag (L i)=0
    · cases he : L i with
      | none => simpa [Observable.Regions.roleList,he,entryBid] using D.E.d_nonneg
      | some b =>
        have hh : b≤ D.E.d := by
          by_contra hn
          by_cases hp : b∈D.E.privateBids <;>
            simp [he,Observable.Regions.localTag,hn,hp] at ht
        have ht' : D.E.localTag (some b)=0 := by simpa only [he] using ht
        simpa only [Observable.Regions.roleList,he,if_pos ht',entryBid] using hh
    · simpa [Observable.Regions.roleList,ht,entryBid] using D.E.d_nonneg
  have hfac0 : 0≤1-D.ξ*NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c
      (otherProposer j) X i := by nlinarith [mul_le_mul_of_nonneg_left hp.2 D.xi_pos.le,D.xi_lt_one]
  have hfac1 : 1-D.ξ*NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c
      (otherProposer j) X i≤1 := by nlinarith [mul_nonneg D.xi_pos.le hp.1]
  exact ⟨mul_nonneg (hX i) hfac0,
    (mul_le_of_le_one_right (hX i) hfac1).trans hb⟩

def numericalReceipt (j : Fin 2) (L : LocalList m) (i : Fin m) : ℝ :=
  D.highReceipt j L i+D.lowReceipt j L i

lemma numericalReceipt_high (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L∪ids D.E 2 L) : D.numericalReceipt j L i=D.highReceipt j L i := by
  have ht : D.E.localTag (L i)≠0 := by
    rcases Finset.mem_union.mp hi with hi | hi <;>
      have hh := (Finset.mem_filter.mp hi).2 <;> simp [hh]
  simp [numericalReceipt,D.lowReceipt_zero j L i ht]

lemma numericalReceipt_low (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∉ids D.E 1 L∪ids D.E 2 L) : D.numericalReceipt j L i=D.lowReceipt j L i := by
  simp [numericalReceipt,D.highReceipt_zero j L i hi]

lemma high_mask (j : Fin 2) (L : LocalList m) :
    (fun i => if i∈ids D.E 1 L∪ids D.E 2 L then D.numericalReceipt j L i else 0)=
      D.highReceipt j L := by
  funext i
  by_cases hi : i∈ids D.E 1 L∪ids D.E 2 L
  · simp [hi,D.numericalReceipt_high j L i hi]
  · simp [hi,D.highReceipt_zero j L i hi]

lemma low_mask (j : Fin 2) (L : LocalList m) :
    (fun i => if i∈ids D.E 1 L∪ids D.E 2 L then 0 else D.numericalReceipt j L i)=
      D.lowReceipt j L := by
  funext i
  by_cases hi : i∈ids D.E 1 L∪ids D.E 2 L
  · have ht : D.E.localTag (L i)≠0 := by
      rcases Finset.mem_union.mp hi with hi | hi <;>
        have hh := (Finset.mem_filter.mp hi).2 <;> simp [hh]
    simp [hi,D.lowReceipt_zero j L i ht]
  · simp [hi,D.numericalReceipt_low j L i hi]

theorem numerical_optimal (hlow : D.E.d<1-D.ξ) (j : Fin 2) (L : LocalList m)
    (hL : NonnegativeList L) (u : NativeLocalPolicy.Seed) :
    Finite.Optimal c (D.numericalReceipt j L) ((D.policy j L u).val) := by
  let H := ids D.E 1 L∪ids D.E 2 L
  let T := Observable.Regions.lowSelect D.E
    D.ξ D.xi_pos D.xi_lt_one c j L u.2
  have hcard : H.card=D.E.localCount L 1+D.E.localCount L 2 := by
    rw [Finset.card_union_of_disjoint (ids_disjoint D.E (by decide) L),ids_card,ids_card]
  have hdisj : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro i hi ht
    have hlo := (Observable.Regions.lowSelect_present D.E
      D.ξ D.xi_pos D.xi_lt_one c j L u.2 i ht).2
    rcases Finset.mem_union.mp hi with hi | hi <;>
      have hh := (Finset.mem_filter.mp hi).2 <;> simp_all
  change Finite.Optimal c (D.numericalReceipt j L) (D.high j L u.1∪T)
  apply LowResidualCompletion.high_low_union_optimal c _ H _ T (D.high_subset j L u.1) hdisj
  · rw [D.high_mask]
    exact D.high_numerical_optimal j L u.1
  · rw [D.low_mask,hcard]
    exact Observable.Regions.lowSelect_optimal D.E D.ξ D.xi_pos D.xi_lt_one
      c j L hL u.2
  · intro i
    exact add_nonneg (D.highReceipt_nonneg j L i) (D.lowReceipt_bounds j L hL i).1
  · intro i hi
    rw [D.numericalReceipt_high j L i hi]
    exact (lt_min (by linarith [D.xi_lt_one])
      (D.E.d_nonneg.trans_lt D.E.d_lt_R)).trans_le (D.highReceipt_floor j L i hi)
  · intro i hi k hk
    rw [D.numericalReceipt_high j L i hi,D.numericalReceipt_low j L k hk]
    exact (D.lowReceipt_bounds j L hL k).2.trans
      ((le_min hlow.le D.E.d_lt_R.le).trans (D.highReceipt_floor j L i hi))

lemma numericalReceipt_private (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 2 L) : D.numericalReceipt j L i=entryBid (L i) := by
  rw [D.numericalReceipt_high j L i (Finset.mem_union_right _ hi),D.highReceipt_private j L i hi]

lemma numericalReceipt_active (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : i∈ids D.E 1 L) (hb : entryBid (L i)∈Icc (1:ℝ) D.E.U) :
    D.numericalReceipt j L i=entryBid (L i)*(1-D.ξ*D.oppositeActiveMean j L
      (rankFin (ids D.E 1 L) (bidVector L) ⟨i,hi⟩)) := by
  rw [D.numericalReceipt_high j L i (Finset.mem_union_left _ hi),D.highReceipt_active j L i hi hb]

lemma numericalReceipt_low_formula (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : D.E.localTag (L i)=0) :
    D.numericalReceipt j L i=entryBid (L i)*(1-D.ξ*
      NativeExactLow.acceptance D.ξ D.xi_pos D.xi_lt_one c (otherProposer j)
        (Observable.Regions.lowContext D.E j L) i) := by
  have hn : i∉ids D.E 1 L∪ids D.E 2 L := by simp [ids,hi]
  rw [D.numericalReceipt_low j L i hn]
  simp [lowReceipt,NativeExactLow.receipt,
    Observable.Regions.lowContext,Observable.Regions.context,
    Observable.Regions.roleList,hi]

lemma numericalReceipt_absent (j : Fin 2) (L : LocalList m) (i : Fin m)
    (hi : L i=none) : D.numericalReceipt j L i=0 := by
  have ht : D.E.localTag (L i)=3 := by simp [hi,Observable.Regions.localTag]
  have hn : i∉ids D.E 1 L∪ids D.E 2 L := by simp [ids,ht]
  simp [numericalReceipt,D.highReceipt_zero j L i hn,D.lowReceipt_zero j L i (by simp [ht])]

end FCAppendix.Affine.Tail04.NativeLocalPolicy.Data
