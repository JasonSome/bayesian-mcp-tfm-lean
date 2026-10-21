import FCAppendix.Affine.Tail04.EqualPrivateUpper

noncomputable section
namespace FCAppendix.Affine.Tail04.LocalHighCommon
open MeasureTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper

local instance (N H : ℕ) : TopologicalSpace (Finset (Target N H)) := ⊥
local instance (N H : ℕ) : DiscreteTopology (Finset (Target N H)) := ⟨rfl⟩
local instance (N H : ℕ) : MeasurableSpace (Finset (Target N H)) := ⊤
local instance (N H : ℕ) : BorelSpace (Finset (Target N H)) := ⟨borel_eq_top_of_discrete.symm⟩

def activeLift {N : ℕ} (H : ℕ) (A : Finset (Fin N)) : Finset (Target N H) :=
  A.image Sum.inl

def privateAll (N H : ℕ) : Finset (Target N H) :=
  Finset.univ.image Sum.inr

def activeAll (N H : ℕ) : Finset (Target N H) := activeLift H Finset.univ

def activePart {N H : ℕ} (S : Finset (Target N H)) : Finset (Fin N) :=
  Finset.univ.filter fun i => Sum.inl i ∈ S

@[simp] theorem inl_mem_activeLift {N H : ℕ} (A : Finset (Fin N)) (i : Fin N) :
    Sum.inl i ∈ activeLift H A ↔ i ∈ A := by simp [activeLift]

@[simp] theorem inr_not_mem_activeLift {N H : ℕ} (A : Finset (Fin N)) (j : Fin H) :
    Sum.inr j ∉ activeLift H A := by simp [activeLift]

@[simp] theorem inl_not_mem_privateAll {N H : ℕ} (i : Fin N) :
    Sum.inl i ∉ privateAll N H := by simp [privateAll]

@[simp] theorem inr_mem_privateAll {N H : ℕ} (j : Fin H) :
    Sum.inr j ∈ privateAll N H := by simp [privateAll]

@[simp] theorem activeLift_card {N H : ℕ} (A : Finset (Fin N)) :
    (activeLift H A).card=A.card :=
  Finset.card_image_of_injective _ Sum.inl_injective

@[simp] theorem privateAll_card (N H : ℕ) : (privateAll N H).card=H := by
  rw [privateAll,Finset.card_image_of_injective _ Sum.inr_injective]
  simp

@[simp] theorem activeAll_card (N H : ℕ) : (activeAll N H).card=N := by
  simp [activeAll]

theorem active_private_disjoint {N H : ℕ} (A : Finset (Fin N)) :
    Disjoint (activeLift H A) (privateAll N H) := by
  apply Finset.disjoint_left.mpr
  intro i hi hp
  cases i <;> simp_all

theorem active_private_cover (N H : ℕ) :
    activeAll N H ∪ privateAll N H = Finset.univ := by
  ext i
  cases i <;> simp [activeAll]

theorem activeLift_mono {N H : ℕ} {A B : Finset (Fin N)} (h : A ⊆ B) :
    activeLift H A ⊆ activeLift H B := Finset.image_subset_image h

theorem activeLift_disjoint {N H : ℕ} {A B : Finset (Fin N)}
    (h : Disjoint A B) : Disjoint (activeLift H A) (activeLift H B) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases i with
  | inl i => exact (Finset.disjoint_left.mp h) (by simpa using hi) (by simpa using hj)
  | inr j => simp at hi

theorem activePart_card_le {N H : ℕ} (S : Finset (Target N H)) :
    (activePart S).card ≤ S.card := by
  rw [← activeLift_card (H := H) (activePart S)]
  apply Finset.card_le_card
  intro i hi
  cases i with
  | inl i => simpa [activePart] using hi
  | inr j => simp at hi

theorem sum_activeLift {N H : ℕ} (A : Finset (Fin N)) (f : Target N H → ℝ) :
    (∑ i ∈ activeLift H A, f i) = ∑ i ∈ A, f (Sum.inl i) := by
  exact Finset.sum_image (fun i hi j hj hij => Sum.inl_injective hij)

theorem sum_zero_private {N H : ℕ} (S : Finset (Target N H)) (r : Fin N → ℝ) :
    (∑ i ∈ S, Sum.elim r (fun _ : Fin H => (0:ℝ)) i) =
      ∑ i ∈ activePart S, r i := by
  classical
  calc
    _ = ∑ i : Target N H, if i ∈ S then Sum.elim r (fun _ : Fin H => (0:ℝ)) i else 0 :=
      (by simpa only [Finset.univ_inter] using
        (Finset.sum_ite_mem Finset.univ S (Sum.elim r (fun _ : Fin H => (0:ℝ)))).symm)
    _ = (∑ i : Fin N, if Sum.inl i ∈ S then r i else 0) := by
      rw [Fintype.sum_sum_type]
      simp
    _ = _ := by simp [activePart,Finset.sum_filter]

theorem lift_optimal {N H r : ℕ} (b : Fin N → ℝ) (S : Finset (Fin N))
    (hS : Finite.Optimal r b S) :
    Finite.Optimal r (Sum.elim b (fun _ : Fin H => 0)) (activeLift H S) := by
  refine ⟨by simpa using hS.1,?_⟩
  intro T hT
  rw [sum_zero_private,sum_activeLift]
  exact hS.2 (activePart T) ((activePart_card_le T).trans hT)

def numericalBid {N H : ℕ} {R Rp Rm : ℝ} (b : Fin N → ℝ)
    (row : Row H R Rp Rm) : Target N H → ℝ :=
  Sum.elim b (fun j => numericalEntry (row j))

lemma continuous_numericalBid {N H : ℕ} {R Rp Rm : ℝ} (i : Target N H) :
    Continuous (fun z : (Fin N → ℝ) × Row H R Rp Rm => numericalBid z.1 z.2 i) := by
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr j => exact continuous_numericalEntry.comp ((continuous_apply j).comp continuous_snd)

lemma numerical_private_ge {N H : ℕ} {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (row : Row H R Rp Rm) (hRRm : R ≤ Rm)
    (j : Target N H) (hj : j ∈ privateAll N H) : R ≤ numericalBid b row j := by
  cases j with
  | inl i => simp at hj
  | inr j =>
    cases hrow : row j with
    | inl v => simpa [numericalBid,numericalEntry,hrow] using hRRm.trans v.2
    | inr v => simpa [numericalBid,numericalEntry,hrow] using v.2.1

lemma numerical_nonneg {N H : ℕ} {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (row : Row H R Rp Rm)
    (hb : ∀ i, 0 ≤ b i) (hR : 0 ≤ R) (hRm : 0 ≤ Rm) :
    ∀ i, 0 ≤ numericalBid b row i := by
  intro i
  cases i with
  | inl i => exact hb i
  | inr j =>
    cases hrow : row j with
    | inl v => simpa [numericalBid,numericalEntry,hrow] using hRm.trans v.2
    | inr v => simpa [numericalBid,numericalEntry,hrow] using hR.trans v.2.1

lemma upperPool_subset_private {N H : ℕ} {R Rp Rm : ℝ} (row : Row H R Rp Rm) :
    upperPool N row ⊆ privateAll N H := by
  intro i hi
  cases i with
  | inl i => simp at hi
  | inr j => simp

lemma private_nonupper_le {N H : ℕ} {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (row : Row H R Rp Rm)
    (j : Target N H) (hj : j ∈ privateAll N H) (hnot : j ∉ upperPool N row) :
    numericalBid b row j ≤ Rp := by
  cases j with
  | inl i => simp at hj
  | inr j =>
    cases hrow : row j with
    | inl v => exact (hnot (by simp [upperPool,signal,signalEntry,hrow,isUpper])).elim
    | inr v => simpa [numericalBid,numericalEntry,hrow] using v.2.2

theorem univ_optimal {N H : ℕ} (c : ℕ) (r : Target N H → ℝ)
    (hcard : N+H ≤ c) (hr : ∀ i, 0 ≤ r i) :
    Finite.Optimal c r Finset.univ := by
  refine ⟨by simpa [Fintype.card_sum] using hcard,?_⟩
  intro S hS
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun i _ _ => hr i)

end FCAppendix.Affine.Tail04.LocalHighCommon
