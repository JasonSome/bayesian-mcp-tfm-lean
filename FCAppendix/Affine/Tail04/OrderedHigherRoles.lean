import FCAppendix.Affine.Tail04.AllCountAtypical

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedHigherRoles
open Set Classical
open EqualPrivateSignal EqualPrivateUpper LocalHighCommon

def first (j : Fin 2) (own other : ℕ) : Prop :=
  own < other ∨ (own = other ∧ j = 0)

lemma first_of_lt {j : Fin 2} {own other : ℕ} (h : own < other) : first j own other :=
  Or.inl h

lemma not_first_of_gt {j : Fin 2} {own other : ℕ} (h : other < own) : ¬first j own other := by
  rintro (hlt | ⟨he,_⟩)
  · omega
  · omega

lemma first_equal (j : Fin 2) (H : ℕ) : first j H H ↔ j = 0 := by
  simp [first]

lemma first_le {j : Fin 2} {own other : ℕ} (h : first j own other) : own ≤ other := by
  rcases h with h | ⟨h,_⟩ <;> omega

lemma second_le {j : Fin 2} {own other : ℕ} (h : ¬first j own other) : other ≤ own := by
  by_contra hn
  exact h (Or.inl (by omega))

lemma unequal_role_exchange (j k : Fin 2) {own other : ℕ} (hne : own ≠ other) :
    first j own other ↔ ¬first k other own := by
  unfold first
  omega

def selectOwn (N own other c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Fin 2) (row : Row own R Rp Rm) :
    Finset (Target N own) :=
  if first j own other then AllCountAtypical.select N own other c ξ b false row
  else AllCountAtypical.select N other own c ξ b true row

lemma selectOwn_capacity (N own other c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j : Fin 2) (row : Row own R Rp Rm) :
    (selectOwn N own other c ξ b j row).card ≤ c := by
  unfold selectOwn
  split
  · exact AllCountAtypical.capacity N own other c ξ b false row
  · exact AllCountAtypical.capacity N other own c ξ b true row

lemma measurable_selectOwn (N own other c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ} (j : Fin 2) :
    Measurable (fun z : (Fin N → ℝ) × Row own R Rp Rm =>
      selectOwn N own other c ξ z.1 j z.2) := by
  unfold selectOwn
  split
  · exact AllCountAtypical.measurable_select N own other c ξ false
  · exact AllCountAtypical.measurable_select N other own c ξ true

lemma selectOwn_label_independent (N own other c : ℕ) (ξ : ℝ) {R Rp Rm : ℝ}
    (b : Fin N → ℝ) (j k : Fin 2) (hne : own ≠ other) (row : Row own R Rp Rm) :
    selectOwn N own other c ξ b j row = selectOwn N own other c ξ b k row := by
  have he : first j own other ↔ first k own other := by unfold first;omega
  simp only [selectOwn,propext he]

end FCAppendix.Affine.Tail04.OrderedHigherRoles
