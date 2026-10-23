import FCAppendix.CommonReserve.Accounting

noncomputable section
namespace FCAppendix.CommonReserve
open Game
variable {m n c : ℕ} {r : ℝ} {Seed : Type*}

def eraseProfile (x : Profile m n r) (i : Fin m) (j : Fin n) : Profile m n r := by
  classical
  exact Function.update x i (erase (x i) j)

theorem observe_erase_other (x : Profile m n r) (i : Fin m) (j l : Fin n) (hl : l ≠ j) :
    observe (eraseProfile x i j) l = observe x l := by
  classical
  funext u
  by_cases hu : u = i
  · subst u
    simp [observe, eraseProfile, erase, Function.update, hl]
  · simp [observe, eraseProfile, Function.update, hu]

theorem allocation_erase_other (x : Profile m n r) (i : Fin m) (j l : Fin n)
    (hl : l ≠ j) (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) :
    allocation (eraseProfile x i j) policy seed l = allocation x policy seed l := by
  unfold allocation
  rw [observe_erase_other x i j l hl]

theorem accepted_erase (x : Profile m n r) (i : Fin m) (j : Fin n)
    (policy : Fin n → LocalPolicy m c Seed) (seed : Fin n → Seed) :
    accepted (eraseProfile x i j) policy seed i = (accepted x policy seed i).erase j := by
  classical
  have hnot : j ∉ accepted (eraseProfile x i j) policy seed i := by
    intro hj
    have hp := accepted_present (eraseProfile x i j) policy seed i j hj
    apply hp
    simp [eraseProfile, erase, Function.update]
  ext l
  by_cases hl : l = j
  · subst l
    simp [hnot]
  · simp only [Finset.mem_erase]
    simp only [accepted, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [allocation_erase_other x i j l hl]
    simp [hl]

theorem base_charge_deletion_bound (G : Schedule n) (K : ℕ)
    (hK : 2 ≤ K) (hKn : K ≤ n) :
    -((n : ℝ) - 2) ≤ G.charge K - G.charge (K - 1) := by
  have hl := G.lower K (by omega) hKn
  have hu := G.upper (K - 1) (by omega)
  have hc : ((K - 1 : ℕ) : ℝ) ≤ (n : ℝ) - 1 := by
    have he : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
    rw [he]
    exact sub_le_sub_right (Nat.cast_le.mpr hKn) 1
  linarith

end FCAppendix.CommonReserve
