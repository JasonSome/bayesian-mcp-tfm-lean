import FCAppendix.Finite.BinomialLogBounds

noncomputable section
namespace FCAppendix.Affine.Uniform06.BinomialPivotal

open Set
open scoped BigOperators

theorem pmf_nonneg (N r : ℕ) {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    0 ≤ PiBinomial.pmf N p r := by
  unfold PiBinomial.pmf
  have hp0 := hp.1
  have hp1 := hp.2
  positivity

theorem pmf_pos (N r : ℕ) (hr : r ≤ N) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < PiBinomial.pmf N p r := by
  unfold PiBinomial.pmf
  have hc : (0:ℝ) < N.choose r := Nat.cast_pos.mpr (Nat.choose_pos hr)
  have hp0 := hp.1
  have hp1 := hp.2
  positivity

theorem hasDerivAt_mass_zero (N : ℕ) (p : ℝ) :
    HasDerivAt (fun q => PiBinomial.pmf (N+1) q 0)
      (-((N:ℝ)+1)*PiBinomial.pmf N p 0) p := by
  have h := (((hasDerivAt_id p).const_sub 1).pow (N+1))
  have hf : (fun q => PiBinomial.pmf (N+1) q 0) = (fun q : ℝ => (1-q)^(N+1)) := by
    funext q
    simp [PiBinomial.pmf]
  rw [hf]
  convert! h using 1
  simp only [PiBinomial.pmf, Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.cast_add, id_eq]
  ring

theorem hasDerivAt_mass_successor (N k : ℕ) (hk : k ≤ N) (p : ℝ) :
    HasDerivAt (fun q => PiBinomial.pmf (N+1) q (k+1))
      (((N:ℝ)+1)*(PiBinomial.pmf N p k-PiBinomial.pmf N p (k+1))) p := by
  have hnat₁ := Nat.add_one_mul_choose_eq N k
  have hnat₂ := Nat.choose_mul_succ_eq N (k+1)
  have hc₁ : ((N:ℝ)+1)*(N.choose k:ℝ)=
      ((N+1).choose (k+1):ℝ)*((k:ℝ)+1) := by exact_mod_cast hnat₁
  have hc₂ : (N.choose (k+1):ℝ)*((N:ℝ)+1)=
      ((N+1).choose (k+1):ℝ)*(N-k:ℕ) := by
    have he : N+1-(k+1)=N-k := by omega
    rw [he] at hnat₂
    exact_mod_cast hnat₂
  have he : N+1-(k+1)=N-k := by omega
  have h := ((hasDerivAt_pow (k+1) p).mul
    ((((hasDerivAt_id p).const_sub 1).pow (N-k)))).const_mul
      ((N+1).choose (k+1):ℝ)
  have hf : (fun q => PiBinomial.pmf (N+1) q (k+1)) =
      (fun q => ((N+1).choose (k+1):ℝ)*(q^(k+1)*(1-q)^(N-k))) := by
    funext q
    simp only [PiBinomial.pmf,he,mul_assoc]
  rw [hf]
  apply h.congr_deriv
  unfold PiBinomial.pmf
  simp only [Nat.add_sub_cancel, Pi.pow_apply, id_eq]
  by_cases hEq : k=N
  · subst k
    simp only [Nat.sub_self, pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero,
      Nat.choose_self, Nat.cast_one, Nat.choose_succ_self, sub_zero, Nat.cast_add]
    ring
  · have hk' : k < N := lt_of_le_of_ne hk hEq
    have hpred : N-k-1=N-(k+1) := by omega
    rw [hpred]
    simp only [Nat.cast_add,Nat.cast_one]
    linear_combination
      -(p^k*(1-p)^(N-k))*hc₁ +
      (p^(k+1)*(1-p)^(N-(k+1)))*hc₂

theorem hasDerivAt_binomBelow (N k : ℕ) (hk : k ≤ N) (p : ℝ) :
    HasDerivAt (fun q => Bayes.binomBelow (N+1) q (k+1))
      (-((N:ℝ)+1)*PiBinomial.pmf N p k) p := by
  induction k with
  | zero =>
    simpa only [Bayes.binomBelow, Nat.zero_add, Finset.sum_range_one] using hasDerivAt_mass_zero N p
  | succ k ih =>
    have hik := ih (by omega)
    have hmass := hasDerivAt_mass_successor N k (by omega) p
    have hh := hik.add hmass
    have he : (fun q => Bayes.binomBelow (N+1) q (k+1)+PiBinomial.pmf (N+1) q (k+1))=
        (fun q => Bayes.binomBelow (N+1) q (k+1+1)) := by
      funext q
      simp only [Bayes.binomBelow,Finset.sum_range_succ]
    change HasDerivAt (fun q => Bayes.binomBelow (N+1) q (k+1)+PiBinomial.pmf (N+1) q (k+1)) _ p at hh
    rw [he] at hh
    convert! hh using 1
    ring

theorem pivotal_mass_lower_hazard
    (N k : ℕ) (hk : k ≤ N) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    ((((N:ℝ)+1)*p-k)/(p*(1-p)))*Bayes.binomBelow (N+1) p (k+1) ≤
      ((N:ℝ)+1)*PiBinomial.pmf N p k := by
  have hQ := Bayes.binomBelow_pos (N+1) (k+1) (by omega) p hp
  have hder := (hasDerivAt_binomBelow N k hk p).log hQ.ne'
  have hscore := (Bayes.log_binomBelow_deriv_bounds (N+1) (k+1)
    (by omega) (by omega) p hp).2
  rw [hder.deriv] at hscore
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hscore
  have hh := (div_le_iff₀ hQ).mp hscore
  simp only [neg_div, neg_mul] at hh
  linarith

theorem pivotal_mass_lower_of_gap
    (N k : ℕ) (hk : k ≤ N) {p g : ℝ}
    (hp : p ∈ Ioo (0:ℝ) 1) (hg : 0 ≤ g)
    (hgap : g*((N:ℝ)+1) ≤ ((N:ℝ)+1)*p-k) :
    g*((N:ℝ)+1)*Bayes.binomBelow (N+1) p (k+1) ≤
      ((N:ℝ)+1)*PiBinomial.pmf N p k := by
  have hden : 0 < p*(1-p) := mul_pos hp.1 (sub_pos.mpr hp.2)
  have hden1 : p*(1-p) ≤ 1 := by nlinarith [sq_nonneg p]
  have hnum : g*((N:ℝ)+1) ≤ (((N:ℝ)+1)*p-k)/(p*(1-p)) := by
    apply (le_div_iff₀ hden).mpr
    exact (mul_le_of_le_one_right (by positivity) hden1).trans hgap
  exact (mul_le_mul_of_nonneg_right hnum
    (Bayes.binomBelow_pos (N+1) (k+1) (by omega) p hp).le).trans
      (pivotal_mass_lower_hazard N k hk hp)

end FCAppendix.Affine.Uniform06.BinomialPivotal
