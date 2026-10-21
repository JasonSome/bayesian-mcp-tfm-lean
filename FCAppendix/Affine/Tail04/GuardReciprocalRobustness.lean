import FCAppendix.Affine.Tail04.TwoFocalGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.MenuError
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators

theorem reciprocal_lipschitz_on_one {x y : ℝ} (hx : 1≤ x) (hy : 1≤ y) :
    |1/x-1/y|≤|x-y| := by
  have hx0 : 0< x := (by norm_num : (0:ℝ)<1).trans_le hx
  have hy0 : 0< y := (by norm_num : (0:ℝ)<1).trans_le hy
  have he : 1/x-1/y=(y-x)/(x*y) := by field_simp [hx0.ne',hy0.ne']
  rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm]
  exact div_le_self (abs_nonneg _) (by nlinarith)

theorem marked_reciprocal_perturb {X : Type*}
    (active : X→ Bool) (p : X→ unitInterval) (bid bid' : X→ℝ)
    {r : ℝ} (hr : 0≤ r) (z : X×unitInterval)
    (hbox : active z.1=true → 1≤ bid z.1 ∧ 1≤ bid' z.1)
    (hnear : active z.1=true → |bid z.1-bid' z.1|≤ r) :
    |Empirical.markedStatistic p (reciprocalWeight active bid) z-
      Empirical.markedStatistic p (reciprocalWeight active bid') z|≤ r := by
  cases hf : Empirical.flag (p z.1) z.2
  · simpa [Empirical.markedStatistic,hf] using hr
  · by_cases ha : active z.1=true
    · have hb := hbox ha
      simpa only [Empirical.markedStatistic,hf,ite_true,
        reciprocalWeight_physical active bid z.1 ha hb.1,
        reciprocalWeight_physical active bid' z.1 ha hb.2] using
        (reciprocal_lipschitz_on_one hb.1 hb.2).trans (hnear ha)
    · simpa [Empirical.markedStatistic,hf,reciprocalWeight,ha] using hr

theorem twoReciprocal_perturb {X Ω : Type*} (N : ℕ) (hN : 0< N)
    (row : Ω→ Fin N→ X×unitInterval) (active : X→ Bool) (p : X→ unitInterval)
    (bid bid' : X→ℝ) (b0 b1 : ℝ) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    {r : ℝ} (hr : 0≤ r) (x : Ω)
    (hbox : ∀ i,active (row x i).1=true → 1≤ bid (row x i).1 ∧ 1≤ bid' (row x i).1)
    (hnear : ∀ i,active (row x i).1=true → |bid (row x i).1-bid' (row x i).1|≤ r) :
    |twoReciprocal N row active p bid b0 b1 f0 f1 target x-
      twoReciprocal N row active p bid' b0 b1 f0 f1 target x|≤ r := by
  let W0 := twoPrefixWeight N row (Empirical.markedStatistic p (reciprocalWeight active bid))
    (if f0 then 1/b0 else 0) (if f1 then 1/b1 else 0) x
  let W1 := twoPrefixWeight N row (Empirical.markedStatistic p (reciprocalWeight active bid'))
    (if f0 then 1/b0 else 0) (if f1 then 1/b1 else 0) x
  let bound : Fin (N+2)→ℝ := Fin.cases 0 (Fin.cases 0 (fun _ : Fin N => r))
  have hb (i : Fin (N+2)) :
      |(if i=target x then 0 else W0 i)-(if i=target x then 0 else W1 i)|≤ bound i := by
    by_cases hi : i=target x
    · simp only [if_pos hi,sub_self,abs_zero]
      exact Fin.cases (by norm_num [bound])
        (fun j => Fin.cases (by change (0:ℝ)≤0;exact le_rfl) (fun _ => hr) j) i
    · simp only [if_neg hi]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [W0,W1,twoPrefixWeight,bound]
      · refine Fin.cases ?_ (fun k => ?_) j
        · change |(if f1 then (1/b1:ℝ) else 0)-(if f1 then (1/b1:ℝ) else 0)|≤0
          simp only [sub_self,abs_zero,le_refl]
        · exact marked_reciprocal_perturb active p bid bid' hr (row x k) (hbox k) (hnear k)
  have hsum := (Finset.abs_sum_le_sum_abs
    (fun i : Fin (N+2) => (if i=target x then 0 else W0 i)-(if i=target x then 0 else W1 i))
      Finset.univ).trans (Finset.sum_le_sum (fun i _ => hb i))
  have hbound : (∑ i : Fin (N+2),bound i)=(N:ℝ)*r := by
    simp [bound,Fin.sum_univ_succ]
  rw [hbound] at hsum
  have hn : (0:ℝ)< N := Nat.cast_pos.mpr hN
  unfold twoReciprocal twoForcedMean
  rw [←sub_div,←Finset.sum_sub_distrib,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm r (N:ℝ)] using hsum

theorem twoGuardError_perturb {X Ω : Type*} (N : ℕ) (hN : 0< N)
    (row : Ω→ Fin N→ X×unitInterval) (active private0 private1 : X→ Bool) (p : X→ unitInterval)
    (bid bid' : X→ℝ) (b0 b1 : ℝ) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (abar mbar hbar wbar : ℝ) {r : ℝ} (hr : 0≤ r) (x : Ω)
    (hbox : ∀ i,active (row x i).1=true → 1≤ bid (row x i).1 ∧ 1≤ bid' (row x i).1)
    (hnear : ∀ i,active (row x i).1=true → |bid (row x i).1-bid' (row x i).1|≤ r) :
    twoGuardError N row active p private0 private1 bid' b0 b1 f0 f1 target abar mbar hbar wbar x≤
      twoGuardError N row active p private0 private1 bid b0 b1 f0 f1 target abar mbar hbar wbar x+r := by
  have hc := twoReciprocal_perturb N hN row active p bid bid' b0 b1 f0 f1 target hr x hbox hnear
  have he := abs_sub_le (twoReciprocal N row active p bid' b0 b1 f0 f1 target x)
    (twoReciprocal N row active p bid b0 b1 f0 f1 target x) wbar
  rw [abs_sub_comm] at hc
  unfold twoGuardError guardError
  linarith

theorem twoGuardError_lt_after_perturb {X Ω : Type*} (N : ℕ) (hN : 0< N)
    (row : Ω→ Fin N→ X×unitInterval) (active private0 private1 : X→ Bool) (p : X→ unitInterval)
    (bid bid' : X→ℝ) (b0 b1 : ℝ) (f0 f1 : Bool) (target : Ω→ Fin (N+2))
    (abar mbar hbar wbar δ r : ℝ) (hr : 0≤ r) (hrδ : r≤ δ/2) (x : Ω)
    (hgood : twoGuardError N row active p private0 private1 bid b0 b1 f0 f1 target abar mbar hbar wbar x< δ/2)
    (hbox : ∀ i,active (row x i).1=true → 1≤ bid (row x i).1 ∧ 1≤ bid' (row x i).1)
    (hnear : ∀ i,active (row x i).1=true → |bid (row x i).1-bid' (row x i).1|≤ r) :
    twoGuardError N row active p private0 private1 bid' b0 b1 f0 f1 target abar mbar hbar wbar x< δ := by
  have h := twoGuardError_perturb N hN row active private0 private1 p bid bid' b0 b1 f0 f1 target
    abar mbar hbar wbar hr x hbox hnear
  linarith

theorem guarded_marginal_lower {ξ γ lam b : ℝ} (hξ : 0< ξ) (_hγ : 0≤ γ) (hγ1 : γ≤1)
    (hb : 1≤ b) (hlam : lam+γ≤1) : γ/ξ≤(1-lam/b)/ξ := by
  have hb0 : 0< b := (by norm_num : (0:ℝ)<1).trans_le hb
  have hlamb : lam≤(1-γ)*b := by nlinarith
  have hd := (div_le_iff₀ hb0).mpr hlamb
  exact div_le_div_of_nonneg_right (by linarith : γ≤1-lam/b) hξ.le

end FCAppendix.Affine.Tail04.MenuError
