import FCAppendix.Probability.FairBinomialBound
import Mathlib.Analysis.SpecialFunctions.Stirling

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryParity
open Set Filter Topology
open FCAppendix.PiBinomial

theorem fairCentral_wallis (n : ℕ) :
    fairCentral n^2*Real.Wallis.W n*(2*(n : ℝ)+1)=1 := by
  induction n with
  | zero => norm_num [fairCentral,Real.Wallis.W]
  | succ n ih =>
    rw [fairCentral_succ,Real.Wallis.W_succ,Nat.cast_add_one]
    calc
      ((((n : ℝ)+1/2)/((n : ℝ)+1))*fairCentral n)^2*
          (Real.Wallis.W n*((2*(n : ℝ)+2)/(2*(n : ℝ)+1)*
            ((2*(n : ℝ)+2)/(2*(n : ℝ)+3))))*(2*((n : ℝ)+1)+1) =
          fairCentral n^2*Real.Wallis.W n*(2*(n : ℝ)+1) := by
        field_simp [show (n : ℝ)+1 ≠ 0 by positivity,
          show 2*(n : ℝ)+1 ≠ 0 by positivity,show 2*(n : ℝ)+3 ≠ 0 by positivity]
        ring
      _ = 1 := ih

theorem fairCentral_sq_mul_tendsto :
    Tendsto (fun n : ℕ => fairCentral n^2*(n : ℝ)) atTop (𝓝 (1/Real.pi)) := by
  have h := Stirling.tendsto_self_div_two_mul_self_add_one.div
    Real.Wallis.tendsto_W_nhds_pi_div_two (by positivity : Real.pi/2 ≠ 0)
  have he (n : ℕ) : fairCentral n^2*(n : ℝ)=
      ((n : ℝ)/(2*(n : ℝ)+1))/Real.Wallis.W n := by
    have hw := fairCentral_wallis n
    field_simp [(Real.Wallis.W_pos n).ne',show 2*(n : ℝ)+1 ≠ 0 by positivity]
    nlinarith [congrArg (fun x : ℝ => x*(n : ℝ)) hw]
  simp_rw [he]
  convert! h using 1
  congr 1
  field_simp [Real.pi_ne_zero]

theorem fairCentral_mul_sqrt_tendsto :
    Tendsto (fun n : ℕ => fairCentral n*Real.sqrt (n : ℝ)) atTop
      (𝓝 (1/Real.sqrt Real.pi)) := by
  have h := fairCentral_sq_mul_tendsto.sqrt
  have he (n : ℕ) : Real.sqrt (fairCentral n^2*(n : ℝ))=
      fairCentral n*Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg (fairCentral_nonneg n)]
  simp_rw [he] at h
  simpa only [Real.sqrt_div zero_le_one,Real.sqrt_one] using h

def upperRatio (n e r : ℕ) : ℝ :=
  ((2*n+e).choose (n+e+r) : ℝ)/((2*n+e).choose (n+e) : ℝ)

lemma upperRatio_nonneg (n e r : ℕ) : 0 ≤ upperRatio n e r := by unfold upperRatio; positivity
lemma upperRatio_zero (n e : ℕ) : upperRatio n e 0=1 := by
  unfold upperRatio
  simp only [add_zero]
  exact div_self (by exact_mod_cast Nat.choose_ne_zero (show n+e ≤ 2*n+e by omega))

lemma upperRatio_le_one (n : ℕ) {e : ℕ} (he : e ≤ 1) (r : ℕ) :
    upperRatio n e r ≤ 1 := by
  have hc : 0 < ((2*n+e).choose (n+e) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show n+e ≤ 2*n+e by omega)
  apply (div_le_one hc).2
  have h := Nat.choose_le_middle (n+e+r) (2*n+e)
  rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
  · simpa using (show (((2*n).choose (n+r) : ℕ) : ℝ) ≤ ((2*n).choose n : ℝ) from by
      exact_mod_cast (by simpa using h))
  · have heq := Nat.choose_symm_half n
    have hd : (2*n+1)/2=n := by omega
    rw [hd,← heq] at h
    exact_mod_cast h

lemma upperRatio_succ (n e r : ℕ) (hr : r ≤ n) :
    upperRatio n e (r+1)=((n : ℝ)-(r : ℝ))/((n : ℝ)+(e : ℝ)+(r : ℝ)+1)*
      upperRatio n e r := by
  have hc : ((2*n+e).choose (n+e) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show n+e ≤ 2*n+e by omega)
  have hd : (n : ℝ)+(e : ℝ)+(r : ℝ)+1 ≠ 0 := by positivity
  have hrec := Nat.choose_succ_right_eq (2*n+e) (n+e+r)
  have hnr : 2*n+e-(n+e+r)=n-r := by omega
  rw [hnr] at hrec
  have hcast : (((2*n+e).choose (n+e+r+1) : ℕ) : ℝ)*
      ((n : ℝ)+(e : ℝ)+(r : ℝ)+1)=
      ((2*n+e).choose (n+e+r) : ℝ)*((n : ℝ)-(r : ℝ)) := by
    exact_mod_cast hrec
  unfold upperRatio
  rw [show n+e+(r+1)=n+e+r+1 by omega]
  field_simp [hc,hd]
  nlinarith [hcast]

theorem upperRatio_relative_error (n : ℕ) (hn : 0 < n) {e : ℕ} (he : e ≤ 1)
    (r : ℕ) (hr : r ≤ n) :
    |upperRatio n e r-1| ≤ (r : ℝ)*((r : ℝ)+(e : ℝ))/(n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmain : ∀ r : ℕ, r ≤ n →
      1-upperRatio n e r ≤ (r : ℝ)*((r : ℝ)+(e : ℝ))/(n : ℝ) := by
    intro r
    induction r with
    | zero => intro _; simp [upperRatio_zero]
    | succ r ih =>
      intro hr
      have hprev := ih (by omega)
      have hu := upperRatio_le_one n he r
      have hd : 0 < (n : ℝ)+(e : ℝ)+(r : ℝ)+1 := by positivity
      have ha : 0 ≤ 2*(r : ℝ)+(e : ℝ)+1 := by positivity
      have hdif :
          1-upperRatio n e (r+1) ≤ 1-upperRatio n e r+
          (2*(r : ℝ)+(e : ℝ)+1)/((n : ℝ)+(e : ℝ)+(r : ℝ)+1) := by
        rw [upperRatio_succ n e r (by omega)]
        have heq : (1-((n : ℝ)-(r : ℝ))/((n : ℝ)+(e : ℝ)+(r : ℝ)+1))=
            (2*(r : ℝ)+(e : ℝ)+1)/((n : ℝ)+(e : ℝ)+(r : ℝ)+1) := by
          field_simp [hd.ne']; ring
        have hp := mul_le_mul_of_nonneg_right hu (div_nonneg ha hd.le)
        rw [← heq] at hp
        nlinarith
      have hdiv : (2*(r : ℝ)+(e : ℝ)+1)/((n : ℝ)+(e : ℝ)+(r : ℝ)+1) ≤
          (2*(r : ℝ)+(e : ℝ)+1)/(n : ℝ) :=
        div_le_div_of_nonneg_left ha hnR (by
          nlinarith [show (0 : ℝ) ≤ (e : ℝ) from Nat.cast_nonneg e,
            show (0 : ℝ) ≤ (r : ℝ) from Nat.cast_nonneg r])
      have halg : (r : ℝ)*((r : ℝ)+(e : ℝ))/(n : ℝ)+
          (2*(r : ℝ)+(e : ℝ)+1)/(n : ℝ)=
          ((r : ℝ)+1)*((r : ℝ)+1+(e : ℝ))/(n : ℝ) := by ring
      push_cast
      linarith
  rw [abs_of_nonpos (sub_nonpos.mpr (upperRatio_le_one n he r)),neg_sub]
  exact hmain r hr

theorem upperRatio_tendsto_one (n e r : ℕ → ℕ)
    (hn : ∀ᶠ m in atTop, 0 < n m) (he : ∀ m, e m ≤ 1)
    (hr : ∀ᶠ m in atTop, r m ≤ n m)
    (hwindow : Tendsto (fun m => (r m : ℝ)*((r m : ℝ)+(e m : ℝ))/(n m : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun m => upperRatio (n m) (e m) (r m)) atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hwindow
  filter_upwards [hn,hr] with m hnm hrm
  simpa only [Real.norm_eq_abs] using upperRatio_relative_error (n m) hnm (he m) (r m) hrm

lemma even_peak_eq (n : ℕ) : pmf (2*n) (1/2) n=fairCentral n := by
  rw [pmf_half_eq_choose_div]
  unfold fairCentral Nat.centralBinom
  rw [pow_mul]
  norm_num

lemma odd_peak_eq (n : ℕ) :
    pmf (2*n+1) (1/2) (n+1)=((2*(n : ℝ)+1)/(2*((n : ℝ)+1)))*fairCentral n := by
  have hrec := Nat.add_one_mul_choose_eq (2*n) n
  have hcast : (2*(n : ℝ)+1)*((2*n).choose n : ℝ)=
      ((2*n+1).choose (n+1) : ℝ)*((n : ℝ)+1) := by exact_mod_cast hrec
  rw [pmf_half_eq_choose_div]
  unfold fairCentral Nat.centralBinom
  rw [pow_succ,pow_mul]
  norm_num only [show (2 : ℝ)^2=4 by norm_num]
  field_simp [show (n : ℝ)+1 ≠ 0 by positivity,show (4 : ℝ)^n ≠ 0 by positivity]
  nlinarith [hcast]

theorem odd_peak_mul_sqrt_tendsto :
    Tendsto (fun n : ℕ => pmf (2*n+1) (1/2) (n+1)*Real.sqrt (n : ℝ)) atTop
      (𝓝 (1/Real.sqrt Real.pi)) := by
  have hden : Tendsto (fun n : ℕ => 2*((n : ℝ)+1)) atTop atTop := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact (hn.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).const_mul_atTop (by norm_num)
  have hfactor : Tendsto (fun n : ℕ => (2*(n : ℝ)+1)/(2*((n : ℝ)+1))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_nhds.div_atTop hden :
      Tendsto (fun n : ℕ => 1/(2*((n : ℝ)+1))) atTop (𝓝 0))
    simp only [sub_zero] at h
    apply h.congr
    intro n
    field_simp [show (n : ℝ)+1 ≠ 0 by positivity]
    ring
  have hh := hfactor.mul fairCentral_mul_sqrt_tendsto
  simp only [one_mul] at hh
  simp_rw [odd_peak_eq]
  simpa only [mul_assoc] using hh

lemma pmf_eq_ratio_mul_peak (n e r : ℕ) :
    pmf (2*n+e) (1/2) (n+e+r)=upperRatio n e r*pmf (2*n+e) (1/2) (n+e) := by
  simp only [pmf_half_eq_choose_div,upperRatio]
  have hc : ((2*n+e).choose (n+e) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show n+e ≤ 2*n+e by omega)
  field_simp [hc]

theorem peak_mul_sqrt_tendsto (n e : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (he : ∀ m, e m ≤ 1) :
    Tendsto (fun m => pmf (2*n m+e m) (1/2) (n m+e m)*Real.sqrt (n m : ℝ))
      atTop (𝓝 (1/Real.sqrt Real.pi)) := by
  have hE := fairCentral_mul_sqrt_tendsto.comp hn
  have hO := odd_peak_mul_sqrt_tendsto.comp hn
  have hEL := (hE.sub_const (1/Real.sqrt Real.pi)).abs
  have hOL := (hO.sub_const (1/Real.sqrt Real.pi)).abs
  simp only [sub_self,abs_zero] at hEL hOL
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) ?_ (by simpa only [zero_add] using hEL.add hOL)
  intro m
  rw [Real.norm_eq_abs]
  rcases (show e m=0 ∨ e m=1 by have := he m; omega) with h0 | h1
  · simp only [h0,add_zero,even_peak_eq]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · simp only [h1]
    exact le_add_of_nonneg_left (abs_nonneg _)

theorem parity_local_relative (n e r : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (he : ∀ m, e m ≤ 1) (hr : ∀ᶠ m in atTop, r m ≤ n m)
    (hwindow : Tendsto (fun m => (r m : ℝ)*((r m : ℝ)+(e m : ℝ))/(n m : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun m => pmf (2*n m+e m) (1/2) (n m+e m+r m)*
      Real.sqrt (n m : ℝ)/(1/Real.sqrt Real.pi)) atTop (𝓝 1) := by
  have hratio := upperRatio_tendsto_one n e r (hn.eventually_gt_atTop 0) he hr hwindow
  have hpeak := peak_mul_sqrt_tendsto n e hn he
  have h := (hratio.mul hpeak).div_const (1/Real.sqrt Real.pi)
  have hpos : 0 < 1/Real.sqrt Real.pi := by positivity
  simp only [one_mul,div_self hpos.ne'] at h
  simp_rw [pmf_eq_ratio_mul_peak]
  simpa only [mul_assoc] using h

end FCAppendix.Affine.Uniform06.EntryParity
