import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05ProductMenu

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open FCAppendix.Affine Crossover Crossover.Physical

theorem product_counts_of_two_payoff_errors
    {η t b q d p e : ℝ} (hη : 0<η) (hη1 : η≤ 1) (ht : 0< t)
    (hb : 0≤ b) (hbt : b≤ t) (he : 0≤ e) (hd : 0≤ d) (hdq : d≤ q)
    (hsmall : b≤ t/4→ p=0)
    (h0 : |utilityTwo η 0 b q d-utilityTwo η 0 b p (p^2)|≤ e)
    (hT : |utilityTwo η t b q d-utilityTwo η t b p (p^2)|≤ e) :
    |q-p|≤ 20/(η*t)*e ∧ |d-p^2|≤ 20/(η*t)*e := by
  let eS:=2*q-d-(2*p-p^2)
  let eD:=d-p^2
  let u0:=-b*eS-η*b*eD
  let uT:=(t-b)*eS-η*b*eD
  have h0' : |u0|≤ e := by
    have heq : utilityTwo η 0 b q d-utilityTwo η 0 b p (p^2)=u0 := by
      dsimp [u0,eS,eD,utilityTwo]
      ring
    rwa [heq] at h0
  have hT' : |uT|≤ e := by
    have heq : utilityTwo η t b q d-utilityTwo η t b p (p^2)=uT := by
      dsimp [uT,eS,eD,utilityTwo]
      ring
    rwa [heq] at hT
  have hS : t*|eS|≤ 2*e := by
    calc
      t*|eS|=|uT-u0| := by
        rw [show uT-u0=t*eS by dsimp [uT,u0]; ring,abs_mul,abs_of_pos ht]
      _≤|uT|+|u0| := abs_sub _ _
      _≤ 2*e := by linarith
  have hηt : 0<η*t := mul_pos hη ht
  have hrewrite : 20/(η*t)*e=20*e/(η*t) := by ring
  simp only [hrewrite]
  have hηS : η*t*|eS|≤ 2*e := by
    have hmul:=mul_le_mul_of_nonneg_left hS hη.le
    have herr:=mul_le_mul_of_nonneg_right hη1 (mul_nonneg (by norm_num : (0:ℝ)≤ 2) he)
    nlinarith
  by_cases hlow : b≤ t/4
  · have hp:=hsmall hlow
    have hq : 0≤ q:=hd.trans hdq
    have hqS : q≤ eS := by dsimp [eS]; rw [hp]; nlinarith
    have hqA : q≤|eS|:=hqS.trans (le_abs_self _)
    have hdA : d≤|eS|:=hdq.trans hqA
    have hqB:=mul_le_mul_of_nonneg_left hqA hηt.le
    have hdB:=mul_le_mul_of_nonneg_left hdA hηt.le
    simp only [hp,sub_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      abs_of_nonneg hq,abs_of_nonneg hd]
    constructor <;> apply (le_div_iff₀ hηt).2 <;> nlinarith
  · have hhigh : t/4≤ b:=le_of_not_ge hlow
    have hbS : b*|eS|≤ 2*e :=
      (mul_le_mul_of_nonneg_right hbt (abs_nonneg _)).trans hS
    have hD : η*b*|eD|≤ 3*e := by
      calc
        η*b*|eD|=|u0+b*eS| := by
          rw [show u0+b*eS=-(η*b*eD) by dsimp [u0]; ring,abs_neg,
            abs_mul,abs_of_nonneg (mul_nonneg hη.le hb)]
        _≤|u0|+|b*eS| := abs_add_le _ _
        _=|u0|+b*|eS| := by rw [abs_mul,abs_of_nonneg hb]
        _≤ 3*e := by linarith
    have hDwide : η*t*|eD|≤ 12*e := by
      have hgap:=mul_nonneg (mul_nonneg hη.le
        (show 0≤ 4*b-t by linarith)) (abs_nonneg eD)
      nlinarith
    have hq : 2*|q-p|≤|eS|+|eD| := by
      calc
        2*|q-p|=|eS+eD| := by
          rw [show eS+eD=2*(q-p) by dsimp [eS,eD]; ring,abs_mul]
          norm_num
        _≤|eS|+|eD| := abs_add_le _ _
    have hqscale:=mul_le_mul_of_nonneg_left hq hηt.le
    constructor
    · apply (le_div_iff₀ hηt).2
      nlinarith
    · change |eD|≤ 20*e/(η*t)
      apply (le_div_iff₀ hηt).2
      nlinarith

def productErrorScale (row : Uniform07.Row) : ℝ:=
  20/(Uniform07.eta row*Uniform07.cutoff row)

theorem productErrorScale_pos (row : Uniform07.Row) : 0< productErrorScale row :=
  div_pos (by norm_num) (mul_pos (Uniform07.eta_pos row) (Uniform07.cutoff_pos row))

theorem eventual_native_positive_product_kernels (row : Uniform07.Row)
    {tol : ℝ} (htol : 0< tol) :
    ∀ᶠ M : ℕ in atTop,∀E : UniformFinite.ExactRestrictedLaw row M,
      ∀hc : 1≤ Uniform07.capacity M,∀i : Fin M,∀b∈Ioo (0:ℝ) (sourceLowerPriceCeiling row),
      |q (exactNativeGame E hc (sourceLowerPriceCeiling row)) i b-
        sourceProductMarginal row b|≤ tol ∧
      |duplicate (exactNativeGame E hc (sourceLowerPriceCeiling row)) i b-
        (sourceProductMarginal row b)^2|≤ tol := by
  let e:=tol/productErrorScale row
  have he : 0< e:=div_pos htol (productErrorScale_pos row)
  filter_upwards [eventual_native_positive_source_menu row he] with M hMenu
  intro E hc i b hb
  let Γ:=exactNativeGame E hc (sourceLowerPriceCeiling row)
  have h0:=hMenu E hc i 0 (two b) ⟨le_rfl,(Uniform07.cutoff_pos row).le⟩
    (two_routes b) (by simpa only [two_bid hb.1.le] using hb.1)
    (by simpa only [two_bid hb.1.le] using hb.2)
  have hT:=hMenu E hc i (Uniform07.cutoff row) (two b)
    ⟨(Uniform07.cutoff_pos row).le,le_rfl⟩ (two_routes b)
    (by simpa only [two_bid hb.1.le] using hb.1)
    (by simpa only [two_bid hb.1.le] using hb.2)
  simp only [two_bid hb.1.le,exact_native_two_payoff E hc _ i _ hb.1.le,
    source_product_payoff_eq] at h0 hT
  have hh:=product_counts_of_two_payoff_errors (Uniform07.eta_pos row)
    (source_eta_mem row).2 (Uniform07.cutoff_pos row) hb.1.le
    (hb.2.le.trans (source_auxiliary_floor_guards row).2.2.1.le) he.le
    (duplicate_nonneg Γ i b) (duplicate_le_q Γ i hb.1.le)
    (source_product_zero_below_quarter row) h0.le hT.le
  have hscale : productErrorScale row*e=tol :=
    mul_div_cancel₀ tol (productErrorScale_pos row).ne'
  change |q Γ i b-sourceProductMarginal row b|≤ productErrorScale row*e ∧
    |duplicate Γ i b-(sourceProductMarginal row b)^2|≤ productErrorScale row*e at hh
  simpa only [Γ,hscale] using hh

end FCAppendix.Affine.Uniform07Finishing.Concrete05
