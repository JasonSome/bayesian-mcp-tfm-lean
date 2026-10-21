import FCAppendix.Affine.Tail04.ActualActiveFiniteGain
import FCAppendix.Affine.Tail04.TypicalGuardEndpoints

noncomputable section
namespace FCAppendix.Affine.Tail04.ActualGuardMarginals
open MeasureTheory Set Classical
open EqualPrivateSignal TypicalGuardStatistics TypicalGuardEndpoints
open TypicalFinitePromotion ActualFallbackPromotion ActualActiveFiniteGain
open scoped BigOperators

lemma listMinimum_le_one {A : Type*} (as : List A) (f : A → ℝ) :
    TypicalGuard.listMinimum as f≤1 := by
  induction as with
  | nil => exact le_rfl
  | cons a as ih => exact (min_le_right _ _).trans ih

lemma realizationMargin_le_one (H c ell M : ℕ) (ξ B W : ℝ) (reg : Bool) :
    realizationMargin H c ell M ξ B reg W≤1 := listMinimum_le_one _ _

lemma probabilityClip_eq_one_iff (x : ℝ) : probabilityClip x=1 ↔ 1≤ x := by
  constructor
  · intro h
    by_contra hn
    have hx : x<1 := lt_of_not_ge hn
    have hm : max (0:ℝ) x<1 := max_lt (by norm_num) hx
    have hh : probabilityClip x<1 := (min_le_right _ _).trans_lt hm
    rw [h] at hh
    exact (lt_irrefl _ hh)
  · intro h
    exact min_eq_left (h.trans (le_max_right _ _))

theorem weight_one_properties (H0 H1 c ell0 ell1 M : ℕ)
    (ξ B R Rp width W : ℝ) (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hw : 0< width)
    (hone : weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0 ν1 W=1) :
    Structural H0 H1 c ell0 ell1 M ∧ width≤1 ∧
      (∀ z,TypicalGuardStatistics.multiplier H0 c ell0 M ξ reg W z≤1-width) ∧
      (∀ z,TypicalGuardStatistics.multiplier H1 c ell1 M ξ reg W z≤1-width) := by
  have hs : Structural H0 H1 c ell0 ell1 M := by
    by_contra hn
    simp only [weight,if_neg hn] at hone
    norm_num at hone
  have hm : width≤ margin H0 H1 c ell0 ell1 M ξ B R Rp reg ν0 ν1 W := by
    rw [weight,if_pos hs,probabilityClip_eq_one_iff] at hone
    simpa only [one_mul] using (le_div_iff₀ hw).mp hone
  have hr0 : width≤ realizationMargin H0 c ell0 M ξ B reg W :=
    hm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr1 : width≤ realizationMargin H1 c ell1 M ξ B reg W :=
    hm.trans ((min_le_left _ _).trans (min_le_right _ _))
  refine ⟨hs,hr0.trans (realizationMargin_le_one H0 c ell0 M ξ B W reg),?_,?_⟩
  · intro z
    have hz := hr0.trans (TypicalGuard.finiteMinimum_le _ z)
    have hh := hz.trans (min_le_right _ _)
    linarith
  · intro z
    have hz := hr1.trans (TypicalGuard.finiteMinimum_le _ z)
    have hh := hz.trans (min_le_right _ _)
    linarith

def sourceQmin (ξ width : ℝ) : ℝ := min 1 (width/ξ)

lemma sourceQmin_pos {ξ width : ℝ} (hξ : 0< ξ) (hw : 0< width) : 0< sourceQmin ξ width :=
  lt_min (by norm_num) (div_pos hw hξ)

lemma clippedMarginal_lower {ξ width lam bi : ℝ}
    (hξ : 0< ξ) (_hw : 0< width) (hw1 : width≤1) (hbi : 1≤ bi) (hlam : lam≤1-width) :
    sourceQmin ξ width≤ probabilityClip ((1-lam/bi)/ξ) := by
  have hb0 : 0< bi := (by norm_num : (0:ℝ)<1).trans_le hbi
  have hlb : lam≤(1-width)*bi := by nlinarith
  have hd := (div_le_iff₀ hb0).mpr hlb
  have hr : width/ξ≤(1-lam/bi)/ξ :=
    div_le_div_of_nonneg_right (by linarith) hξ.le
  exact le_min (min_le_left _ _)
    (((min_le_right _ _).trans hr).trans (le_max_right _ _))

theorem weight_one_mean_marginals (H0 H1 c ell0 ell1 M : ℕ)
    {ξ B R Rp width W bi : ℝ} (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hw : 0< width) (hbi : 1≤ bi)
    (hone : weight H0 H1 c ell0 ell1 M ξ B R Rp width reg ν0 ν1 W=1) :
    sourceQmin ξ width≤ meanMarginal ξ c ell0 (NativeTypicalCount.privateMean H0 reg ν0) M W bi ∧
      sourceQmin ξ width≤ meanMarginal ξ c ell1 (NativeTypicalCount.privateMean H1 reg ν1) M W bi := by
  obtain ⟨hs,hw1,h0,h1⟩ := weight_one_properties H0 H1 c ell0 ell1 M ξ B R Rp width W reg ν0 ν1 hw hone
  have havg0 : TypicalGuardStatistics.meanMultiplier H0 c ell0 M ξ reg ν0 W≤1-width :=
    ν0.expect_le_const h0
  have havg1 : TypicalGuardStatistics.meanMultiplier H1 c ell1 M ξ reg ν1 W≤1-width :=
    ν1.expect_le_const h1
  rw [meanMultiplier_eq_lambda H0 c ell0 M ξ reg ν0 W hs.1] at havg0
  rw [meanMultiplier_eq_lambda H1 c ell1 M ξ reg ν1 W hs.2.1] at havg1
  have h0' := clippedMarginal_lower hξ hw hw1 hbi havg0
  have h1' := clippedMarginal_lower hξ hw hw1 hbi havg1
  have he (ell : ℕ) (pm : ℝ) : (1-lambda c ell M ξ W pm/bi)/ξ=
      rawMeanMarginal ξ c ell pm M W bi := by
    unfold lambda rawMeanMarginal
    congr 3
    ring
  rw [he] at h0' h1'
  exact ⟨h0',h1'⟩

variable {N : ℕ} [Nonempty (Fin N)]

omit [Nonempty (Fin N)] in
theorem phi_one_marginals (H0 H1 c : ℕ) {ξ B R Rp width : ℝ} (reg : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hw : 0< width) (b : Fin N → ℝ) (i target : Fin N)
    (hbi : 1≤ b i) (z : Fin N → Bool)
    (hone : targetTypicalWeight (phi N H0 H1 c ξ B R Rp width reg ν0 ν1) b target z=1) :
    sourceQmin ξ width≤ marginal0 (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1) b i target z ∧
      sourceQmin ξ width≤ marginal1 (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1) b i target z := by
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  exact weight_one_mean_marginals H0 H1 c (P.owner0 (targetMixedSet target z).card)
    (P.owner1 (targetMixedSet target z).card) (targetMixedSet target z).card reg ν0 ν1 hξ hw hbi hone

omit [Nonempty (Fin N)] in

theorem goodFlags_iff_weightFlags (H0 H1 c : ℕ) {ξ B R Rp width : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hw : 0< width) (b : Fin N → ℝ) (i : Fin N) (hbi : 1≤ b i)
    (z : Fin N → Bool) :
    GoodFlags (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1))
      b i (sourceQmin ξ width) z ↔
    WeightFlags (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1)) b z := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,?_⟩
    cases lowPresent
    · have hh := h i
      change (0:ℝ)=1 at hh
      norm_num at hh
    · exact phi_one_marginals H0 H1 c reg ν0 ν1 hξ hw b i i hbi z (h i)

omit [Nonempty (Fin N)] in
theorem badProbability_eq_badWeight (H0 H1 c : ℕ) {ξ B R Rp width e0 F : ℝ}
    (reg lowPresent : Bool) (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : 0< ξ) (hw : 0< width) (b : Fin N → ℝ) (i : Fin N) (hbi : 1≤ b i) :
    badProbability (NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1)
      (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1)) e0 F b i
      (sourceQmin ξ width)=
    badWeightProbability (effectivePhi lowPresent (phi N H0 H1 c ξ B R Rp width reg ν0 ν1)) e0 F b := by
  unfold badProbability badWeightProbability FiniteLaw.prob
  apply FiniteLaw.expect_congr
  intro z
  simp only [goodFlags_iff_weightFlags H0 H1 c reg lowPresent ν0 ν1 hξ hw b i hbi z]
  split_ifs <;> rfl

end FCAppendix.Affine.Tail04.ActualGuardMarginals
