import FCAppendix.Exclusive.NarrowExistenceGameCalculus

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open Set
open scoped BigOperators

def interpolateLogBid {V : Type*} (beta gamma : V → ℝ) (t : ℝ) (v : V) : ℝ :=
  beta v+t*(gamma v-beta v)

theorem interpolateLogBid_mem {V : Type*} (beta gamma : V → ℝ) (lo hi t : ℝ)
    (hb : ∀ v, beta v ∈ Icc lo hi) (hg : ∀ v, gamma v ∈ Icc lo hi)
    (ht : t ∈ Icc (0:ℝ) 1) : ∀ v, interpolateLogBid beta gamma t v ∈ Icc lo hi := by
  intro v
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr (hg v).1)
  have h2 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hb v).1)
  have h3 := mul_nonneg ht.1 (sub_nonneg.mpr (hg v).2)
  have h4 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hb v).2)
  dsimp [interpolateLogBid]
  constructor <;> nlinarith

def rivalInverseDerivative {m : ℕ} {V : Type*} (r : ℝ)
    (beta gamma : V → ℝ) (t : ℝ) (omega : RivalProfile m V) : ℝ :=
  ∑ i, activeBit (omega i).1*Real.exp (-r*interpolateLogBid beta gamma t (omega i).2)*
    (-r*(gamma (omega i).2-beta (omega i).2))

theorem hasDerivAt_rivalInverseSum_interpolate {m : ℕ} {V : Type*}
    (r : ℝ) (beta gamma : V → ℝ) (t : ℝ) (omega : RivalProfile m V) :
    HasDerivAt (fun s => rivalInverseSum r (interpolateLogBid beta gamma s) omega)
      (rivalInverseDerivative r beta gamma t omega) t := by
  unfold rivalInverseSum rivalInverseDerivative
  apply HasDerivAt.fun_sum
  intro i _
  have hi := (((hasDerivAt_const t (beta (omega i).2)).add
    ((hasDerivAt_id t).mul_const (gamma (omega i).2-beta (omega i).2))).const_mul (-r)).exp
  apply (hi.const_mul (activeBit (omega i).1)).congr_deriv
  dsimp [interpolateLogBid]
  ring

theorem rivalInverseDerivative_bound {m : ℕ} {V : Type*}
    (r delta : ℝ) (hr : 0 ≤ r) (beta gamma : V → ℝ)
    (hdiff : ∀ v, |gamma v-beta v| ≤ delta) (t : ℝ) (omega : RivalProfile m V) :
    |rivalInverseDerivative r beta gamma t omega| ≤
      r*rivalInverseSum r (interpolateLogBid beta gamma t) omega*delta := by
  unfold rivalInverseDerivative rivalInverseSum
  calc
    _ ≤ ∑ i : Fin m, |activeBit (omega i).1*
        Real.exp (-r*interpolateLogBid beta gamma t (omega i).2)*
        (-r*(gamma (omega i).2-beta (omega i).2))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, (activeBit (omega i).1*
        Real.exp (-r*interpolateLogBid beta gamma t (omega i).2))*(r*delta) := by
      apply Finset.sum_le_sum
      intro i _
      have hw : 0 ≤ activeBit (omega i).1*Real.exp (-r*interpolateLogBid beta gamma t (omega i).2) :=
        mul_nonneg (activeBit_nonneg _) (Real.exp_pos _).le
      rw [abs_mul, abs_of_nonneg hw, abs_mul, abs_neg, abs_of_nonneg hr]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdiff _) hr) hw
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem finiteRowScore_interpolate_deriv_bound {m : ℕ} {V : Type*}
    (d c : ℕ) (hd : 1 ≤ d) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio delta : ℝ) (beta gamma : V → ℝ)
    (hdiff : ∀ v, |gamma v-beta v| ≤ delta) (v z t : ℝ) (omega : RivalProfile m V) :
    ∃ D : ℝ,
      HasDerivAt (fun s => finiteRowScore d c a G p0 baseRatio
        (interpolateLogBid beta gamma s) v z omega) D t ∧
      |D| ≤ |sourceStateInfluence d a G p0
        (finiteRowState d c baseRatio (interpolateLogBid beta gamma t) v z omega)| * delta := by
  let r := 1/(d:ℝ)
  let W := rivalInverseSum r (interpolateLogBid beta gamma t) omega
  let A := ((1+activeCount omega-c:ℕ):ℝ)
  let vf := v*sourceValueFactor d a p0
  let gf := baseRatio*sourceValueFactor d a p0
  let P := logAllocation r A W z
  let R := vf*polynomialFirst (d+1) successIndicator P-
    Real.exp z*polynomialFirst (d+1) a.charge P-gf*polynomialFirst (d+1) G.charge P
  let Rp := vf*polynomialSecond (d+1) successIndicator P-
    Real.exp z*polynomialSecond (d+1) a.charge P-gf*polynomialSecond (d+1) G.charge P
  let Dw := rivalSumScoreDerivative r (1-P) (logShare r W z) (Real.exp z) R Rp
    (polynomialFirst (d+1) a.charge P) (W+Real.exp (-r*z))
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hr : 0 ≤ r := by dsimp [r]; exact (one_div_pos.mpr hdpos).le
  have hW : 0 ≤ W := rivalInverseSum_nonneg _ _ omega
  have hscalar := hasDerivAt_score_rivalSum r A W vf gf z hW
    (polynomialFirst (d+1) successIndicator) (polynomialSecond (d+1) successIndicator)
    (binomialPolynomial (d+1) a.charge) (polynomialFirst (d+1) a.charge)
    (polynomialSecond (d+1) a.charge) (polynomialFirst (d+1) G.charge)
    (polynomialSecond (d+1) G.charge)
    (hasDerivAt_polynomialFirst _ _ _) (hasDerivAt_binomialPolynomial _ _ _)
    (hasDerivAt_polynomialFirst _ _ _) (hasDerivAt_polynomialFirst _ _ _)
  have hpath := hscalar.comp t (hasDerivAt_rivalInverseSum_interpolate r beta gamma t omega)
  have hc := cross_eq_rivalSumDerivative r A W z (Real.exp z) R Rp
    (polynomialFirst (d+1) a.charge P) hW
  have hlink := actualCross_eq_sourceStateInfluence d c a G p0 baseRatio
    (interpolateLogBid beta gamma t) v z omega
  have hcross : sourceStateInfluence d a G p0
      (finiteRowState d c baseRatio (interpolateLogBid beta gamma t) v z omega) = -r*W*Dw := by
    rw [← hlink]
    exact hc
  refine ⟨Dw*rivalInverseDerivative r beta gamma t omega, hpath, ?_⟩
  rw [abs_mul]
  calc
    _ ≤ |Dw| * (r*W*delta) := mul_le_mul_of_nonneg_left
      (rivalInverseDerivative_bound r delta hr beta gamma hdiff t omega) (abs_nonneg _)
    _ = |-r*W*Dw| * delta := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hr, abs_of_nonneg hW]
      ring
    _ = _ := by rw [hcross]

theorem finiteRowScore_parameter_bound {m : ℕ} {V : Type*}
    (d c : ℕ) (hd : 1 ≤ d) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio delta L : ℝ) (hdelta : 0 ≤ delta) (beta gamma : V → ℝ)
    (hdiff : ∀ v, |gamma v-beta v| ≤ delta) (v z : ℝ) (omega : RivalProfile m V)
    (hcross : ∀ t ∈ Icc (0:ℝ) 1, |sourceStateInfluence d a G p0
      (finiteRowState d c baseRatio (interpolateLogBid beta gamma t) v z omega)| ≤ L) :
    |finiteRowScore d c a G p0 baseRatio gamma v z omega-
      finiteRowScore d c a G p0 baseRatio beta v z omega| ≤ L*delta := by
  choose D hD hbound using fun t => finiteRowScore_interpolate_deriv_bound
    d c hd a G p0 baseRatio delta beta gamma hdiff v z t omega
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hD t).hasDerivWithinAt)
    (fun t ht => (by simpa only [Real.norm_eq_abs] using
      (hbound t).trans (mul_le_mul_of_nonneg_right (hcross t ⟨ht.1, ht.2.le⟩) hdelta)))
  have hzero : interpolateLogBid beta gamma 0 = beta := by
    funext w
    simp only [interpolateLogBid, zero_mul, add_zero]
  have hone : interpolateLogBid beta gamma 1 = gamma := by
    funext w
    dsimp [interpolateLogBid]
    ring
  simpa only [Real.norm_eq_abs, hzero, hone] using hh

end FCAppendix.Exclusive.Narrow.Existence
