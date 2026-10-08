import FCAppendix.Exclusive.CompletionForcedConcentration
import FCAppendix.Exclusive.NarrowFOCTransfer
import FCAppendix.Exclusive.NarrowLocalIdentification
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
namespace FCAppendix.Completion.Exclusive
open MeasureTheory ProbabilityTheory Filter Topology Set
open FCAppendix Game Bayes Exclusive Exclusive.Narrow Exclusive.Narrow.Finite
open Bayes.ExclusiveNarrow
open scoped BigOperators ProbabilityTheory ContDiff

structure PolynomialBounds (n : ℕ) (f : ℕ → ℝ) (B L : ℝ) : Prop where
  B_nonneg : 0 ≤ B
  L_nonneg : 0 ≤ L
  value : ∀ p ∈ Icc (0:ℝ) 1, |binomialPolynomial n f p| ≤ B
  derivative : ∀ p ∈ Icc (0:ℝ) 1, |binomialPolynomialDerivative n f p| ≤ B
  derivative_lipschitz : ∀ p ∈ Icc (0:ℝ) 1, ∀ q ∈ Icc (0:ℝ) 1,
    |binomialPolynomialDerivative n f p-binomialPolynomialDerivative n f q| ≤ L*|p-q|

theorem polynomialBounds_exists (n : ℕ) (f : ℕ → ℝ) :
    ∃ B L, PolynomialBounds n f B L := by
  obtain ⟨K,hK⟩ := countTestBound_exists n f
  have hc : Continuous (fun p => |deriv (binomialPolynomialDerivative n f) p|) :=
    ((contDiff_binomialPolynomialDerivative n f).continuous_deriv (by simp)).abs
  obtain ⟨x,_hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by constructor <;> norm_num⟩) hc.continuousOn
  rw [isMaxOn_iff] at hmax
  let B := max K (2*(n:ℝ)*K)
  let L := |deriv (binomialPolynomialDerivative n f) x|
  refine ⟨B,L,⟨hK.1.trans (le_max_left _ _), abs_nonneg _, ?_, ?_, ?_⟩⟩
  · exact fun p hp => (abs_binomialPolynomial_le n f hK hp).trans (le_max_left _ _)
  · exact fun p hp => (abs_binomialPolynomialDerivative_le n f hK hp).trans (le_max_right _ _)
  · intro p hp q hq
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z _ => (contDiff_binomialPolynomialDerivative n f).differentiable (by simp) z)
      (fun z hz => by simpa [Real.norm_eq_abs] using hmax z hz)
      (convex_Icc (0:ℝ) 1) hq hp
    simpa [Real.norm_eq_abs,L] using hmv

theorem PolynomialBounds.value_lipschitz {n : ℕ} {f : ℕ → ℝ} {B L : ℝ}
    (H : PolynomialBounds n f B L) {p q : ℝ}
    (hp : p ∈ Icc (0:ℝ) 1) (hq : q ∈ Icc (0:ℝ) 1) :
    |binomialPolynomial n f p-binomialPolynomial n f q| ≤ B*|p-q| := by
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hasDerivAt_binomialPolynomial n f z).hasDerivWithinAt)
    (fun z hz => by simpa [Real.norm_eq_abs] using H.derivative z hz)
    (convex_Icc (0:ℝ) 1) hq hp
  simpa [Real.norm_eq_abs] using hmv

theorem PolynomialBounds.mono {n : ℕ} {f : ℕ → ℝ} {B L B' L' : ℝ}
    (H : PolynomialBounds n f B L) (hB : B ≤ B') (hL : L ≤ L') :
    PolynomialBounds n f B' L' :=
  ⟨H.B_nonneg.trans hB,H.L_nonneg.trans hL,
    fun p hp => (H.value p hp).trans hB,
    fun p hp => (H.derivative p hp).trans hB,
    fun p hp q hq => (H.derivative_lipschitz p hp q hq).trans
      (mul_le_mul_of_nonneg_right hL (abs_nonneg _))⟩

theorem polynomial_mix (n : ℕ) (f g : ℕ → ℝ) (a b p : ℝ) :
    binomialPolynomial n (fun j => a*f j+b*g j) p =
      a*binomialPolynomial n f p+b*binomialPolynomial n g p := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binomialPolynomial,ih]; ring

theorem polynomialDerivative_mix (n : ℕ) (f g : ℕ → ℝ) (a b p : ℝ) :
    binomialPolynomialDerivative n (fun j => a*f j+b*g j) p =
      a*binomialPolynomialDerivative n f p+b*binomialPolynomialDerivative n g p := by
  induction n generalizing f g with
  | zero => simp [binomialPolynomialDerivative]
  | succ n ih => simp only [binomialPolynomialDerivative,polynomial_mix,ih]; ring

theorem PolynomialBounds.mix {n : ℕ} {f g : ℕ → ℝ} {B L eta : ℝ}
    (hf : PolynomialBounds n f B L) (hg : PolynomialBounds n g B L)
    (heta : eta ∈ Icc (0:ℝ) 1) :
    PolynomialBounds n (fun j => (1-eta)*f j+eta*g j) B L := by
  have hweighted {x y K : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) :
      |(1-eta)*x+eta*y| ≤ K := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr heta.2),abs_of_nonneg heta.1]
    nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr heta.2),
      mul_le_mul_of_nonneg_left hy heta.1]
  refine ⟨hf.B_nonneg,hf.L_nonneg,?_,?_,?_⟩
  · intro p hp; rw [polynomial_mix]; exact hweighted (hf.value p hp) (hg.value p hp)
  · intro p hp; rw [polynomialDerivative_mix]; exact hweighted (hf.derivative p hp) (hg.derivative p hp)
  · intro p hp q hq
    rw [polynomialDerivative_mix,polynomialDerivative_mix]
    have he : (1-eta)*binomialPolynomialDerivative n f p+eta*binomialPolynomialDerivative n g p-
        ((1-eta)*binomialPolynomialDerivative n f q+eta*binomialPolynomialDerivative n g q) =
        (1-eta)*(binomialPolynomialDerivative n f p-binomialPolynomialDerivative n f q)+
        eta*(binomialPolynomialDerivative n g p-binomialPolynomialDerivative n g q) := by ring
    rw [he]
    exact hweighted (hf.derivative_lipschitz p hp q hq) (hg.derivative_lipschitz p hp q hq)

theorem source_polynomial_bounds (n : ℕ) (G : Schedule n) :
    ∃ B L, PolynomialBounds n successIndicator B L ∧
      PolynomialBounds n G.charge B L ∧
      ∀ a : UserTariff, a.Allowed → PolynomialBounds n a.charge B L := by
  obtain ⟨Bs,Ls,hs⟩ := polynomialBounds_exists n successIndicator
  obtain ⟨Bg,Lg,hg⟩ := polynomialBounds_exists n G.charge
  obtain ⟨Bu,Lu,hu⟩ := polynomialBounds_exists n UserTariff.unique.charge
  obtain ⟨B0,L0,h0⟩ := polynomialBounds_exists n (UserTariff.affine 0).charge
  obtain ⟨B1,L1,h1⟩ := polynomialBounds_exists n (UserTariff.affine 1).charge
  let B := Bs+Bg+Bu+B0+B1
  let L := Ls+Lg+Lu+L0+L1
  have hBs : Bs ≤ B := by dsimp [B]; linarith [hg.B_nonneg,hu.B_nonneg,h0.B_nonneg,h1.B_nonneg]
  have hBg : Bg ≤ B := by dsimp [B]; linarith [hs.B_nonneg,hu.B_nonneg,h0.B_nonneg,h1.B_nonneg]
  have hBu : Bu ≤ B := by dsimp [B]; linarith [hs.B_nonneg,hg.B_nonneg,h0.B_nonneg,h1.B_nonneg]
  have hB0 : B0 ≤ B := by dsimp [B]; linarith [hs.B_nonneg,hg.B_nonneg,hu.B_nonneg,h1.B_nonneg]
  have hB1 : B1 ≤ B := by dsimp [B]; linarith [hs.B_nonneg,hg.B_nonneg,hu.B_nonneg,h0.B_nonneg]
  have hLs : Ls ≤ L := by dsimp [L]; linarith [hg.L_nonneg,hu.L_nonneg,h0.L_nonneg,h1.L_nonneg]
  have hLg : Lg ≤ L := by dsimp [L]; linarith [hs.L_nonneg,hu.L_nonneg,h0.L_nonneg,h1.L_nonneg]
  have hLu : Lu ≤ L := by dsimp [L]; linarith [hs.L_nonneg,hg.L_nonneg,h0.L_nonneg,h1.L_nonneg]
  have hL0 : L0 ≤ L := by dsimp [L]; linarith [hs.L_nonneg,hg.L_nonneg,hu.L_nonneg,h1.L_nonneg]
  have hL1 : L1 ≤ L := by dsimp [L]; linarith [hs.L_nonneg,hg.L_nonneg,hu.L_nonneg,h0.L_nonneg]
  refine ⟨B,L,hs.mono hBs hLs,hg.mono hBg hLg,?_⟩
  intro a ha
  cases a with
  | unique => exact hu.mono hBu hLu
  | affine eta =>
    have he : (UserTariff.affine eta).charge = fun j =>
        (1-eta)*(UserTariff.affine 0).charge j+eta*(UserTariff.affine 1).charge j := by
      funext j
      by_cases hj : j = 0 <;> simp [UserTariff.charge,hj]
    rw [he]
    exact (h0.mono hB0 hL0).mix (h1.mono hB1 hL1) ha

theorem scaled_test_pointwise {n : ℕ} {f : ℕ → ℝ} {B L u p z s : ℝ}
    (H : PolynomialBounds n f B L) (hu : u < 1)
    (hp : p ∈ Icc (0:ℝ) u) (hz : z ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    |binomialPolynomialDerivative n f z*((1-z)/(1-p))*(1-s)-
      binomialPolynomialDerivative n f p| ≤ ((L+B)/(1-u))*(|z-p|+s) := by
  have hp1 : p ∈ Icc (0:ℝ) 1 := ⟨hp.1,hp.2.trans hu.le⟩
  have hq : 0 < 1-p := sub_pos.mpr (hp.2.trans_lt hu)
  have hqu : 0 < 1-u := sub_pos.mpr hu
  have hr : 0 ≤ (1-z)/(1-p)*(1-s) :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hz.2) hq.le) (sub_nonneg.mpr hs.2)
  have hrb : (1-z)/(1-p)*(1-s) ≤ 1/(1-u) := by
    have hqle : 1-u ≤ 1-p := by linarith [hp.2]
    have hzle : (1-z)*(1-s) ≤ 1 := by
      calc
        _ ≤ (1:ℝ)*1 := mul_le_mul (by linarith [hz.1]) (by linarith [hs.1])
          (sub_nonneg.mpr hs.2) zero_le_one
        _ = 1 := one_mul 1
    rw [div_mul_eq_mul_div]
    exact (div_le_div_of_nonneg_right hzle hq.le).trans
      (one_div_le_one_div_of_le hqu hqle)
  have hratio : |(1-z)/(1-p)*(1-s)-1| ≤ (|z-p|+s)/(1-u) := by
    have he : (1-z)/(1-p)*(1-s)-1 = ((p-z)-(1-z)*s)/(1-p) := by
      field_simp [hq.ne']
      ring
    rw [he,abs_div,abs_of_pos hq]
    have hn : |(p-z)-(1-z)*s| ≤ |z-p|+s := by
      apply (show |(p-z)-(1-z)*s| ≤ |p-z|+|(1-z)*s| from
        by simpa using abs_sub_le (p-z) 0 ((1-z)*s)).trans
      rw [abs_sub_comm p z,abs_mul,abs_of_nonneg (sub_nonneg.mpr hz.2),abs_of_nonneg hs.1]
      nlinarith [mul_nonneg hz.1 hs.1]
    exact (div_le_div_of_nonneg_right hn hq.le).trans
      (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) hs.1) hqu (by linarith [hp.2]))
  have hid : binomialPolynomialDerivative n f z*((1-z)/(1-p))*(1-s)-
      binomialPolynomialDerivative n f p =
      (binomialPolynomialDerivative n f z-binomialPolynomialDerivative n f p)*
        ((1-z)/(1-p)*(1-s)) + binomialPolynomialDerivative n f p*
        ((1-z)/(1-p)*(1-s)-1) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul (binomialPolynomialDerivative n f z-binomialPolynomialDerivative n f p),
    abs_mul (binomialPolynomialDerivative n f p),abs_of_nonneg hr]
  have h1 := mul_le_mul (H.derivative_lipschitz z hz p hp1) hrb hr
    (mul_nonneg H.L_nonneg (abs_nonneg _))
  have h2 := mul_le_mul (H.derivative p hp1) hratio (abs_nonneg _) H.B_nonneg
  calc
    _ ≤ L*|z-p| *(1/(1-u))+B*((|z-p|+s)/(1-u)) := add_le_add h1 h2
    _ = (L*|z-p|+B*(|z-p|+s))/(1-u) := by ring
    _ ≤ ((L+B)*(|z-p|+s))/(1-u) := by
      apply div_le_div_of_nonneg_right _ hqu.le
      nlinarith [mul_nonneg H.L_nonneg hs.1]
    _ = _ := by ring

variable {m c d : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem scaled_row_velocity (P : Corridor (d+1) m c) (hd : 1 ≤ d)
    {N : ℕ} {W b p : ℝ} (hb : 0 < b) (hp : p < 1) :
    bidCoordinateScale d b p*P.velocity N W b =
      ((1-P.allocation N W b)/(1-p))*(1-P.share W b) := by
  have hr : (d:ℝ)*rate (d+1) = 1 := by
    have he := rate_mul (d+1) (by omega)
    simpa only [Nat.add_sub_cancel,mul_comm] using he
  unfold bidCoordinateScale Corridor.velocity Corridor.velocity0
  calc
    ((d:ℝ)*b/(1-p))*(rate (d+1)*(1-P.allocation N W b)/b*(1-P.share W b)) =
        ((d:ℝ)*rate (d+1))*(((1-P.allocation N W b)/(1-p))*(1-P.share W b)) := by
      field_simp [hb.ne',(sub_pos.mpr hp).ne']
    _ = _ := by rw [hr,one_mul]

theorem scaled_row_moment_error (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (hd : 1 ≤ d) (i : Fin m)
    (f : ℕ → ℝ) {B L u b p : ℝ} (H : PolynomialBounds (d+1) f B L)
    (hu : u < 1) (hb : b ∈ Icc P.lower P.upper) (hp : p ∈ Icc (0:ℝ) u) :
    |bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative f b-
      binomialPolynomialDerivative (d+1) f p| ≤
      ((L+B)/(1-u))*((∫ z, |boundedP Γ P hplay i b z-p| ∂userProfileLaw Γ)+
        ∫ z, boundedShare Γ P hplay i b z ∂userProfileLaw Γ) := by
  let R := gameRow Γ P hplay i
  have he : ∀ᵐ z ∂userProfileLaw Γ,
      bidCoordinateScale d b p*(binomialPolynomialDerivative (d+1) f (R.p b z)*R.dp b z)-
        binomialPolynomialDerivative (d+1) f p =
      binomialPolynomialDerivative (d+1) f (boundedP Γ P hplay i b z)*
        ((1-boundedP Γ P hplay i b z)/(1-p))*(1-boundedShare Γ P hplay i b z)-
        binomialPolynomialDerivative (d+1) f p := by
    filter_upwards [boundedP_eq_row Γ P hplay i hb,boundedShare_eq_row Γ P hplay i hb] with z hz hs
    rw [hz,hs]
    have hv := scaled_row_velocity P hd (N := R.count z) (W := R.weight z)
      (P.lower_pos.trans_le hb.1) (hp.2.trans_lt hu)
    change bidCoordinateScale d b p *
        (binomialPolynomialDerivative (d+1) f (P.allocation (R.count z) (R.weight z) b) *
          P.velocity (R.count z) (R.weight z) b) - _ = _
    rw [mul_left_comm (bidCoordinateScale d b p), hv]
    dsimp only [R, Row.p]
    ring
  obtain ⟨K,hK⟩ := countTestBound_exists (d+1) f
  have hi := R.integrable_testDerivative f hK hb
  have hiP := boundedP_distance_integrable Γ P hplay i b p
  have hiS := boundedShare_integrable Γ P hplay i b
  have heI : bidCoordinateScale d b p*R.momentDerivative f b-
      binomialPolynomialDerivative (d+1) f p =
      ∫ z, bidCoordinateScale d b p*(binomialPolynomialDerivative (d+1) f (R.p b z)*R.dp b z)-
        binomialPolynomialDerivative (d+1) f p ∂userProfileLaw Γ := by
    rw [integral_sub (hi.const_mul _) (integrable_const _),integral_const_mul]
    simp [Row.momentDerivative]
  rw [heI]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, ((L+B)/(1-u))*(|boundedP Γ P hplay i b z-p|+boundedShare Γ P hplay i b z)
        ∂userProfileLaw Γ := by
      apply integral_mono_ae ((hi.const_mul _).sub (integrable_const _)).abs
        ((hiP.add hiS).const_mul _)
      filter_upwards [he] with z hz
      simp only [Pi.sub_apply, Pi.add_apply]
      rw [hz]
      exact scaled_test_pointwise H hu hp (unitClamp_mem _) (unitClamp_mem _)
    _ = _ := by rw [integral_const_mul,integral_add hiP hiS]

theorem row_value_error (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (i : Fin m)
    (f : ℕ → ℝ) {B L b p : ℝ} (H : PolynomialBounds (d+1) f B L)
    (hb : b ∈ Icc P.lower P.upper) (hp : p ∈ Icc (0:ℝ) 1) :
    |(gameRow Γ P hplay i).moment f b-binomialPolynomial (d+1) f p| ≤
      B*(∫ z, |boundedP Γ P hplay i b z-p| ∂userProfileLaw Γ) := by
  let R := gameRow Γ P hplay i
  obtain ⟨K,hK⟩ := countTestBound_exists (d+1) f
  have hi := R.integrable_test f hK hb
  have hiP := boundedP_distance_integrable Γ P hplay i b p
  have he : R.moment f b-binomialPolynomial (d+1) f p =
      ∫ z, binomialPolynomial (d+1) f (R.p b z)-binomialPolynomial (d+1) f p
        ∂userProfileLaw Γ := by
    rw [integral_sub hi (integrable_const _)]
    simp only [Row.moment, integral_const, probReal_univ, one_smul]
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, B*|boundedP Γ P hplay i b z-p| ∂userProfileLaw Γ := by
      apply integral_mono_ae (hi.sub (integrable_const _)).abs (hiP.const_mul B)
      filter_upwards [boundedP_eq_row Γ P hplay i hb] with z hz
      simp only [Pi.sub_apply]
      change |binomialPolynomial (d+1) f ((gameRow Γ P hplay i).p b z) - _| ≤ _
      rw [← hz]
      exact H.value_lipschitz (unitClamp_mem _) hp
    _ = _ := integral_const_mul _ _

theorem derivativeCorrection_with_bounds (Γ : FiniteGame m (d+1) c Seed)
    (P : Corridor (d+1) m c) (hplay : CorridorPlay Γ P) (hd : 1 ≤ d) (i : Fin m)
    {l u : ℝ} (hl : 0 ≤ l) (hu : u < 1) (B L : ℝ)
    (hS : PolynomialBounds (d+1) successIndicator B L)
    (hG : PolynomialBounds (d+1) Γ.G.charge B L)
    (hA : ∀ a : UserTariff, a.Allowed → PolynomialBounds (d+1) a.charge B L) :
    ∀ a : UserTariff, a.Allowed →
      FiniteBroadcastDerivativeCorrection Γ a i P.lower P.upper l u
        ((L+B)/(1-u)+(d:ℝ)*P.upper/(1-u)*B+(P.upper+|Γ.g|)*((L+B)/(1-u)))
        ((gameRow Γ P hplay i).momentDerivative successIndicator)
        ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g)
        (boundedP Γ P hplay i) (boundedShare Γ P hplay i) := by
  let D := (L+B)/(1-u)
  let V := (d:ℝ)*P.upper/(1-u)
  let K := D+V*B+(P.upper+|Γ.g|)*D
  have hu0 : 0 < 1-u := sub_pos.mpr hu
  have hB := hS.B_nonneg
  have hL := hS.L_nonneg
  have hup := P.upper_pos
  have hD : 0 ≤ D := div_nonneg (add_nonneg hL hB) hu0.le
  have hV : 0 ≤ V := div_nonneg (mul_nonneg (Nat.cast_nonneg d) hup.le) hu0.le
  have hK0 : 0 ≤ K := by
    exact add_nonneg (add_nonneg hD (mul_nonneg hV hB))
      (mul_nonneg (add_nonneg hup.le (abs_nonneg Γ.g)) hD)
  have hDK : D ≤ K := by
    dsimp only [K]
    linarith [mul_nonneg hV hB, mul_nonneg (add_nonneg hup.le (abs_nonneg Γ.g)) hD]
  change ∀ a : UserTariff, a.Allowed →
    FiniteBroadcastDerivativeCorrection Γ a i P.lower P.upper l u K
      ((gameRow Γ P hplay i).momentDerivative successIndicator)
      ((gameRow Γ P hplay i).costDerivative a Γ.G Γ.g)
      (boundedP Γ P hplay i) (boundedShare Γ P hplay i)
  intro a ha
  refine ⟨hK0, ?_, ?_⟩
  · intro b hb p hp
    have he0 : 0 ≤ (∫ z, |boundedP Γ P hplay i b z-p| ∂userProfileLaw Γ)+
        ∫ z, boundedShare Γ P hplay i b z ∂userProfileLaw Γ :=
      add_nonneg (integral_nonneg fun _ => abs_nonneg _)
        (integral_nonneg fun _ => (unitClamp_mem _).1)
    have h := scaled_row_moment_error Γ P hplay hd i successIndicator hS hu
      ⟨hb.1.le,hb.2.le⟩ ⟨hl.trans hp.1,hp.2⟩
    have heq : binomialPolynomialDerivative (d+1) successIndicator p = Exclusive.Narrow.successSlope d p := by
      simpa only [Exclusive.Narrow.successSlope, Nat.add_sub_cancel] using
        binomialPolynomialDerivative_success d p
    rw [heq] at h
    exact h.trans (mul_le_mul_of_nonneg_right hDK he0)
  · intro b hb p hp
    let e := (∫ z, |boundedP Γ P hplay i b z-p| ∂userProfileLaw Γ)+
      ∫ z, boundedShare Γ P hplay i b z ∂userProfileLaw Γ
    have he0 : 0 ≤ e := add_nonneg (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => (unitClamp_mem _).1)
    have hb0 : 0 < b := P.lower_pos.trans hb.1
    have hp0 : 0 ≤ p := hl.trans hp.1
    have hp1 : p < 1 := hp.2.trans_lt hu
    have hta : |bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative a.charge b-
        binomialPolynomialDerivative (d+1) a.charge p| ≤ D*e :=
      scaled_row_moment_error Γ P hplay hd i a.charge (hA a ha) hu
        ⟨hb.1.le,hb.2.le⟩ ⟨hp0,hp.2⟩
    have htg : |bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative Γ.G.charge b-
        binomialPolynomialDerivative (d+1) Γ.G.charge p| ≤ D*e :=
      scaled_row_moment_error Γ P hplay hd i Γ.G.charge hG hu
        ⟨hb.1.le,hb.2.le⟩ ⟨hp0,hp.2⟩
    have hv : |bidCoordinateScale d b p| ≤ V := by
      have hs0 : 0 ≤ bidCoordinateScale d b p :=
        div_nonneg (mul_nonneg (Nat.cast_nonneg d) hb0.le) (sub_pos.mpr hp1).le
      rw [abs_of_nonneg hs0]
      change (d:ℝ)*b/(1-p) ≤ (d:ℝ)*P.upper/(1-u)
      calc
        _ ≤ (d:ℝ)*P.upper/(1-p) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb.2.le (Nat.cast_nonneg d)) (sub_pos.mpr hp1).le
        _ ≤ _ := div_le_div_of_nonneg_left
          (mul_nonneg (Nat.cast_nonneg d) hup.le) hu0 (by linarith [hp.2])
    have hmoment : |(gameRow Γ P hplay i).moment a.charge b-
        binomialPolynomial (d+1) a.charge p| ≤ B*e := by
      apply (row_value_error Γ P hplay i a.charge (hA a ha)
        ⟨hb.1.le,hb.2.le⟩ ⟨hp0,hp1.le⟩).trans
      apply mul_le_mul_of_nonneg_left _ hB
      exact le_add_of_nonneg_right (integral_nonneg fun _ => (unitClamp_mem _).1)
    have hexpand : bidCoordinateScale d b p*(gameRow Γ P hplay i).costDerivative a Γ.G Γ.g b-
        finiteCostTarget d a Γ.G Γ.g b p =
        bidCoordinateScale d b p*((gameRow Γ P hplay i).moment a.charge b-
          binomialPolynomial (d+1) a.charge p)+
        b*(bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative a.charge b-
          binomialPolynomialDerivative (d+1) a.charge p)+
        Γ.g*(bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative Γ.G.charge b-
          binomialPolynomialDerivative (d+1) Γ.G.charge p) := by
      unfold Row.costDerivative finiteCostTarget
      ring
    rw [hexpand]
    have h1 := mul_le_mul hv hmoment (abs_nonneg _) hV
    have h2 := mul_le_mul (show |b| ≤ P.upper by simpa [abs_of_pos hb0] using hb.2.le)
      hta (abs_nonneg _) hup.le
    have h3 := mul_le_mul_of_nonneg_left htg (abs_nonneg Γ.g)
    calc
      _ ≤ |bidCoordinateScale d b p| *
          |(gameRow Γ P hplay i).moment a.charge b-binomialPolynomial (d+1) a.charge p|+
          |b| *|bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative a.charge b-
            binomialPolynomialDerivative (d+1) a.charge p|+
          |Γ.g| *|bidCoordinateScale d b p*(gameRow Γ P hplay i).momentDerivative Γ.G.charge b-
            binomialPolynomialDerivative (d+1) Γ.G.charge p| := by
        rw [← abs_mul, ← abs_mul, ← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ V*(B*e)+P.upper*(D*e)+|Γ.g| *(D*e) := add_le_add (add_le_add h1 h2) h3
      _ ≤ K*e := by
        dsimp only [K]
        nlinarith [mul_nonneg hD he0]

end FCAppendix.Completion.Exclusive
