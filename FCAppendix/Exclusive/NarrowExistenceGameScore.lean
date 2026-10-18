import FCAppendix.Exclusive.NarrowExistenceGameState
import FCAppendix.Exclusive.NarrowExistenceTariffJets
import FCAppendix.Exclusive.CompactBestResponse
import Mathlib.Probability.Distributions.Bernoulli

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

abbrev ValueBand (eps : ℝ) := Icc (1-eps) (1+eps)
abbrev RivalProfile (m : ℕ) (V : Type*) := Fin m → Bool × V

def activeBit (a : Bool) : ℝ := if a then 1 else 0
def activeNat (a : Bool) : ℕ := if a then 1 else 0

theorem activeBit_nonneg (a : Bool) : 0 ≤ activeBit a := by cases a <;> norm_num [activeBit]

theorem continuous_activeBit : Continuous activeBit := continuous_of_discreteTopology
theorem continuous_activeNat : Continuous activeNat := continuous_of_discreteTopology

def activeCount {m : ℕ} {V : Type*} (omega : RivalProfile m V) : ℕ :=
  ∑ i, activeNat (omega i).1

def rivalInverseSum {m : ℕ} {V : Type*} (r : ℝ) (beta : V → ℝ)
    (omega : RivalProfile m V) : ℝ :=
  ∑ i, activeBit (omega i).1*Real.exp (-r*beta (omega i).2)

theorem rivalInverseSum_nonneg {m : ℕ} {V : Type*} (r : ℝ) (beta : V → ℝ)
    (omega : RivalProfile m V) : 0 ≤ rivalInverseSum r beta omega :=
  Finset.sum_nonneg fun i _ => mul_nonneg (activeBit_nonneg (omega i).1) (Real.exp_pos _).le

theorem activeCount_le {m : ℕ} {V : Type*} (omega : RivalProfile m V) :
    activeCount omega ≤ m := by
  have h : activeCount omega ≤ ∑ _i : Fin m, 1 := by
    apply Finset.sum_le_sum
    intro i _
    cases (omega i).1 <;> simp [activeNat]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h

def sampleLaw {V : Type*} [MeasurableSpace V] (h : unitInterval) (nu : Measure V) :
    Measure (Bool × V) := (bernoulliMeasure true false h).prod nu

instance sampleLaw_probability {V : Type*} [MeasurableSpace V]
    (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (sampleLaw h nu) := by unfold sampleLaw; infer_instance

def iidRivalLaw {V : Type*} [MeasurableSpace V] (m : ℕ) (h : unitInterval)
    (nu : Measure V) : Measure (RivalProfile m V) :=
  Measure.pi fun _ : Fin m => sampleLaw h nu

instance iidRivalLaw_probability {V : Type*} [MeasurableSpace V]
    (m : ℕ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (iidRivalLaw m h nu) := by unfold iidRivalLaw; infer_instance

theorem continuous_activeCount {m : ℕ} {V : Type*} [TopologicalSpace V] :
    Continuous (activeCount (m := m) (V := V)) := by
  unfold activeCount
  exact continuous_finsetSum _ fun i _ => continuous_activeNat.comp
    (continuous_fst.comp (continuous_apply i))

theorem continuous_rivalInverseSum {m : ℕ} {V : Type*} [TopologicalSpace V]
    (r : ℝ) (beta : V → ℝ) (hbeta : Continuous beta) :
    Continuous (rivalInverseSum (m := m) r beta) := by
  unfold rivalInverseSum
  apply continuous_finsetSum
  intro i _
  have hi : Continuous (fun omega : RivalProfile m V => omega i) := continuous_apply i
  exact (continuous_activeBit.comp (continuous_fst.comp hi)).mul
    (Real.continuous_exp.comp ((hbeta.comp (continuous_snd.comp hi)).const_mul (-r)))

abbrev ActiveIndex {m : ℕ} {V : Type*} (omega : RivalProfile m V) :=
  Option {i : Fin m // (omega i).1 = true}

def activeLogProfile {m : ℕ} {V : Type*} (beta : V → ℝ) (z : ℝ)
    (omega : RivalProfile m V) : ActiveIndex omega → ℝ
  | none => z
  | some i => beta (omega i.val).2

theorem activeIndex_card {m : ℕ} {V : Type*} (omega : RivalProfile m V) :
    Fintype.card (ActiveIndex omega) = 1+activeCount omega := by
  classical
  simp only [ActiveIndex, Fintype.card_option, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  unfold activeCount
  rw [add_comm]
  congr 1

theorem activeLogProfile_band {m : ℕ} {V : Type*}
    (beta : V → ℝ) (delta z : ℝ) (hz : z ∈ Icc (-delta) delta)
    (hbeta : ∀ v, beta v ∈ Icc (-delta) delta) (omega : RivalProfile m V) :
    ∀ i : ActiveIndex omega, activeLogProfile beta z omega i ∈ Icc (-delta) delta := by
  intro i
  cases i with
  | none => exact hz
  | some i => exact hbeta _

theorem activeLogProfile_sum {m : ℕ} {V : Type*}
    (r : ℝ) (beta : V → ℝ) (z : ℝ) (omega : RivalProfile m V) :
    Exclusive.Existence.inverseLogBidSum r (activeLogProfile beta z omega) =
      Real.exp (-r*z)+rivalInverseSum r beta omega := by
  classical
  unfold Exclusive.Existence.inverseLogBidSum
  rw [Fintype.sum_option]
  change Real.exp (-r*z)+(∑ i : {i : Fin m // (omega i).1 = true},
      Real.exp (-r*beta (omega i.val).2)) = _
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (fun i : Fin m => (omega i).1 = true))
    (by simp) (fun i : Fin m => Real.exp (-r*beta (omega i).2)), Finset.sum_filter]
  unfold rivalInverseSum
  apply Finset.sum_congr rfl
  intro i _
  cases (omega i).1 <;> simp [activeBit]

theorem logShare_eq_activeProfileShare {m : ℕ} {V : Type*}
    (r : ℝ) (beta : V → ℝ) (z : ℝ) (omega : RivalProfile m V) :
    logShare r (rivalInverseSum r beta omega) z =
      profileShare r (activeLogProfile beta z omega) none := by
  rw [profileShare, activeLogProfile_sum]
  dsimp [logShare, activeLogProfile]
  rw [add_comm]

def sourceValueFactor (d : ℕ) (a : UserTariff) (p0 : ℝ) : ℝ :=
  (1-p0)^d*fTariff d a p0

def polynomialFirst (n : ℕ) (f : ℕ → ℝ) : ℝ → ℝ := binomialPolynomialDerivative n f
def polynomialSecond (n : ℕ) (f : ℕ → ℝ) : ℝ → ℝ :=
  deriv (binomialPolynomialDerivative n f)

def finiteRowScore {m : ℕ} {V : Type*} (d c : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 baseRatio : ℝ) (beta : V → ℝ)
    (v z : ℝ) (omega : RivalProfile m V) : ℝ :=
  score (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
    (rivalInverseSum (1/(d:ℝ)) beta omega)
    (v*sourceValueFactor d a p0) (baseRatio*sourceValueFactor d a p0)
    (polynomialFirst (d+1) successIndicator)
    (binomialPolynomial (d+1) a.charge)
    (polynomialFirst (d+1) a.charge)
    (polynomialFirst (d+1) G.charge) z

def finiteExpectedScore {m : ℕ} {V : Type*} [MeasurableSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V)
    (beta : V → ℝ) (v z : ℝ) : ℝ :=
  ∫ omega, finiteRowScore (m := m) d c a G p0 baseRatio beta v z omega
    ∂iidRivalLaw m h nu

theorem binomialPolynomial_linear (n : ℕ) (f k : ℕ → ℝ) (a b p : ℝ) :
    binomialPolynomial n (fun j => a*f j+b*k j) p =
      a*binomialPolynomial n f p+b*binomialPolynomial n k p := by
  induction n generalizing f k with
  | zero => rfl
  | succ n ih => simp only [binomialPolynomial, ih]; ring

theorem binomialPolynomialDerivative_linear (n : ℕ) (f k : ℕ → ℝ) (a b p : ℝ) :
    binomialPolynomialDerivative n (fun j => a*f j+b*k j) p =
      a*binomialPolynomialDerivative n f p+b*binomialPolynomialDerivative n k p := by
  induction n generalizing f k with
  | zero => simp [binomialPolynomialDerivative]
  | succ n ih => simp only [binomialPolynomialDerivative, binomialPolynomial_linear, ih]; ring

theorem affine_charge_mix (eta : ℝ) :
    (UserTariff.affine eta).charge = fun j =>
      (1-eta)*(UserTariff.affine 0).charge j+eta*(UserTariff.affine 1).charge j := by
  funext j
  dsimp [UserTariff.charge]
  ring

theorem finiteRowScore_affine {m : ℕ} {V : Type*} (d c : ℕ)
    (eta : ℝ) (G : Schedule (d+1)) (p0 baseRatio : ℝ) (beta : V → ℝ)
    (v z : ℝ) (omega : RivalProfile m V) :
    finiteRowScore d c (.affine eta) G p0 baseRatio beta v z omega =
      (1-eta)*finiteRowScore d c (.affine 0) G p0 baseRatio beta v z omega+
        eta*finiteRowScore d c (.affine 1) G p0 baseRatio beta v z omega := by
  dsimp [finiteRowScore, sourceValueFactor, fTariff, score, polynomialFirst]
  rw [affine_charge_mix, binomialPolynomial_linear, binomialPolynomialDerivative_linear]
  simp only [sub_zero, one_mul, zero_mul, add_zero, sub_self, zero_add]
  ring

end FCAppendix.Exclusive.Narrow.Existence
