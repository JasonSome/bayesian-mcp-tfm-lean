import FCAppendix.Exclusive.NarrowExistenceGameStationary
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
namespace FCAppendix.Exclusive.Narrow.Existence
open MeasureTheory Set Filter Topology

def finiteRowUtility {m : ℕ} {V : Type*} (d c : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 baseRatio : ℝ) (beta : V → ℝ)
    (v z : ℝ) (omega : RivalProfile m V) : ℝ :=
  utility (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
    (rivalInverseSum (1/(d:ℝ)) beta omega)
    (v*sourceValueFactor d a p0) (baseRatio*sourceValueFactor d a p0)
    (binomialPolynomial (d+1) successIndicator) (binomialPolynomial (d+1) a.charge)
    (binomialPolynomial (d+1) G.charge) z

def finiteExpectedUtility {m : ℕ} {V : Type*} [MeasurableSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (h : unitInterval) (nu : Measure V) (beta : V → ℝ) (v z : ℝ) : ℝ :=
  ∫ omega, finiteRowUtility d c a G p0 baseRatio beta v z omega ∂iidRivalLaw m h nu

theorem hasDerivAt_finiteRowUtility {m : ℕ} {V : Type*} (d c : ℕ)
    (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (v z : ℝ) (omega : RivalProfile m V) :
    HasDerivAt (fun x => finiteRowUtility d c a G p0 baseRatio beta v x omega)
      (finiteRowScore d c a G p0 baseRatio beta v z omega) z :=
  hasDerivAt_utility (1/(d:ℝ)) ((1+activeCount omega-c:ℕ):ℝ)
    (rivalInverseSum (1/(d:ℝ)) beta omega)
    (v*sourceValueFactor d a p0) (baseRatio*sourceValueFactor d a p0) z
    (rivalInverseSum_nonneg _ _ omega)
    (binomialPolynomial (d+1) successIndicator) (polynomialFirst (d+1) successIndicator)
    (binomialPolynomial (d+1) a.charge) (polynomialFirst (d+1) a.charge)
    (binomialPolynomial (d+1) G.charge) (polynomialFirst (d+1) G.charge)
    (hasDerivAt_binomialPolynomial _ _ _) (hasDerivAt_binomialPolynomial _ _ _)
    (hasDerivAt_binomialPolynomial _ _ _)

theorem continuous_finiteRowState_joint {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (baseRatio : ℝ) (beta : V → ℝ) (hbeta : Continuous beta) (v : ℝ) :
    Continuous (fun t : ℝ × RivalProfile m V => finiteRowState d c baseRatio beta v t.1 t.2) := by
  have hW : Continuous (fun t : ℝ × RivalProfile m V => rivalInverseSum (1/(d:ℝ)) beta t.2) :=
    (continuous_rivalInverseSum (m := m) (1/(d:ℝ)) beta hbeta).comp continuous_snd
  have hex : Continuous (fun t : ℝ × RivalProfile m V => Real.exp (-(1/(d:ℝ))*t.1)) := by fun_prop
  have hden := hW.add hex
  have hdenpos (t : ℝ × RivalProfile m V) :
      0 < rivalInverseSum (1/(d:ℝ)) beta t.2+Real.exp (-(1/(d:ℝ))*t.1) :=
    add_pos_of_nonneg_of_pos (rivalInverseSum_nonneg _ _ t.2) (Real.exp_pos _)
  have hs : Continuous (fun t : ℝ × RivalProfile m V =>
      logShare (1/(d:ℝ)) (rivalInverseSum (1/(d:ℝ)) beta t.2) t.1) :=
    hex.div hden (fun t => (hdenpos t).ne')
  have hN : Continuous (fun t : ℝ × RivalProfile m V => ((1+activeCount t.2-c:ℕ):ℝ)) :=
    (continuous_of_discreteTopology : Continuous (fun N : ℕ => ((1+N-c:ℕ):ℝ))).comp
      (continuous_activeCount.comp continuous_snd)
  apply continuous_pi
  intro i
  fin_cases i
  · exact hN.mul hs
  · exact hs
  · exact Real.continuous_exp.comp continuous_fst
  · exact continuous_const
  · exact continuous_const

theorem continuous_finiteRowScore_joint {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (hbeta : Continuous beta) (v : ℝ) :
    Continuous (fun t : ℝ × RivalProfile m V => finiteRowScore d c a G p0 baseRatio beta v t.1 t.2) := by
  simp_rw [finiteRowScore_eq_sourceStateScore]
  exact (continuous_sourceStateScore d a G p0).comp
    (continuous_finiteRowState_joint d c baseRatio beta hbeta v)

theorem continuous_finiteRowUtility_joint {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (hbeta : Continuous beta) (v : ℝ) :
    Continuous (fun t : ℝ × RivalProfile m V => finiteRowUtility d c a G p0 baseRatio beta v t.1 t.2) := by
  have hstate := continuous_finiteRowState_joint (m := m) d c baseRatio beta hbeta v
  have hp : Continuous (fun t : ℝ × RivalProfile m V =>
      1-(finiteRowState d c baseRatio beta v t.1 t.2) 0) :=
    continuous_const.sub ((continuous_apply 0).comp hstate)
  exact ((continuous_const.mul ((contDiff_binomialPolynomial (d+1) successIndicator).continuous.comp hp)).sub
    ((Real.continuous_exp.comp continuous_fst).mul ((contDiff_binomialPolynomial (d+1) a.charge).continuous.comp hp))).sub
      (continuous_const.mul ((contDiff_binomialPolynomial (d+1) G.charge).continuous.comp hp))

theorem continuous_finiteRowUtility {m : ℕ} {V : Type*} [TopologicalSpace V]
    (d c : ℕ) (a : UserTariff) (G : Schedule (d+1)) (p0 baseRatio : ℝ)
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    Continuous (finiteRowUtility (m := m) d c a G p0 baseRatio beta v z) := by
  have hc := (continuous_finiteRowUtility_joint (m := m) d c a G p0 baseRatio beta hbeta v).comp
    ((continuous_const : Continuous (fun _ : RivalProfile m V => z)).prodMk continuous_id)
  exact hc

section Expected
variable {m : ℕ} {V : Type*} [TopologicalSpace V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompactSpace V]

theorem integrable_finiteRowUtility (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    Integrable (finiteRowUtility (m := m) d c a G p0 baseRatio beta v z) (iidRivalLaw m h nu) := by
  have hc := continuous_finiteRowUtility (m := m) d c a G p0 baseRatio beta hbeta v z
  obtain ⟨B, _hB, hb⟩ := compact_curvature_bounds _ _ hc hc Set.univ isCompact_univ
  apply Integrable.of_bound hc.measurable.aestronglyMeasurable B
  filter_upwards [] with omega
  simpa only [Real.norm_eq_abs] using (hb omega (Set.mem_univ _)).1

theorem hasDerivAt_finiteExpectedUtility (d c : ℕ) (a : UserTariff) (G : Schedule (d+1))
    (p0 baseRatio : ℝ) (h : unitInterval) (nu : Measure V) [IsProbabilityMeasure nu]
    (beta : V → ℝ) (hbeta : Continuous beta) (v z : ℝ) :
    HasDerivAt (finiteExpectedUtility (m := m) d c a G p0 baseRatio h nu beta v)
      (finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v z) z := by
  have hc := continuous_finiteRowScore_joint (m := m) d c a G p0 baseRatio beta hbeta v
  obtain ⟨B, _hB, hb⟩ := compact_curvature_bounds _ _ hc hc
    (Icc (z-1) (z+1) ×ˢ Set.univ) (isCompact_Icc.prod isCompact_univ)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := iidRivalLaw m h nu)
    (F := fun x omega => finiteRowUtility d c a G p0 baseRatio beta v x omega)
    (F' := fun x omega => finiteRowScore d c a G p0 baseRatio beta v x omega)
    (s := Ioo (z-1) (z+1)) (bound := fun _ : RivalProfile m V => B)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun x =>
      (continuous_finiteRowUtility (m := m) d c a G p0 baseRatio beta hbeta v x).measurable.aestronglyMeasurable))
    (integrable_finiteRowUtility (m := m) d c a G p0 baseRatio h nu beta hbeta v z)
    (continuous_finiteRowScore (m := m) d c a G p0 baseRatio beta hbeta v z).measurable.aestronglyMeasurable
    (by
      filter_upwards [] with omega x hx
      simpa only [Real.norm_eq_abs] using (hb (x,omega) ⟨⟨hx.1.le,hx.2.le⟩,Set.mem_univ _⟩).1)
    (integrable_const B)
    (Filter.Eventually.of_forall (fun omega x _ => hasDerivAt_finiteRowUtility d c a G p0 baseRatio beta v x omega))
  exact hderiv.2

theorem finiteExpectedUtility_maximizes_of_decrease (d c : ℕ) (a : UserTariff)
    (G : Schedule (d+1)) (p0 baseRatio : ℝ) (h : unitInterval)
    (nu : Measure V) [IsProbabilityMeasure nu] (beta : V → ℝ) (hbeta : Continuous beta)
    (v lo hi k b : ℝ) (hk : 0 < k) (hb : b ∈ Icc lo hi)
    (hroot : finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v b = 0)
    (hdec : ∀ x ∈ Icc lo hi, ∀ y ∈ Icc lo hi, x ≤ y →
      k*(y-x) ≤ finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v x-
        finiteExpectedScore (m := m) d c a G p0 baseRatio h nu beta v y)
    (z : ℝ) (hz : z ∈ Icc lo hi) :
    finiteExpectedUtility (m := m) d c a G p0 baseRatio h nu beta v z ≤
      finiteExpectedUtility (m := m) d c a G p0 baseRatio h nu beta v b := by
  let U := finiteExpectedUtility (m := m) d c a G p0 baseRatio h nu beta v
  have hd (x : ℝ) := hasDerivAt_finiteExpectedUtility (m := m) d c a G p0 baseRatio h nu beta hbeta v x
  have hc : ContinuousOn U (Icc lo hi) := fun x _ => (hd x).continuousAt.continuousWithinAt
  rcases le_total z b with hzb | hbz
  · have hsub : Icc lo b ⊆ Icc lo hi := Icc_subset_Icc_right hb.2
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc lo b) (hc.mono hsub)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' := interior_subset hx
        rw [(hd x).deriv]
        have hh := hdec x (hsub hx') b hb hx'.2
        have hp := mul_nonneg hk.le (sub_nonneg.mpr hx'.2)
        rw [hroot] at hh
        linarith)
    exact hm ⟨hz.1,hzb⟩ ⟨hb.1,le_rfl⟩ hzb
  · have hsub : Icc b hi ⊆ Icc lo hi := Icc_subset_Icc_left hb.1
    have hm := antitoneOn_of_deriv_nonpos (convex_Icc b hi) (hc.mono hsub)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' := interior_subset hx
        rw [(hd x).deriv]
        have hh := hdec b hb x (hsub hx') hx'.1
        have hp := mul_nonneg hk.le (sub_nonneg.mpr hx'.1)
        rw [hroot] at hh
        linarith)
    exact hm ⟨le_rfl,hb.2⟩ ⟨hbz,hz.2⟩ hbz

end Expected

namespace UniformFiniteConstants
variable {d : ℕ} {G : Schedule (d+1)} {h rho : ℝ}
    (U : UniformFiniteConstants d G h rho)

theorem exists_pure_restricted_maximizer (hd : 1 ≤ d) (hh : h ∈ Icc (0:ℝ) 1)
    (hp0 : 0 ≤ rho/h) (hp1 : rho/h < 1) {m : ℕ} (c : ℕ)
    (hM : U.M0 ≤ m+1) (hC : |(c:ℝ)/((m:ℝ)+1)-rho| < U.eta)
    (nu : Measure (ValueBand U.eps)) [IsProbabilityMeasure nu]
    (a : UserTariff) (ha : a.Allowed) (baseRatio : ℝ) (hbase : baseRatio ∈ Icc (0:ℝ) U.eps) :
    ∃ beta : Exclusive.Existence.bidBand (ValueBand U.eps) (-U.delta) U.delta,
      StrictMono beta.val ∧
      (∀ v : ValueBand U.eps, finiteExpectedScore (m := m) d c a G (rho/h) baseRatio
        ⟨h,hh⟩ nu beta.val v.val (beta.val v) = 0) ∧
      ∀ (v : ValueBand U.eps) z, z ∈ Icc (-U.delta) U.delta →
        finiteExpectedUtility (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val v.val z ≤
          finiteExpectedUtility (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val v.val (beta.val v) := by
  obtain ⟨beta, hmono, hroot⟩ := U.exists_pure_stationary hd hh hp0 hp1 c hM hC nu a ha baseRatio hbase
  refine ⟨beta, hmono, hroot, ?_⟩
  intro v z hz
  let D := U.finiteScoreData hd hh c hM hC nu a ha baseRatio hbase
  have he : beta.val v = D.reply beta v := D.root_unique beta v (beta.property v) (hroot v)
  have hm := D.reply_maximizes beta v
    (finiteExpectedUtility (m := m) d c a G (rho/h) baseRatio ⟨h,hh⟩ nu beta.val v.val)
    (fun y _ => hasDerivAt_finiteExpectedUtility d c a G (rho/h) baseRatio ⟨h,hh⟩ nu
      beta.val beta.val.continuous v.val y) z hz
  rw [← he] at hm
  exact hm

end UniformFiniteConstants
end FCAppendix.Exclusive.Narrow.Existence
