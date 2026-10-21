import FCAppendix.Affine.Tail04.PrivateComposition
import FCAppendix.Finite.CapacityFill
import FCAppendix.Probability.ContactHoeffding

noncomputable section
namespace FCAppendix.Affine.Tail04.Underfill
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open scoped BigOperators

def contactLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteLaw (Finset (Fin 1)) :=
  (IndependentCounts.bernoulli p hp0 hp1).map
    (fun b => if b then {0} else ∅)

lemma contactLaw_marginal (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Proposer.marginal (contactLaw p hp0 hp1) 0 = p := by
  rw [CommonList.marginal_eq_expect]
  unfold contactLaw
  rw [FiniteLaw.expect_map,IndependentCounts.expect_bernoulli]
  simp

theorem binomial_underload_exp (m c : ℕ) (p δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (hc : (c:ℝ) ≤ m*(p-δ)) :
    (IndependentCounts.binomial m p hp0 hp1).prob (fun k => k.val < c) ≤
      Real.exp (-2*m*δ^2) := by
  have h := SimultaneousCongestion.marginal_underload_le_exp
    (contactLaw p hp0 hp1) 0 m c hδ
    (by simpa only [contactLaw_marginal] using hc)
  have he : (CommonList.iid (contactLaw p hp0 hp1) m).prob
      (fun T => CommonList.includers 0 T < c) =
      (IndependentCounts.binomial m p hp0 hp1).prob (fun k => k.val < c) := by
    rw [FiniteLaw.prob_eq_expect,
      CommonList.expect_includers (contactLaw p hp0 hp1) 0 m
        (fun k => if k< c then (1:ℝ) else 0)]
    simp only [contactLaw_marginal]
    rw [FiniteLaw.prob_eq_expect]
  rwa [he] at h

theorem binomial_shortfall_exp (m c : ℕ) (p δ : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (hc : (c:ℝ) ≤ m*(p-δ)) :
    (IndependentCounts.binomial m p hp0 hp1).expect
      (fun k => max ((c:ℝ)-k.val) 0) ≤ c*Real.exp (-2*m*δ^2) := by
  let μ := IndependentCounts.binomial m p hp0 hp1
  have hb : μ.expect (fun k => max ((c:ℝ)-k.val) 0) ≤
      (c:ℝ)*μ.prob (fun k => k.val< c) := by
    rw [FiniteLaw.prob_eq_expect,←FiniteLaw.expect_const_mul]
    apply μ.expect_mono
    intro k
    by_cases hk : k.val< c
    · rw [if_pos hk,mul_one]
      exact max_le (sub_le_self _ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    · rw [if_neg hk,mul_zero]
      have hck : (c:ℝ) ≤ k.val := by exact_mod_cast (le_of_not_gt hk)
      rw [max_eq_right (sub_nonpos.mpr hck)]
  exact hb.trans (mul_le_mul_of_nonneg_left
    (binomial_underload_exp m c p δ hp0 hp1 hδ hc) (Nat.cast_nonneg c))

theorem original_iid_shortfall_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (m c : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hc : (c:ℝ) ≤ m*(μ.real E-δ)) :
    (∫ ω : Fin m → Ω, max ((c:ℝ)-PiBinomial.count E Finset.univ ω) 0
      ∂Measure.pi (fun _ : Fin m => μ)) ≤ c*Real.exp (-2*m*δ^2) := by
  have he := PiBinomial.integral_count_eq μ E hE (Finset.univ : Finset (Fin m))
    (fun k => max ((c:ℝ)-k) 0)
  rw [he]
  have hcard : (Finset.univ : Finset (Fin m)).card=m := by simp
  have hcap : (c:ℝ)≤(Finset.univ : Finset (Fin m)).card*(μ.real E-δ) := by
    simpa only [hcard] using hc
  have hh := binomial_shortfall_exp (Finset.univ : Finset (Fin m)).card c
    (μ.real E) δ measureReal_nonneg measureReal_le_one hδ hcap
  simpa only [hcard] using hh

variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def broadcastHigh (R : ℝ) : Set (ℝ × JointAction 2) :=
  {p | R ≤ p.2.bid ∧ p.2.routeCount=2}
def privateHigh (R : ℝ) : Set (ℝ × JointAction 2) :=
  {p | R ≤ p.2.bid ∧ p.2.routeCount=1}

lemma measurableSet_broadcastHigh (R : ℝ) : MeasurableSet (broadcastHigh R) :=
  (measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
    (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const)
lemma measurableSet_privateHigh (R : ℝ) : MeasurableSet (privateHigh R) :=
  (measurableSet_le measurable_const ((measurable_bid 2).comp measurable_snd)).inter
    (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const)

theorem high_arrival_lower (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (t R : ℝ) (htR : t< R) :
    (Γ.F ⊗ₘ Γ.σ).real (broadcastHigh R) +
      (Γ.F ⊗ₘ Γ.σ).real (privateHigh R)/2 ≤ alphaGt Γ j t := by
  let μ := Γ.F ⊗ₘ Γ.σ
  let C : Set (UserDraw 2) := broadcastHigh R ×ˢ univ
  let P : Set (UserDraw 2) := privateHigh R ×ˢ oneRouteEvent j
  have hC : MeasurableSet C := (measurableSet_broadcastHigh R).prod MeasurableSet.univ
  have hP : MeasurableSet P := (measurableSet_privateHigh R).prod
    (measurableSet_oneRouteEvent j)
  have hdis : Disjoint C P := by
    rw [Set.disjoint_left]
    intro u huC huP
    have h2 : u.1.2.routeCount=2 := huC.1.2
    have h1 : u.1.2.routeCount=1 := huP.1.2
    omega
  have hsub : C ∪ P ⊆ aboveAt j t := by
    intro u hu
    rcases hu with hu | hu
    · refine ⟨?_,htR.trans_le hu.1.1⟩
      have huj := (u.2 j).isLt
      simp only [mem_firstK,hu.1.2]
      omega
    · have hj : j ∈ firstK u.2 1 := hu.2
      exact ⟨by simpa only [hu.1.2] using hj,htR.trans_le hu.1.1⟩
  have hmassC : (userLaw Γ).real C = μ.real (broadcastHigh R) := by
    simp only [userLaw,C,Measure.real,Measure.prod_prod,measure_univ,mul_one]
    rfl
  have hmassP : (userLaw Γ).real P = μ.real (privateHigh R)/2 := by
    change ((μ.prod (permLaw 2)) (privateHigh R ×ˢ oneRouteEvent j)).toReal = _
    rw [Measure.prod_prod,ENNReal.toReal_mul]
    change μ.real (privateHigh R)*(permLaw 2).real (oneRouteEvent j) = _
    rw [original_fair_route_mass]
    ring
  have hmass := measureReal_union (μ := userLaw Γ) hdis hP
  rw [hmassC,hmassP] at hmass
  rw [←hmass]
  exact measureReal_mono hsub

theorem native_unused_exp (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (hj : ProposerRationalOnPath Γ j) (a t δ : ℝ) (ha : 0< a) (ht : 0< t)
    (hδ : 0≤ δ)
    (hA : ∀ r : ℕ, 0< r → r≤2 → a*(r:ℝ) ≤ Γ.A.charge r)
    (hc : (c:ℝ) ≤ m*(alphaGt Γ j t-δ)) :
    (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) ≤ c*Real.exp (-2*m*δ^2) :=
  (integral_unusedCapacity_le_shortfall Γ j hj a ha hA t ht).trans
    (original_iid_shortfall_exp (userLaw Γ) (aboveAt j t)
      (measurableSet_aboveAt j t) m c δ hδ hc)

theorem both_source_arrival_margins (δ hm : ℝ)
    (hδ : δ ≤ 8/125) (hupper : hm ≤ 1/10) :
    (3/5:ℝ) ≤ (8/25)+(67/100-δ)/2 ∧
      (3/5:ℝ) ≤ (67/100-δ-hm)+(8/25+hm)/2 := by
  constructor <;> linarith

theorem native_unused_source_bound (Γ : FiniteGame m 2 c Seed) (j : Fin 2)
    (hj : ProposerRationalOnPath Γ j) (a t R : ℝ) (ha : 0< a) (ht : 0< t)
    (htR : t< R)
    (hA : ∀ r : ℕ, 0< r → r≤2 → a*(r:ℝ) ≤ Γ.A.charge r)
    (hc : (c:ℝ) ≤ (m:ℝ)/2)
    (hmass : (3/5:ℝ) ≤ (Γ.F ⊗ₘ Γ.σ).real (broadcastHigh R) +
      (Γ.F ⊗ₘ Γ.σ).real (privateHigh R)/2) :
    (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) ≤
      c*Real.exp (-(m:ℝ)/50) := by
  have harr : (3/5:ℝ) ≤ alphaGt Γ j t :=
    hmass.trans (high_arrival_lower Γ j t R htR)
  have hcap : (c:ℝ) ≤ m*(alphaGt Γ j t-(1/10:ℝ)) := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have h := native_unused_exp Γ j hj a t (1/10) ha ht (by norm_num) hA hcap
  convert! h using 1 ; ring

theorem native_load_gap_bound (Γ : FiniteGame m 2 c Seed) (_hm : 0< m)
    (E : ℝ) (hE : ∀ j, (∫ ω, unusedCapacity Γ j ω ∂backgroundLaw Γ) ≤ E) :
    0 ≤ 2*((c:ℝ)/m)-finiteLoad Γ ∧
      2*((c:ℝ)/m)-finiteLoad Γ ≤ 2*E/m := by
  constructor
  · exact sub_nonneg.mpr (finiteLoad_le_capacity Γ)
  · have hid := sum_unusedCapacity_eq_load_gap Γ
    norm_num only [Nat.cast_ofNat] at hid
    rw [←hid]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hE j)
    simpa using h

end FCAppendix.Affine.Tail04.Underfill
