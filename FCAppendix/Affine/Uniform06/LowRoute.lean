import FCAppendix.Probability.FinitePushforward
import FCAppendix.Affine.Uniform07.Parameters

set_option autoImplicit false

noncomputable section
namespace FCAppendix.Affine.Uniform06.LowRoute

open MeasureTheory Set
open scoped BigOperators

abbrev Copies := Bool × Bool

def bit (x : Bool) : ℝ := if x then 1 else 0

def copySuccess (x : Copies) : ℝ :=
  bit x.1 + bit x.2 - bit x.1 * bit x.2

def copyDuplicate (x : Copies) : ℝ := bit x.1 * bit x.2

def success (P : FiniteLaw Copies) : ℝ := P.expect copySuccess

def duplicate (P : FiniteLaw Copies) : ℝ := P.expect copyDuplicate

def fairHiddenLaw (P : FiniteLaw Copies) : FiniteLaw Bool :=
  (P.map Prod.fst).mixture (P.map Prod.snd) (1 / 2)
    (by norm_num) (by norm_num)

def singletonSuccess (P : FiniteLaw Bool) : ℝ := P.expect bit

def broadcastUtility (η v b : ℝ) (P : FiniteLaw Copies) : ℝ :=
  (v - b) * success P - η * b * duplicate P

def singletonUtility (v b : ℝ) (P : FiniteLaw Bool) : ℝ :=
  (v - b) * singletonSuccess P

theorem copySuccess_values (x : Copies) :
    copySuccess x = if x.1 = true ∨ x.2 = true then 1 else 0 := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [copySuccess, bit]

theorem copyDuplicate_values (x : Copies) :
    copyDuplicate x = if x.1 = true ∧ x.2 = true then 1 else 0 := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [copyDuplicate, bit]

theorem success_eq_probability (P : FiniteLaw Copies) :
    success P = P.prob (fun x => x.1 = true ∨ x.2 = true) := by
  apply P.expect_congr
  rintro ⟨a,b⟩
  cases a <;> cases b <;> norm_num [copySuccess, bit]

theorem duplicate_eq_probability (P : FiniteLaw Copies) :
    duplicate P = P.prob (fun x => x.1 = true ∧ x.2 = true) := by
  apply P.expect_congr
  rintro ⟨a,b⟩
  cases a <;> cases b <;> norm_num [copyDuplicate, bit]

theorem success_bounds (P : FiniteLaw Copies) : success P ∈ Icc 0 1 := by
  rw [success_eq_probability]
  exact ⟨P.prob_nonneg _, P.prob_le_one _⟩

theorem duplicate_bounds (P : FiniteLaw Copies) : duplicate P ∈ Icc 0 1 := by
  rw [duplicate_eq_probability]
  exact ⟨P.prob_nonneg _, P.prob_le_one _⟩

theorem singletonSuccess_bounds (P : FiniteLaw Bool) :
    singletonSuccess P ∈ Icc 0 1 := by
  constructor
  · apply P.expect_nonneg
    intro a
    cases a <;> norm_num [bit]
  · apply P.expect_le_const
    intro a
    cases a <;> norm_num [bit]

theorem fair_hidden_success (P : FiniteLaw Copies) :
    singletonSuccess (fairHiddenLaw P) = (success P + duplicate P) / 2 := by
  unfold singletonSuccess fairHiddenLaw
  rw [FiniteLaw.expect_mixture, FiniteLaw.expect_map, FiniteLaw.expect_map]
  have hsum : success P + duplicate P =
      P.expect (fun x => bit x.1) + P.expect (fun x => bit x.2) := by
    unfold success duplicate copySuccess copyDuplicate
    rw [P.expect_sub, P.expect_add]
    ring
  rw [hsum]
  ring

theorem success_ofMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Copies) (hK : Measurable K) :
    success (FiniteLaw.ofMeasure μ K hK) =
      ∫ ω, copySuccess (K ω) ∂μ :=
  FiniteLaw.expect_ofMeasure μ K hK copySuccess

theorem duplicate_ofMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → Copies) (hK : Measurable K) :
    duplicate (FiniteLaw.ofMeasure μ K hK) =
      ∫ ω, copyDuplicate (K ω) ∂μ :=
  FiniteLaw.expect_ofMeasure μ K hK copyDuplicate

theorem exact_route_difference (η v b : ℝ) (P : FiniteLaw Copies) :
    broadcastUtility η v b P - singletonUtility v b (fairHiddenLaw P) =
      singletonUtility v b (fairHiddenLaw P) -
        ((v - b) + η * b) * duplicate P := by
  unfold broadcastUtility singletonUtility
  rw [fair_hidden_success]
  ring

theorem route_gap_of_local_transport (η v b : ℝ)
    (P : FiniteLaw Copies) (P₁ : FiniteLaw Bool)
    (hlocal : P₁ = fairHiddenLaw P) :
    broadcastUtility η v b P - singletonUtility v b P₁ =
      singletonUtility v b P₁ - ((v - b) + η * b) * duplicate P := by
  rw [hlocal]
  exact exact_route_difference η v b P

theorem low_route_margin {η v b L : ℝ} (P : FiniteLaw Copies)
    (_hv : 0 < v) (hb : 0 ≤ b) (hη : η ≤ 1)
    (hlower : v * L / 2 ≤ singletonUtility v b (fairHiddenLaw P)) :
    v * (L / 2 - duplicate P) ≤
      broadcastUtility η v b P - singletonUtility v b (fairHiddenLaw P) := by
  rw [exact_route_difference]
  have hcost : ((v - b) + η * b) * duplicate P ≤ v * duplicate P := by
    apply mul_le_mul_of_nonneg_right _ (duplicate_bounds P).1
    nlinarith
  nlinarith

theorem low_route_strict {η v b L : ℝ} (P : FiniteLaw Copies)
    (hv : 0 < v) (hb : 0 ≤ b) (hη : η ≤ 1)
    (hlower : v * L / 2 ≤ singletonUtility v b (fairHiddenLaw P))
    (hdup : duplicate P < L / 2) :
    singletonUtility v b (fairHiddenLaw P) < broadcastUtility η v b P := by
  have hg := low_route_margin P hv hb hη hlower
  have hp := mul_pos hv (sub_pos.mpr hdup)
  linarith

theorem positive_singleton_implies_underbid {v b : ℝ} (P : FiniteLaw Bool)
    (hu : 0 < singletonUtility v b P) : b < v := by
  by_contra h
  have hb : v ≤ b := le_of_not_gt h
  have hq := (singletonSuccess_bounds P).1
  have hnon : singletonUtility v b P ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) hq
  linarith

theorem exists_raw_singleton_optimizer {v L : ℝ}
    (P : ℝ → FiniteLaw Bool) (hv : 0 < v) (hL : 0 < L)
    (hq : ContinuousOn (fun b => singletonSuccess (P b)) (Icc 0 v))
    (hbenchmark : v*L/2 ≤ singletonUtility v (v/2) (P (v/2))) :
    ∃ bStar ∈ Ico 0 v,
      v*L/2 ≤ singletonUtility v bStar (P bStar) ∧
      ∀ b, 0 ≤ b → singletonUtility v b (P b) ≤
        singletonUtility v bStar (P bStar) := by
  have hu : ContinuousOn (fun b => singletonUtility v b (P b)) (Icc 0 v) :=
    (continuousOn_const.sub continuousOn_id).mul hq
  obtain ⟨bStar, hbStar, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) v).Nonempty from ⟨0, le_rfl, hv.le⟩) hu
  have hhalf : v/2 ∈ Icc (0:ℝ) v := by constructor <;> linarith
  have hlower := hbenchmark.trans (hmax hhalf)
  have hpos : 0 < singletonUtility v bStar (P bStar) :=
    (show 0 < v*L/2 by positivity).trans_le hlower
  refine ⟨bStar, ⟨hbStar.1, positive_singleton_implies_underbid _ hpos⟩,
    hlower, ?_⟩
  intro b hb
  by_cases hbv : b ≤ v
  · exact hmax ⟨hb, hbv⟩
  · have hbad : singletonUtility v b (P b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (le_of_not_ge hbv)) (singletonSuccess_bounds _).1
    exact hbad.trans hpos.le

theorem tiny_value_optimizer_dominance {η v L bLow bStar : ℝ}
    (P : ℝ → FiniteLaw Copies)
    (hv : 0 < v) (hvlow : v ≤ bLow) (hη : η ≤ 1) (hL : 0 < L)
    (hstar : 0 ≤ bStar)
    (hopt : ∀ b, 0 ≤ b →
      singletonUtility v b (fairHiddenLaw (P b)) ≤
        singletonUtility v bStar (fairHiddenLaw (P bStar)))
    (hbenchmark : v * L / 2 ≤
      singletonUtility v (v / 2) (fairHiddenLaw (P (v / 2))))
    (hdup : ∀ b ∈ Icc 0 bLow, duplicate (P b) < L / 2) :
    0 < broadcastUtility η v bStar (P bStar) ∧
      ∀ b, 0 ≤ b → singletonUtility v b (fairHiddenLaw (P b)) <
        broadcastUtility η v bStar (P bStar) := by
  have hbase : 0 < v * L / 2 := by positivity
  have hstarLower := hbenchmark.trans (hopt (v / 2) (by positivity))
  have hstarPos := hbase.trans_le hstarLower
  have hunder := positive_singleton_implies_underbid
    (fairHiddenLaw (P bStar)) hstarPos
  have hsmall := hdup bStar ⟨hstar, hunder.le.trans hvlow⟩
  have hstrict := low_route_strict (P bStar) hv hstar hη hstarLower hsmall
  exact ⟨hstarPos.trans hstrict, fun b hb => (hopt b hb).trans_lt hstrict⟩

theorem tiny_value_exists_improving_broadcast {η v L bLow : ℝ}
    (P : ℝ → FiniteLaw Copies)
    (hv : 0 < v) (hvlow : v ≤ bLow) (hη : η ≤ 1) (hL : 0 < L)
    (hq : ContinuousOn (fun b => singletonSuccess (fairHiddenLaw (P b))) (Icc 0 v))
    (hbenchmark : v*L/2 ≤
      singletonUtility v (v/2) (fairHiddenLaw (P (v/2))))
    (hdup : ∀ b ∈ Icc 0 bLow, duplicate (P b) < L/2) :
    ∃ bStar ∈ Ico 0 v,
      0 < broadcastUtility η v bStar (P bStar) ∧
      ∀ b, 0 ≤ b → singletonUtility v b (fairHiddenLaw (P b)) <
        broadcastUtility η v bStar (P bStar) := by
  obtain ⟨bStar, hbStar, _, hopt⟩ := exists_raw_singleton_optimizer
    (fun b => fairHiddenLaw (P b)) hv hL hq hbenchmark
  exact ⟨bStar, hbStar, tiny_value_optimizer_dominance P hv hvlow hη hL
    hbStar.1 hopt hbenchmark hdup⟩

end FCAppendix.Affine.Uniform06.LowRoute
