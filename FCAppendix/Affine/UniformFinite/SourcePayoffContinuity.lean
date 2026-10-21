import FCAppendix.Affine.UniformFinite.ActualContinuation
import FCAppendix.Affine.UniformFinite.GuardedPayoffContinuity
import FCAppendix.Affine.UniformFinite.AffineNoiseContinuity
import FCAppendix.Affine.LowBody.FirstCopyPair

set_option maxHeartbeats 1000000

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace SourceContinuity
open Uniform05 ClippedResidual
open WeightedSampling (Path pathLaw finalSet totalWeight)

variable {M : ℕ}

def State (i : Row) (M : ℕ) := RestrictedLaw i × (Fin M → Bid i)

instance stateTopology (i : Row) (M : ℕ) : TopologicalSpace (State i M) :=
  inferInstanceAs (TopologicalSpace (RestrictedLaw i × (Fin M → Bid i)))

instance stateMeasurableSpace (i : Row) (M : ℕ) : MeasurableSpace (State i M) :=
  borel (State i M)

instance stateBorel (i : Row) (M : ℕ) : BorelSpace (State i M) := ⟨rfl⟩

def fixedLawState (i : Row) (G : RestrictedLaw i) (b : Fin M → Bid i) : State i M :=
  (G, b)

theorem continuous_fixedLawState (i : Row) (G : RestrictedLaw i) :
    Continuous (fixedLawState (M := M) i G) :=
  continuous_const.prodMk continuous_id

theorem measurable_fixedLawState (i : Row) (G : RestrictedLaw i) :
    Measurable (fixedLawState (M := M) i G) :=
  (continuous_fixedLawState i G).measurable

def bids (i : Row) (x : State i M) : Fin M → ℝ := fun a => x.2 a

theorem continuous_bids (i : Row) : Continuous (bids (M := M) i) := by
  apply continuous_pi
  intro a
  exact continuous_subtype_val.comp ((continuous_apply a).comp continuous_snd)

theorem bids_bounds (i : Row) (x : State i M) (a : Fin M) :
    0 ≤ bids i x a ∧ bids i x a ≤ cap i := (x.2 a).property

theorem continuous_lowerBids (i : Row) (row : Source.CountRow M) :
    Continuous (fun x : State i M => Source.lowerBids row (bids i x)) := by
  apply continuous_pi
  intro a
  by_cases ha : a ∈ row.lower
  · simpa only [Source.lowerBids, if_pos ha, Function.comp_def] using
      (continuous_apply a).comp (continuous_bids i)
  · simp only [Source.lowerBids, if_neg ha]
    exact continuous_const

theorem continuous_weights (i : Row) (row : Source.CountRow M) :
    Continuous (fun x : State i M => Source.sourceWeights i x.1 row (bids i x)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  by_cases ha : a ∈ row.lower
  · simp only [if_pos ha]
    exact (continuous_lawWeight i).comp
      (continuous_fst.prodMk ((continuous_apply a).comp (continuous_bids i)))
  · simp only [if_neg ha]
    exact continuous_const

def rawWeight (i : Row) (row : Source.CountRow M) (x : State i M) : ℝ :=
  Source.rawAlpha i x.1 row (bids i x)

theorem continuous_rawWeight (i : Row) (row : Source.CountRow M) :
    Continuous (rawWeight i row) := by
  unfold rawWeight
  have h : Continuous (fun x : State i M => (x.1, bids i x)) :=
    continuous_fst.prodMk (continuous_bids i)
  simpa only [Function.comp_def] using (Source.continuous_rawAlpha i row).comp h

theorem rawWeight_bounds (i : Row) (row : Source.CountRow M) (x : State i M) :
    0 ≤ rawWeight i row x ∧ rawWeight i row x ≤ 1 :=
  Literal.guardWeight_bounds (Source.commonGuardMargin i) (2*Source.commonGuardMargin i)
    (Source.sourceSlacks i x.1 row (bids i x))

abbrev Guarded (i : Row) (row : Source.CountRow M) :=
  {x : State i M // 0 < rawWeight i row x}

theorem guarded_data [NeZero M] (i : Row) (row : Source.CountRow M)
    (x : Guarded i row) :
    Literal.WeightedGuard (xi i) (cap i) (Source.rootLo i x.1.1)
      (Source.rootHi i x.1.1) (Source.commonGuardMargin i * M)
      (Source.lowerBids row (bids i x.1)) (Source.sourceWeights i x.1.1 row (bids i x.1))
      (Source.small row) (Source.imbalance row) ∧
      0 < Source.small row ∧ 0 < Source.commonGuardMargin i * M :=
  Source.rawAlpha_pos i x.1.1 row (bids i x.1)
    (Nat.pos_of_ne_zero (NeZero.ne M)) (fun a _ => (bids_bounds i x.1 a).2) x.2

def pathRoot (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : Guarded i row) : ℝ :=
  Literal.root (xi i) (Source.rootLo i x.1.1) (Source.rootHi i x.1.1)
    (Source.lowerBids row (bids i x.1)) (finalSet (Source.imbalance row) ∅ p)
    (Source.small row)

theorem pathRoot_spec [NeZero M] (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : Guarded i row) :
    pathRoot i row p x ∈ Icc (Source.rootLo i x.1.1) (Source.rootHi i x.1.1) ∧
      remainingDemand (xi i) (Source.lowerBids row (bids i x.1))
        (finalSet (Source.imbalance row) ∅ p) (pathRoot i row p x) = (Source.small row : ℝ) := by
  have hg := guarded_data i row x
  have hr := Source.rootBounds i x.1.1
  have hcNat : (finalSet (Source.imbalance row) (∅ : Finset (Fin M)) p).card ≤
      Source.imbalance row := by
    simpa using Literal.finalSet_card_le (Source.imbalance row) (∅ : Finset (Fin M)) p
  have hc : ((finalSet (Source.imbalance row) (∅ : Finset (Fin M)) p).card : ℝ) ≤
      Source.imbalance row := by exact_mod_cast hcNat
  exact Literal.root_spec _ _ _ (xi_range i).1 (xi_range i).2 (cap_pos i)
    hr.1 hr.2.1 hr.2.2 hg.1.1 hg.2.1 hg.2.2 (by linarith [hg.1.2.1]) hg.1.2.2.1

theorem pathRoot_broad_bounds [NeZero M] (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : Guarded i row) :
    pathRoot i row p x ∈ Icc ((1-xi i)*cap i) (cap i+guardRadius i) := by
  have h := (pathRoot_spec i row p x).1
  have hb := Source.rootBounds i x.1.1
  refine ⟨hb.2.2.trans h.1, ?_⟩
  have hu := x.1.1.multiplier_guards.2.2.1
  dsimp only [Source.rootHi] at h
  linarith [h.2]

theorem continuous_pathRoot [NeZero M] (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) : Continuous (pathRoot i row p) := by
  by_cases hd : 0 < Source.small row
  · have hlo : 0 < (1-xi i)*cap i :=
      mul_pos (sub_pos.mpr (xi_range i).2) (cap_pos i)
    apply root_continuous
      (fun x : Guarded i row => remainingDemand (xi i)
        (Source.lowerBids row (bids i x.1)) (finalSet (Source.imbalance row) ∅ p))
      (pathRoot i row p)
      (show 0 < 1/(xi i*cap i) by exact one_div_pos.mpr (mul_pos (xi_range i).1 (cap_pos i)))
      (show (0 : ℝ) < Source.small row by exact_mod_cast hd)
    · intro x
      exact ⟨pathRoot_broad_bounds i row p x, (pathRoot_spec i row p x).2⟩
    · intro x z₁ z₂ hz₁ hz₂ h12
      have hb := (guarded_data i row x).1.1
      have hh := remainingDemand_drop
        (Source.lowerBids row (bids i x.1)) (finalSet (Source.imbalance row) ∅ p)
        (xi_range i).1 (xi_range i).2 (cap_pos i) hlo le_rfl hz₁.1 h12 hb
      convert! hh using 1; ring
    · intro z hz
      unfold remainingDemand
      apply continuous_finsetSum
      intro a _
      by_cases ha : a ∈ finalSet (Source.imbalance row) ∅ p
      · simp only [if_pos ha]
        exact continuous_const
      · simp only [if_neg ha]
        exact (continuous_exposure (xi_range i).1 (hlo.trans_le hz.1)).comp
          ((continuous_apply a).comp ((continuous_lowerBids i row).comp continuous_subtype_val))
  · rw [continuous_iff_continuousAt]
    intro x
    exact False.elim (hd (guarded_data i row x).2.1)

theorem continuous_pathExposure [NeZero M] (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (a : Fin M) :
    Continuous (fun x : Guarded i row =>
      exposure (xi i) (pathRoot i row p x) (Source.lowerBids row (bids i x.1) a)) := by
  have hz := continuous_pathRoot i row p
  have hb : Continuous (fun x : Guarded i row => Source.lowerBids row (bids i x.1) a) :=
    (continuous_apply a).comp ((continuous_lowerBids i row).comp continuous_subtype_val)
  unfold exposure
  apply continuous_const.min
  exact (continuous_const.max (hb.sub hz)).div
    (continuous_const.mul (hb.max hz)) (fun x => by
      have hr0 := (Source.rootBounds i x.1.1).1
      have hr := (pathRoot_spec i row p x).1.1
      exact ne_of_gt (mul_pos (xi_range i).1
        ((hr0.trans_le hr).trans_le (le_max_right _ _))))

theorem canonical_expected_eq_path [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) (v : ℝ) (x : Guarded i row) :
    (canonicalLaw i x.1.1 row (bids i x.1)).expect
      (pairPayoff (eta i) v (bids i x.1 a) a) =
      (pathLaw (Source.sourceWeights i x.1.1 row (bids i x.1))
        (Source.imbalance row) ∅).expect
        (Literal.pathPayoff (xi i) (Source.rootLo i x.1.1) (Source.rootHi i x.1.1)
          (eta i) v (Source.lowerBids row (bids i x.1))
          (Source.small row) (Source.imbalance row) a) := by
  have hg := guarded_data i row x
  have hr := Source.rootBounds i x.1.1
  rw [canonicalLaw, FiniteLaw.expect_map]
  calc
    _ = (Literal.weightedExperiment (xi i) (Source.rootLo i x.1.1) (Source.rootHi i x.1.1)
          (Source.lowerBids row (bids i x.1)) (Source.sourceWeights i x.1.1 row (bids i x.1))
          (Source.small row) (Source.imbalance row)).expect
        (fun out => Literal.countPayoff (eta i) v
          (Source.lowerBids row (bids i x.1) a) a out.2) := by
      apply FiniteLaw.expect_congr
      intro out
      simp only [pairPayoff, Literal.countPayoff, orient_success, orient_duplicate,
        Source.lowerBids_of_mem row (bids i x.1) ha]
    _ = _ := Literal.weighted_payoff _ _ _ _ (xi_range i).1 (xi_range i).2 (cap_pos i)
      hr.1 hr.2.1 hr.2.2 hg.2.1 hg.2.2 hg.1 a

theorem continuous_guarded_canonicalPayoff [NeZero M] (i : Row)
    (row : Source.CountRow M) (a : Fin M) (ha : a ∈ row.lower) :
    Continuous (fun x : ℝ × Guarded i row =>
      (canonicalLaw i x.2.1.1 row (bids i x.2.1)).expect
        (pairPayoff (eta i) x.1 (bids i x.2.1 a) a)) := by
  simp_rw [canonical_expected_eq_path i row a ha]
  unfold FiniteLaw.expect
  apply continuous_finsetSum
  intro p _
  have hm : Continuous (fun x : Guarded i row =>
      (pathLaw (Source.sourceWeights i x.1.1 row (bids i x.1))
        (Source.imbalance row) ∅).mass p) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hg := guarded_data i row x
    have hw : ((∅ : Finset (Fin M)).card : ℝ) + Source.imbalance row <
        totalWeight (Source.sourceWeights i x.1.1 row (bids i x.1)) := by
      simp only [Finset.card_empty, Nat.cast_zero, zero_add]
      linarith [hg.1.2.2.2.1, hg.2.2]
    exact (Literal.continuousAt_path_mass _ ∅ p _ hw).comp
      (x := x) (((continuous_weights i row).comp continuous_subtype_val).continuousAt)
  apply (hm.comp continuous_snd).mul
  have hp : Continuous (fun x : ℝ × Guarded i row => exposure (xi i) (pathRoot i row p x.2)
      (Source.lowerBids row (bids i x.2.1) a)) :=
    (continuous_pathExposure i row p a).comp continuous_snd
  have hb : Continuous (fun x : ℝ × Guarded i row => Source.lowerBids row (bids i x.2.1) a) :=
    (continuous_apply a).comp
      ((continuous_lowerBids i row).comp (continuous_subtype_val.comp continuous_snd))
  unfold Literal.pathPayoff
  by_cases haE : a ∈ finalSet (Source.imbalance row) ∅ p
  · simp only [if_pos haE]
    exact continuous_fst.sub hb
  · simp only [if_neg haE]
    exact ((continuous_fst.sub hb).mul
      ((continuous_const.mul hp).sub (hp.pow 2))).sub
        ((continuous_const.mul hb).mul (hp.pow 2))

theorem continuous_guard_product {X : Type*} [TopologicalSpace X]
    (α f B : X → ℝ) (hα : Continuous α) (hα0 : ∀ x, 0 ≤ α x)
    (hf : ContinuousOn f {x | 0 < α x}) (hB : Continuous B)
    (hbound : ∀ x, |f x| ≤ B x) : Continuous (fun x => α x * f x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : α x = 0
  · have hBx : 0 ≤ B x := (abs_nonneg _).trans (hbound x)
    have he : ∀ᶠ y in 𝓝 x, |f y| ≤ B x+1 := by
      have hnear : ∀ᶠ y in 𝓝 x, B y < B x+1 :=
        (isOpen_lt hB continuous_const).mem_nhds (show B x < B x+1 by linarith)
      exact hnear.mono (fun y hy => (hbound y).trans hy.le)
    have hzero := Literal.guard_times_bounded_tendsto_zero α f (B x+1)
      (by linarith) (by simpa only [hx] using hα.tendsto x) he
    simpa only [ContinuousAt, hx, zero_mul] using hzero
  · have hxpos : 0 < α x := lt_of_le_of_ne (hα0 x) (Ne.symm hx)
    have hfc : ContinuousAt f x :=
      (hf x hxpos).continuousAt ((isOpen_lt continuous_const hα).mem_nhds hxpos)
    exact hα.continuousAt.mul hfc

def canonicalPayoff [NeZero M] (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) : ℝ :=
  (canonicalLaw i x.2.1 row (bids i x.2)).expect
    (pairPayoff (eta i) x.1 (bids i x.2 a) a)

theorem canonicalPayoff_bound [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (x : ℝ × State i M) :
    |canonicalPayoff i row a x| ≤ |x.1|+(1+|eta i|)*cap i := by
  have hpoint (P : Allocation M) : |pairPayoff (eta i) x.1 (bids i x.2 a) a P| ≤
      |x.1|+(1+|eta i|)*cap i := by
    have hb := bids_bounds i x.2 a
    have h := pairPayoff_bound (eta i) x.1 (bids i x.2 a) a P
    rw [abs_of_nonneg hb.1] at h
    have hh := mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 1+|eta i| by positivity)
    linarith
  apply abs_le.mpr
  constructor
  · exact FiniteLaw.const_le_expect _ (fun P => (abs_le.mp (hpoint P)).1)
  · exact FiniteLaw.expect_le_const _ (fun P => (abs_le.mp (hpoint P)).2)

theorem continuousOn_canonicalPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) :
    ContinuousOn (canonicalPayoff i row a)
      {x : ℝ × State i M | 0 < rawWeight i row x.2} := by
  rw [continuousOn_iff_continuous_restrict]
  let f : {x : ℝ × State i M // 0 < rawWeight i row x.2} → ℝ × Guarded i row :=
    fun x => (x.1.1, ⟨x.1.2, x.2⟩)
  have hf : Continuous f := by
    exact continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.subtype_mk _)
  have h := (continuous_guarded_canonicalPayoff i row a ha).comp hf
  change Continuous (fun x : {x : ℝ × State i M // 0 < rawWeight i row x.2} =>
    canonicalPayoff i row a x.1)
  simpa only [Function.comp_def, f, canonicalPayoff] using h

def rawCanonicalPayoff [NeZero M] (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) : ℝ := rawWeight i row x.2 * canonicalPayoff i row a x

theorem continuous_rawCanonicalPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) : Continuous (rawCanonicalPayoff i row a) := by
  apply continuous_guard_product (fun x : ℝ × State i M => rawWeight i row x.2)
    (canonicalPayoff i row a) (fun x => |x.1|+(1+|eta i|)*cap i)
    ((continuous_rawWeight i row).comp continuous_snd)
    (fun x => (rawWeight_bounds i row x.2).1)
    (continuousOn_canonicalPayoff i row a ha) (by fun_prop)
    (canonicalPayoff_bound i row a)

def weightedPayoff [NeZero M] (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) : ℝ :=
  Source.guardAlpha i x.2.1 row (bids i x.2) * canonicalPayoff i row a x

theorem weightedPayoff_eq [NeZero M] (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) :
    weightedPayoff i row a x =
      if Source.seedCount i row (bids i x.2)=0 then 0 else rawCanonicalPayoff i row a x := by
  unfold weightedPayoff Source.guardAlpha rawCanonicalPayoff rawWeight
  split_ifs <;> simp

theorem measurable_seedCount (i : Row) (row : Source.CountRow M) :
    Measurable (fun x : State i M => Source.seedCount i row (bids i x)) := by
  have he (x : State i M) : Source.seedCount i row (bids i x) =
      ∑ a ∈ row.lower, if bids i x a ≤ t i/2 then (1 : ℕ) else 0 := by
    simp only [Source.seedCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [he]
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite
    (measurableSet_le (((continuous_apply a).comp (continuous_bids i)).measurable)
      measurable_const) measurable_const measurable_const

theorem seedCount_eventually_eq (i : Row) (row : Source.CountRow M) (x : State i M)
    (hcut : ∀ a ∈ row.lower, bids i x a ≠ t i/2) :
    ∀ᶠ y in 𝓝 x, Source.seedCount i row (bids i y) = Source.seedCount i row (bids i x) := by
  have he (a : Fin M) : ∀ᶠ y in 𝓝 x,
      a ∈ row.lower → (bids i y a ≤ t i/2 ↔ bids i x a ≤ t i/2) := by
    by_cases ha : a ∈ row.lower
    · by_cases hax : bids i x a ≤ t i/2
      · have hlt : bids i x a < t i/2 := lt_of_le_of_ne hax (hcut a ha)
        have hy : ∀ᶠ y in 𝓝 x, bids i y a < t i/2 :=
          (isOpen_lt ((continuous_apply a).comp (continuous_bids i)) continuous_const).mem_nhds hlt
        exact hy.mono (fun y hy _ => ⟨fun _ => hax, fun _ => hy.le⟩)
      · have hgt : t i/2 < bids i x a := lt_of_not_ge hax
        have hy : ∀ᶠ y in 𝓝 x, t i/2 < bids i y a :=
          (isOpen_lt continuous_const ((continuous_apply a).comp (continuous_bids i))).mem_nhds hgt
        exact hy.mono (fun y hy _ => by simp [not_le_of_gt hy, hax])
    · exact Eventually.of_forall (fun _ h => False.elim (ha h))
  filter_upwards [Filter.eventually_all.mpr he] with y hy
  unfold Source.seedCount
  congr 1
  ext a
  simp only [Finset.mem_filter]
  exact and_congr_right (fun ha => hy a ha)

theorem continuousAt_guardAlpha (i : Row) (row : Source.CountRow M) (x : State i M)
    (hcut : ∀ a ∈ row.lower, bids i x a ≠ t i/2) :
    ContinuousAt (fun y : State i M => Source.guardAlpha i y.1 row (bids i y)) x := by
  have he := seedCount_eventually_eq i row x hcut
  by_cases hz : Source.seedCount i row (bids i x) = 0
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [Source.guardAlpha, hy, hz]
  · apply (continuous_rawWeight i row).continuousAt.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [Source.guardAlpha, hy, hz, rawWeight]

theorem measurable_guardAlpha (i : Row) (row : Source.CountRow M) :
    Measurable (fun x : State i M => Source.guardAlpha i x.1 row (bids i x)) :=
  Measurable.ite (measurableSet_eq_fun (measurable_seedCount i row) measurable_const)
    measurable_const (continuous_rawWeight i row).measurable

theorem measurable_weightedPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) : Measurable (weightedPayoff i row a) := by
  have he : weightedPayoff i row a = fun x : ℝ × State i M =>
      if Source.seedCount i row (bids i x.2)=0 then 0 else rawCanonicalPayoff i row a x :=
    funext (weightedPayoff_eq i row a)
  rw [he]
  exact Measurable.ite
    (measurableSet_eq_fun ((measurable_seedCount i row).comp measurable_snd) measurable_const)
    measurable_const (continuous_rawCanonicalPayoff i row a ha).measurable

theorem continuousAt_weightedPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) (x : ℝ × State i M)
    (hcut : ∀ j ∈ row.lower, bids i x.2 j ≠ t i/2) :
    ContinuousAt (weightedPayoff i row a) x := by
  have he := (continuous_snd : Continuous (fun y : ℝ × State i M => y.2)).continuousAt
    (seedCount_eventually_eq i row x.2 hcut)
  by_cases hz : Source.seedCount i row (bids i x.2)=0
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    rw [weightedPayoff_eq, if_pos (hy.trans hz)]
  · apply (continuous_rawCanonicalPayoff i row a ha).continuousAt.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    rw [weightedPayoff_eq, if_neg (fun h => hz (hy.symm.trans h))]

def purePayoff (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) : ℝ :=
  pairPayoff (eta i) x.1 (bids i x.2 a) a
    ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x.2)))

theorem measurable_purePayoff (i : Row) (row : Source.CountRow M) (a : Fin M) :
    Measurable (purePayoff i row a) := by
  have hs : Measurable (fun x : ℝ × State i M =>
      (Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x.2))) :=
    ((Source.lowerTemplate row).measurable_selection (kappa i)).comp
      (((continuous_lowerBids i row).comp continuous_snd).measurable)
  have hfirst := (measurable_of_countable (Literal.firstCopy a)).comp hs
  have hdup := (measurable_of_countable (Literal.duplicateCopy a)).comp hs
  have hb : Measurable (fun x : ℝ × State i M => bids i x.2 a) :=
    (((continuous_apply a).comp ((continuous_bids i).comp continuous_snd)).measurable)
  exact ((measurable_fst.sub hb).mul hfirst).sub
    ((measurable_const.mul hb).mul hdup)

theorem continuousAt_purePayoff (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M)
    (hgeneric : ∀ P Q : (Source.lowerTemplate row).Candidate,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        P.val.1 P.val.2 =
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        Q.val.1 Q.val.2 → LowBody.focalCopy P.val a = LowBody.focalCopy Q.val a) :
    ContinuousAt (purePayoff i row a) x := by
  classical
  let T := Source.lowerTemplate row
  have hlabel (y : ℝ × State i M) (P Q : T.Candidate)
      (hPQ : LowBody.focalCopy P.val a = LowBody.focalCopy Q.val a) :
      pairPayoff (eta i) y.1 (bids i y.2 a) a P.val =
        pairPayoff (eta i) y.1 (bids i y.2 a) a Q.val := by
    have he (R : Allocation M) : pairPayoff (eta i) y.1 (bids i y.2 a) a R =
        (if LowBody.focalCopy R a = 2 then y.1-(1+eta i)*bids i y.2 a
          else if LowBody.focalCopy R a = 1 then y.1-bids i y.2 a else 0) := by
      by_cases h0 : a ∈ R.1 <;> by_cases h1 : a ∈ R.2 <;>
        simp [pairPayoff, Literal.firstCopy, Literal.duplicateCopy,
          WeightedSampling.indicator, LowBody.focalCopy, h0, h1]; ring
    rw [he, he, hPQ]
  exact LowBody.continuousAt_selected_payoff
    (fun y : ℝ × State i M => fun P : T.Candidate =>
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i y.2))
        P.val.1 P.val.2)
    (fun P => (LowBody.continuous_potential (kappa i) P.val).comp
      ((continuous_lowerBids i row).comp continuous_snd))
    (fun P : T.Candidate => LowBody.focalCopy P.val a)
    (fun y P => pairPayoff (eta i) y.1 (bids i y.2 a) a P.val)
    (fun P => by unfold pairPayoff bids; fun_prop) hlabel x hgeneric

def equalMarginal (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : State i M) : ℝ :=
  EqualCapacity.positiveMarginal (xi i) (Source.small row) (Source.lowerBids row (bids i x)) a

theorem equalPayoff_eq (i : Row) (row : Source.CountRow M) (a : Fin M)
    (x : ℝ × State i M) :
    (equalLaw i row (bids i x.2)).expect (pairPayoff (eta i) x.1 (bids i x.2 a) a) =
      (x.1-bids i x.2 a)*(2*equalMarginal i row a x.2-(equalMarginal i row a x.2)^2)-
        eta i*bids i x.2 a*(equalMarginal i row a x.2)^2 := by
  have hm := (EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
    (Source.small row) (Source.lowerBids row (bids i x.2))).2 a
  have hi : (equalLottery i row (bids i x.2)).expect (WeightedSampling.indicator a) =
      equalMarginal i row a x.2 := (FiniteLaw.prob_eq_expect _ _).symm.trans hm
  have hf : (equalLaw i row (bids i x.2)).expect
      (fun P => WeightedSampling.indicator a P.1) = equalMarginal i row a x.2 := by
    rw [equalLaw, FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const, hi]
  have hs : (equalLaw i row (bids i x.2)).expect
      (fun P => WeightedSampling.indicator a P.2) = equalMarginal i row a x.2 := by
    rw [equalLaw, FiniteLaw.expect_prod]
    simp only [hi, FiniteLaw.expect_const]
  have hd : (equalLaw i row (bids i x.2)).expect (Literal.duplicateCopy a) =
      equalMarginal i row a x.2 ^ 2 := by
    change (equalLaw i row (bids i x.2)).expect
      (fun P => WeightedSampling.indicator a P.1 * WeightedSampling.indicator a P.2) = _
    rw [equalLaw, FiniteLaw.expect_prod_mul, hi]
    ring
  have hsuccess : (equalLaw i row (bids i x.2)).expect (Literal.firstCopy a) =
      2*equalMarginal i row a x.2-equalMarginal i row a x.2^2 := by
    change (equalLaw i row (bids i x.2)).expect (fun P =>
      WeightedSampling.indicator a P.1 + WeightedSampling.indicator a P.2 -
        WeightedSampling.indicator a P.1 * WeightedSampling.indicator a P.2) = _
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_add, hf, hs]
    change equalMarginal i row a x.2 + equalMarginal i row a x.2 -
      (equalLaw i row (bids i x.2)).expect (Literal.duplicateCopy a) = _
    rw [hd]
    ring
  unfold pairPayoff
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul,
    hsuccess, hd]

theorem measurable_equalMarginal (i : Row) (row : Source.CountRow M) (a : Fin M) :
    Measurable (equalMarginal i row a) :=
  (measurable_pi_apply a).comp
    ((EqualCapacity.measurable_positiveMarginal (xi i) (Source.small row)
      (xi_range i).1 (xi_range i).2).comp (continuous_lowerBids i row).measurable)

theorem continuousAt_equalMarginal (i : Row) (row : Source.CountRow M) (a : Fin M)
    (ha : a ∈ row.lower) (x : State i M) (hpos : 0 < bids i x a) :
    ContinuousAt (equalMarginal i row a) x := by
  have hb : ∀ j, 0 ≤ Source.lowerBids row (bids i x) j := by
    intro j
    by_cases hj : j ∈ row.lower
    · simpa [Source.lowerBids, hj] using (bids_bounds i x j).1
    · simp [Source.lowerBids, hj]
  exact (EqualCapacity.continuousAt_positiveMarginal_focal (xi_range i).1 (xi_range i).2
    (Source.small row) (Source.lowerBids row (bids i x)) hb a
    (by simpa [Source.lowerBids, ha] using hpos)).comp
      (x := x) (continuous_lowerBids i row).continuousAt

theorem measurable_rowPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) :
    Measurable (fun x : ℝ × State i M => rowPayoff i x.2.1 row x.1 (bids i x.2) a) := by
  have hb : Measurable (fun x : ℝ × State i M => bids i x.2 a) :=
    (((continuous_apply a).comp ((continuous_bids i).comp continuous_snd)).measurable)
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp only [rowPayoff, continuation_equal i _ row _ he]
    simp_rw [equalPayoff_eq]
    have hp : Measurable (fun x : ℝ × State i M => equalMarginal i row a x.2) :=
      (measurable_equalMarginal i row a).comp measurable_snd
    exact ((measurable_fst.sub hb).mul
      ((measurable_const.mul hp).sub (hp.pow_const 2))).sub
        ((measurable_const.mul hb).mul (hp.pow_const 2))
  · simp_rw [rowPayoff_unequal i _ row _ _ a he]
    exact (measurable_weightedPayoff i row a ha).add
      ((measurable_const.sub ((measurable_guardAlpha i row).comp measurable_snd)).mul
        (measurable_purePayoff i row a))

theorem continuousAt_rowPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) (x : ℝ × State i M)
    (hpos : 0 < bids i x.2 a)
    (hcut : ∀ j ∈ row.lower, bids i x.2 j ≠ t i/2)
    (hgeneric : ∀ P Q : (Source.lowerTemplate row).Candidate,
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        P.val.1 P.val.2 =
      LowBody.CompleteInformation.potential (kappa i) (Source.lowerBids row (bids i x.2))
        Q.val.1 Q.val.2 → LowBody.focalCopy P.val a = LowBody.focalCopy Q.val a) :
    ContinuousAt (fun y : ℝ × State i M => rowPayoff i y.2.1 row y.1 (bids i y.2) a) x := by
  have hb : ContinuousAt (fun y : ℝ × State i M => bids i y.2 a) x :=
    (((continuous_apply a).comp ((continuous_bids i).comp continuous_snd)).continuousAt)
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp only [rowPayoff, continuation_equal i _ row _ he]
    simp_rw [equalPayoff_eq]
    have hp := (continuousAt_equalMarginal i row a ha x.2 hpos).comp continuousAt_snd
    exact ((continuousAt_fst.sub hb).mul
      ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
        ((continuousAt_const.mul hb).mul (hp.pow 2))
  · simp_rw [rowPayoff_unequal i _ row _ _ a he]
    exact (continuousAt_weightedPayoff i row a ha x hcut).add
      ((continuousAt_const.sub ((continuousAt_guardAlpha i row x.2 hcut).comp continuousAt_snd)).mul
        (continuousAt_purePayoff i row a x hgeneric))

theorem continuousAt_rowPayoff_zero [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (x : ℝ × State i M) (hv : x.1 = 0) (hb : bids i x.2 a = 0) :
    ContinuousAt (fun y : ℝ × State i M =>
      rowPayoff i y.2.1 row y.1 (bids i y.2) a) x := by
  have hbound (y : ℝ × State i M) :
      |rowPayoff i y.2.1 row y.1 (bids i y.2) a| ≤
        |y.1| + (1+|eta i|)*|bids i y.2 a| := rowPayoff_bound _ _ _ _ _ _
  have hz : rowPayoff i x.2.1 row x.1 (bids i x.2) a = 0 := by
    apply abs_eq_zero.mp
    exact le_antisymm (by simpa [hv, hb] using hbound x) (abs_nonneg _)
  rw [ContinuousAt, hz]
  have hc : Tendsto (fun y : ℝ × State i M => |y.1|+(1+|eta i|)*|bids i y.2 a|)
      (𝓝 x) (𝓝 0) := by
    have hcont : Continuous (fun y : ℝ × State i M =>
        |y.1|+(1+|eta i|)*|bids i y.2 a|) := by
      exact continuous_fst.abs.add
        (continuous_const.mul (((continuous_apply a).comp ((continuous_bids i).comp continuous_snd)).abs))
    simpa only [hv, hb, abs_zero, mul_zero, add_zero] using hcont.tendsto x
  apply squeeze_zero_norm' _ hc
  exact Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hbound y)

end SourceContinuity
end FCAppendix.Affine.UniformFinite
