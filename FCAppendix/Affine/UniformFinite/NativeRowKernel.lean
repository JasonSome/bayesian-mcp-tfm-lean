import FCAppendix.Affine.UniformFinite.SeedErasure
import FCAppendix.Affine.WeightedSampler
import FCAppendix.Affine.Hybrid.NativeContinuation
import FCAppendix.Affine.UniformFinite.ExtensionalSampler

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open scoped BigOperators

namespace NativeRow
open Uniform05 SourceContinuity ClippedResidual WeightedSampling
variable {M : ℕ} [NeZero M]

abbrev Signal (row : Source.CountRow M) := Option (Path (Fin M) (Source.imbalance row))

instance signalMeasurableSpace (row : Source.CountRow M) : MeasurableSpace (Signal row) := ⊤
instance signalSingleton (row : Source.CountRow M) : MeasurableSingletonClass (Signal row) :=
  ⟨fun _=>trivial⟩
instance signalStandardBorel (row : Source.CountRow M) : StandardBorelSpace (Signal row) := by
  infer_instance

def actualRoot (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : State i M) : ℝ :=
  Literal.root (xi i) (Source.rootLo i x.1) (Source.rootHi i x.1)
    (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p) (Source.small row)

def usableRoot (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) : State i M → ℝ :=
  {x | 0 < rawWeight i row x}.piecewise (actualRoot i row p) (fun _ => 0)

theorem measurable_usableRoot (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) : Measurable (usableRoot i row p) := by
  apply ContinuousOn.measurable_piecewise _ continuousOn_const
    ((isOpen_lt continuous_const (continuous_rawWeight i row)).measurableSet)
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_pathRoot i row p

omit [NeZero M] in
theorem usableRoot_eq (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : State i M)
    (hraw : 0 < rawWeight i row x) : usableRoot i row p x = actualRoot i row p x := by
  simp only [usableRoot, Set.piecewise, mem_setOf_eq, if_pos hraw]

def smallLaw (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : State i M) : FiniteLaw (Finset (Fin M)) :=
  Literal.completion (xi i) (usableRoot i row p x) (Source.lowerBids row (bids i x))
    (finalSet (Source.imbalance row) ∅ p)

def largeLaw (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (x : State i M) : FiniteLaw (Finset (Fin M)) :=
  (smallLaw i row p x).map (fun S => finalSet (Source.imbalance row) ∅ p ∪ S)

theorem measurable_smallLaw_mass (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (S : Finset (Fin M)) :
    Measurable (fun x => (smallLaw i row p x).mass S) := by
  apply (ExactCapacity.measurable_symmetricLottery_mass S).comp
  apply measurable_pi_lambda
  intro a
  by_cases ha : a ∈ finalSet (Source.imbalance row) ∅ p
  · simp only [smallMarginal, if_pos ha]
    exact measurable_const
  · simp only [smallMarginal, if_neg ha]
    have hb := ((continuous_apply a).comp (continuous_lowerBids i row)).measurable
    have hz := measurable_usableRoot i row p
    exact measurable_const.min
      ((measurable_const.max (hb.sub hz)).div (measurable_const.mul (hb.max hz)))

theorem measurable_largeLaw_mass (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (S : Finset (Fin M)) :
    Measurable (fun x => (largeLaw i row p x).mass S) := by
  unfold largeLaw FiniteLaw.map
  dsimp only
  apply Finset.measurable_sum
  intro T _
  split_ifs
  · exact measurable_smallLaw_mass i row p T
  · exact measurable_const

def largeSide (row : Source.CountRow M) : Fin 2 :=
  if Source.residual row 0 < Source.residual row 1 then 1 else 0

def pureSet (i : Row) (row : Source.CountRow M) (j : Fin 2) (x : State i M) : Finset (Fin M) :=
  if j=0 then ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x))).1
  else ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x))).2

omit [NeZero M] in
theorem measurable_pureSet (i : Row) (row : Source.CountRow M) (j : Fin 2) :
    Measurable (pureSet i row j) := by
  have hp := ((Source.lowerTemplate row).measurable_selection (kappa i)).comp
    (continuous_lowerBids i row).measurable
  unfold pureSet
  split_ifs
  · exact hp.fst
  · exact hp.snd

def commonLaw (i : Row) (row : Source.CountRow M) (x : State i M) : FiniteLaw (Signal row) :=
  if Source.residual row 0 = Source.residual row 1 then FiniteLaw.dirac none
  else Literal.signalLaw (Source.sourceWeights i x.1 row (bids i x)) (Source.imbalance row)
    (Source.guardAlpha i x.1 row (bids i x))
    (Source.guardAlpha_bounds i x.1 row (bids i x)).1
    (Source.guardAlpha_bounds i x.1 row (bids i x)).2

theorem measurable_commonLaw_mass (i : Row) (row : Source.CountRow M) (q : Signal row) :
    Measurable (fun x => (commonLaw i row x).mass q) := by
  unfold commonLaw
  split_ifs
  · exact measurable_const
  · have hm : Measurable (fun x => ((pathLaw
        (Source.sourceWeights i x.1 row (bids i x)) (Source.imbalance row) ∅).map some).mass q) := by
      unfold FiniteLaw.map
      dsimp only
      apply Finset.measurable_sum
      intro p _
      split_ifs
      · exact (WeightedSampling.measurable_pathLaw_mass _ _ p).comp (continuous_weights i row).measurable
      · exact measurable_const
    simp only [Literal.signalLaw, FiniteLaw.mixture]
    exact ((measurable_guardAlpha i row).mul hm).add
      ((measurable_const.sub (measurable_guardAlpha i row)).mul measurable_const)

def privateLaw (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (q : Signal row) : FiniteLaw (Finset (Fin M)) :=
  if Source.residual row 0 = Source.residual row 1 then equalLottery i row (bids i x)
  else match q with
  | none => FiniteLaw.dirac (pureSet i row j x)
  | some p => if j = largeSide row then largeLaw i row p x else smallLaw i row p x

theorem measurable_privateLaw_mass (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (S : Finset (Fin M)) :
    Measurable (fun x : State i M × Signal row => (privateLaw i row j x.1 x.2).mass S) := by
  have hsec (q : Signal row) : Measurable (fun x => (privateLaw i row j x q).mass S) := by
    by_cases he : Source.residual row 0 = Source.residual row 1
    · simp only [privateLaw, if_pos he]
      have hm := (ExactCapacity.measurable_symmetricLottery_mass S).comp
        ((EqualCapacity.measurable_positiveMarginal (xi i) (Source.small row)
          (xi_range i).1 (xi_range i).2).comp (continuous_lowerBids i row).measurable)
      convert! hm using 1
    · simp only [privateLaw, if_neg he]
      cases q with
      | none =>
        have hh : (fun x : State i M => (FiniteLaw.dirac (pureSet i row j x)).mass S) =
            (fun x => if S=pureSet i row j x then (1:ℝ) else 0) := by
          funext x
          by_cases h : S=pureSet i row j x <;> simp [FiniteLaw.dirac,h]
        change Measurable (fun x => (FiniteLaw.dirac (pureSet i row j x)).mass S)
        rw [hh]
        exact Measurable.ite (measurableSet_eq_fun measurable_const (measurable_pureSet i row j))
          measurable_const measurable_const
      | some p =>
        by_cases hj : j = largeSide row
        · simpa only [if_pos hj] using measurable_largeLaw_mass i row p S
        · simpa only [if_neg hj] using measurable_smallLaw_mass i row p S
  have hm : Measurable (fun x : Signal row×State i M => (privateLaw i row j x.2 x.1).mass S) := by
    apply measurable_from_prod_countable_right
    intro q
    exact hsec q
  convert! hm.comp measurable_swap using 1

def commonSample (i : Row) (row : Source.CountRow M) (x : State i M)
    (u : unitInterval) : Signal row := ExtensionalSampler.sample (commonLaw i row x) u

theorem commonSample_measurable (i : Row) (row : Source.CountRow M) :
    Measurable (Function.uncurry (commonSample i row)) :=
  ExtensionalSampler.measurable_family (commonLaw i row) (measurable_commonLaw_mass i row)

theorem commonSample_support (i : Row) (row : Source.CountRow M) (x : State i M) (u : unitInterval) :
    0 < (commonLaw i row x).mass (commonSample i row x u) :=
  ExtensionalSampler.support (commonLaw i row x) u

theorem commonSample_law (i : Row) (row : Source.CountRow M) (x : State i M) :
    volume.map (commonSample i row x) = FiniteLaw.probabilityMeasure (commonLaw i row x) :=
  ExtensionalSampler.law (commonLaw i row x)

def privateSample (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M × Signal row) (u : unitInterval) : Finset (Fin M) :=
  ExtensionalSampler.sample (privateLaw i row j x.1 x.2) u

theorem privateSample_measurable (i : Row) (row : Source.CountRow M) (j : Fin 2) :
    Measurable (Function.uncurry (privateSample i row j)) := by
  convert! ExtensionalSampler.measurable_family (fun x : State i M×Signal row =>
    privateLaw i row j x.1 x.2) (measurable_privateLaw_mass i row j) using 1

theorem privateSample_support (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M × Signal row) (u : unitInterval) :
    0 < (privateLaw i row j x.1 x.2).mass (privateSample i row j x u) :=
  ExtensionalSampler.support (privateLaw i row j x.1 x.2) u

theorem privateSample_law (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M × Signal row) :
    volume.map (privateSample i row j x) = FiniteLaw.probabilityMeasure (privateLaw i row j x.1 x.2) :=
  ExtensionalSampler.law (privateLaw i row j x.1 x.2)

theorem privateSamples_joint (i : Row) (row : Source.CountRow M)
    (x : State i M × Signal row) :
    ((volume : Measure unitInterval).prod volume).map
      (fun s => (privateSample i row 0 x s.1, privateSample i row 1 x s.2)) =
      (FiniteLaw.probabilityMeasure (privateLaw i row 0 x.1 x.2)).prod
        (FiniteLaw.probabilityMeasure (privateLaw i row 1 x.1 x.2)) := by
  have h0 := (privateSample_measurable i row 0).comp ((measurable_const (a := x)).prodMk measurable_id)
  have h1 := (privateSample_measurable i row 1).comp ((measurable_const (a := x)).prodMk measurable_id)
  change Measurable (privateSample i row 0 x) at h0
  change Measurable (privateSample i row 1 x) at h1
  change ((volume : Measure unitInterval).prod volume).map
    (Prod.map (privateSample i row 0 x) (privateSample i row 1 x)) = _
  rw [← Measure.map_prod_map _ _ h0 h1, privateSample_law, privateSample_law]

theorem common_some_support (i : Row) (row : Source.CountRow M) (x : State i M)
    (p : Path (Fin M) (Source.imbalance row))
    (hp : 0 < (commonLaw i row x).mass (some p)) :
    Source.residual row 0 ≠ Source.residual row 1 ∧
      0 < Source.guardAlpha i x.1 row (bids i x) ∧
      0 < (pathLaw (Source.sourceWeights i x.1 row (bids i x)) (Source.imbalance row) ∅).mass p := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp [commonLaw, he, FiniteLaw.dirac] at hp
  have hm : (commonLaw i row x).mass (some p) =
      Source.guardAlpha i x.1 row (bids i x) *
      (pathLaw (Source.sourceWeights i x.1 row (bids i x)) (Source.imbalance row) ∅).mass p := by
    simp [commonLaw, he, Literal.signalLaw, FiniteLaw.mixture, FiniteLaw.map, FiniteLaw.dirac]
  rw [hm] at hp
  have ha : 0 < Source.guardAlpha i x.1 row (bids i x) := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (Source.guardAlpha_bounds i x.1 row (bids i x)).1
    rw [hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  have hpath : 0 < (pathLaw (Source.sourceWeights i x.1 row (bids i x))
      (Source.imbalance row) ∅).mass p := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (FiniteLaw.nonneg _ p)
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  exact ⟨he, ha, hpath⟩

omit [NeZero M] in
theorem alpha_pos_raw (i : Row) (row : Source.CountRow M) (x : State i M)
    (ha : 0 < Source.guardAlpha i x.1 row (bids i x)) : 0 < rawWeight i row x := by
  have hs := (Source.guardAlpha_pos_slacks i x.1 row (bids i x) ha).1
  simpa only [Source.guardAlpha, if_neg (Nat.ne_of_gt hs),rawWeight] using ha

theorem privateLaw_some_card (i : Row) (row : Source.CountRow M) (x : State i M)
    (p : Path (Fin M) (Source.imbalance row))
    (hp : 0 < (commonLaw i row x).mass (some p)) (j : Fin 2)
    (S : Finset (Fin M)) (hS : (privateLaw i row j x (some p)).mass S ≠ 0) :
    S.card = Source.residual row j ∧ S ⊆ row.lower := by
  obtain ⟨hne,ha,hpath⟩ := common_some_support i row x p hp
  have hr := Source.guarded_weighted_path_root i x.1 row (bids i x)
    (fun a _ => (bids_bounds i x a).2) ha p hpath
  have hz := (Source.rootBounds i x.1).1.trans_le hr.2.1.1
  have hsmall := Literal.completion_implements (xi_range i).1 hz _ _ (Source.small row) hr.2.2.1
  have hlarge := Literal.largeCompletion_implements (xi_range i).1 hz _ _ (Source.small row) hr.2.2.1
  have hE : finalSet (Source.imbalance row) ∅ p ⊆ row.lower := by
    intro a haE
    by_contra hal
    have hh := hr.2.2.2 a haE
    rw [Source.lowerBids_of_not_mem row _ hal] at hh
    linarith [(Source.rootBounds i x.1).1, (Source.rootBounds i x.1).2.1]
  have hzero (a : Fin M) (hal : a ∉ row.lower) :
      smallMarginal (xi i) (actualRoot i row p x) (Source.lowerBids row (bids i x))
        (finalSet (Source.imbalance row) ∅ p) a = 0 ∧
      largeMarginal (xi i) (actualRoot i row p x) (Source.lowerBids row (bids i x))
        (finalSet (Source.imbalance row) ∅ p) a = 0 := by
    have hn : a ∉ finalSet (Source.imbalance row) ∅ p := fun h => hal (hE h)
    simp only [smallMarginal, largeMarginal, if_neg hn, Source.lowerBids_of_not_mem row _ hal,
      actualRoot,exposure_zero hz.le]
    exact ⟨trivial,trivial⟩
  have hcapL : Source.small row+(finalSet (Source.imbalance row) ∅ p).card = Source.large row := by
    rw [hr.1, Source.small_add_imbalance]
  have hside : Source.residual row j = if j=largeSide row then Source.large row else Source.small row := by
    by_cases h01 : Source.residual row 0 < Source.residual row 1
    · fin_cases j <;> simp [largeSide, h01, Source.large, Source.small,
        max_eq_right h01.le, min_eq_left h01.le]
    · have h10 : Source.residual row 1 ≤ Source.residual row 0 := le_of_not_gt h01
      fin_cases j <;> simp [largeSide, h01, Source.large, Source.small,
        max_eq_left h10, min_eq_right h10]
  simp only [privateLaw, if_neg hne] at hS
  rw [hside]
  by_cases hj : j=largeSide row
  · rw [if_pos hj] at hS ⊢
    change (Literal.largeCompletion (xi i) (usableRoot i row p x)
      (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p)).mass S ≠ 0 at hS
    rw [usableRoot_eq i row p x (alpha_pos_raw i row x ha)] at hS
    refine ⟨(hlarge.1 S hS).trans hcapL,?_⟩
    intro a haS
    by_contra hal
    have hm : Proposer.marginal (Literal.largeCompletion (xi i) (actualRoot i row p x)
        (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p)) a = 0 :=
      (hlarge.2 a).trans (hzero a hal).2
    exact Literal.zero_marginal_omitted _ a hm S hS haS
  · rw [if_neg hj] at hS ⊢
    change (Literal.completion (xi i) (usableRoot i row p x)
      (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p)).mass S ≠ 0 at hS
    rw [usableRoot_eq i row p x (alpha_pos_raw i row x ha)] at hS
    refine ⟨hsmall.1 S hS,?_⟩
    intro a haS
    by_contra hal
    have hm : Proposer.marginal (Literal.completion (xi i) (actualRoot i row p x)
        (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p)) a = 0 :=
      (hsmall.2 a).trans (hzero a hal).1
    exact Literal.zero_marginal_omitted _ a hm S hS haS

theorem privateLaw_feasible (i : Row) (row : Source.CountRow M) (x : State i M)
    (q : Signal row) (hq : 0 < (commonLaw i row x).mass q) (j : Fin 2)
    (S : Finset (Fin M)) (hS : (privateLaw i row j x q).mass S ≠ 0) :
    S.card ≤ Source.residual row j ∧ S ⊆ row.lower := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · have hm := EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row (bids i x))
    have hse : Source.small row = Source.residual row j := by
      fin_cases j <;> simp [Source.small, he]
    simp only [privateLaw, if_pos he] at hS
    refine ⟨(hm.1 S hS).le.trans ((min_le_left _ _).trans_eq hse),?_⟩
    intro a haS
    by_contra hal
    have hz : EqualCapacity.positiveMarginal (xi i) (Source.small row)
        (Source.lowerBids row (bids i x)) a = 0 := by
      apply EqualCapacity.onSupport_outside
      simp [Existence.PayOnceBounded.mem_positiveSupport, Source.lowerBids, hal]
    exact Literal.zero_marginal_omitted _ a ((hm.2 a).trans hz) S hS haS
  · cases q with
    | some p => exact ⟨(privateLaw_some_card i row x p hq j S hS).1.le,
        (privateLaw_some_card i row x p hq j S hS).2⟩
    | none =>
      have hSel : pureSet i row j x = S := by
        by_contra hn
        apply hS
        simp only [privateLaw,if_neg he]
        simp [FiniteLaw.dirac,Ne.symm hn]
      rw [← hSel]
      have hf := (Source.lowerTemplate row).selection_feasible (kappa i)
        (Source.lowerBids row (bids i x))
      fin_cases j
      · simpa [pureSet, Source.lowerTemplate] using And.intro hf.1 hf.2.1
      · simpa [pureSet, Source.lowerTemplate] using And.intro hf.2.2.1 hf.2.2.2

def select (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (common privateSeed : unitInterval) : Finset (Fin M) :=
  privateSample i row j (x, commonSample i row x common) privateSeed

theorem select_measurable (i : Row) (row : Source.CountRow M) (j : Fin 2) :
    Measurable (fun x : (State i M × unitInterval) × unitInterval =>
      select i row j x.1.1 x.1.2 x.2) := by
  convert! (privateSample_measurable i row j).comp
    ((measurable_fst.fst.prodMk ((commonSample_measurable i row).comp measurable_fst)).prodMk measurable_snd) using 1

theorem select_feasible (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : State i M) (common privateSeed : unitInterval) :
    (select i row j x common privateSeed).card ≤ Source.residual row j ∧
      select i row j x common privateSeed ⊆ row.lower := by
  let q := commonSample i row x common
  let S := privateSample i row j (x,q) privateSeed
  have hq := commonSample_support i row x common
  have hS := (privateSample_support i row j (x,q) privateSeed).ne'
  have hf := privateLaw_feasible i row x q hq j S hS
  convert! hf using 1

end NativeRow
end FCAppendix.Affine.UniformFinite
