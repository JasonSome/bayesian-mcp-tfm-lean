import FCAppendix.Affine.UniformFinite.Late.ExceptionalContinuation
import FCAppendix.Affine.UniformFinite.NativeRowLaw

set_option maxHeartbeats 1000000

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

abbrev Signal (row : Source.CountRow M) := NativeRow.Signal row

def Good (i : Row) (row : Source.CountRow M) (a : Fin M) (b : Fin M → ℝ) : Prop :=
  a ∈ row.lower ∧ (∀ j ∈ row.lower, 0 ≤ b j) ∧
    (∀ j ∈ row.lower, j ≠ a → b j ≤ cap i)

def smallLaw (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (b : Fin M → ℝ) : FiniteLaw (Finset (Fin M)) :=
  Exceptional.completion (xi i) (Source.small row) (Source.lowerBids row b)
    (finalSet (Source.imbalance row) ∅ p)

def largeLaw (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (b : Fin M → ℝ) : FiniteLaw (Finset (Fin M)) :=
  Exceptional.largeCompletion (xi i) (Source.small row) (Source.lowerBids row b)
    (finalSet (Source.imbalance row) ∅ p)

omit [NeZero M] in
theorem measurable_smallLaw_mass (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (S : Finset (Fin M)) :
    Measurable (fun b => (smallLaw i row p b).mass S) :=
  (Exceptional.measurable_completion_mass (xi_range i).1 (xi_range i).2
    (Source.small row) _ S).comp (Exceptional.continuous_lowerBids row).measurable

omit [NeZero M] in
theorem measurable_largeLaw_mass (i : Row) (row : Source.CountRow M)
    (p : Path (Fin M) (Source.imbalance row)) (S : Finset (Fin M)) :
    Measurable (fun b => (largeLaw i row p b).mass S) :=
  (Exceptional.measurable_largeCompletion_mass (xi_range i).1 (xi_range i).2
    (Source.small row) _ S).comp (Exceptional.continuous_lowerBids row).measurable

def pureSet (i : Row) (row : Source.CountRow M) (j : Fin 2) (b : Fin M → ℝ) : Finset (Fin M) :=
  if j=0 then ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row b)).1
  else ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row b)).2

omit [NeZero M] in
theorem measurable_pureSet (i : Row) (row : Source.CountRow M) (j : Fin 2) :
    Measurable (pureSet i row j) := by
  have hm := ((Source.lowerTemplate row).measurable_selection (kappa i)).comp
    (Exceptional.continuous_lowerBids row).measurable
  unfold pureSet
  split_ifs
  · exact hm.fst
  · exact hm.snd

def commonLaw (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) : FiniteLaw (Signal row) :=
  if Source.residual row 0 = Source.residual row 1 then FiniteLaw.dirac none
  else Literal.signalLaw (Exceptional.weight i G row b a) (Source.imbalance row)
    (Exceptional.alpha i G row b a) (Exceptional.alpha_bounds i G row b a).1
    (Exceptional.alpha_bounds i G row b a).2

theorem measurable_commonLaw_mass (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (q : Signal row) : Measurable (fun b => (commonLaw i G row a b).mass q) := by
  unfold commonLaw
  split_ifs
  · exact measurable_const
  · have hm : Measurable (fun b => ((pathLaw
        (Exceptional.weight i G row b a) (Source.imbalance row) ∅).map some).mass q) := by
      unfold FiniteLaw.map
      dsimp only
      apply Finset.measurable_sum
      intro p _
      split_ifs
      · exact (WeightedSampling.measurable_pathLaw_mass _ _ p).comp
          (Exceptional.continuous_weight i G row a).measurable
      · exact measurable_const
    exact ((Exceptional.measurable_alpha i G row a).mul hm).add
      ((measurable_const.sub (Exceptional.measurable_alpha i G row a)).mul measurable_const)

def privateLaw (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (b : Fin M → ℝ) (q : Signal row) : FiniteLaw (Finset (Fin M)) :=
  if Source.residual row 0 = Source.residual row 1 then equalLottery i row b
  else match q with
  | none => FiniteLaw.dirac (pureSet i row j b)
  | some p => if j = NativeRow.largeSide row then largeLaw i row p b else smallLaw i row p b

omit [NeZero M] in
theorem measurable_privateLaw_mass (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (S : Finset (Fin M)) :
    Measurable (fun x : (Fin M → ℝ) × Signal row => (privateLaw i row j x.1 x.2).mass S) := by
  have hsec (q : Signal row) : Measurable (fun x => (privateLaw i row j x q).mass S) := by
    by_cases he : Source.residual row 0 = Source.residual row 1
    · simp only [privateLaw, if_pos he]
      have hm := (ExactCapacity.measurable_symmetricLottery_mass S).comp
        ((EqualCapacity.measurable_positiveMarginal (xi i) (Source.small row)
          (xi_range i).1 (xi_range i).2).comp (Exceptional.continuous_lowerBids row).measurable)
      convert! hm using 1
    · simp only [privateLaw, if_neg he]
      cases q with
      | none =>
        have hh : (fun x : (Fin M → ℝ) => (FiniteLaw.dirac (pureSet i row j x)).mass S) =
            (fun x => if S=pureSet i row j x then (1:ℝ) else 0) := by
          funext x
          by_cases h : S=pureSet i row j x <;> simp [FiniteLaw.dirac,h]
        change Measurable (fun x => (FiniteLaw.dirac (pureSet i row j x)).mass S)
        rw [hh]
        exact Measurable.ite (measurableSet_eq_fun measurable_const (measurable_pureSet i row j))
          measurable_const measurable_const
      | some p =>
        by_cases hj : j = NativeRow.largeSide row
        · simpa only [if_pos hj] using measurable_largeLaw_mass i row p S
        · simpa only [if_neg hj] using measurable_smallLaw_mass i row p S
  have hm : Measurable (fun x : Signal row×(Fin M → ℝ) => (privateLaw i row j x.2 x.1).mass S) := by
    apply measurable_from_prod_countable_right
    intro q
    exact hsec q
  convert! hm.comp measurable_swap using 1

def commonSample (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (u : unitInterval) : Signal row :=
  ExtensionalSampler.sample (commonLaw i G row a b) u

theorem commonSample_measurable (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) : Measurable (Function.uncurry (commonSample i G row a)) :=
  ExtensionalSampler.measurable_family (commonLaw i G row a) (measurable_commonLaw_mass i G row a)

theorem commonSample_support (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (u : unitInterval) :
    0 < (commonLaw i G row a b).mass (commonSample i G row a b u) :=
  ExtensionalSampler.support (commonLaw i G row a b) u

theorem commonSample_law (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) :
    volume.map (commonSample i G row a b) = FiniteLaw.probabilityMeasure (commonLaw i G row a b) :=
  ExtensionalSampler.law (commonLaw i G row a b)

def privateSample (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : (Fin M → ℝ) × Signal row) (u : unitInterval) : Finset (Fin M) :=
  ExtensionalSampler.sample (privateLaw i row j x.1 x.2) u

theorem privateSample_measurable (i : Row) (row : Source.CountRow M) (j : Fin 2) :
    Measurable (Function.uncurry (privateSample i row j)) :=
by
  convert! ExtensionalSampler.measurable_family (fun x : (Fin M → ℝ) × Signal row =>
    privateLaw i row j x.1 x.2) (measurable_privateLaw_mass i row j) using 1

theorem privateSample_support (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : (Fin M → ℝ) × Signal row) (u : unitInterval) :
    0 < (privateLaw i row j x.1 x.2).mass (privateSample i row j x u) :=
  ExtensionalSampler.support (privateLaw i row j x.1 x.2) u

theorem privateSample_law (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : (Fin M → ℝ) × Signal row) :
    volume.map (privateSample i row j x) = FiniteLaw.probabilityMeasure (privateLaw i row j x.1 x.2) :=
  ExtensionalSampler.law (privateLaw i row j x.1 x.2)

theorem privateSamples_joint (i : Row) (row : Source.CountRow M)
    (x : (Fin M → ℝ) × Signal row) :
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

theorem common_some_support (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (p : Path (Fin M) (Source.imbalance row))
    (hp : 0 < (commonLaw i G row a b).mass (some p)) :
    Source.residual row 0 ≠ Source.residual row 1 ∧
      0 < Exceptional.alpha i G row b a ∧
      0 < (pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).mass p := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp [commonLaw, he, FiniteLaw.dirac] at hp
  have hm : (commonLaw i G row a b).mass (some p) = Exceptional.alpha i G row b a *
      (pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).mass p := by
    simp [commonLaw, he, Literal.signalLaw, FiniteLaw.mixture, FiniteLaw.map, FiniteLaw.dirac]
  rw [hm] at hp
  have ha : 0 < Exceptional.alpha i G row b a := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (Exceptional.alpha_bounds i G row b a).1
    rw [hz, zero_mul] at hp
    exact (lt_irrefl 0) hp
  have hpath : 0 < (pathLaw (Exceptional.weight i G row b a) (Source.imbalance row) ∅).mass p := by
    by_contra hn
    have hz := le_antisymm (le_of_not_gt hn) (FiniteLaw.nonneg _ p)
    rw [hz, mul_zero] at hp
    exact (lt_irrefl 0) hp
  exact ⟨he,ha,hpath⟩

omit [NeZero M] in
theorem residual_side (row : Source.CountRow M) (j : Fin 2) :
    Source.residual row j = if j=NativeRow.largeSide row then Source.large row else Source.small row := by
  by_cases h01 : Source.residual row 0 < Source.residual row 1
  · fin_cases j <;> simp [NativeRow.largeSide, h01, Source.large, Source.small,
      max_eq_right h01.le, min_eq_left h01.le]
  · have h10 : Source.residual row 1 ≤ Source.residual row 0 := le_of_not_gt h01
    fin_cases j <;> simp [NativeRow.largeSide, h01, Source.large, Source.small,
      max_eq_left h10, min_eq_right h10]

theorem privateLaw_feasible (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (hb : Good i row a b)
    (q : Signal row) (hq : 0 < (commonLaw i G row a b).mass q) (j : Fin 2)
    (S : Finset (Fin M)) (hS : (privateLaw i row j b q).mass S ≠ 0) :
    S.card ≤ Source.residual row j ∧ S ⊆ row.lower := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · have hm := EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row b)
    have hse : Source.small row = Source.residual row j := by
      fin_cases j <;> simp [Source.small,he]
    simp only [privateLaw, if_pos he] at hS
    refine ⟨(hm.1 S hS).le.trans ((min_le_left _ _).trans_eq hse),?_⟩
    intro k hkS
    by_contra hk
    have hz : EqualCapacity.positiveMarginal (xi i) (Source.small row)
        (Source.lowerBids row b) k = 0 := by
      apply EqualCapacity.onSupport_outside
      simp [Existence.PayOnceBounded.mem_positiveSupport, Source.lowerBids, hk]
    exact Literal.zero_marginal_omitted _ k ((hm.2 k).trans hz) S hS hkS
  · cases q with
    | none =>
      have hSel : pureSet i row j b = S := by
        by_contra hn
        simp [privateLaw, he, FiniteLaw.dirac, Ne.symm hn] at hS
      rw [← hSel]
      have hf := (Source.lowerTemplate row).selection_feasible (kappa i) (Source.lowerBids row b)
      fin_cases j
      · simpa [pureSet, Source.lowerTemplate] using And.intro hf.1 hf.2.1
      · simpa [pureSet, Source.lowerTemplate] using And.intro hf.2.2.1 hf.2.2.2
    | some p =>
      obtain ⟨hne,hα,hpath⟩ := common_some_support i G row a b p hq
      have h := Exceptional.guarded_private_implements i G row b a hb.1 hb.2.1 hb.2.2 hα p hpath
      simp only [privateLaw,if_neg he] at hS
      rw [residual_side]
      by_cases hj : j=NativeRow.largeSide row
      · rw [if_pos hj] at hS ⊢
        exact ⟨(h.2.1.1 S hS).le.trans_eq (Source.small_add_imbalance row),h.2.2.2 S hS⟩
      · rw [if_neg hj] at hS ⊢
        exact ⟨(h.1.1 S hS).le,h.2.2.1 S hS⟩

def select (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (a : Fin M)
    (j : Fin 2) (b : Fin M → ℝ) (common privateSeed : unitInterval) : Finset (Fin M) :=
  privateSample i row j (b,commonSample i G row a b common) privateSeed

theorem select_measurable (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (j : Fin 2) :
    Measurable (fun x : ((Fin M → ℝ) × unitInterval) × unitInterval =>
      select i G row a j x.1.1 x.1.2 x.2) := by
  convert! (privateSample_measurable i row j).comp
    ((measurable_fst.fst.prodMk ((commonSample_measurable i G row a).comp measurable_fst)).prodMk
      measurable_snd) using 1

theorem select_feasible (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (hb : Good i row a b)
    (j : Fin 2) (common privateSeed : unitInterval) :
    (select i G row a j b common privateSeed).card ≤ Source.residual row j ∧
      select i G row a j b common privateSeed ⊆ row.lower := by
  have hf := privateLaw_feasible i G row a b hb
    (commonSample i G row a b common) (commonSample_support i G row a b common) j
    (privateSample i row j (b,commonSample i G row a b common) privateSeed)
    (privateSample_support i row j (b,commonSample i G row a b common) privateSeed).ne'
  simpa only [select] using hf

theorem privateLaw_optimal (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (hb : Good i row a b)
    (q : Signal row) (hq : 0 < (commonLaw i G row a b).mass q) (j : Fin 2)
    (S : Finset (Fin M)) (hS : (privateLaw i row j b q).mass S ≠ 0) :
    Finite.Optimal (Source.residual row j)
      (fun (k : Fin M) => Source.lowerBids row b k *
        (1-xi i*Proposer.marginal (privateLaw i row (Hybrid.otherProposer j) b q) k)) S := by
  by_cases he : Source.residual row 0 = Source.residual row 1
  · have hs : Source.small row = Source.residual row j := by
      fin_cases j <;> simp [Source.small, he]
    have hopt := EqualCapacity.canonicalLottery_support_optimal (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row b) S
      (by simpa only [privateLaw, if_pos he, equalLottery, EqualCapacity.canonicalLottery] using hS)
    have hm := (EqualCapacity.canonicalLottery_implements (xi_range i).1 (xi_range i).2
      (Source.small row) (Source.lowerBids row b)).2
    have hmass (k : Fin M) : Proposer.marginal
        (privateLaw i row (Hybrid.otherProposer j) b q) k =
        EqualCapacity.positiveMarginal (xi i) (Source.small row) (Source.lowerBids row b) k := by
      simpa only [privateLaw,if_pos he,equalLottery,EqualCapacity.canonicalLottery,Proposer.marginal]
        using hm k
    simp only [hmass]
    simpa only [hs] using hopt
  · cases q with
    | none =>
      have hsel : S = pureSet i row j b := by
        by_contra hn
        simp [privateLaw, he, FiniteLaw.dirac, hn] at hS
      subst S
      have hp := NativeRow.pure_numerical_optimal (Source.lowerTemplate row) (xi i)
        (Source.lowerBids row b) (fun k hk => Source.lowerBids_of_not_mem row _ hk)
      have hm (k : Fin 2) (l : Fin M) : Proposer.marginal (ι := Fin M) (privateLaw i row k b none) l =
          if l∈pureSet i row k b then (1:ℝ) else 0 := by
        simp [privateLaw, he, Proposer.marginal, FiniteLaw.prob_eq_expect, FiniteLaw.expect_dirac]
      simp only [hm]
      fin_cases j
      · simpa [pureSet,Hybrid.otherProposer,Source.lowerTemplate,kappa] using hp.1
      · simpa [pureSet,Hybrid.otherProposer,Source.lowerTemplate,kappa] using hp.2
    | some p =>
      obtain ⟨hne,hα,hpath⟩ := common_some_support i G row a b p hq
      have himp := Exceptional.guarded_private_implements i G row b a hb.1 hb.2.1 hb.2.2 hα p hpath
      have hbr := Exceptional.guarded_conditional_nash i G row b a hb.1 hb.2.1 hb.2.2 hα p hpath
      have hsBR : ∀ A, (smallLaw i row p b).mass A ≠ 0 →
          Finite.Optimal (Source.small row)
            (fun k => Source.lowerBids row b k*(1-xi i*Proposer.marginal (largeLaw i row p b) k)) A :=
        NativeRow.supported_best_reply (xi i) (Source.lowerBids row b) (Source.small row)
          (smallLaw i row p b) (largeLaw i row p b)
          (fun A hA => (himp.1.1 A hA).le) hbr.1
      have hlBR : ∀ A, (largeLaw i row p b).mass A ≠ 0 →
          Finite.Optimal (Source.large row)
            (fun k => Source.lowerBids row b k*(1-xi i*Proposer.marginal (smallLaw i row p b) k)) A := by
        rw [← Source.small_add_imbalance]
        exact NativeRow.supported_best_reply (xi i) (Source.lowerBids row b)
          (Source.small row+Source.imbalance row) (largeLaw i row p b) (smallLaw i row p b)
          (fun A hA => (himp.2.1.1 A hA).le) hbr.2
      by_cases h01 : Source.residual row 0 < Source.residual row 1
      · have hs0 : Source.small row = Source.residual row 0 := min_eq_left h01.le
        have hl1 : Source.large row = Source.residual row 1 := max_eq_right h01.le
        fin_cases j
        · have hA : (smallLaw i row p b).mass S ≠ 0 := by
            simpa [privateLaw,he,NativeRow.largeSide,h01] using hS
          simpa [privateLaw,he,NativeRow.largeSide,h01,Hybrid.otherProposer,hs0] using hsBR S hA
        · have hA : (largeLaw i row p b).mass S ≠ 0 := by
            simpa [privateLaw,he,NativeRow.largeSide,h01] using hS
          simpa [privateLaw,he,NativeRow.largeSide,h01,Hybrid.otherProposer,hl1] using hlBR S hA
      · have h10 : Source.residual row 1 ≤ Source.residual row 0 := le_of_not_gt h01
        have hs1 : Source.small row = Source.residual row 1 := min_eq_right h10
        have hl0 : Source.large row = Source.residual row 0 := max_eq_left h10
        fin_cases j
        · have hA : (largeLaw i row p b).mass S ≠ 0 := by
            simpa [privateLaw,he,NativeRow.largeSide,h01] using hS
          simpa [privateLaw,he,NativeRow.largeSide,h01,Hybrid.otherProposer,hl0] using hlBR S hA
        · have hA : (smallLaw i row p b).mass S ≠ 0 := by
            simpa [privateLaw,he,NativeRow.largeSide,h01] using hS
          simpa [privateLaw,he,NativeRow.largeSide,h01,Hybrid.otherProposer,hs1] using hsBR S hA

theorem privateSample_acceptance (i : Row) (row : Source.CountRow M) (j : Fin 2)
    (x : (Fin M → ℝ) × Signal row) (a : Fin M) :
    (∫ s : unitInterval, if a∈privateSample i row j x s then (1:ℝ) else 0) =
      Proposer.marginal (privateLaw i row j x.1 x.2) a := by
  have hm := (privateSample_measurable i row j).comp ((measurable_const (a := x)).prodMk measurable_id)
  have h := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure volume _ hm
    (privateLaw i row j x.1 x.2) (privateSample_law i row j x)
  rw [Proposer.marginal, FiniteLaw.prob_eq_expect, ← h, FiniteLaw.expect_ofMeasure]
  rfl

def acceptance (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (a : Fin M)
    (j : Fin 2) (b : Fin M → ℝ) (common : unitInterval) (k : Fin M) : ℝ :=
  ∫ s : unitInterval, if k∈select i G row a j b common s then (1:ℝ) else 0

theorem acceptance_eq (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (a : Fin M)
    (j : Fin 2) (b : Fin M → ℝ) (common : unitInterval) (k : Fin M) :
    acceptance i G row a j b common k =
      Proposer.marginal (privateLaw i row j b (commonSample i G row a b common)) k :=
  privateSample_acceptance i row j _ k

theorem select_optimal (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (hb : Good i row a b)
    (j : Fin 2) (common privateSeed : unitInterval) :
    Finite.Optimal (Source.residual row j)
      (fun k => Source.lowerBids row b k*
        (1-xi i*acceptance i G row a (Hybrid.otherProposer j) b common k))
      (select i G row a j b common privateSeed) := by
  have hopt := privateLaw_optimal i G row a b hb
    (commonSample i G row a b common) (commonSample_support i G row a b common) j
    (privateSample i row j (b,commonSample i G row a b common) privateSeed)
    (privateSample_support i row j (b,commonSample i G row a b common) privateSeed).ne'
  simpa only [acceptance_eq,select] using hopt

end FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
