import FCAppendix.Affine.UniformFinite.NativeRowOptimality
import FCAppendix.Affine.UniformFinite.SeedConditioning

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.NativeRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

theorem prod_dirac {A B : Type*} [Fintype A] [Fintype B] (a : A) (b : B) :
    (FiniteLaw.dirac a).prod (FiniteLaw.dirac b) = FiniteLaw.dirac (a,b) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_prod, FiniteLaw.expect_dirac, FiniteLaw.expect_dirac, FiniteLaw.expect_dirac]

theorem prod_swap {A B : Type*} [Fintype A] [Fintype B]
    (P : FiniteLaw A) (Q : FiniteLaw B) :
    (P.prod Q).map Prod.swap = Q.prod P := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map, FiniteLaw.expect_prod, FiniteLaw.expect_prod]
  simp only [FiniteLaw.expect, Prod.swap_prod_mk, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

omit [NeZero M] in
theorem map_id (P : FiniteLaw (Allocation M)) : P.map id = P := by
  apply FiniteLaw.ext_expect
  intro f
  exact FiniteLaw.expect_map P id f

def privatePair (i : Row) (row : Source.CountRow M) (x : State i M) (q : Signal row) :
    FiniteLaw (Allocation M) := (privateLaw i row 0 x q).prod (privateLaw i row 1 x q)

omit [NeZero M] in
theorem privatePair_none (i : Row) (row : Source.CountRow M) (x : State i M)
    (he : Source.residual row 0 ≠ Source.residual row 1) :
    privatePair i row x none = pureLaw i row (bids i x) := by
  simp only [privatePair, privateLaw, if_neg he]
  rw [prod_dirac]
  simp [pureSet, pureLaw]

omit [NeZero M] in
theorem privatePair_some (i : Row) (row : Source.CountRow M) (x : State i M)
    (he : Source.residual row 0 ≠ Source.residual row 1)
    (ha : 0 < Source.guardAlpha i x.1 row (bids i x))
    (p : Path (Fin M) (Source.imbalance row)) :
    privatePair i row x (some p) =
      (Literal.conditionalCompletion (xi i) (actualRoot i row p x)
        (Source.lowerBids row (bids i x)) (finalSet (Source.imbalance row) ∅ p)).map (orient row) := by
  have hroot := usableRoot_eq i row p x (alpha_pos_raw i row x ha)
  by_cases h01 : Source.residual row 0 < Source.residual row 1
  · have hor : orient row = Prod.swap := by funext P; simp [orient,h01]; rfl
    rw [hor, Literal.conditionalCompletion, prod_swap]
    simp [privatePair, privateLaw, he, largeSide, h01, smallLaw, largeLaw, hroot,
      Literal.largeCompletion]
  · have hor : orient row = id := by funext P; simp [orient,h01]
    rw [hor, map_id]
    simp [privatePair, privateLaw, he, largeSide, h01, smallLaw, largeLaw, hroot,
      Literal.conditionalCompletion, Literal.largeCompletion]

def experimentLaw (i : Row) (row : Source.CountRow M) (x : State i M) :
    FiniteLaw (Allocation M) :=
  (WeightedSampling.pairLaw (commonLaw i row x) (privatePair i row x)).map Prod.snd

theorem experimentLaw_eq_continuation (i : Row) (row : Source.CountRow M) (x : State i M) :
    experimentLaw i row x = continuationLaw i x.1 row (bids i x) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [experimentLaw, FiniteLaw.expect_map, WeightedSampling.expect_pairLaw]
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp only [commonLaw, FiniteLaw.expect_dirac, privatePair,
      privateLaw, continuationLaw, if_pos he, equalLaw]
  · rw [commonLaw, if_neg he, Literal.signalLaw_expect, privatePair_none i row x he,
      continuationLaw, if_neg he, FiniteLaw.expect_mixture]
    by_cases ha : Source.guardAlpha i x.1 row (bids i x) = 0
    · simp only [ha, zero_mul]
    · have hapos : 0 < Source.guardAlpha i x.1 row (bids i x) :=
        lt_of_le_of_ne (Source.guardAlpha_bounds i x.1 row (bids i x)).1 (Ne.symm ha)
      congr 1
      congr 1
      simp only [canonicalLaw, Literal.weightedExperiment, FiniteLaw.expect_map,
        WeightedSampling.expect_pairLaw, privatePair_some i row x he hapos, actualRoot]

def privateDraw (i : Row) (row : Source.CountRow M) (x : State i M × Signal row)
    (s : unitInterval × unitInterval) : Allocation M :=
  (privateSample i row 0 x s.1, privateSample i row 1 x s.2)

theorem privateDraw_measurable (i : Row) (row : Source.CountRow M)
    (x : State i M × Signal row) : Measurable (privateDraw i row x) := by
  convert! ((privateSample_measurable i row 0).comp
    ((measurable_const (a := x)).prodMk measurable_fst)).prodMk
    ((privateSample_measurable i row 1).comp
      ((measurable_const (a := x)).prodMk measurable_snd)) using 1

omit [NeZero M] in
theorem finite_bound (f : Allocation M → ℝ) (P : Allocation M) : |f P| ≤ ∑ Q, |f Q| :=
  Finset.single_le_sum (fun Q _ => abs_nonneg (f Q)) (Finset.mem_univ P)

theorem privateDraw_integral (i : Row) (row : Source.CountRow M)
    (x : State i M × Signal row) (f : Allocation M → ℝ) :
    (∫ s, f (privateDraw i row x s) ∂((volume : Measure unitInterval).prod volume)) =
      (privatePair i row x.1 x.2).expect f := by
  have hf : Measurable f := measurable_of_countable f
  have hint : Integrable (fun s => f (privateDraw i row x s))
      ((volume : Measure unitInterval).prod volume) :=
    Integrable.of_bound (hf.comp (privateDraw_measurable i row x)).aestronglyMeasurable
      (∑ P, |f P|) (Eventually.of_forall (fun s => finite_bound f _))
  rw [integral_prod _ hint, privatePair, FiniteLaw.expect_prod]
  have hm0 := (privateSample_measurable i row 0).comp ((measurable_const (a := x)).prodMk measurable_id)
  have hm1 := (privateSample_measurable i row 1).comp ((measurable_const (a := x)).prodMk measurable_id)
  change Measurable (privateSample i row 0 x) at hm0
  change Measurable (privateSample i row 1 x) at hm1
  have hinner (s0 : unitInterval) :
      (∫ s1 : unitInterval, f (privateSample i row 0 x s0, privateSample i row 1 x s1)) =
        (privateLaw i row 1 x.1 x.2).expect (fun S => f (privateSample i row 0 x s0,S)) := by
    rw [← integral_map hm1.aemeasurable
      (measurable_of_countable (fun S : Finset (Fin M)=>f (privateSample i row 0 x s0,S))).aestronglyMeasurable,
      privateSample_law, Literal.integral_finiteLaw]
  simp only [privateDraw]
  simp_rw [hinner]
  rw [← integral_map hm0.aemeasurable
    (measurable_of_countable (fun S : Finset (Fin M)=>
      (privateLaw i row 1 x.1 x.2).expect (fun T=>f (S,T)))).aestronglyMeasurable,
    privateSample_law, Literal.integral_finiteLaw]

abbrev Seeds := unitInterval × (unitInterval × unitInterval)

def seedsLaw : Measure Seeds := (volume : Measure unitInterval).prod (volume.prod volume)

instance : IsProbabilityMeasure seedsLaw := by unfold seedsLaw; infer_instance

def draw (i : Row) (row : Source.CountRow M) (x : State i M) (s : Seeds) : Allocation M :=
  (select i row 0 x s.1 s.2.1, select i row 1 x s.1 s.2.2)

theorem draw_measurable (i : Row) (row : Source.CountRow M) (x : State i M) :
    Measurable (draw i row x) := by
  convert! ((select_measurable i row 0).comp
    (((measurable_const (a := x)).prodMk measurable_fst).prodMk measurable_snd.fst)).prodMk
      ((select_measurable i row 1).comp
        (((measurable_const (a := x)).prodMk measurable_fst).prodMk measurable_snd.snd)) using 1

theorem draw_integral (i : Row) (row : Source.CountRow M) (x : State i M)
    (f : Allocation M → ℝ) :
    (∫ s, f (draw i row x s) ∂seedsLaw) = (continuationLaw i x.1 row (bids i x)).expect f := by
  have hm : Measurable (fun s => f (draw i row x s)) :=
    (measurable_of_countable f).comp (draw_measurable i row x)
  have hint : Integrable (fun s => f (draw i row x s)) seedsLaw :=
    Integrable.of_bound hm.aestronglyMeasurable (∑ P, |f P|)
      (Eventually.of_forall (fun s => finite_bound f _))
  rw [seedsLaw, integral_prod _ hint]
  change (∫ u : unitInterval, ∫ s, f (privateDraw i row (x,commonSample i row x u) s)
    ∂((volume : Measure unitInterval).prod volume)) = _
  simp_rw [privateDraw_integral]
  have hcommon := (commonSample_measurable i row).comp ((measurable_const (a := x)).prodMk measurable_id)
  change Measurable (commonSample i row x) at hcommon
  rw [← integral_map hcommon.aemeasurable
    (measurable_of_countable (fun q : Signal row=>(privatePair i row x q).expect f)).aestronglyMeasurable,
    commonSample_law, Literal.integral_finiteLaw]
  have he := congrArg (fun P : FiniteLaw (Allocation M) => P.expect f)
    (experimentLaw_eq_continuation i row x)
  simpa only [experimentLaw, FiniteLaw.expect_map, WeightedSampling.expect_pairLaw] using he

theorem draw_law (i : Row) (row : Source.CountRow M) (x : State i M) :
    FiniteLaw.ofMeasure seedsLaw (draw i row x) (draw_measurable i row x) =
      continuationLaw i x.1 row (bids i x) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_ofMeasure, draw_integral]

end FCAppendix.Affine.UniformFinite.NativeRow
