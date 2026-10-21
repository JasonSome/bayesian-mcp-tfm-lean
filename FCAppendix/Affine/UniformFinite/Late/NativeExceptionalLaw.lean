import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

def privatePair (i : Row) (row : Source.CountRow M) (b : Fin M → ℝ) (q : Signal row) :
    FiniteLaw (Allocation M) := (privateLaw i row 0 b q).prod (privateLaw i row 1 b q)

omit [NeZero M] in
theorem privatePair_none (i : Row) (row : Source.CountRow M) (b : Fin M → ℝ)
    (he : Source.residual row 0 ≠ Source.residual row 1) :
    privatePair i row b none = pureLaw i row b := by
  simp only [privatePair, privateLaw, if_neg he]
  rw [NativeRow.prod_dirac]
  simp [pureSet, pureLaw]

omit [NeZero M] in
theorem privatePair_some (i : Row) (row : Source.CountRow M) (b : Fin M → ℝ)
    (he : Source.residual row 0 ≠ Source.residual row 1)
    (p : Path (Fin M) (Source.imbalance row)) :
    privatePair i row b (some p) =
      (Exceptional.conditionalCompletion (xi i) (Source.small row)
        (Source.lowerBids row b) (finalSet (Source.imbalance row) ∅ p)).map (orient row) := by
  by_cases h01 : Source.residual row 0 < Source.residual row 1
  · have hor : orient row = Prod.swap := by funext P; simp [orient,h01]; rfl
    rw [hor, Exceptional.conditionalCompletion, NativeRow.prod_swap]
    simp [privatePair, privateLaw, he, NativeRow.largeSide, h01, smallLaw, largeLaw]
  · have hor : orient row = id := by funext P; simp [orient,h01]
    rw [hor, NativeRow.map_id]
    simp [privatePair, privateLaw, he, NativeRow.largeSide, h01, smallLaw, largeLaw,
      Exceptional.conditionalCompletion]

def experimentLaw (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) : FiniteLaw (Allocation M) :=
  (WeightedSampling.pairLaw (commonLaw i G row a b) (privatePair i row b)).map Prod.snd

theorem experimentLaw_eq_continuation (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) :
    experimentLaw i G row a b = Exceptional.continuationLaw i G row b a := by
  apply FiniteLaw.ext_expect
  intro f
  rw [experimentLaw, FiniteLaw.expect_map, WeightedSampling.expect_pairLaw]
  by_cases he : Source.residual row 0 = Source.residual row 1
  · simp only [commonLaw, FiniteLaw.expect_dirac, privatePair,
      privateLaw, Exceptional.continuationLaw, if_pos he, equalLaw]
  · rw [commonLaw, if_neg he, Literal.signalLaw_expect, privatePair_none i row b he,
      Exceptional.continuationLaw, if_neg he, FiniteLaw.expect_mixture]
    simp only [Exceptional.canonicalLaw, FiniteLaw.expect_map,
      WeightedSampling.expect_pairLaw, privatePair_some i row b he]

def privateDraw (i : Row) (row : Source.CountRow M) (x : (Fin M → ℝ) × Signal row)
    (s : unitInterval × unitInterval) : Allocation M :=
  (privateSample i row 0 x s.1, privateSample i row 1 x s.2)

theorem privateDraw_measurable (i : Row) (row : Source.CountRow M)
    (x : (Fin M → ℝ) × Signal row) : Measurable (privateDraw i row x) := by
  convert! ((privateSample_measurable i row 0).comp
    ((measurable_const (a := x)).prodMk measurable_fst)).prodMk
    ((privateSample_measurable i row 1).comp
      ((measurable_const (a := x)).prodMk measurable_snd)) using 1

theorem privateDraw_integral (i : Row) (row : Source.CountRow M)
    (x : (Fin M → ℝ) × Signal row) (f : Allocation M → ℝ) :
    (∫ s, f (privateDraw i row x s) ∂((volume : Measure unitInterval).prod volume)) =
      (privatePair i row x.1 x.2).expect f := by
  have hf : Measurable f := measurable_of_countable f
  have hint : Integrable (fun s => f (privateDraw i row x s))
      ((volume : Measure unitInterval).prod volume) :=
    Integrable.of_bound (hf.comp (privateDraw_measurable i row x)).aestronglyMeasurable
      (∑ P, |f P|) (Eventually.of_forall (fun s => NativeRow.finite_bound f _))
  rw [integral_prod _ hint, privatePair, FiniteLaw.expect_prod]
  have hm0 := (privateSample_measurable i row 0).comp ((measurable_const (a := x)).prodMk measurable_id)
  have hm1 := (privateSample_measurable i row 1).comp ((measurable_const (a := x)).prodMk measurable_id)
  change Measurable (privateSample i row 0 x) at hm0
  change Measurable (privateSample i row 1 x) at hm1
  have hinner (s0 : unitInterval) :
      (∫ s1 : unitInterval, f (privateSample i row 0 x s0, privateSample i row 1 x s1)) =
        (privateLaw i row 1 x.1 x.2).expect (fun S => f (privateSample i row 0 x s0,S)) := by
    rw [← integral_map hm1.aemeasurable
      (measurable_of_countable (fun S : Finset (Fin M) => f (privateSample i row 0 x s0,S))).aestronglyMeasurable,
      privateSample_law, Literal.integral_finiteLaw]
  simp only [privateDraw]
  simp_rw [hinner]
  rw [← integral_map hm0.aemeasurable
    (measurable_of_countable (fun S : Finset (Fin M) =>
      (privateLaw i row 1 x.1 x.2).expect (fun T => f (S,T)))).aestronglyMeasurable,
    privateSample_law, Literal.integral_finiteLaw]

def draw (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (s : NativeRow.Seeds) : Allocation M :=
  (select i G row a 0 b s.1 s.2.1, select i G row a 1 b s.1 s.2.2)

theorem draw_measurable (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) : Measurable (draw i G row a b) := by
  convert! ((select_measurable i G row a 0).comp
    (((measurable_const (a := b)).prodMk measurable_fst).prodMk measurable_snd.fst)).prodMk
      ((select_measurable i G row a 1).comp
        (((measurable_const (a := b)).prodMk measurable_fst).prodMk measurable_snd.snd)) using 1

theorem draw_integral (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) (f : Allocation M → ℝ) :
    (∫ s, f (draw i G row a b s) ∂NativeRow.seedsLaw) =
      (Exceptional.continuationLaw i G row b a).expect f := by
  have hm : Measurable (fun s => f (draw i G row a b s)) :=
    (measurable_of_countable f).comp (draw_measurable i G row a b)
  have hint : Integrable (fun s => f (draw i G row a b s)) NativeRow.seedsLaw :=
    Integrable.of_bound hm.aestronglyMeasurable (∑ P, |f P|)
      (Eventually.of_forall (fun s => NativeRow.finite_bound f _))
  rw [NativeRow.seedsLaw, integral_prod _ hint]
  change (∫ u : unitInterval, ∫ s,
    f (privateDraw i row (b,commonSample i G row a b u) s)
      ∂((volume : Measure unitInterval).prod volume)) = _
  simp_rw [privateDraw_integral]
  have hcommon := (commonSample_measurable i G row a).comp ((measurable_const (a := b)).prodMk measurable_id)
  change Measurable (commonSample i G row a b) at hcommon
  rw [← integral_map hcommon.aemeasurable
    (measurable_of_countable (fun q : Signal row => (privatePair i row b q).expect f)).aestronglyMeasurable,
    commonSample_law, Literal.integral_finiteLaw]
  have he := congrArg (fun P : FiniteLaw (Allocation M) => P.expect f)
    (experimentLaw_eq_continuation i G row a b)
  simpa only [experimentLaw, FiniteLaw.expect_map, WeightedSampling.expect_pairLaw] using he

theorem draw_law (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ) :
    FiniteLaw.ofMeasure NativeRow.seedsLaw (draw i G row a b)
      (draw_measurable i G row a b) = Exceptional.continuationLaw i G row b a := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_ofMeasure, draw_integral]

theorem focal_count_law (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a focal : Fin M) (b : Fin M → ℝ) :
    (FiniteLaw.ofMeasure NativeRow.seedsLaw (draw i G row a b)
      (draw_measurable i G row a b)).map (pairCount focal) =
      (Exceptional.continuationLaw i G row b a).map (pairCount focal) := by
  rw [draw_law]

end FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
