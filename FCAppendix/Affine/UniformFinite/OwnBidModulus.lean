import FCAppendix.Affine.UniformFinite.CountRowCode
import FCAppendix.Affine.UniformFinite.RestrictedCompact
import FCAppendix.Affine.UniformFinite.SeedPayoffRejection
import FCAppendix.Affine.Hybrid.FavoredUniformContinuity
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical TopologicalSpace
open scoped BigOperators

namespace OwnBid
open Uniform05 SourceContinuity

instance restrictedLawMetrizable (i : Row) : MetrizableSpace (RestrictedLaw i) :=
  MetrizableSpace.subtype _

instance stateCompact (i : Row) (M : ℕ) : CompactSpace (State i M) :=
  inferInstanceAs (CompactSpace (RestrictedLaw i × (Fin M→Bid i)))

instance stateMetrizable (i : Row) (M : ℕ) : MetrizableSpace (State i M) :=
  inferInstanceAs (MetrizableSpace (RestrictedLaw i × (Fin M→Bid i)))

variable {M : ℕ}

abbrev Box (i : Row) (M : ℕ) := Value i × State i M

def realBox (i : Row) (x : Box i M) : ℝ × State i M := (x.1,x.2)

theorem continuous_realBox (i : Row) : Continuous (realBox (M := M) i) :=
  continuous_fst.subtype_val.prodMk continuous_snd

def bound (i : Row) : ℝ := t i+(1+|eta i|)*cap i

theorem bound_pos (i : Row) : 0 < bound i := by
  unfold bound
  have ht := t_pos i
  have hU := cap_pos i
  positivity

theorem pure_bound (i : Row) (row : Source.CountRow M) (a : Fin M) (x : Box i M) :
    |SourceContinuity.purePayoff i row a (realBox i x)| ≤ bound i := by
  have h := pairPayoff_bound (eta i) (x.1:ℝ) (bids i x.2 a) a
    ((Source.lowerTemplate row).selection (kappa i) (Source.lowerBids row (bids i x.2)))
  have hb := bids_bounds i x.2 a
  rw [abs_of_nonneg x.1.property.1, abs_of_nonneg hb.1] at h
  exact h.trans (add_le_add x.1.property.2
    (mul_le_mul_of_nonneg_left hb.2 (by positivity)))

def change (i : Row) (x : Box i M) (a : Fin M) (b : Bid i) : Box i M :=
  (x.1, x.2.1, Function.update x.2.2 a b)

theorem bids_change (i : Row) (x : Box i M) (a : Fin M) (b : Bid i) :
    bids i (change i x a b).2 = Function.update (bids i x.2) a (b:ℝ) := by
  funext j
  by_cases hj : j=a
  · subst j
    simp [bids, change]
  · simp [bids, change, Function.update_of_ne hj]

theorem seedCount_zero_of_raise (i : Row) (row : Source.CountRow M) (x : Box i M)
    (a : Fin M) (b : Bid i) (hraise : bids i x.2 a ≤ (b:ℝ))
    (hzero : Source.seedCount i row (bids i x.2)=0) :
    Source.seedCount i row (bids i (change i x a b).2)=0 := by
  have hs : row.lower.filter (fun j => bids i (change i x a b).2 j ≤ t i/2) ⊆
      row.lower.filter (fun j => bids i x.2 j ≤ t i/2) := by
    intro j hj
    obtain ⟨hjl,hjb⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hjl,?_⟩
    rw [bids_change] at hjb
    by_cases hja : j=a
    · subst j
      simp only [Function.update_self] at hjb
      exact hraise.trans hjb
    · simpa only [Function.update_of_ne hja] using hjb
  have hc : Source.seedCount i row (bids i (change i x a b).2) ≤
      Source.seedCount i row (bids i x.2) := Finset.card_le_card hs
  rw [hzero] at hc
  exact Nat.eq_zero_of_le_zero hc

theorem seed_lost_own_low (i : Row) (row : Source.CountRow M) (x : Box i M)
    (a : Fin M) (b : Bid i) (hseed : Source.seedCount i row (bids i x.2) ≠ 0)
    (hzero : Source.seedCount i row (bids i (change i x a b).2)=0) : bids i x.2 a ≤ t i/2 := by
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hseed)
  obtain ⟨hjl,hjb⟩ := Finset.mem_filter.mp hj
  by_cases hja : j=a
  · simpa only [hja] using hjb
  · have hjnew : j ∈ row.lower.filter (fun j => bids i (change i x a b).2 j ≤ t i/2) := by
      apply Finset.mem_filter.mpr
      refine ⟨hjl,?_⟩
      simpa only [bids_change, Function.update_of_ne hja] using hjb
    have hp := Finset.card_pos.mpr ⟨j,hjnew⟩
    change 0 < Source.seedCount i row (bids i (change i x a b).2) at hp
    rw [hzero] at hp
    omega

private theorem weighted_decomposition [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (hne : Source.residual row 0 ≠ Source.residual row 1) (x : Box i M)
    (hs : Source.seedCount i row (bids i x.2) ≠ 0) :
    rowPayoff i x.2.1 row x.1 (bids i x.2) a =
      rawCanonicalPayoff i row a (realBox i x) +
        (1-rawWeight i row x.2)*SourceContinuity.purePayoff i row a (realBox i x) := by
  rw [rowPayoff_unequal i _ row _ _ a hne]
  simp only [Source.guardAlpha, if_neg hs]
  rfl

theorem exists_unequal_raise_modulus [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower)
    (hne : Source.residual row 0 ≠ Source.residual row 1) {err : ℝ} (herr : 0 < err) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ x : Box i M, ∀ b : Bid i,
      bids i x.2 a ≤ (b:ℝ) → (b:ℝ)-bids i x.2 a < radius →
      (1-Source.guardAlpha i x.2.1 row (bids i x.2)) *
          (SourceContinuity.purePayoff i row a (realBox i (change i x a b))-
            SourceContinuity.purePayoff i row a (realBox i x))-err ≤
        rowPayoff i x.2.1 row x.1 (bids i (change i x a b).2) a-
          rowPayoff i x.2.1 row x.1 (bids i x.2) a := by
  letI : MetricSpace (RestrictedLaw i) := TopologicalSpace.metrizableSpaceMetric (RestrictedLaw i)
  letI : MetricSpace (State i M) :=
    inferInstanceAs (MetricSpace (RestrictedLaw i × (Fin M→Bid i)))
  let B := bound i
  have hB : 0 < B := bound_pos i
  have hα : Continuous (fun x : Box i M => rawWeight i row x.2) :=
    (continuous_rawWeight i row).comp continuous_snd
  have hC : Continuous (fun x : Box i M => rawCanonicalPayoff i row a (realBox i x)) :=
    (continuous_rawCanonicalPayoff i row a ha).comp (continuous_realBox i)
  obtain ⟨rα,hrα,hmodα⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hα) (err/(2*B)) (by positivity)
  obtain ⟨rC,hrC,hmodC⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hC) (err/2) (by positivity)
  let radius := min (min rα rC) (t i/200)
  have hradius : 0 < radius := lt_min (lt_min hrα hrC) (div_pos (t_pos i) (by norm_num))
  refine ⟨radius,hradius,?_⟩
  intro x b hraise hnear
  let y := change i x a b
  change (1-Source.guardAlpha i x.2.1 row (bids i x.2)) *
    (SourceContinuity.purePayoff i row a (realBox i y)-
      SourceContinuity.purePayoff i row a (realBox i x))-err ≤
    rowPayoff i y.2.1 row y.1 (bids i y.2) a-
      rowPayoff i x.2.1 row x.1 (bids i x.2) a
  have hdist : dist x y < radius := by
    have hd := Hybrid.dist_update_box_le x.2.2 a b
    have he : dist x y = dist x.2.2 (Function.update x.2.2 a b) := by
      change max (dist x.1 x.1) (max (dist x.2.1 x.2.1)
        (dist x.2.2 (Function.update x.2.2 a b))) = _
      simp only [dist_self, max_eq_right dist_nonneg]
    rw [he]
    apply hd.trans_lt
    change |bids i x.2 a-(b:ℝ)| < radius
    rwa [abs_of_nonpos (sub_nonpos.mpr hraise), neg_sub]
  have hαclose : |rawWeight i row y.2-rawWeight i row x.2| < err/(2*B) := by
    rw [abs_sub_comm]
    simpa only [Real.dist_eq] using hmodα
      (hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have hCclose : |rawCanonicalPayoff i row a (realBox i y)-
      rawCanonicalPayoff i row a (realBox i x)| < err/2 := by
    rw [abs_sub_comm]
    simpa only [Real.dist_eq] using hmodC
      (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
  have hPBx := pure_bound i row a x
  have hPBy := pure_bound i row a y
  have herror : |(rawWeight i row y.2-rawWeight i row x.2)*
      SourceContinuity.purePayoff i row a (realBox i y)| < err/2 := by
    rw [abs_mul]
    have hmul := mul_lt_mul_of_pos_right hαclose hB
    have he : err/(2*B)*B=err/2 := by field_simp [hB.ne']
    rw [he] at hmul
    exact (mul_le_mul_of_nonneg_left hPBy (abs_nonneg _)).trans_lt hmul
  by_cases hsx : Source.seedCount i row (bids i x.2)=0
  · have hsy := seedCount_zero_of_raise i row x a b hraise hsx
    have hAx : Source.guardAlpha i x.2.1 row (bids i x.2)=0 := by simp [Source.guardAlpha,hsx]
    have hAy : Source.guardAlpha i y.2.1 row (bids i y.2)=0 := by simp [Source.guardAlpha,y,hsy]
    rw [rowPayoff_unequal i _ row _ _ a hne, rowPayoff_unequal i _ row _ _ a hne,
      hAx, hAy]
    simp only [zero_mul, sub_zero, one_mul, zero_add]
    exact sub_le_self _ herr.le
  · by_cases hsy : Source.seedCount i row (bids i y.2)=0
    · have hxlow := seed_lost_own_low i row x a b hsx hsy
      have hxneigh : bids i x.2 a ≤ SeedRejection.cutoffNeighborhood i :=
        hxlow.trans (SeedRejection.cutoffNeighborhood_gt_seed i).le
      have hyneigh : bids i y.2 a ≤ SeedRejection.cutoffNeighborhood i := by
        have hsmall : (b:ℝ)-bids i x.2 a < t i/200 := hnear.trans_le (min_le_right _ _)
        rw [show bids i y.2 a=(b:ℝ) by simp [y,change,bids]]
        unfold SeedRejection.cutoffNeighborhood
        nlinarith [t_pos i]
      have hFx := SeedRejection.rowPayoff_eq_pure_near_seed i row a ha hne (realBox i x) hxneigh
      have hFy := SeedRejection.rowPayoff_eq_pure_near_seed i row a ha hne (realBox i y) hyneigh
      change rowPayoff i x.2.1 row x.1 (bids i x.2) a =
        SourceContinuity.purePayoff i row a (realBox i x) at hFx
      change rowPayoff i y.2.1 row y.1 (bids i y.2) a =
        SourceContinuity.purePayoff i row a (realBox i y) at hFy
      rw [hFx,hFy]
      have hAx : Source.guardAlpha i x.2.1 row (bids i x.2)=rawWeight i row x.2 := by
        simp [Source.guardAlpha,hsx,rawWeight]
      rw [hAx]
      by_cases hraw : rawWeight i row x.2=0
      · rw [hraw]
        simp only [sub_zero,one_mul]
        exact sub_le_self _ herr.le
      · have hrawpos := lt_of_le_of_ne (rawWeight_bounds i row x.2).1 (Ne.symm hraw)
        have hPx := SeedRejection.purePayoff_zero_near_seed i row a ha
          (realBox i x) hrawpos hxneigh
        rw [hPx,sub_zero]
        by_cases hyraw : rawWeight i row y.2=0
        · have he : |rawWeight i row x.2*SourceContinuity.purePayoff i row a (realBox i y)| < err/2 := by
            simpa only [hyraw,zero_sub,neg_mul,abs_neg] using herror
          have hlow := (abs_lt.mp he).1
          nlinarith
        · have hypos := lt_of_le_of_ne (rawWeight_bounds i row y.2).1 (Ne.symm hyraw)
          rw [SeedRejection.purePayoff_zero_near_seed i row a ha (realBox i y) hypos hyneigh]
          simp only [mul_zero,zero_sub]
          linarith
    · have hAx : Source.guardAlpha i x.2.1 row (bids i x.2)=rawWeight i row x.2 := by
        simp [Source.guardAlpha,hsx,rawWeight]
      rw [weighted_decomposition i row a hne x hsx,
        weighted_decomposition i row a hne y hsy,hAx]
      have hClow := (abs_lt.mp hCclose).1
      have hEhigh := (abs_lt.mp herror).2
      nlinarith

theorem exists_all_unequal_raise_modulus [NeZero M] (i : Row) {err : ℝ} (herr : 0 < err) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (row : Source.CountRow M) (a : Fin M),
      a ∈ row.lower → Source.residual row 0 ≠ Source.residual row 1 →
      ∀ x : Box i M, ∀ b : Bid i,
        bids i x.2 a ≤ (b:ℝ) → (b:ℝ)-bids i x.2 a < radius →
        (1-Source.guardAlpha i x.2.1 row (bids i x.2)) *
            (SourceContinuity.purePayoff i row a (realBox i (change i x a b))-
              SourceContinuity.purePayoff i row a (realBox i x))-err ≤
          rowPayoff i x.2.1 row x.1 (bids i (change i x a b).2) a-
            rowPayoff i x.2.1 row x.1 (bids i x.2) a := by
  have hlocal (j : Source.CountRow M × Fin M) :
      ∃ radius : ℝ, 0 < radius ∧ ∀ ha : j.2 ∈ j.1.lower,
        ∀ hne : Source.residual j.1 0 ≠ Source.residual j.1 1,
        ∀ x : Box i M, ∀ b : Bid i,
          bids i x.2 j.2 ≤ (b:ℝ) → (b:ℝ)-bids i x.2 j.2 < radius →
          (1-Source.guardAlpha i x.2.1 j.1 (bids i x.2)) *
              (SourceContinuity.purePayoff i j.1 j.2 (realBox i (change i x j.2 b))-
                SourceContinuity.purePayoff i j.1 j.2 (realBox i x))-err ≤
            rowPayoff i x.2.1 j.1 x.1 (bids i (change i x j.2 b).2) j.2-
              rowPayoff i x.2.1 j.1 x.1 (bids i x.2) j.2 := by
    by_cases ha : j.2 ∈ j.1.lower
    · by_cases hne : Source.residual j.1 0 ≠ Source.residual j.1 1
      · obtain ⟨r,hr,h⟩ := exists_unequal_raise_modulus i j.1 j.2 ha hne herr
        exact ⟨r,hr,fun _ _ => h⟩
      · exact ⟨1,by norm_num,fun _ h => False.elim (hne h)⟩
    · exact ⟨1,by norm_num,fun h => False.elim (ha h)⟩
  choose r hr hspec using hlocal
  let radius := Finset.univ.inf' Finset.univ_nonempty r
  have hrad : 0 < radius := (Finset.lt_inf'_iff _).mpr (fun j _ => hr j)
  refine ⟨radius,hrad,?_⟩
  intro row a ha hne x b hraise hnear
  exact hspec (row,a) ha hne x b hraise
    (hnear.trans_le (Finset.inf'_le r (Finset.mem_univ (row,a))))

abbrev PositiveBox (i : Row) (M : ℕ) (a : Fin M) (L : ℝ) :=
  {x : Box i M // L ≤ bids i x.2 a}

theorem continuous_positive_equalPayoff [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) (heq : Source.residual row 0=Source.residual row 1)
    {L : ℝ} (hL : 0 < L) :
    Continuous (fun x : PositiveBox i M a L =>
      rowPayoff i x.1.2.1 row x.1.1 (bids i x.1.2) a) := by
  have he (x : PositiveBox i M a L) :
      rowPayoff i x.1.2.1 row x.1.1 (bids i x.1.2) a =
        ((x.1.1:ℝ)-bids i x.1.2 a)*
          (2*equalMarginal i row a x.1.2-(equalMarginal i row a x.1.2)^2)-
          eta i*bids i x.1.2 a*(equalMarginal i row a x.1.2)^2 := by
    rw [rowPayoff, continuation_equal i _ row _ heq]
    exact equalPayoff_eq i row a (realBox i x.1)
  simp_rw [he]
  rw [continuous_iff_continuousAt]
  intro x
  have hp := (continuousAt_equalMarginal i row a ha x.1.2 (hL.trans_le x.2)).comp
    (x := x) (continuous_subtype_val.snd.continuousAt)
  have hv : ContinuousAt (fun y : PositiveBox i M a L => (y.1.1:ℝ)) x := by fun_prop
  have hb : ContinuousAt (fun y : PositiveBox i M a L => bids i y.1.2 a) x :=
    ((continuous_apply a).comp ((continuous_bids i).comp continuous_subtype_val.snd)).continuousAt
  exact ((hv.sub hb).mul ((continuousAt_const.mul hp).sub (hp.pow 2))).sub
    ((continuousAt_const.mul hb).mul (hp.pow 2))

theorem exists_equal_raise_modulus [NeZero M] (i : Row) (row : Source.CountRow M)
    (a : Fin M) (ha : a ∈ row.lower) (heq : Source.residual row 0=Source.residual row 1)
    {L err : ℝ} (hL : 0 < L) (herr : 0 < err) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ x : Box i M, ∀ b : Bid i,
      L ≤ bids i x.2 a → bids i x.2 a ≤ (b:ℝ) → (b:ℝ)-bids i x.2 a < radius →
      -err ≤ rowPayoff i x.2.1 row x.1 (bids i (change i x a b).2) a-
        rowPayoff i x.2.1 row x.1 (bids i x.2) a := by
  letI : MetricSpace (RestrictedLaw i) := TopologicalSpace.metrizableSpaceMetric (RestrictedLaw i)
  letI : MetricSpace (State i M) :=
    inferInstanceAs (MetricSpace (RestrictedLaw i × (Fin M→Bid i)))
  have hclosed : IsClosed {x : Box i M | L ≤ bids i x.2 a} :=
    isClosed_le continuous_const ((continuous_apply a).comp ((continuous_bids i).comp continuous_snd))
  letI : CompactSpace (PositiveBox i M a L) := isCompact_iff_compactSpace.mp hclosed.isCompact
  obtain ⟨radius,hradius,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous
      (continuous_positive_equalPayoff i row a ha heq hL)) err herr
  refine ⟨radius,hradius,?_⟩
  intro x b hx hraise hnear
  let x' : PositiveBox i M a L := ⟨x,hx⟩
  let y' : PositiveBox i M a L :=
    ⟨change i x a b,by simpa [change,bids] using hx.trans hraise⟩
  have hd : dist x' y' < radius := by
    rw [Subtype.dist_eq]
    have he : dist x (change i x a b)=dist x.2.2 (Function.update x.2.2 a b) := by
      change max (dist x.1 x.1) (max (dist x.2.1 x.2.1)
        (dist x.2.2 (Function.update x.2.2 a b))) = _
      simp only [dist_self, max_eq_right dist_nonneg]
    rw [he]
    apply (Hybrid.dist_update_box_le x.2.2 a b).trans_lt
    change |bids i x.2 a-(b:ℝ)| < radius
    rwa [abs_of_nonpos (sub_nonpos.mpr hraise), neg_sub]
  have hh := hmod hd
  rw [Real.dist_eq, abs_sub_comm] at hh
  exact (abs_lt.mp hh).1.le

end OwnBid
end FCAppendix.Affine.UniformFinite
