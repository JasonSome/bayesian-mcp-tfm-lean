import FCAppendix.Affine.Uniform05CategoryGuards
import FCAppendix.Affine.UniformFinite.GuardMixture
import FCAppendix.Affine.LowBody.PureTemplate

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Source
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Uniform05

structure CountRow (M : ℕ) where
  lower : Finset (Fin M)
  upper0 : ℕ
  upper1 : ℕ
  partition : lower.card + upper0 + upper1 = M

def countRowOfKind {M : ℕ} (kind : Fin M → Fin 3) : CountRow M where
  lower := Finset.univ.filter (fun a => kind a = 0)
  upper0 := (Finset.univ.filter (fun a => kind a = 1)).card
  upper1 := (Finset.univ.filter (fun a => kind a = 2)).card
  partition := by
    classical
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc
      (∑ a : Fin M, ((if kind a = 0 then 1 else 0) +
          (if kind a = 1 then 1 else 0) + (if kind a = 2 then 1 else 0) : ℕ))
        = ∑ _a : Fin M, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          generalize h : kind a = k
          fin_cases k <;> simp
      _ = M := by simp

def upperCount {M : ℕ} (row : CountRow M) (j : Fin 2) : ℕ :=
  if j = 0 then row.upper0 else row.upper1

def residual {M : ℕ} (row : CountRow M) (j : Fin 2) : ℕ :=
  min row.lower.card (Uniform07.capacity M - upperCount row j)

def small {M : ℕ} (row : CountRow M) : ℕ := min (residual row 0) (residual row 1)
def large {M : ℕ} (row : CountRow M) : ℕ := max (residual row 0) (residual row 1)
def imbalance {M : ℕ} (row : CountRow M) : ℕ := large row - small row
def totalResidual {M : ℕ} (row : CountRow M) : ℕ := residual row 0 + residual row 1

@[simp] theorem small_add_imbalance {M : ℕ} (row : CountRow M) :
    small row + imbalance row = large row := by
  dsimp [small, large, imbalance]
  omega

theorem residual_le_lower {M : ℕ} (row : CountRow M) (j : Fin 2) :
    residual row j ≤ row.lower.card := Nat.min_le_left _ _

theorem totalResidual_eq {M : ℕ} (row : CountRow M) :
    totalResidual row = 2 * small row + imbalance row := by
  dsimp [totalResidual, imbalance, large, small]
  omega

def lowerTemplate {M : ℕ} (row : CountRow M) : LowBody.PureTemplate (Fin M) where
  support := row.lower
  residual₀ := residual row 0
  residual₁ := residual row 1

def lowerBids {M : ℕ} (row : CountRow M) (b : Fin M → ℝ) : Fin M → ℝ :=
  fun a => if a ∈ row.lower then b a else 0

@[simp] theorem lowerBids_of_mem {M : ℕ} (row : CountRow M) (b : Fin M → ℝ)
    {a : Fin M} (ha : a ∈ row.lower) : lowerBids row b a = b a := by
  simp [lowerBids, ha]

@[simp] theorem lowerBids_of_not_mem {M : ℕ} (row : CountRow M) (b : Fin M → ℝ)
    {a : Fin M} (ha : a ∉ row.lower) : lowerBids row b a = 0 := by
  simp [lowerBids, ha]

def sourceWeights {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : WeightedSampling.Weights (Fin M) :=
  ⟨fun a => if a ∈ row.lower then lawWeight i G (b a) else 0, by
    intro a
    change (if a ∈ row.lower then lawWeight i G (b a) else 0) ∈ Icc (0 : ℝ) 1
    by_cases ha : a ∈ row.lower
    · rw [if_pos ha]
      exact ⟨(lawWeight_range i G (b a)).1,(lawWeight_range i G (b a)).2⟩
    · simp [ha]⟩

theorem sourceWeights_pos_lower {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) {a : Fin M}
    (ha : 0 < (sourceWeights i G row b).1 a) : a ∈ row.lower := by
  by_contra hn
  simp [sourceWeights, hn] at ha

def rootLo (i : Row) (G : RestrictedLaw i) : ℝ := G.multiplier - guardRadius i
def rootHi (i : Row) (G : RestrictedLaw i) : ℝ := G.multiplier + guardRadius i

theorem rootBounds (i : Row) (G : RestrictedLaw i) :
    0 < rootLo i G ∧ rootLo i G < rootHi i G ∧
      (1 - xi i) * cap i ≤ rootLo i G := by
  have h := shifted_multiplier_guards i G
  have h0 := (rejectionLo_pos i).trans ((le_max_right _ _).trans_lt h)
  have ha := guardRadius_pos i
  refine ⟨h0, ?_, ?_⟩
  · dsimp [rootLo, rootHi]
    linarith
  · simpa only [rootLo, kappa] using ((le_max_left _ _).trans_lt h).le

def meanResidual (i : Row) : ℝ := t i * requiredDemand i
def demandMargin (i : Row) : ℝ := t i * lawDemandSlack i
def weightMargin (i : Row) : ℝ := t i * (requiredDemand i / (2 - requiredDemand i))

def commonGuardMargin (i : Row) : ℝ :=
  min (demandMargin i) (min (weightMargin i) (meanResidual i)) / 100

theorem meanResidual_pos (i : Row) : 0 < meanResidual i :=
  mul_pos (t_pos i) (requiredDemand_range i).1

theorem demandMargin_pos (i : Row) : 0 < demandMargin i :=
  mul_pos (t_pos i) (lawDemandSlack_pos i)

theorem weightMargin_pos (i : Row) : 0 < weightMargin i := by
  have hr := requiredDemand_range i
  exact mul_pos (t_pos i) (div_pos hr.1 (by linarith))

theorem common_guard_margin (i : Row) : 0 < commonGuardMargin i := by
  exact div_pos (lt_min (demandMargin_pos i)
    (lt_min (weightMargin_pos i) (meanResidual_pos i))) (by norm_num)

theorem commonGuardMargin_bounds (i : Row) :
    100 * commonGuardMargin i ≤ demandMargin i ∧
    100 * commonGuardMargin i ≤ weightMargin i ∧
    100 * commonGuardMargin i ≤ meanResidual i := by
  have hd := min_le_left (demandMargin i) (min (weightMargin i) (meanResidual i))
  have hw := (min_le_right (demandMargin i)
    (min (weightMargin i) (meanResidual i))).trans (min_le_left _ _)
  have hr := (min_le_right (demandMargin i)
    (min (weightMargin i) (meanResidual i))).trans (min_le_right _ _)
  dsimp [commonGuardMargin]
  constructor
  · linarith
  constructor <;> linarith

theorem count_margin (i : Row) : commonGuardMargin i < t i / 200 := by
  have he := commonGuardMargin_bounds i
  have hr := mul_lt_mul_of_pos_left (requiredDemand_range i).2 (t_pos i)
  dsimp [meanResidual] at he
  linarith

def lowDemand {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  ∑ a, exposure (xi i) (rootLo i G) (lowerBids row b a)

def highDemand {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  ∑ a, exposure (xi i) (rootHi i G) (lowerBids row b a)

def rejectionSum {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  ∑ a, rejectionExposure (rejectionScale i) G.rejectionRoot (lowerBids row b a)

def seedCount {M : ℕ} (i : Row) (row : CountRow M) (b : Fin M → ℝ) : ℕ :=
  (row.lower.filter (fun a => b a ≤ t i / 2)).card

def sourceSlacks {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : Fin 7 → ℝ :=
  ![(lowDemand i G row b - (small row : ℝ) - imbalance row) / M,
    ((small row : ℝ) - highDemand i G row b) / M,
    (WeightedSampling.totalWeight (sourceWeights i G row b) - imbalance row) / M,
    (rejectionSum i G row b - totalResidual row) / M,
    10 * commonGuardMargin i - |(row.lower.card : ℝ) / M - t i|,
    10 * commonGuardMargin i - |(row.upper0 : ℝ) / M - (1 - t i) / 2|,
    10 * commonGuardMargin i - |(row.upper1 : ℝ) / M - (1 - t i) / 2|]

def rawAlpha {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  Literal.guardWeight (commonGuardMargin i) (2 * commonGuardMargin i)
    (sourceSlacks i G row b)

def guardAlpha {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  if seedCount i row b = 0 then 0 else rawAlpha i G row b

theorem continuous_rootLo (i : Row) : Continuous (rootLo i) :=
  RestrictedLaw.continuous_multiplier.sub continuous_const

theorem continuous_rootHi (i : Row) : Continuous (rootHi i) :=
  RestrictedLaw.continuous_multiplier.add continuous_const

private theorem continuous_moving_exposure (i : Row) (z : RestrictedLaw i → ℝ)
    (hz : Continuous z) (hz0 : ∀ G, 0 < z G) :
    Continuous (fun p : RestrictedLaw i × ℝ => exposure (xi i) (z p.1) p.2) := by
  unfold ClippedResidual.exposure
  apply continuous_const.min
  exact (continuous_const.max (continuous_snd.sub (hz.comp continuous_fst))).div
    (continuous_const.mul (continuous_snd.max (hz.comp continuous_fst))) (fun p => by
      exact ne_of_gt (mul_pos (xi_range i).1
        ((hz0 p.1).trans_le (le_max_right _ _))))

theorem continuous_sourceSlacks {M : ℕ} (i : Row) (row : CountRow M) :
    Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) => sourceSlacks i p.1 row p.2) := by
  classical
  have hb (a : Fin M) : Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) =>
      lowerBids row p.2 a) := by
    by_cases ha : a ∈ row.lower
    · simp only [lowerBids, if_pos ha]
      exact (continuous_apply a).comp continuous_snd
    · simp only [lowerBids, if_neg ha]
      exact continuous_const
  have hlo : Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) =>
      lowDemand i p.1 row p.2) := by
    apply continuous_finsetSum
    intro a _
    exact (continuous_moving_exposure i (rootLo i) (continuous_rootLo i)
      (fun G => (rootBounds i G).1)).comp (continuous_fst.prodMk (hb a))
  have hhi : Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) =>
      highDemand i p.1 row p.2) := by
    apply continuous_finsetSum
    intro a _
    exact (continuous_moving_exposure i (rootHi i) (continuous_rootHi i)
      (fun G => (rootBounds i G).1.trans (rootBounds i G).2.1)).comp
        (continuous_fst.prodMk (hb a))
  have hw : Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) =>
      WeightedSampling.totalWeight (sourceWeights i p.1 row p.2)) := by
    apply continuous_finsetSum
    intro a _
    by_cases ha : a ∈ row.lower
    · simp only [sourceWeights, if_pos ha]
      exact (continuous_lawWeight i).comp
        (continuous_fst.prodMk ((continuous_apply a).comp continuous_snd))
    · simp only [sourceWeights, if_neg ha]
      exact continuous_const
  have hz : Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) =>
      rejectionSum i p.1 row p.2) := by
    apply continuous_finsetSum
    intro a _
    exact (continuous_rejection_statistic i).comp (continuous_fst.prodMk (hb a))
  apply continuous_pi
  intro k
  fin_cases k
  · exact ((hlo.sub continuous_const).sub continuous_const).div_const _
  · exact (continuous_const.sub hhi).div_const _
  · exact (hw.sub continuous_const).div_const _
  · exact (hz.sub continuous_const).div_const _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem continuous_rawAlpha {M : ℕ} (i : Row) (row : CountRow M) :
    Continuous (fun p : RestrictedLaw i × (Fin M → ℝ) => rawAlpha i p.1 row p.2) :=
  (Literal.continuous_guardWeight _ _).comp (continuous_sourceSlacks i row)

theorem guardAlpha_bounds {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) :
    0 ≤ guardAlpha i G row b ∧ guardAlpha i G row b ≤ 1 := by
  unfold guardAlpha
  split
  · constructor <;> norm_num
  · exact Literal.guardWeight_bounds _ _ _

theorem guardAlpha_pos_slacks {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (ha : 0 < guardAlpha i G row b) :
    0 < seedCount i row b ∧ ∀ k, commonGuardMargin i < sourceSlacks i G row b k := by
  have he := common_guard_margin i
  have hs : seedCount i row b ≠ 0 := by
    intro hs
    simp [guardAlpha, hs] at ha
  refine ⟨Nat.pos_of_ne_zero hs, ?_⟩
  apply Literal.guardWeight_pos_outer
    (outer := commonGuardMargin i) (inner := 2 * commonGuardMargin i) (by linarith) _
  simpa [guardAlpha, rawAlpha, hs] using ha

theorem guardAlpha_one {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (hseed : 0 < seedCount i row b)
    (hinner : ∀ k, 2 * commonGuardMargin i ≤ sourceSlacks i G row b k) :
    guardAlpha i G row b = 1 := by
  have he := common_guard_margin i
  rw [guardAlpha, if_neg (Nat.ne_of_gt hseed)]
  exact Literal.guardWeight_one (by linarith) _ hinner

theorem rawAlpha_pos_slacks {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (ha : 0 < rawAlpha i G row b) :
    ∀ k, commonGuardMargin i < sourceSlacks i G row b k :=
  Literal.guardWeight_pos_outer (by linarith [common_guard_margin i]) _ ha

theorem rawAlpha_pos {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (hM : 0 < M)
    (hb : ∀ a ∈ row.lower, b a ≤ cap i) (ha : 0 < rawAlpha i G row b) :
    Literal.WeightedGuard (xi i) (cap i) (rootLo i G) (rootHi i G)
      (commonGuardMargin i * M) (lowerBids row b) (sourceWeights i G row b)
      (small row) (imbalance row) ∧
      0 < small row ∧ 0 < commonGuardMargin i * M := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have he := common_guard_margin i
  have hsl := rawAlpha_pos_slacks i G row b ha
  have hlo := hsl 0
  have hhi := hsl 1
  have hw := hsl 2
  norm_num [sourceSlacks] at hlo hhi hw
  have hlo' := (lt_div_iff₀ hMr).mp hlo
  have hhi' := (lt_div_iff₀ hMr).mp hhi
  have hw' := (lt_div_iff₀ hMr).mp hw
  have hroots := rootBounds i G
  have hnonneg : 0 ≤ highDemand i G row b :=
    Finset.sum_nonneg (fun a _ => exposure_nonneg (xi_range i).1
      (hroots.1.trans hroots.2.1))
  have hdreal : 0 < (small row : ℝ) := by linarith [mul_pos he hMr]
  have hd : 0 < small row := by exact_mod_cast hdreal
  refine ⟨?_, hd, mul_pos he hMr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ row.lower
    · simpa [lowerBids, ha] using hb a ha
    · simpa [lowerBids, ha] using (cap_pos i).le
  · change (small row : ℝ) + imbalance row + commonGuardMargin i * M <
      lowDemand i G row b
    linarith
  · change highDemand i G row b < (small row : ℝ) - commonGuardMargin i * M
    linarith
  · linarith
  · intro a haw
    have hal := sourceWeights_pos_lower i G row b haw
    have hap : 0 < lawWeight i G (b a) := by
      simpa [sourceWeights, hal] using haw
    have he := positive_weight_eligibility i G (hb a hal) hap
    rw [lowerBids_of_mem row b hal]
    dsimp [rootHi]
    linarith [guardRadius_pos i]

theorem guardAlpha_pos {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (hM : 0 < M)
    (hb : ∀ a ∈ row.lower, b a ≤ cap i) (ha : 0 < guardAlpha i G row b) :
    Literal.WeightedGuard (xi i) (cap i) (rootLo i G) (rootHi i G)
      (commonGuardMargin i * M) (lowerBids row b) (sourceWeights i G row b)
      (small row) (imbalance row) ∧
      0 < small row ∧ 0 < commonGuardMargin i * M := by
  apply rawAlpha_pos i G row b hM hb
  have hs := (guardAlpha_pos_slacks i G row b ha).1
  simpa [guardAlpha, Nat.ne_of_gt hs] using ha

theorem guarded_weighted_path_root {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (hb : ∀ a ∈ row.lower, b a ≤ cap i) (ha : 0 < guardAlpha i G row b)
    (p : WeightedSampling.Path (Fin M) (imbalance row))
    (hp : 0 < (WeightedSampling.pathLaw (sourceWeights i G row b)
      (imbalance row) ∅).mass p) :
    (WeightedSampling.finalSet (imbalance row) ∅ p).card = imbalance row ∧
      Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b)
        (WeightedSampling.finalSet (imbalance row) ∅ p) (small row) ∈
          Icc (rootLo i G) (rootHi i G) ∧
      ClippedResidual.remainingDemand (xi i) (lowerBids row b)
        (WeightedSampling.finalSet (imbalance row) ∅ p)
        (Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b)
          (WeightedSampling.finalSet (imbalance row) ∅ p) (small row)) = (small row : ℝ) ∧
      ∀ a ∈ WeightedSampling.finalSet (imbalance row) ∅ p, rootHi i G ≤ lowerBids row b a := by
  have hg := guardAlpha_pos i G row b (Nat.pos_of_ne_zero (NeZero.ne M)) hb ha
  have hr := rootBounds i G
  exact Literal.weighted_path_root (lowerBids row b) (sourceWeights i G row b)
    (small row) (imbalance row) (xi_range i).1 (xi_range i).2 (cap_pos i)
    hr.1 hr.2.1 hr.2.2 hg.2.1 hg.2.2 hg.1 p hp

theorem guarded_rejection_count {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (hM : 0 < M)
    (ha : 0 < guardAlpha i G row b) :
    (totalResidual row : ℝ) + commonGuardMargin i * M <
      ((Finset.univ.filter (fun a => G.rejectionRoot < lowerBids row b a)).card : ℝ) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have h := (guardAlpha_pos_slacks i G row b ha).2 3
  norm_num only [sourceSlacks, Matrix.cons_val_succ, Matrix.cons_val_zero] at h
  have hh := (lt_div_iff₀ hMr).mp h
  have hc := Literal.rejection_count (rejectionScale_pos i) (lowerBids row b)
    (z := G.rejectionRoot)
  change rejectionSum i G row b ≤ _ at hc
  linarith

theorem residual_fraction_control {M : ℕ} (i : Row) (row : CountRow M)
    (hM : 0 < M)
    (hc : |(Uniform07.capacity M : ℝ) / M - rho| ≤ commonGuardMargin i)
    (hN : |(row.lower.card : ℝ) / M - t i| ≤ commonGuardMargin i)
    (j : Fin 2)
    (hH : |(upperCount row j : ℝ) / M - (1-t i)/2| ≤ commonGuardMargin i) :
    residual row j = Uniform07.capacity M - upperCount row j ∧
      |(residual row j : ℝ)/M - meanResidual i| ≤ 2*commonGuardMargin i := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have he := common_guard_margin i
  have heb := (commonGuardMargin_bounds i).2.2
  have heT := count_margin i
  have hq : meanResidual i < t i / 2 := by
    have h := mul_lt_mul_of_pos_left (requiredDemand_range i).2 (t_pos i)
    simpa [meanResidual, div_eq_mul_inv] using h
  have hmean : rho-(1-t i)/2 = meanResidual i := residual_mean_identity i
  obtain ⟨hcL, hcR⟩ := abs_le.mp hc
  obtain ⟨hnL, hnR⟩ := abs_le.mp hN
  obtain ⟨hhL, hhR⟩ := abs_le.mp hH
  have hClo : (rho-commonGuardMargin i)*M ≤ (Uniform07.capacity M : ℝ) :=
    (le_div_iff₀ hMr).mp (by linarith)
  have hChi : (Uniform07.capacity M : ℝ) ≤ (rho+commonGuardMargin i)*M :=
    (div_le_iff₀ hMr).mp (by linarith)
  have hHlo : ((1-t i)/2-commonGuardMargin i)*M ≤ (upperCount row j : ℝ) :=
    (le_div_iff₀ hMr).mp (by linarith)
  have hHhi : (upperCount row j : ℝ) ≤ ((1-t i)/2+commonGuardMargin i)*M :=
    (div_le_iff₀ hMr).mp (by linarith)
  have hNlo : (t i-commonGuardMargin i)*M ≤ (row.lower.card : ℝ) :=
    (le_div_iff₀ hMr).mp (by linarith)
  have hpos : 0 < meanResidual i-2*commonGuardMargin i := by linarith
  have hless : (upperCount row j : ℝ) < Uniform07.capacity M := by
    have hp := mul_pos hpos hMr
    nlinarith
  have hHc : upperCount row j ≤ Uniform07.capacity M := by
    exact_mod_cast hless.le
  have hgap : meanResidual i+3*commonGuardMargin i < t i := by linarith
  have hCsubN : (Uniform07.capacity M : ℝ) - upperCount row j ≤ row.lower.card := by
    have hp := mul_pos (sub_pos.mpr hgap) hMr
    nlinarith
  have hnat : Uniform07.capacity M - upperCount row j ≤ row.lower.card := by
    exact_mod_cast (show ((Uniform07.capacity M - upperCount row j : ℕ) : ℝ) ≤
      row.lower.card by simpa only [Nat.cast_sub hHc] using hCsubN)
  have heq : residual row j = Uniform07.capacity M - upperCount row j :=
    Nat.min_eq_right hnat
  refine ⟨heq, ?_⟩
  rw [heq, Nat.cast_sub hHc, sub_div]
  apply abs_le.mpr
  constructor <;> linarith

theorem count_control {M : ℕ} (i : Row) (row : CountRow M) (hM : 0 < M)
    (hc : |(Uniform07.capacity M : ℝ) / M - rho| ≤ commonGuardMargin i)
    (hN : |(row.lower.card : ℝ) / M - t i| ≤ commonGuardMargin i)
    (hH0 : |(row.upper0 : ℝ) / M - (1-t i)/2| ≤ commonGuardMargin i)
    (hH1 : |(row.upper1 : ℝ) / M - (1-t i)/2| ≤ commonGuardMargin i) :
    meanResidual i-2*commonGuardMargin i ≤ (small row : ℝ)/M ∧
    (large row : ℝ)/M ≤ meanResidual i+2*commonGuardMargin i ∧
    (imbalance row : ℝ)/M ≤ 4*commonGuardMargin i ∧
    (totalResidual row : ℝ)/M ≤ 2*meanResidual i+4*commonGuardMargin i := by
  have h0 := (residual_fraction_control i row hM hc hN 0
    (by simpa [upperCount] using hH0)).2
  have h1 := (residual_fraction_control i row hM hc hN 1
    (by simpa [upperCount] using hH1)).2
  obtain ⟨h0L,h0R⟩ := abs_le.mp h0
  obtain ⟨h1L,h1R⟩ := abs_le.mp h1
  have hs : meanResidual i-2*commonGuardMargin i ≤ (small row : ℝ)/M := by
    by_cases h : residual row 0 ≤ residual row 1
    · rw [small, Nat.min_eq_left h]
      linarith
    · rw [small, Nat.min_eq_right (le_of_not_ge h)]
      linarith
  have hl : (large row : ℝ)/M ≤ meanResidual i+2*commonGuardMargin i := by
    by_cases h : residual row 0 ≤ residual row 1
    · rw [large, Nat.max_eq_right h]
      linarith
    · rw [large, Nat.max_eq_left (le_of_not_ge h)]
      linarith
  have hd : (imbalance row : ℝ)/M ≤ 4*commonGuardMargin i := by
    have hsl : small row ≤ large row := by unfold small large; omega
    rw [imbalance, Nat.cast_sub hsl, sub_div]
    linarith
  refine ⟨hs, hl, hd, ?_⟩
  rw [totalResidual, Nat.cast_add, add_div]
  linarith

theorem empirical_control_guardAlpha_one {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) (hM : 0 < M)
    (hc : |(Uniform07.capacity M : ℝ)/M-rho| ≤ commonGuardMargin i)
    (hN : |(row.lower.card : ℝ)/M-t i| ≤ commonGuardMargin i)
    (hH0 : |(row.upper0 : ℝ)/M-(1-t i)/2| ≤ commonGuardMargin i)
    (hH1 : |(row.upper1 : ℝ)/M-(1-t i)/2| ≤ commonGuardMargin i)
    (hlo : |lowDemand i G row b/M-
      t i*lawDemand i G.bidLaw (rootLo i G)| ≤ commonGuardMargin i)
    (hhi : |highDemand i G row b/M-
      t i*lawDemand i G.bidLaw (rootHi i G)| ≤ commonGuardMargin i)
    (hw : |WeightedSampling.totalWeight (sourceWeights i G row b)/M-
      t i*(∫ x : Bid i, lawWeight i G x ∂(G.bidLaw : Measure (Bid i)))| ≤
        commonGuardMargin i)
    (hz : |rejectionSum i G row b/M-3*meanResidual i| ≤ commonGuardMargin i)
    (hseed : 0 < seedCount i row b) : guardAlpha i G row b = 1 := by
  have he := common_guard_margin i
  have heb := commonGuardMargin_bounds i
  have hcount := count_control i row hM hc hN hH0 hH1
  have hD := shifted_lawDemand_slack i G
  have hDlo := mul_le_mul_of_nonneg_left hD.1 (t_pos i).le
  have hDhi := mul_le_mul_of_nonneg_left hD.2 (t_pos i).le
  have hW := mul_le_mul_of_nonneg_left (mean_lawWeight_lower i G) (t_pos i).le
  have hDlo' : meanResidual i+demandMargin i ≤
      t i*lawDemand i G.bidLaw (rootLo i G) := by
    simpa only [meanResidual, demandMargin, rootLo, mul_add] using hDlo
  have hDhi' : t i*lawDemand i G.bidLaw (rootHi i G) ≤
      meanResidual i-demandMargin i := by
    simpa only [meanResidual, demandMargin, rootHi, mul_sub] using hDhi
  change weightMargin i ≤ _ at hW
  obtain ⟨hloL,hloR⟩ := abs_le.mp hlo
  obtain ⟨hhiL,hhiR⟩ := abs_le.mp hhi
  obtain ⟨hwL,hwR⟩ := abs_le.mp hw
  obtain ⟨hzL,hzR⟩ := abs_le.mp hz
  apply guardAlpha_one i G row b hseed
  intro k
  fin_cases k
  · norm_num [sourceSlacks]
    have hsum : ((small row : ℝ)+imbalance row)/M = (large row : ℝ)/M := by
      rw [← Nat.cast_add, small_add_imbalance]
    rw [show lowDemand i G row b-(small row:ℝ)-imbalance row =
        lowDemand i G row b-((small row:ℝ)+imbalance row) by ring, sub_div, hsum]
    linarith
  · norm_num [sourceSlacks, sub_div]
    linarith
  · norm_num [sourceSlacks, sub_div]
    linarith
  · norm_num [sourceSlacks, sub_div]
    linarith
  · norm_num [sourceSlacks]
    linarith
  · norm_num [sourceSlacks]
    linarith
  · norm_num [sourceSlacks]
    linarith

end FCAppendix.Affine.UniformFinite.Source
