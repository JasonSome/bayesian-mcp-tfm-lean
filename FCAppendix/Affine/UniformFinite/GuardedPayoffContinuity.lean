import FCAppendix.Affine.UniformFinite.WeightedContinuation

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory Filter Topology
open scoped BigOperators

namespace Literal
open ClippedResidual
open WeightedSampling (Weights Path pathLaw finalSet totalWeight)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem finalSet_card_le (n : ℕ) (S : Finset ι) (p : Path ι n) :
    (finalSet n S p).card ≤ S.card + n := by
  induction n generalizing S with
  | zero => simp [finalSet]
  | succ n ih =>
    have h := ih (insert p.1 S) p.2
    have hc := Finset.card_insert_le p.1 S
    dsimp only [finalSet]
    omega

theorem root_eq_clearing {ξ U lo hi slack : ℝ} {d : ℕ} (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (b : GuardedBids ξ U lo hi slack d E) :
    root ξ lo hi b.1 E d = clearing E hξ hξ1 hU hlo hlh hg hd hs b := by
  obtain ⟨z, hz, huniq⟩ := exists_unique_balanced_root b.1 E hξ hξ1 hU hlo hlh hg
    b.2.1 (by exact_mod_cast hd) hs b.2.2.1 b.2.2.2
  have hr := root_spec b.1 E d hξ hξ1 hU hlo hlh hg b.2.1 hd hs b.2.2.1 b.2.2.2
  have hc := clearing_spec E hξ hξ1 hU hlo hlh hg hd hs b
  exact (huniq _ hr).trans (huniq _ hc).symm

theorem continuous_root_guarded {ξ U lo hi slack : ℝ} {d : ℕ} (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack) :
    Continuous (fun b : GuardedBids ξ U lo hi slack d E => root ξ lo hi b.1 E d) := by
  have he : (fun b : GuardedBids ξ U lo hi slack d E => root ξ lo hi b.1 E d) =
      clearing E hξ hξ1 hU hlo hlh hg hd hs :=
    funext (root_eq_clearing E hξ hξ1 hU hlo hlh hg hd hs)
  rw [he]
  exact continuous_clearing E hξ hξ1 hU hlo hlh hg hd hs

abbrev GuardedState (ξ U lo hi slack : ℝ) (d Δ : ℕ) :=
  {x : (ι → ℝ) × Weights ι //
    (∀ i, x.1 i ≤ U) ∧
    (d : ℝ) + Δ + slack < ∑ i, exposure ξ lo (x.1 i) ∧
    (∑ i, exposure ξ hi (x.1 i)) < (d : ℝ) - slack ∧
    (Δ : ℝ) + slack < totalWeight x.2}

def pathBids {ξ U lo hi slack : ℝ} {d Δ : ℕ} (p : Path ι Δ)
    (x : GuardedState (ι := ι) ξ U lo hi slack d Δ) :
    GuardedBids ξ U lo hi slack d (finalSet Δ ∅ p) := by
  refine ⟨x.1.1, x.2.1, ?_, x.2.2.2.1⟩
  have hcNat : (finalSet Δ (∅ : Finset ι) p).card ≤ Δ := by
    simpa using finalSet_card_le Δ (∅ : Finset ι) p
  have hc : ((finalSet Δ ∅ p).card : ℝ) ≤ Δ := by
    exact_mod_cast hcNat
  linarith [x.2.2.1]

theorem continuous_pathBids {ξ U lo hi slack : ℝ} {d Δ : ℕ} (p : Path ι Δ) :
    Continuous (pathBids (ξ := ξ) (U := U) (lo := lo) (hi := hi) (slack := slack) (d := d) p) := by
  exact ((continuous_subtype_val.fst)).subtype_mk _

theorem continuous_path_root {ξ U lo hi slack : ℝ} {d Δ : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (p : Path ι Δ) :
    Continuous (fun x : GuardedState (ι := ι) ξ U lo hi slack d Δ =>
      root ξ lo hi x.1.1 (finalSet Δ ∅ p) d) :=
  (continuous_root_guarded (finalSet Δ ∅ p) hξ hξ1 hU hlo hlh hg hd hs).comp
    (continuous_pathBids p)

theorem continuous_path_exposure {ξ U lo hi slack : ℝ} {d Δ : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (p : Path ι Δ) (i : ι) :
    Continuous (fun x : GuardedState (ι := ι) ξ U lo hi slack d Δ =>
      exposure ξ (root ξ lo hi x.1.1 (finalSet Δ ∅ p) d) (x.1.1 i)) := by
  have hr := continuous_path_root hξ hξ1 hU hlo hlh hg hd hs p
  have hb : Continuous (fun x : GuardedState (ι := ι) ξ U lo hi slack d Δ => x.1.1 i) := by
    fun_prop
  unfold exposure
  apply continuous_const.min
  apply (continuous_const.max (hb.sub hr)).div (continuous_const.mul (hb.max hr))
  intro x
  have hsx := root_spec (pathBids p x).1 (finalSet Δ ∅ p) d hξ hξ1 hU hlo hlh hg
    (pathBids p x).2.1 hd hs (pathBids p x).2.2.1 (pathBids p x).2.2.2
  exact ne_of_gt (mul_pos hξ ((hlo.trans_le hsx.1.1).trans_le (le_max_right _ _)))

def countPayoff (η v b : ℝ) (i : ι) (P : Finset ι × Finset ι) : ℝ :=
  (v - b) * firstCopy i P - η * b * duplicateCopy i P

def pathPayoff (ξ lo hi η v : ℝ) (b : ι → ℝ) (d Δ : ℕ) (i : ι) (p : Path ι Δ) : ℝ :=
  let E := finalSet Δ ∅ p
  let q := exposure ξ (root ξ lo hi b E d) (b i)
  if i ∈ E then v - b i else (v - b i) * (2 * q - q ^ 2) - η * b i * q ^ 2

variable [Nonempty ι]

theorem weighted_payoff {ξ U lo hi slack η v : ℝ} (b : ι → ℝ) (w : Weights ι)
    (d Δ : ℕ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (h : WeightedGuard ξ U lo hi slack b w d Δ) (i : ι) :
    (weightedExperiment ξ lo hi b w d Δ).expect (fun out => countPayoff η v (b i) i out.2) =
      (pathLaw w Δ ∅).expect (pathPayoff ξ lo hi η v b d Δ i) := by
  unfold countPayoff
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul,
    weighted_first_copy b w d Δ hξ hξ1 hU hlo hlh hg hd hs h i,
    weighted_duplicate_copy b w d Δ hξ hξ1 hU hlo hlh hg hd hs h i,
    ← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_sub]
  apply FiniteLaw.expect_congr
  intro p
  by_cases hi : i ∈ finalSet Δ ∅ p <;> simp [pathPayoff, hi]

theorem continuous_weighted_path_payoff {ξ U lo hi slack : ℝ} {d Δ : ℕ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack)
    (η : ℝ) (i : ι) :
    Continuous (fun x : ℝ × GuardedState (ι := ι) ξ U lo hi slack d Δ =>
      (pathLaw x.2.1.2 Δ ∅).expect (pathPayoff ξ lo hi η x.1 x.2.1.1 d Δ i)) := by
  unfold FiniteLaw.expect
  apply continuous_finsetSum
  intro p _
  have hm : Continuous (fun x : GuardedState (ι := ι) ξ U lo hi slack d Δ =>
      (pathLaw x.1.2 Δ ∅).mass p) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hw : ((∅ : Finset ι).card : ℝ) + Δ < totalWeight x.1.2 := by
      simp only [Finset.card_empty, Nat.cast_zero, zero_add]
      linarith [x.2.2.2.2]
    exact (continuousAt_path_mass Δ ∅ p x.1.2 hw).comp
      (f := fun y : GuardedState (ι := ι) ξ U lo hi slack d Δ => y.1.2)
      (x := x) (by fun_prop)
  apply (hm.comp continuous_snd).mul
  have hp := (continuous_path_exposure hξ hξ1 hU hlo hlh hg hd hs p i).comp
    (continuous_snd : Continuous (Prod.snd : ℝ × GuardedState (ι := ι) ξ U lo hi slack d Δ → _))
  unfold pathPayoff
  by_cases hi : i ∈ finalSet Δ ∅ p
  · simp only [if_pos hi]
    fun_prop
  · simp only [if_neg hi]
    exact ((continuous_fst.sub (by fun_prop)).mul
      ((continuous_const.mul hp).sub (hp.pow 2))).sub
        ((continuous_const.mul (by fun_prop)).mul (hp.pow 2))

theorem exists_private_completion_samplers {ξ U lo hi slack : ℝ} {d : ℕ}
    (E : Finset ι) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hlh : lo < hi) (hg : (1 - ξ) * U ≤ lo) (hd : 0 < d) (hs : 0 < slack) :
    ∃ small large : GuardedBids ξ U lo hi slack d E → unitInterval → Finset ι,
      Measurable (Function.uncurry small) ∧ Measurable (Function.uncurry large) ∧
      (∀ x u, 0 < (completion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E).mass (small x u)) ∧
      (∀ x u, 0 < (largeCompletion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E).mass (large x u)) ∧
      (∀ x, volume.map (small x) = FiniteLaw.probabilityMeasure
        (completion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E)) ∧
      (∀ x, volume.map (large x) = FiniteLaw.probabilityMeasure
        (largeCompletion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E)) ∧
      ∀ x, ((volume : Measure unitInterval).prod volume).map
        (fun u => (large x u.1, small x u.2)) =
        (FiniteLaw.probabilityMeasure (largeCompletion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E)).prod
          (FiniteLaw.probabilityMeasure (completion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E)) := by
  classical
  let P : GuardedBids ξ U lo hi slack d E → FiniteLaw (Finset ι) :=
    fun x => completion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E
  let Q : GuardedBids ξ U lo hi slack d E → FiniteLaw (Finset ι) :=
    fun x => largeCompletion ξ (clearing E hξ hξ1 hU hlo hlh hg hd hs x) x.1 E
  have hP (S : Finset ι) : Measurable (fun x => (P x).mass S) :=
    measurable_guardedSmallLottery_mass E hξ hξ1 hU hlo hlh hg hd hs S
  have hQ (S : Finset ι) : Measurable (fun x => (Q x).mass S) := by
    simp only [Q, largeCompletion, FiniteLaw.map]
    apply Finset.measurable_sum
    intro T _
    by_cases hTS : E ∪ T = S
    · simpa only [if_pos hTS] using hP T
    · simp only [if_neg hTS]
      exact measurable_const
  obtain ⟨small, hsmall, hsmallPos, hsmallLaw⟩ := Hybrid.exists_support_sampler P hP
  obtain ⟨large, hlarge, hlargePos, hlargeLaw⟩ := Hybrid.exists_support_sampler Q hQ
  refine ⟨small, large, hsmall, hlarge, hsmallPos, hlargePos, hsmallLaw, hlargeLaw, ?_⟩
  intro x
  have hsx : Measurable (small x) := hsmall.comp (measurable_const.prodMk measurable_id)
  have hlx : Measurable (large x) := hlarge.comp (measurable_const.prodMk measurable_id)
  change (volume.prod volume).map (Prod.map (large x) (small x)) = _
  rw [← Measure.map_prod_map _ _ hlx hsx, hlargeLaw x, hsmallLaw x]

end Literal
end FCAppendix.Affine.UniformFinite
