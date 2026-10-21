import FCAppendix.Affine.Uniform07Finishing.Native.SourcePhysicalCounts
import FCAppendix.Affine.EqualCapacityLottery
import FCAppendix.Affine.WeightedSampling

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open Existence.PayOnceBounded (listBids)
open scoped BigOperators

variable {m : ℕ} [Nonempty (Fin m)]

theorem literal_source_path_card_margin (row : Uniform07.Row)
    {Λ zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ) (X : ClassifiedContext m)
    (hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ))
    (p : FCAppendix.Affine.WeightedSampling.Path (Fin m)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X))
    (hp : 0 < (FCAppendix.Affine.WeightedSampling.pathLaw
      (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).mass p) :
    (FCAppendix.Affine.WeightedSampling.finalSet
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p).card =
        max (budget c 0 X) (budget c 1 X)-commonBudget c X ∧
    ∀k ∈ FCAppendix.Affine.WeightedSampling.finalSet
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p,
      Λ+3*Early.nativeRadius row < entryBid (X.1 k) := by
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let w := sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1
  have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have hw := sourceGuardAlpha_outer c hm hε X hα 2
  change ε*m < FCAppendix.Affine.WeightedSampling.totalWeight w-(Δ : ℝ) at hw
  have hW : ((∅ : Finset (Fin m)).card : ℝ)+(Δ : ℝ) <
      FCAppendix.Affine.WeightedSampling.totalWeight w := by
    simp only [Finset.card_empty,Nat.cast_zero,zero_add]
    linarith
  refine ⟨by simpa using FCAppendix.Affine.WeightedSampling.finalSet_card w Δ ∅ hW p hp,?_⟩
  intro k hk
  have hkpos := FCAppendix.Affine.WeightedSampling.finalSet_weight_pos
    w Δ ∅ hW (by simp) p hp k hk
  cases hb : X.1 k with
  | none => simp [w,sourceWeights,eligibleWeight,hb] at hkpos
  | some b =>
    by_cases hbU : b ≤ Early.bidCap row
    · simp only [w,sourceWeights,eligibleWeight,hb,if_pos hbU] at hkpos
      simpa only [hb,entryBid] using source_weight_positive_margin row hΛ hkpos
    · simp [w,sourceWeights,eligibleWeight,hb,hbU] at hkpos

theorem literal_source_path_root_certificate (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k, entryBid (X.1 k) ≤ R)
    (hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ))
    (p : FCAppendix.Affine.WeightedSampling.Path (Fin m)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X))
    (hp : 0 < (FCAppendix.Affine.WeightedSampling.pathLaw
      (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).mass p) :
    let E := FCAppendix.Affine.WeightedSampling.finalSet
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p
    ValidExclusive (Uniform07.xi row) X.1 (budget c 0 X) (budget c 1 X) E ∧
    ∃y ∈ Icc (Λ-Early.nativeRadius row) (Λ+Early.nativeRadius row),
      ClippedResidual.remainingDemand (Uniform07.xi row) (fun k => entryBid (X.1 k)) E y =
        (commonBudget c X : ℝ) ∧
      EqualCapacity.positiveMarginal (Uniform07.xi row) (commonBudget c X)
        (listBids (remainder X.1 E)) =
          ClippedResidual.smallMarginal (Uniform07.xi row) y (fun k => entryBid (X.1 k)) E := by
  let E := FCAppendix.Affine.WeightedSampling.finalSet
    (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p
  have ho := sourceGuardAlpha_outer c hm hε X hα
  have hlo := ho 0
  have hhi := ho 1
  simp only [sourceSlacks,Matrix.cons_val_zero,Matrix.cons_val_one] at hlo hhi
  have hs : 0 < ε*m := mul_pos hε (by exact_mod_cast hm)
  have ha : 0 < Early.nativeRadius row := (Early.native_sampling_margin_guards row).1
  have hκ : Uniform07.kappa row = 1-Uniform07.xi row := by
    cases row <;> norm_num [Uniform07.kappa,Uniform07.kappaQ,Uniform07.xi,Uniform07.xiQ]
  have hξ1 : Uniform07.xi row < 1 := source_xi_lt_one row
  have hl0 : 0 < Λ-Early.nativeRadius row :=
    (mul_pos (by rw [hκ]; linarith) hR).trans hguard
  have hdn : 0 < commonBudget c X := by
    have hn : 0 ≤ sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 :=
      Finset.sum_nonneg (fun k _ => ClippedResidual.exposure_nonneg
        (Uniform07.xi_pos row) (by linarith))
    have hh : (0 : ℝ) < commonBudget c X := by linarith
    exact_mod_cast hh
  obtain ⟨hcard,hmarg⟩ := literal_source_path_card_margin row hΛ hm hε c X hα p hp
  have hl : (commonBudget c X : ℝ)+(E.card : ℝ)+ε*m <
      ∑k, ClippedResidual.exposure (Uniform07.xi row) (Λ-Early.nativeRadius row)
        (entryBid (X.1 k)) := by
    rw [hcard]
    change _ < sourceDemand (Uniform07.xi row) (Λ-Early.nativeRadius row) X.1
    linarith
  have hh : (∑k, ClippedResidual.exposure (Uniform07.xi row) (Λ+Early.nativeRadius row)
      (entryBid (X.1 k))) < (commonBudget c X : ℝ)-ε*m := by
    change sourceDemand (Uniform07.xi row) (Λ+Early.nativeRadius row) X.1 < _
    linarith
  exact source_U4_passes_native_test X.1 hX (budget c 0 X) (budget c 1 X) E
    (Uniform07.xi_pos row) hξ1 hR hl0 (by linarith) (by rwa [←hκ]) hbid hdn hs
    hcard hl hh (fun k hk => by linarith [hmarg k hk])

theorem literal_source_path_certificate (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k, entryBid (X.1 k) ≤ R)
    (hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ))
    (p : FCAppendix.Affine.WeightedSampling.Path (Fin m)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X))
    (hp : 0 < (FCAppendix.Affine.WeightedSampling.pathLaw
      (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).mass p) :
    ValidExclusive (Uniform07.xi row) X.1 (budget c 0 X) (budget c 1 X)
      (FCAppendix.Affine.WeightedSampling.finalSet
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p) :=
  (literal_source_path_root_certificate row hΛ hR hguard hm hε c X hX hbid hα p hp).1

omit [Nonempty (Fin m)] in

theorem finite_pair_count_moment
    (P Q : FiniteLaw (Finset (Fin m))) (i : Fin m) (q : Fin 3 → ℝ) :
    (P.prod Q).expect (fun S => q (focalCopy S i)) =
      twoCountPolynomial q
        (P.expect (fun S => if i ∈ S then (1 : ℝ) else 0))
        (Q.expect (fun S => if i ∈ S then (1 : ℝ) else 0)) := by
  let f : Finset (Fin m) → ℝ := fun S => if i ∈ S then 1 else 0
  have hfirst : (P.prod Q).expect (fun S => f S.1) = P.expect f := by
    rw [FiniteLaw.expect_prod]
    simp only [FiniteLaw.expect_const]
  have hsecond : (P.prod Q).expect (fun S => f S.2) = Q.expect f := by
    rw [FiniteLaw.expect_prod]
    change P.expect (fun _ => Q.expect f) = Q.expect f
    exact P.expect_const _
  have hprod : (P.prod Q).expect (fun S => f S.1*f S.2) = P.expect f*Q.expect f :=
    FiniteLaw.expect_prod_mul P Q f f
  calc
    _ = (P.prod Q).expect (fun S =>
        q 0+(q 1-q 0)*(f S.1+f S.2)+(q 2-2*q 1+q 0)*(f S.1*f S.2)) := by
      apply FiniteLaw.expect_congr
      intro S
      by_cases h0 : i ∈ S.1 <;> by_cases h1 : i ∈ S.2 <;>
        simp [focalCopy,f,h0,h1]
      ring
    _ = _ := by
      simp only [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_const,
        hfirst,hsecond,hprod,twoCountPolynomial]
      ring

def sourceForcedSide (c : ℕ) (X : ClassifiedContext m) (E : Finset (Fin m))
    (j : Fin 2) (S : Finset (Fin m)) : Finset (Fin m) :=
  if j = larger c X then E ∪ S else S

def sourceForcedPair (c : ℕ) (X : ClassifiedContext m) (E : Finset (Fin m))
    (S : Finset (Fin m) × Finset (Fin m)) : Finset (Fin m) × Finset (Fin m) :=
  (sourceForcedSide c X E 0 S.1,sourceForcedSide c X E 1 S.2)

def sourceResidualLottery (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) : FiniteLaw (Finset (Fin m)) :=
  EqualCapacity.canonicalLottery ξ (commonBudget c X) (listBids (remainder X.1 E))

def sourceBalancedCompletionLaw (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) : FiniteLaw (Finset (Fin m) × Finset (Fin m)) :=
  ((sourceResidualLottery ξ c X E).prod (sourceResidualLottery ξ c X E)).map
    (sourceForcedPair c X E)

def sourceBalancedPolynomial (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (i : Fin m) (q : Fin 3 → ℝ) : ℝ :=
  let p := EqualCapacity.positiveMarginal ξ (commonBudget c X)
    (listBids (remainder X.1 E)) i
  twoCountPolynomial q
    (if (0 : Fin 2) = larger c X ∧ i ∈ E then 1 else p)
    (if (1 : Fin 2) = larger c X ∧ i ∈ E then 1 else p)

omit [Nonempty (Fin m)] in
theorem sourceResidualLottery_marginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (X : ClassifiedContext m) (E : Finset (Fin m)) (i : Fin m) :
    (sourceResidualLottery ξ c X E).expect (fun S => if i ∈ S then (1 : ℝ) else 0) =
      EqualCapacity.positiveMarginal ξ (commonBudget c X) (listBids (remainder X.1 E)) i := by
  simpa only [sourceResidualLottery,FiniteLaw.prob_eq_expect] using
    (EqualCapacity.canonicalLottery_implements hξ hξ1 (commonBudget c X)
      (listBids (remainder X.1 E))).2 i

omit [Nonempty (Fin m)] in
theorem sourceForcedSide_indicator (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) (j : Fin 2) (S : Finset (Fin m)) (i : Fin m) :
    (if i ∈ sourceForcedSide c X E j S then (1 : ℝ) else 0) =
      if j = larger c X ∧ i ∈ E then 1 else (if i ∈ S then 1 else 0) := by
  by_cases hj : j = larger c X <;> by_cases hi : i ∈ E <;>
    simp [sourceForcedSide,hj,hi]

omit [Nonempty (Fin m)] in
theorem sourceForcedSide_marginal {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (X : ClassifiedContext m) (E : Finset (Fin m)) (j : Fin 2) (i : Fin m) :
    ((sourceResidualLottery ξ c X E).map (sourceForcedSide c X E j)).expect
      (fun S => if i ∈ S then (1 : ℝ) else 0) =
      if j = larger c X ∧ i ∈ E then 1 else
        EqualCapacity.positiveMarginal ξ (commonBudget c X) (listBids (remainder X.1 E)) i := by
  rw [FiniteLaw.expect_map]
  simp_rw [sourceForcedSide_indicator]
  by_cases hj : j = larger c X ∧ i ∈ E
  · simp only [if_pos hj,FiniteLaw.expect_const]
  · simp only [if_neg hj]
    exact sourceResidualLottery_marginal hξ hξ1 c X E i

omit [Nonempty (Fin m)] in
theorem sourceBalancedCompletionLaw_eq_prod (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m)) :
    sourceBalancedCompletionLaw ξ c X E =
      ((sourceResidualLottery ξ c X E).map (sourceForcedSide c X E 0)).prod
        ((sourceResidualLottery ξ c X E).map (sourceForcedSide c X E 1)) := by
  apply FiniteLaw.ext_expect
  intro q
  simp only [sourceBalancedCompletionLaw,sourceForcedPair,FiniteLaw.expect_map,
    FiniteLaw.expect_prod]

omit [Nonempty (Fin m)] in
theorem sourceBalancedCompletionLaw_expect {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (X : ClassifiedContext m) (E : Finset (Fin m)) (i : Fin m) (q : Fin 3 → ℝ) :
    (sourceBalancedCompletionLaw ξ c X E).expect (fun S => q (focalCopy S i)) =
      sourceBalancedPolynomial ξ c X E i q := by
  rw [sourceBalancedCompletionLaw_eq_prod,finite_pair_count_moment,
    sourceForcedSide_marginal hξ hξ1,sourceForcedSide_marginal hξ hξ1]
  rfl

theorem privateCountMoment_eq_balancedPolynomial {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ) (X : ClassifiedContext m)
    (E : Finset (Fin m))
    (hE : ValidExclusive ξ X.1 (budget c 0 X) (budget c 1 X) E)
    (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X (some E) i q =
      sourceBalancedPolynomial ξ c X E i q := by
  by_cases he : budget c 0 X = budget c 1 X
  · have hc : E.card = 0 := by simpa only [he,max_self,min_self,Nat.sub_self] using hE.1
    have hz : E = ∅ := Finset.card_eq_zero.mp hc
    subst E
    have hre : remainder X.1 (∅ : Finset (Fin m)) = X.1 := by
      funext j
      simp [remainder]
    simpa only [sourceBalancedPolynomial,commonBudget,he,min_self,hre,
      Finset.notMem_empty,and_false,if_false] using
      privateCountMoment_equal ξ hξ hξ1 c X (some ∅) he i q
  · exact privateCountMoment_weighted ξ hξ hξ1 c X E he hE i q

def sourceOrderedBalancedDrawLaw (ξ Λ r U : ℝ) (c : ℕ) (X : ClassifiedContext m) :
    FiniteLaw (FCAppendix.Affine.WeightedSampling.Path (Fin m)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ×
        (Finset (Fin m) × Finset (Fin m))) :=
  FCAppendix.Affine.WeightedSampling.pairLaw
    (FCAppendix.Affine.WeightedSampling.pathLaw (sourceWeights ξ Λ r U X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅)
    (fun p =>
      let E := FCAppendix.Affine.WeightedSampling.finalSet
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p
      (sourceResidualLottery ξ c X E).prod (sourceResidualLottery ξ c X E))

def sourceBalancedAllocationLaw (ξ Λ r U : ℝ) (c : ℕ) (X : ClassifiedContext m) :
    FiniteLaw (Finset (Fin m) × Finset (Fin m)) :=
  (sourceOrderedBalancedDrawLaw ξ Λ r U c X).map (fun ω =>
    sourceForcedPair c X
      (FCAppendix.Affine.WeightedSampling.finalSet
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ ω.1) ω.2)

theorem sourceBalancedAllocationLaw_expect {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ r U : ℝ) (c : ℕ) (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    (sourceBalancedAllocationLaw ξ Λ r U c X).expect (fun S => q (focalCopy S i)) =
      (FCAppendix.Affine.WeightedSampling.pathLaw (sourceWeights ξ Λ r U X.1)
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).expect
        (fun p => sourceBalancedPolynomial ξ c X
          (FCAppendix.Affine.WeightedSampling.finalSet
            (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p) i q) := by
  rw [sourceBalancedAllocationLaw,FiniteLaw.expect_map,sourceOrderedBalancedDrawLaw,
    FCAppendix.Affine.WeightedSampling.expect_pairLaw]
  apply FiniteLaw.expect_congr
  intro p
  simpa only [sourceBalancedCompletionLaw,FiniteLaw.expect_map] using
    (sourceBalancedCompletionLaw_expect hξ hξ1 c X
      (FCAppendix.Affine.WeightedSampling.finalSet
        (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p) i q)

theorem expect_eq_of_positive_support {Ω : Type*} [Fintype Ω]
    (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (h : ∀ω, 0 < P.mass ω → f ω = g ω) : P.expect f = P.expect g := by
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : 0 < P.mass ω
  · rw [h ω hω]
  · have hz : P.mass ω = 0 := le_antisymm (le_of_not_gt hω) (P.nonneg ω)
    simp only [hz,zero_mul]

theorem literal_source_path_private_moment (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k, entryBid (X.1 k) ≤ R)
    (hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c X : ℝ))
    (i : Fin m) (q : Fin 3 → ℝ) :
    (FCAppendix.Affine.WeightedSampling.pathLaw
      (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
      (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅).expect
      (fun p => privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
        (source_xi_lt_one row) c X
        (some (FCAppendix.Affine.WeightedSampling.finalSet
          (max (budget c 0 X) (budget c 1 X)-commonBudget c X) ∅ p)) i q) =
      (sourceBalancedAllocationLaw (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) c X).expect (fun S => q (focalCopy S i)) := by
  rw [sourceBalancedAllocationLaw_expect (Uniform07.xi_pos row) (source_xi_lt_one row)]
  apply expect_eq_of_positive_support
  intro p hp
  exact privateCountMoment_eq_balancedPolynomial (Uniform07.xi_pos row) (source_xi_lt_one row)
    c X _ (literal_source_path_certificate row hΛ hR hguard hm hε c X hX hbid hα p hp) i q

theorem literal_finitePathCountCorrection_eq_balanced (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (X : ClassifiedContext m) (hX : NonnegativeList X.1)
    (hbid : ∀k, entryBid (X.1 k) ≤ R) (i : Fin m) (q : Fin 3 → ℝ) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
    let w := sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1
    finitePathCountCorrection (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) c α X i q =
      if (exceptionalSet (Early.bidCap row) X.1).card ≤ 1 ∧
          (Δ : ℝ) < FCAppendix.Affine.WeightedSampling.totalWeight w then
        (α X : ℝ)*((sourceBalancedAllocationLaw (Uniform07.xi row) Λ
          (Early.demandRatio row) (Early.bidCap row) c X).expect (fun S => q (focalCopy S i))-
          privateCountMoment (Uniform07.xi row) (Uniform07.xi_pos row)
            (source_xi_lt_one row) c X none i q)
      else 0 := by
  dsimp only
  dsimp only [finitePathCountCorrection]
  split_ifs with hg
  · by_cases hα : 0 < (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
        (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
        zG (Uniform07.cutoff row) width ε c X : ℝ)
    · rw [literal_source_path_private_moment row hΛ hR hguard hm hε c X hX hbid hα]
    · have hz : (sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
          (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
          zG (Uniform07.cutoff row) width ε c X : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hα) (sourceGuardAlpha _ _ _ _ _ _ _ _ _ _ c X).2.1
      simp only [hz,zero_mul]
  · rfl

def sourceBaselineAllocationLaw (ξ : ℝ) (c : ℕ) (X : ClassifiedContext m) :
    FiniteLaw (Finset (Fin m) × Finset (Fin m)) :=
  if budget c 0 X = budget c 1 X then
    (EqualCapacity.canonicalLottery ξ (budget c 0 X) (listBids X.1)).prod
      (EqualCapacity.canonicalLottery ξ (budget c 0 X) (listBids X.1))
  else FiniteLaw.dirac (purePair ξ c X)

theorem sourceBaselineAllocationLaw_expect {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    (sourceBaselineAllocationLaw ξ c X).expect (fun S => q (focalCopy S i)) =
      privateCountMoment ξ hξ hξ1 c X none i q := by
  by_cases he : budget c 0 X = budget c 1 X
  · rw [sourceBaselineAllocationLaw,if_pos he,finite_pair_count_moment,
      privateCountMoment_equal ξ hξ hξ1 c X none he]
    have hp := (EqualCapacity.canonicalLottery_implements hξ hξ1
      (budget c 0 X) (listBids X.1)).2 i
    rw [FiniteLaw.prob_eq_expect] at hp
    simp only [hp]
  · rw [sourceBaselineAllocationLaw,if_neg he,FiniteLaw.expect_dirac,
      privateCountMoment_none ξ hξ hξ1 c X he]

def sourcePhysicalAllocationLaw (ξ Λ r U zs R : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (i : Fin m) (a : JointAction 2)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    FiniteLaw (Finset (Fin m) × Finset (Fin m)) :=
  let X := focalInputContext R i a x
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  if rivalHasSeed zs i (deleteFocal i x.1) ∧
      (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) <
        FCAppendix.Affine.WeightedSampling.totalWeight (sourceWeights ξ Λ r U X.1) then
    FiniteLaw.mixture (sourceBalancedAllocationLaw ξ Λ r U c X)
      (sourceBaselineAllocationLaw ξ c X) (α X : ℝ) (α X).2.1 (α X).2.2
  else sourceBaselineAllocationLaw ξ c X

def sourcePhysicalFiniteCountLaw (ξ Λ r U zs R : ℝ) (c : ℕ)
    (α : ClassifiedContext m → unitInterval) (i : Fin m) (a : JointAction 2)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) : FiniteLaw (Fin 3) :=
  (sourcePhysicalAllocationLaw ξ Λ r U zs R c α i a x).map (fun S => focalCopy S i)

theorem literal_sourcePhysicalCountTest_eq_finiteLaw (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (i : Fin m) (a : JointAction 2) (q : Fin 3 → ℝ)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
      Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a q x =
      (sourcePhysicalFiniteCountLaw (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a x).expect q := by
  let X := focalInputContext R i a x
  have hX : NonnegativeList X.1 := by
    simpa only [X,focalInputContext,deviationList_eq_focalLocalList] using
      focalContext_nonnegative R i a x.2 0 (deleteFocal i x.1)
  have hbid : ∀k, entryBid (X.1 k) ≤ R := by
    simpa only [X,focalInputContext,deviationList_eq_focalLocalList] using
      focalContext_le_floor hR.le i a x.2 0 (deleteFocal i x.1)
  dsimp only
  rw [sourcePhysicalFiniteCountLaw,FiniteLaw.expect_map]
  dsimp only [sourcePhysicalCountTest,sourcePhysicalAllocationLaw]
  rw [literal_finitePathCountCorrection_eq_balanced row hΛ hR hguard hm hε c X hX hbid]
  simp only [←sourceBaselineAllocationLaw_expect (Uniform07.xi_pos row) (source_xi_lt_one row)]
  by_cases hseed : rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1)
  · by_cases hg : (exceptionalSet (Early.bidCap row) X.1).card ≤ 1 ∧
        ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ) <
          FCAppendix.Affine.WeightedSampling.totalWeight
            (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)
    · have hfull := And.intro hseed hg
      dsimp only [X] at hfull
      simp only [if_pos hseed,if_pos hg,if_pos hfull,FiniteLaw.expect_mixture]
      ring
    · have hn : ¬(rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1) ∧
          (exceptionalSet (Early.bidCap row) X.1).card ≤ 1 ∧
          ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ) <
            FCAppendix.Affine.WeightedSampling.totalWeight
              (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)) :=
        fun h => hg h.2
      dsimp only [X] at hn
      simp only [if_pos hseed,if_neg hg,if_neg hn,add_zero]
  · have hn : ¬(rivalHasSeed (Uniform07.cutoff row/2) i (deleteFocal i x.1) ∧
        (exceptionalSet (Early.bidCap row) X.1).card ≤ 1 ∧
        ((max (budget c 0 X) (budget c 1 X)-commonBudget c X : ℕ) : ℝ) <
          FCAppendix.Affine.WeightedSampling.totalWeight
            (sourceWeights (Uniform07.xi row) Λ (Early.demandRatio row) (Early.bidCap row) X.1)) :=
      fun h => hseed h.1
    dsimp only [X] at hn
    simp only [if_neg hseed,if_neg hn,add_zero]

theorem literal_sourcePhysicalFiniteCountLaw_mass (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (i : Fin m) (a : JointAction 2) (k : Fin 3)
    (x : UserProfile m 2 × Equiv.Perm (Fin 2)) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    (sourcePhysicalFiniteCountLaw (Uniform07.xi row) Λ (Early.demandRatio row)
      (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a x).mass k =
      sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a
        (fun r => if r = k then 1 else 0) x := by
  simpa only [FiniteLaw.expect_singleton] using
    (literal_sourcePhysicalCountTest_eq_finiteLaw row hΛ hR hguard hm hε c i a
      (fun r => if r = k then 1 else 0) x).symm

theorem measurable_literal_sourcePhysicalFiniteCountLaw_mass (row : Uniform07.Row)
    {Λ R zG width ε : ℝ}
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ) (hR : 0 < R)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hm : 0 < m) (hε : 0 < ε) (c : ℕ)
    (i : Fin m) (a : JointAction 2) (k : Fin 3) :
    let α := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
      (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
      zG (Uniform07.cutoff row) width ε c
    Measurable (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
      (sourcePhysicalFiniteCountLaw (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a x).mass k) := by
  let α : ClassifiedContext m → unitInterval := sourceGuardAlpha (Uniform07.xi row) Λ (Early.nativeRadius row)
    (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/1000)
    zG (Uniform07.cutoff row) width ε c
  have hα : Measurable α := measurable_sourceGuardAlpha (Uniform07.xi_pos row)
    (Early.native_sampling_margin_guards row).1 (source_guard_root_positive row hΛ)
    (div_pos (Uniform07.cutoff_pos row) (by norm_num : (0 : ℝ) < 1000))
    (Early.demandRatio row) (Early.bidCap row) zG (Uniform07.cutoff row) width ε c
  have he : (fun x : UserProfile m 2 × Equiv.Perm (Fin 2) =>
      (sourcePhysicalFiniteCountLaw (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a x).mass k) =
      sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row) (source_xi_lt_one row)
        Λ (Early.demandRatio row) (Early.bidCap row) (Uniform07.cutoff row/2) R c α i a
        (fun r => if r = k then 1 else 0) := by
    funext x
    exact literal_sourcePhysicalFiniteCountLaw_mass row hΛ hR hguard hm hε c i a k x
  dsimp only
  rw [he]
  exact measurable_sourcePhysicalCountTest (Uniform07.xi row) (Uniform07.xi_pos row)
    (source_xi_lt_one row) Λ (Early.demandRatio row) (Early.bidCap row)
    (Uniform07.cutoff row/2) R (source_guard_multiplier_positive row hΛ) c α hα i a
    (fun r => if r = k then 1 else 0)

end FCAppendix.Affine.Uniform07Finishing.Weighted

namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative Weighted

variable {m : ℕ} [Nonempty (Fin m)]

theorem sourceNativeGame_broadcast_count_expect_balancedExperiment
    (row : Uniform07.Row) (hm : 2 ≤ m) (hc : 1 ≤ Uniform07.capacity m)
    {R Λ zG width ε : ℝ} (hR : 0 < R) (hUR : Early.bidCap row < R)
    (hRt : R < Uniform07.cutoff row)
    (hΛ : (54/100 : ℝ)*Uniform07.cutoff row < Λ)
    (hguard : Uniform07.kappa row*R < Λ-Early.nativeRadius row)
    (hzG : Uniform07.cutoff row/2 ≤ zG) (hε : 0 < ε)
    (PL : ProbabilityMeasure (ℝ × JointAction 2))
    (hLvalue : (PL : Measure (ℝ × JointAction 2)).map Prod.fst =
      (sourceLowerValueLaw row : Measure ℝ))
    (hLroute : ∀ᵐx ∂(PL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ Early.bidCap row ∧ x.2.routeCount = 2)
    (hLatom : ∀b : ℝ, (PL : Measure (ℝ × JointAction 2)) {x | x.2.bid = b} = 0)
    (i : Fin m) (a : JointAction 2) (ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) (q : Fin 3 → ℝ) :
    let Γ := sourceNativeGame row hc R Λ (source_guard_multiplier_positive row hΛ) PL
      (literalSourceAlpha row Λ zG width ε) (measurable_literalSourceAlpha row hΛ zG width ε)
    ((problem Γ i).outcome a).expect q =
      ∫x, (sourcePhysicalFiniteCountLaw (Uniform07.xi row) Λ (Early.demandRatio row)
        (Early.bidCap row) (Uniform07.cutoff row/2) R (Uniform07.capacity m)
        (literalSourceAlpha row Λ zG width ε) i a x).expect q
        ∂(userProfileLaw Γ).prod (permLaw 2) := by
  dsimp only
  rw [sourceNativeGame_broadcast_count_expect_physical row hm hc hR hUR hRt
    hΛ hguard hzG hε PL hLvalue hLroute hLatom i a ha0 haR ha2 q]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  simpa only [sourcePhysicalCountTestOfRow,literalSourceAlpha] using
    literal_sourcePhysicalCountTest_eq_finiteLaw row hΛ hR hguard (by omega) hε
      (Uniform07.capacity m) i a q x

end FCAppendix.Affine.Uniform07Finishing
