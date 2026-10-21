import FCAppendix.Affine.UniformFinite.SourceProductMenu
import FCAppendix.Affine.UniformFinite.CapLocalization
import FCAppendix.Affine.UniformFinite.LowPrefixGuard
import FCAppendix.Affine.Hybrid.NativeEqual

set_option maxHeartbeats 600000

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late.Exceptional
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open scoped BigOperators
open Uniform05 Source ClippedResidual WeightedSampling
open Existence.Distributional

section Generic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def masked (b : ι → ℝ) (E : Finset ι) : ι → ℝ := fun j => if j ∈ E then 0 else b j

def completion (ξ : ℝ) (d : ℕ) (b : ι → ℝ) (E : Finset ι) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (EqualCapacity.positiveMarginal ξ d (masked b E))

def largeCompletion (ξ : ℝ) (d : ℕ) (b : ι → ℝ) (E : Finset ι) : FiniteLaw (Finset ι) :=
  (completion ξ d b E).map (fun S => E ∪ S)

def conditionalCompletion (ξ : ℝ) (d : ℕ) (b : ι → ℝ) (E : Finset ι) :
    FiniteLaw (Finset ι × Finset ι) :=
  (largeCompletion ξ d b E).prod (completion ξ d b E)

theorem measurable_completion_mass {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (d : ℕ) (E S : Finset ι) : Measurable (fun b => (completion ξ d b E).mass S) := by
  apply (ExactCapacity.measurable_symmetricLottery_mass S).comp
  apply (EqualCapacity.measurable_positiveMarginal ξ d hξ hξ1).comp
  apply measurable_pi_lambda
  intro j
  by_cases hj : j ∈ E
  · simp only [masked,if_pos hj]
    exact measurable_const
  · simpa only [masked,if_neg hj] using (measurable_pi_apply j : Measurable (fun b : ι → ℝ => b j))

theorem measurable_largeCompletion_mass {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (d : ℕ) (E S : Finset ι) : Measurable (fun b => (largeCompletion ξ d b E).mass S) := by
  unfold largeCompletion FiniteLaw.map
  dsimp only
  apply Finset.measurable_sum
  intro T _
  by_cases h : E ∪ T=S
  · simpa only [if_pos h] using measurable_completion_mass hξ hξ1 d E T
  · simp only [if_neg h]
    exact measurable_const

theorem completion_eq_literal {ξ z U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hz : 0 < z) (hU : 0 ≤ U) (hguard : (1-ξ)*U ≤ z)
    (d : ℕ) (b : ι → ℝ) (E : Finset ι)
    (hb : ∀j,0 ≤ b j) (hbU : ∀j,b j ≤ U)
    (hr : remainingDemand ξ b E z=(d:ℝ)) :
    completion ξ d b E=Literal.completion ξ z b E := by
  have hp : (fun j => exposure ξ z (masked b E j))=smallMarginal ξ z b E := by
    funext j
    by_cases hj : j ∈ E
    · simp [masked,smallMarginal,hj,exposure_zero hz.le]
    · simp [masked,smallMarginal,hj]
  have h0 (j : ι) : 0 ≤ masked b E j := by
    by_cases hj : j ∈ E <;> simp [masked,hj,hb j]
  have h1 (j : ι) : masked b E j ≤ U := by
    by_cases hj : j ∈ E <;> simp [masked,hj,hbU j,hU]
  have he := positiveMarginal_eq_exposure hξ hξ1 hz hguard d (masked b E) h0 h1
    (by simpa only [hp,smallMarginal,remainingDemand] using hr)
  unfold completion Literal.completion
  rw [he,hp]

theorem conditionalCompletion_eq_literal {ξ z U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hz : 0 < z) (hU : 0 ≤ U) (hguard : (1-ξ)*U ≤ z)
    (d : ℕ) (b : ι → ℝ) (E : Finset ι)
    (hb : ∀j,0 ≤ b j) (hbU : ∀j,b j ≤ U)
    (hr : remainingDemand ξ b E z=(d:ℝ)) :
    conditionalCompletion ξ d b E=Literal.conditionalCompletion ξ z b E := by
  unfold conditionalCompletion largeCompletion Literal.conditionalCompletion Literal.largeCompletion
  rw [completion_eq_literal hξ hξ1 hz hU hguard d b E hb hbU hr]

theorem completion_nash {ξ z U : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hz : 0 < z) (hU : 0 ≤ U) (hguard : (1-ξ)*U ≤ z) (d : ℕ) (b : ι → ℝ) (E : Finset ι)
    (hb0 : ∀ j, 0 ≤ b j) (hbU : ∀ j, b j ≤ U)
    (hselected : ∀ j ∈ E, z ≤ b j) (hr : remainingDemand ξ b E z = (d : ℝ)) :
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d) →
      revenueAgainst ξ b ν (largeCompletion ξ d b E) ≤
        revenueAgainst ξ b (completion ξ d b E) (largeCompletion ξ d b E)) ∧
    (∀ ν : FiniteLaw (Finset ι), (∀ S, ν.mass S ≠ 0 → S.card ≤ d+E.card) →
      revenueAgainst ξ b ν (completion ξ d b E) ≤
        revenueAgainst ξ b (largeCompletion ξ d b E) (completion ξ d b E)) := by
  have he := completion_eq_literal hξ hξ1 hz hU hguard d b E hb0 hbU hr
  have hl : largeCompletion ξ d b E = Literal.largeCompletion ξ z b E := by
    unfold largeCompletion Literal.largeCompletion
    rw [he]
  have hn := Literal.conditional_completion_nash b E d hξ hξ1 hz hguard hbU hselected hr
  rw [←he, ←hl] at hn
  exact hn

theorem remainingDemand_zero_focal {ξ z : ℝ} (hz : 0 < z)
    (b : ι → ℝ) (a : ι) (E : Finset ι) (ha : a ∉ E) :
    remainingDemand ξ b E z =
      remainingDemand ξ (Function.update b a 0) E z+exposure ξ z (b a) := by
  unfold remainingDemand
  rw [← Finset.add_sum_erase Finset.univ
      (fun j => if j ∈ E then 0 else exposure ξ z (b j)) (Finset.mem_univ a),
    ← Finset.add_sum_erase Finset.univ
      (fun j => if j ∈ E then 0 else exposure ξ z (Function.update b a 0 j))
      (Finset.mem_univ a)]
  simp only [if_neg ha,Function.update_self,exposure_zero hz.le,zero_add]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem exceptional_focal_multiplier_shift {ξ U lo hi z0 z : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hguard : (1-ξ)*U ≤ lo) (b : ι → ℝ) (a : ι) (E : Finset ι)
    (ha : a ∉ E) (hbU : ∀j,Function.update b a 0 j ≤ U)
    (d : ℕ) (hd : 1 < (d:ℝ)) (hz0 : z0 ∈ Icc lo hi) (hz : z ∈ Icc lo hi)
    (hzero : remainingDemand ξ (Function.update b a 0) E z0=(d:ℝ))
    (hnew : remainingDemand ξ b E z=(d:ℝ)) :
    0 ≤ z-z0 ∧ z-z0 ≤ ξ*U/((d:ℝ)-1) := by
  have hzpos := hlo.trans_le hz.1
  have he := remainingDemand_zero_focal (ξ := ξ) hzpos b a E ha
  have hp0 : 0 ≤ exposure ξ z (b a) := exposure_nonneg hξ hzpos
  have hp1 : exposure ξ z (b a) ≤ 1 := exposure_le_one _ _ _
  have hbase : (d:ℝ)-1 ≤ remainingDemand ξ (Function.update b a 0) E z ∧
      remainingDemand ξ (Function.update b a 0) E z ≤ (d:ℝ) := by
    rw [hnew] at he
    constructor <;> linarith
  have horder : z0 ≤ z := by
    by_contra hn
    have hzz0 := lt_of_not_ge hn
    have hdrop := remainingDemand_drop (Function.update b a 0) E hξ hξ1 hU hlo
      hguard hz.1 hzz0.le hbU
    rw [hzero] at hdrop
    have hpositive : 0 < (z0-z)/(ξ*U)*(d:ℝ) := by positivity
    linarith [hbase.2]
  have hdrop := remainingDemand_drop (Function.update b a 0) E hξ hξ1 hU hlo
    hguard hz0.1 horder hbU
  rw [hzero] at hdrop
  have hcoef : 0 ≤ (z-z0)/(ξ*U) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase.1 hcoef
  have hone : (z-z0)/(ξ*U)*((d:ℝ)-1) ≤ 1 := by linarith [hbase.1]
  have hratio : (z-z0)*((d:ℝ)-1)/(ξ*U) ≤ 1 := by
    convert! hone using 1
    ring
  have hcross := (div_le_iff₀ (mul_pos hξ hU)).mp hratio
  refine ⟨sub_nonneg.mpr horder,(le_div_iff₀ (by linarith : 0 < (d:ℝ)-1)).mpr ?_⟩
  simpa only [one_mul] using hcross

end Generic

section Source
variable {M : ℕ} [NeZero M]

def ordinary (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) : Fin M → ℝ :=
  Function.update (lowerBids row b) a 0

omit [NeZero M] in
theorem lowerBids_ordinary (row : CountRow M) (b : Fin M → ℝ) (a : Fin M) :
    lowerBids row (ordinary row b a)=ordinary row b a := by
  funext j
  by_cases hj : j=a
  · subst j
    simp [ordinary,lowerBids]
  · by_cases hl : j ∈ row.lower <;> simp [ordinary,lowerBids,hj,hl]

def weight (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : Weights (Fin M) :=
  sourceWeights i G row (ordinary row b a)

def alpha (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : ℝ :=
  if b a ≤ t i ∧ kappa i*t i ≤ rootLo i G ∧ 2 < commonGuardMargin i*M ∧
      1 < seedCount i row (ordinary row b a)
  then rawAlpha i G row (ordinary row b a) else 0

omit [NeZero M] in
theorem alpha_bounds (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : 0 ≤ alpha i G row b a ∧ alpha i G row b a ≤ 1 := by
  unfold alpha
  split_ifs
  · exact Literal.guardWeight_bounds _ _ _
  · constructor <;> norm_num

def canonicalLaw (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : FiniteLaw (Allocation M) :=
  (WeightedSampling.pairLaw (pathLaw (weight i G row b a) (imbalance row) ∅)
    (fun p => conditionalCompletion (xi i) (small row) (lowerBids row b)
      (finalSet (imbalance row) ∅ p))).map (fun x => orient row x.2)

def continuationLaw (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : FiniteLaw (Allocation M) :=
  if residual row 0=residual row 1 then UniformFinite.equalLaw i row b
  else FiniteLaw.mixture (canonicalLaw i G row b a) (UniformFinite.pureLaw i row b)
    (alpha i G row b a) (alpha_bounds i G row b a).1 (alpha_bounds i G row b a).2

def extendedLaw (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : FiniteLaw (Allocation M) :=
  if cap i < b a then continuationLaw i G row b a
  else UniformFinite.continuationLaw i G row b

theorem extendedLaw_on_path (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (hb : b a ≤ cap i) :
    extendedLaw i G row b a=UniformFinite.continuationLaw i G row b := by
  simp only [extendedLaw,if_neg (not_lt_of_ge hb)]

def rowPayoff (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (v : ℝ) (b : Fin M → ℝ) (a : Fin M) : ℝ :=
  (continuationLaw i G row b a).expect (pairPayoff (eta i) v (b a) a)

theorem rowPayoff_bound (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (v : ℝ) (b : Fin M → ℝ) (a : Fin M) :
    |rowPayoff i G row v b a| ≤ |v|+(1+|eta i|)*|b a| := by
  apply abs_le.mpr
  constructor
  · exact FiniteLaw.const_le_expect _ (fun P => (abs_le.mp (pairPayoff_bound _ _ _ _ P)).1)
  · exact FiniteLaw.expect_le_const _ (fun P => (abs_le.mp (pairPayoff_bound _ _ _ _ P)).2)

theorem rowPayoff_overbid (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (v : ℝ) (b : Fin M → ℝ) (a : Fin M) (hv0 : 0 ≤ v) (hvb : v < b a) :
    rowPayoff i G row v b a ≤ 0 :=
  FiniteLaw.expect_le_const _ (fun P => pairPayoff_overbid (eta_range i).1.le hv0 hvb a P)

omit [NeZero M] in
theorem alpha_pos_data (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (h : 0 < alpha i G row b a) :
    b a ≤ t i ∧ kappa i*t i ≤ rootLo i G ∧ 2 < commonGuardMargin i*M ∧
      1 < seedCount i row (ordinary row b a) ∧ 0 < rawAlpha i G row (ordinary row b a) := by
  unfold alpha at h
  split_ifs at h with hg
  · exact ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,h⟩
  · norm_num at h

omit [NeZero M] in

theorem focal_weight_zero (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) : (weight i G row b a).1 a=0 := by
  have hz := lawWeight_zero_on_prefix i G (lowPrefixTop_pos i G).le
  by_cases ha : a ∈ row.lower <;> simp [weight,sourceWeights,ordinary,ha,hz]

theorem guarded_new_state (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (_ha : a ∈ row.lower)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i) (hapos : 0 < alpha i G row b a) :
    Literal.WeightedGuard (xi i) (t i) (rootLo i G) (rootHi i G)
      (commonGuardMargin i*M-1) (lowerBids row b) (weight i G row b a)
      (small row) (imbalance row) ∧ 1 < (small row:ℝ) := by
  have hd := alpha_pos_data i G row b a hapos
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hbase (j : Fin M) (_hj : j ∈ row.lower) : ordinary row b a j ≤ cap i := by
    by_cases hja : j=a
    · subst j
      simp [ordinary,(cap_pos i).le]
    · simpa only [ordinary,Function.update_of_ne hja,lowerBids_of_mem row b _hj] using hb j _hj hja
  have hsource := rawAlpha_pos i G row (ordinary row b a) hM hbase hd.2.2.2.2
  rw [lowerBids_ordinary] at hsource
  have hroot := rootBounds i G
  have hlow := remainingDemand_zero_focal (ξ := xi i) hroot.1 (lowerBids row b) a ∅ (by simp)
  have hhigh := remainingDemand_zero_focal (ξ := xi i) (hroot.1.trans hroot.2.1)
    (lowerBids row b) a ∅ (by simp)
  simp only [remainingDemand,Finset.notMem_empty,if_false] at hlow hhigh
  have hplo : 0 ≤ exposure (xi i) (rootLo i G) (lowerBids row b a) :=
    exposure_nonneg (xi_range i).1 hroot.1
  have hphi := exposure_le_one (xi i) (rootHi i G) (lowerBids row b a)
  have hH0 : 0 ≤ ∑j,exposure (xi i) (rootHi i G) (ordinary row b a j) :=
    Finset.sum_nonneg (fun j _ => exposure_nonneg (xi_range i).1 (hroot.1.trans hroot.2.1))
  have hd1 : 1 < (small row:ℝ) := by linarith [hsource.1.2.2.1,hd.2.2.1]
  refine ⟨⟨?_,?_,?_,?_,?_⟩,hd1⟩
  · intro j
    by_cases hj : j ∈ row.lower
    · rw [lowerBids_of_mem row b hj]
      by_cases hja : j=a
      · simpa only [hja] using hd.1
      · exact (hb j hj hja).trans (cap_lt_t i).le
    · simp [lowerBids,hj,(t_pos i).le]
  · change (∑j,exposure (xi i) (rootLo i G) (lowerBids row b j))=
      (∑j,exposure (xi i) (rootLo i G) (ordinary row b a j))+_ at hlow
    linarith [hsource.1.2.1]
  · change (∑j,exposure (xi i) (rootHi i G) (lowerBids row b j))=
      (∑j,exposure (xi i) (rootHi i G) (ordinary row b a j))+_ at hhigh
    linarith [hsource.1.2.2.1]
  · change (imbalance row : ℝ) + (commonGuardMargin i*M-1) <
      totalWeight (sourceWeights i G row (ordinary row b a))
    linarith [hsource.1.2.2.2.1]
  · intro j hj
    have hel := hsource.1.2.2.2.2 j hj
    have hja : j ≠ a := by
      intro he
      subst j
      rw [focal_weight_zero] at hj
      linarith
    simpa only [ordinary,Function.update_of_ne hja] using hel

theorem guarded_path (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i) (hapos : 0 < alpha i G row b a)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p) :
    let E := finalSet (imbalance row) ∅ p
    let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
    E.card=imbalance row ∧ a ∉ E ∧ z ∈ Icc (rootLo i G) (rootHi i G) ∧
      remainingDemand (xi i) (lowerBids row b) E z=(small row:ℝ) ∧
      ∀j ∈ E,rootHi i G ≤ lowerBids row b j := by
  have hd := alpha_pos_data i G row b a hapos
  have hg := guarded_new_state i G row b a ha hb hapos
  have hr := rootBounds i G
  have hs : 0 < commonGuardMargin i*M-1 := by linarith [hd.2.2.1]
  have hd0 : 0 < small row := by exact_mod_cast (show (0:ℝ)< small row by linarith [hg.2])
  have h := Literal.weighted_path_root (lowerBids row b) (weight i G row b a)
    (small row) (imbalance row) (xi_range i).1 (xi_range i).2 (t_pos i) hr.1 hr.2.1
    hd.2.1 hd0 hs hg.1 p hp
  have haE : a ∉ finalSet (imbalance row) ∅ p := by
    intro haE
    have hw : ((∅ : Finset (Fin M)).card:ℝ)+imbalance row < totalWeight (weight i G row b a) := by
      simp only [Finset.card_empty,Nat.cast_zero,zero_add]
      linarith [hg.1.2.2.2.1]
    have hpos := finalSet_weight_pos (weight i G row b a) (imbalance row) ∅ hw
      (by simp) p hp a haE
    rw [focal_weight_zero] at hpos
    linarith
  exact ⟨h.1,haE,h.2.1,h.2.2.1,h.2.2.2⟩

theorem guarded_conditional_nash (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i) (hapos : 0 < alpha i G row b a)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p) :
    let E := finalSet (imbalance row) ∅ p
    (∀ ν : FiniteLaw (Finset (Fin M)),(∀S,ν.mass S ≠ 0 → S.card ≤ small row) →
      revenueAgainst (xi i) (lowerBids row b) ν (largeCompletion (xi i) (small row) (lowerBids row b) E) ≤
        revenueAgainst (xi i) (lowerBids row b) (completion (xi i) (small row) (lowerBids row b) E)
          (largeCompletion (xi i) (small row) (lowerBids row b) E)) ∧
    (∀ ν : FiniteLaw (Finset (Fin M)),(∀S,ν.mass S ≠ 0 → S.card ≤ small row+imbalance row) →
      revenueAgainst (xi i) (lowerBids row b) ν (completion (xi i) (small row) (lowerBids row b) E) ≤
        revenueAgainst (xi i) (lowerBids row b) (largeCompletion (xi i) (small row) (lowerBids row b) E)
          (completion (xi i) (small row) (lowerBids row b) E)) := by
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b a ha hb hapos p hp
  let E := finalSet (imbalance row) ∅ p
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
  have hroot := rootBounds i G
  have hdata := alpha_pos_data i G row b a hapos
  have hg := guarded_new_state i G row b a ha hb hapos
  have hz0 : 0 < z := hroot.1.trans_le hz.1
  have hb0' (j : Fin M) : 0 ≤ lowerBids row b j := by
    by_cases hj : j ∈ row.lower <;> simp [lowerBids,hj,hb0 j]
  have hn := completion_nash (xi_range i).1 (xi_range i).2 hz0 (t_pos i).le
    (hdata.2.1.trans hz.1) (small row) (lowerBids row b) E hb0' hg.1.1
    (fun j hj => hz.2.trans (hsel j hj)) hclear
  have hcard : E.card = imbalance row := hc
  rw [hcard] at hn
  exact hn

theorem guarded_private_implements (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (ha : a ∈ row.lower)
    (hb0 : ∀j ∈ row.lower,0 ≤ b j)
    (hb : ∀j ∈ row.lower,j ≠ a → b j ≤ cap i) (hapos : 0 < alpha i G row b a)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (weight i G row b a) (imbalance row) ∅).mass p) :
    let E := finalSet (imbalance row) ∅ p
    let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
    ExactCapacity.Implements (smallMarginal (xi i) z (lowerBids row b) E) (small row)
      (completion (xi i) (small row) (lowerBids row b) E) ∧
    ExactCapacity.Implements (largeMarginal (xi i) z (lowerBids row b) E)
      (small row+imbalance row) (largeCompletion (xi i) (small row) (lowerBids row b) E) ∧
    (∀S,(completion (xi i) (small row) (lowerBids row b) E).mass S ≠ 0 → S ⊆ row.lower) ∧
    (∀S,(largeCompletion (xi i) (small row) (lowerBids row b) E).mass S ≠ 0 → S ⊆ row.lower) := by
  obtain ⟨hc,haE,hz,hclear,hsel⟩ := guarded_path i G row b a ha hb hapos p hp
  let E := finalSet (imbalance row) ∅ p
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
  have hz0 : 0 < z := (rootBounds i G).1.trans_le hz.1
  have hdata := alpha_pos_data i G row b a hapos
  have hg := guarded_new_state i G row b a ha hb hapos
  have hb0' (j : Fin M) : 0 ≤ lowerBids row b j := by
    by_cases hj : j ∈ row.lower
    · simpa only [lowerBids,if_pos hj] using hb0 j hj
    · simp only [lowerBids,if_neg hj,le_refl]
  have he := completion_eq_literal (xi_range i).1 (xi_range i).2 hz0 (t_pos i).le
    (hdata.2.1.trans hz.1) (small row) (lowerBids row b) E hb0' hg.1.1 hclear
  have hl : largeCompletion (xi i) (small row) (lowerBids row b) E=
      Literal.largeCompletion (xi i) z (lowerBids row b) E := by
    unfold largeCompletion Literal.largeCompletion
    rw [he]
  have hs := Literal.completion_implements (xi_range i).1 hz0 (lowerBids row b) E (small row) hclear
  have hL := Literal.largeCompletion_implements (xi_range i).1 hz0 (lowerBids row b) E (small row) hclear
  rw [← he] at hs
  rw [← hl,hc] at hL
  have hE : E ⊆ row.lower := by
    intro j hj
    by_contra hn
    have hbid := hsel j hj
    rw [lowerBids,if_neg hn] at hbid
    have hhi : 0 < rootHi i G := (rootBounds i G).1.trans (rootBounds i G).2.1
    linarith
  refine ⟨hs,hL,?_,?_⟩
  · intro S hS j hj
    by_contra hn
    have hpj : Proposer.marginal (completion (xi i) (small row) (lowerBids row b) E) j=0 := by
      change (completion (xi i) (small row) (lowerBids row b) E).prob (fun S => j ∈ S)=0
      rw [hs.2 j]
      simp [smallMarginal,lowerBids,hn,exposure_zero hz0.le]
    exact Literal.zero_marginal_omitted _ j hpj S hS hj
  · intro S hS j hj
    by_contra hn
    have hnE : j ∉ E := fun hjE => hn (hE hjE)
    have hpj : Proposer.marginal (largeCompletion (xi i) (small row) (lowerBids row b) E) j=0 := by
      change (largeCompletion (xi i) (small row) (lowerBids row b) E).prob (fun S => j ∈ S)=0
      rw [hL.2 j]
      simp only [largeMarginal,if_neg hnE,lowerBids,if_neg hn,exposure_zero hz0.le]
    exact Literal.zero_marginal_omitted _ j hpj S hS hj

omit [NeZero M] in
theorem continuous_lowerBids (row : CountRow M) : Continuous (lowerBids row) := by
  apply continuous_pi
  intro j
  by_cases hj : j ∈ row.lower
  · simpa only [lowerBids,if_pos hj] using (continuous_apply j : Continuous (fun b : Fin M → ℝ => b j))
  · simp only [lowerBids,if_neg hj]
    exact continuous_const

omit [NeZero M] in
theorem continuous_ordinary (row : CountRow M) (a : Fin M) :
    Continuous (fun b => ordinary row b a) := by
  apply continuous_pi
  intro j
  by_cases hj : j=a
  · subst j
    simp only [ordinary,Function.update_self]
    exact continuous_const
  · simpa only [ordinary,Function.update_of_ne hj,Function.comp_def] using
      (continuous_apply j).comp (continuous_lowerBids row)

omit [NeZero M] in
theorem continuous_weight (i : Row) (G : RestrictedLaw i) (row : CountRow M) (a : Fin M) :
    Continuous (fun b => weight i G row b a) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  by_cases hj : j ∈ row.lower
  · change Continuous (fun b => if j ∈ row.lower then lawWeight i G (ordinary row b a j) else 0)
    simp only [if_pos hj]
    exact (continuous_lawWeight i).comp (continuous_const.prodMk
      ((continuous_apply j).comp (continuous_ordinary row a)))
  · change Continuous (fun b : Fin M → ℝ => if j ∈ row.lower then lawWeight i G (ordinary row b a j) else 0)
    simp only [if_neg hj]
    exact continuous_const

omit [NeZero M] in
theorem measurable_ordinary_seedCount (i : Row) (row : CountRow M) (a : Fin M) :
    Measurable (fun b => seedCount i row (ordinary row b a)) := by
  have he (b : Fin M → ℝ) : seedCount i row (ordinary row b a)=
      ∑j ∈ row.lower,if ordinary row b a j ≤ t i/2 then (1:ℕ) else 0 := by
    unfold seedCount
    rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp_rw [he]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_le
    (((continuous_apply j).comp (continuous_ordinary row a)).measurable) measurable_const)
    measurable_const measurable_const

omit [NeZero M] in
theorem measurable_alpha (i : Row) (G : RestrictedLaw i) (row : CountRow M) (a : Fin M) :
    Measurable (fun b => alpha i G row b a) := by
  apply Measurable.ite
  · exact (measurableSet_le (measurable_pi_apply a) measurable_const).inter
      ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (measurableSet_lt measurable_const (measurable_ordinary_seedCount i row a))))
  · exact ((continuous_rawAlpha i row).comp
      (continuous_const.prodMk (continuous_ordinary row a))).measurable
  · exact measurable_const

theorem measurable_canonicalLaw_mass (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (a : Fin M) (S : Allocation M) : Measurable (fun b => (canonicalLaw i G row b a).mass S) := by
  unfold canonicalLaw FiniteLaw.map
  simp only [conditionalCompletion,FiniteLaw.prod]
  apply Finset.measurable_sum
  intro x _
  by_cases hx : orient row x.2=S
  · simp only [if_pos hx]
    exact ((Literal.measurable_path_mass (imbalance row) ∅ x.1).comp
      (continuous_weight i G row a).measurable).mul
      (((measurable_largeCompletion_mass (xi_range i).1 (xi_range i).2 (small row) _ _).comp
        (continuous_lowerBids row).measurable).mul
       ((measurable_completion_mass (xi_range i).1 (xi_range i).2 (small row) _ _).comp
        (continuous_lowerBids row).measurable))
  · simp only [if_neg hx]
    exact measurable_const

theorem measurable_continuationLaw_mass (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (a : Fin M) (S : Allocation M) : Measurable (fun b => (continuationLaw i G row b a).mass S) := by
  have hEq (T : Finset (Fin M)) : Measurable (fun b => (UniformFinite.equalLottery i row b).mass T) :=
    (ExactCapacity.measurable_symmetricLottery_mass T).comp
      ((EqualCapacity.measurable_positiveMarginal (xi i) (small row) (xi_range i).1 (xi_range i).2).comp
        (continuous_lowerBids row).measurable)
  have hPure : Measurable (fun b => (UniformFinite.pureLaw i row b).mass S) := by
    have hm := ((lowerTemplate row).measurable_selection (kappa i)).comp
      (continuous_lowerBids row).measurable
    unfold UniformFinite.pureLaw FiniteLaw.dirac
    dsimp only
    exact Measurable.ite (measurableSet_eq_fun measurable_const hm) measurable_const measurable_const
  unfold continuationLaw
  by_cases he : residual row 0=residual row 1
  · simp only [if_pos he]
    exact (hEq S.1).mul (hEq S.2)
  · simp only [if_neg he,FiniteLaw.mixture]
    exact ((measurable_alpha i G row a).mul (measurable_canonicalLaw_mass i G row a S)).add
      ((measurable_const.sub (measurable_alpha i G row a)).mul hPure)

theorem measurable_rowPayoff (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (v : ℝ) (a : Fin M) : Measurable (fun b => rowPayoff i G row v b a) := by
  unfold rowPayoff FiniteLaw.expect
  apply Finset.measurable_sum
  intro P _
  apply (measurable_continuationLaw_mass i G row a P).mul
  unfold pairPayoff
  exact ((measurable_const.sub (measurable_pi_apply a)).mul measurable_const).sub
    ((measurable_const.mul (measurable_pi_apply a)).mul measurable_const)

theorem canonicalLaw_equal (i : Row) (G : RestrictedLaw i) (row : CountRow M)
    (b : Fin M → ℝ) (a : Fin M) (heq : residual row 0=residual row 1) :
    canonicalLaw i G row b a=UniformFinite.equalLaw i row b := by
  have hD : imbalance row=0 := by simp [imbalance,large,small,heq]
  have hE (p : Path (Fin M) (imbalance row)) : finalSet (imbalance row) ∅ p=∅ := by
    have hzero (n : ℕ) (hn : n=0) (p : Path (Fin M) n) : finalSet n ∅ p=∅ := by
      subst n
      rfl
    exact hzero _ hD p
  have hor (P : Allocation M) : orient row P=P := by simp [orient,heq]
  have he : conditionalCompletion (xi i) (small row) (lowerBids row b) ∅=
      UniformFinite.equalLaw i row b := by
    have hm (P : FiniteLaw (Finset (Fin M))) : P.map (fun S => (∅:Finset (Fin M)) ∪ S)=P := by
      apply FiniteLaw.ext_expect
      intro f
      rw [FiniteLaw.expect_map]
      simp
    have hb : masked (lowerBids row b) ∅=lowerBids row b := by funext j; simp [masked]
    unfold conditionalCompletion largeCompletion completion UniformFinite.equalLaw UniformFinite.equalLottery
    rw [hm,hb]
  apply FiniteLaw.ext_expect
  intro f
  rw [canonicalLaw,FiniteLaw.expect_map,WeightedSampling.expect_pairLaw]
  simp_rw [hor,hE,he]
  exact FiniteLaw.expect_const _ _

end Source
end FCAppendix.Affine.UniformFinite.Late.Exceptional
