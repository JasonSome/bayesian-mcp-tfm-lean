import FCAppendix.Affine.Uniform06.EntrySignFiber
import FCAppendix.Affine.Uniform06.EntryActiveMoments
import FCAppendix.Affine.Uniform06.LiteralExperiment

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryLiteralDeficit
open Set MeasureTheory
open FCAppendix.Affine.LowBody FCAppendix.Affine.ClippedResidual
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.EntryUntilting
open FCAppendix.Affine.Uniform06.EntryRenewal
open FCAppendix.Affine.Uniform06.EntryParityRenewal
open FCAppendix.Affine.Uniform06.EntryConditionalRelative
open FCAppendix.Affine.Uniform06.EntrySignFiber
open scoped BigOperators

variable {N : ℕ}

def lowerCount (low : Fin N → Bool) : ℕ := ∑ j, if low j then 1 else 0

lemma classCount_zero (low sign : Fin N → Bool) :
    classCount 0 (patternRow (fun j => tag (low j,sign j)))=lowerCount low := by
  apply Finset.sum_congr rfl
  intro j _
  cases hL : low j <;> cases hS : sign j <;> simp [patternRow,tag,hL,hS]

def bids (b : ℝ) (low : Fin N → Bool) (B : Fin N → ℝ) : Fin (N+1) → ℝ :=
  Fin.cons b (fun j => if low j then B j else 0)

def support (low : Fin N → Bool) : Finset (Fin (N+1)) :=
  Finset.univ.filter (fun j => Fin.cases true (fun r => low r) j=true)

lemma template_support (c : ℕ) (low sign : Fin N → Bool) :
    (patternTemplate c (fun j => tag (low j,sign j))).support=support low := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [patternTemplate,support,rowLowList,patternRow]
  · cases hL : low j <;> cases hS : sign j <;>
      simp [patternTemplate,support,rowLowList,patternRow,tag,hL,hS]

lemma rowBids_mask (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    rowBids b (fun j => rawRowPoint (tag (low j,sign j),B j))=bids b low B := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  cases hL : low j <;> cases hS : sign j <;>
    simp [rowBids,bids,rawRowPoint,tag,hL,hS]

theorem residuals_unclipped (c : ℕ) (low sign : Fin N → Bool)
    (hH : (upperSet low).card ≤ c) (hL : c ≤ lowerCount low+1) :
    (patternTemplate c (fun j => tag (low j,sign j))).residual₀=c-positiveCount low sign ∧
    (patternTemplate c (fun j => tag (low j,sign j))).residual₁=
      c-((upperSet low).card-positiveCount low sign) := by
  have hp := PiBinomial.count_le ({true}:Set Bool) (upperSet low) sign
  change positiveCount low sign ≤ (upperSet low).card at hp
  constructor
  · change min (1+classCount 0 (patternRow (fun j => tag (low j,sign j))))
      (c-classCount 1 (patternRow (fun j => tag (low j,sign j)))-
        classCount 2 (patternRow (fun j => tag (low j,sign j))))=_
    rw [classCount_zero,classCount_one,classCount_two,Nat.sub_zero,min_eq_right (by omega)]
  · change min (1+classCount 0 (patternRow (fun j => tag (low j,sign j))))
      (c-classCount 1 (patternRow (fun j => tag (low j,sign j)))-
        classCount 3 (patternRow (fun j => tag (low j,sign j))))=_
    rw [classCount_zero,classCount_one,classCount_three,Nat.sub_zero,min_eq_right (by omega)]

lemma residual_min_nat (c H r : ℕ) (hr : r ≤ H) (hH : H ≤ c) :
    min (c-r) (c-(H-r))=c-max r (H-r) := by
  by_cases h : r ≤ H-r
  · rw [max_eq_right h,min_eq_right (by omega)]
  · rw [max_eq_left (by omega),min_eq_left (by omega)]

lemma residual_imbalance_nat (c H r : ℕ) (hr : r ≤ H) (hH : H ≤ c) :
    max (c-r) (c-(H-r))-min (c-r) (c-(H-r))=imbalance H r := by
  unfold imbalance
  split_ifs with h
  · rw [max_eq_right (by omega),min_eq_left (by omega)]
    omega
  · rw [max_eq_left (by omega),min_eq_right (by omega)]
    omega

theorem small_template (c : ℕ) (low sign : Fin N → Bool)
    (hH : (upperSet low).card ≤ c) (hL : c ≤ lowerCount low+1) :
    LiteralExperiment.small (patternTemplate c (fun j => tag (low j,sign j)))=
      c-max (positiveCount low sign) ((upperSet low).card-positiveCount low sign) := by
  have hr := residuals_unclipped c low sign hH hL
  rw [LiteralExperiment.small,hr.1,hr.2]
  exact residual_min_nat _ _ _ (PiBinomial.count_le _ _ _) hH

theorem imbalance_template (c : ℕ) (low sign : Fin N → Bool)
    (hH : (upperSet low).card ≤ c) (hL : c ≤ lowerCount low+1) :
    LiteralExperiment.imbalance (patternTemplate c (fun j => tag (low j,sign j)))=
      imbalance (upperSet low).card (positiveCount low sign) := by
  have hr := residuals_unclipped c low sign hH hL
  rw [LiteralExperiment.imbalance,LiteralExperiment.small,hr.1,hr.2]
  exact residual_imbalance_nat _ _ _ (PiBinomial.count_le _ _ _) hH

lemma cast_imbalance (H r : ℕ) (hr : r ≤ H) :
    (imbalance H r : ℝ)=|(r : ℝ)-((H-r : ℕ):ℝ)| := by
  have hrR : (r : ℝ) ≤ H := by exact_mod_cast hr
  rw [Nat.cast_sub hr]
  unfold imbalance
  split_ifs with h
  · have hR : (H : ℝ) ≤ 2*r := by exact_mod_cast h
    rw [Nat.cast_sub h,Nat.cast_mul,Nat.cast_ofNat,abs_of_nonneg (by linarith)]
    ring
  · have h' : 2*r ≤ H := by omega
    have hR : 2*(r : ℝ) ≤ H := by exact_mod_cast h'
    rw [Nat.cast_sub h',Nat.cast_mul,Nat.cast_ofNat,abs_of_nonpos (by linarith)]
    ring

def weights (ξ : ℝ) (g : LiteralExperiment.GuardData) (b : ℝ) (low : Fin N → Bool)
    (B : Fin N → ℝ) : Weights (Fin (N+1)) :=
  ⟨fun j => if j ∈ support low then
      FiniteGuards.eligibility ξ g.multiplier g.requiredDemand (bids b low B j) else 0,
    by intro j; dsimp only; split_ifs; exact FiniteGuards.eligibility_bounds _ _ _ _; norm_num⟩

theorem weights_template (ξ : ℝ) (g : LiteralExperiment.GuardData) (c : ℕ) (b : ℝ)
    (low sign : Fin N → Bool) (B : Fin N → ℝ) :
    LiteralExperiment.weights ξ g (patternTemplate c (fun j => tag (low j,sign j))) (bids b low B)=
      weights ξ g b low B := by
  apply Subtype.ext
  funext j
  simp only [LiteralExperiment.weights,weights,template_support]

def hvector (ξ b : ℝ) (low : Fin N → Bool) (B : Fin N → ℝ) (j : Fin (N+1)) : ℝ :=
  1/2-exposure ξ b (bids b low B j)

def rawDeficit (ξ b : ℝ) (c : ℕ) (low : Fin N → Bool) (B : Fin N → ℝ) : ℝ :=
  (c : ℝ)-(upperSet low).card/2-∑ j ∈ support low, exposure ξ b (bids b low B j)

theorem hvector_bounds {ξ b U a : ℝ} (hξ : 0 < ξ) (hb : 0 < b)
    (_ha : 0 < a) (ha2 : a ≤ 1/2) (hU : 0 ≤ U) (hbf : b ≤ U)
    (hgap : (1-ξ*(1/2-a))*U ≤ b) (hfactor : 0 ≤ 1-ξ*(1/2-a))
    (low : Fin N → Bool) (B : Fin N → ℝ) (hB : ∀ j, B j ≤ U) :
    ∀ j, hvector ξ b low B j ∈ Icc a (1/2:ℝ) := by
  intro j
  have hBU : bids b low B j ≤ U := by
    refine Fin.cases hbf (fun j => ?_) j
    cases hL : low j <;> simp [bids,hL,hU,hB j]
  have hp := EntryActiveMoments.exposure_upper_of_linear_guard hξ hb
    (show 0 ≤ (1/2:ℝ)-a by linarith) hfactor hBU hgap
  constructor
  · dsimp [hvector]
    linarith
  · dsimp [hvector]
    linarith [exposure_nonneg (b := bids b low B j) hξ hb]

lemma sampled_subset_support (ξ : ℝ) (g : LiteralExperiment.GuardData) (b : ℝ)
    (low : Fin N → Bool) (B : Fin N → ℝ) (d : ℕ)
    (hW : (d : ℝ) < totalWeight (weights ξ g b low B))
    (path : Path (Fin (N+1)) d)
    (hp : 0 < (pathLaw (weights ξ g b low B) d ∅).mass path) :
    finalSet d ∅ path ⊆ support low := by
  intro j hj
  have hw := finalSet_weight_pos (weights ξ g b low B) d ∅
    (by simpa using hW) (by simp) path hp j hj
  by_contra hj'
  simp [weights,hj'] at hw

theorem exact_literal_deficit (ξ : ℝ) (g : LiteralExperiment.GuardData) (c : ℕ) (b : ℝ)
    (low sign : Fin N → Bool) (B : Fin N → ℝ)
    (hH : (upperSet low).card ≤ c) (hL : c ≤ lowerCount low+1)
    (hW : (imbalance (upperSet low).card (positiveCount low sign) : ℝ) <
      totalWeight (weights ξ g b low B))
    (path : Path (Fin (N+1)) (imbalance (upperSet low).card (positiveCount low sign)))
    (hp : 0 < (pathLaw (weights ξ g b low B)
      (imbalance (upperSet low).card (positiveCount low sign)) ∅).mass path) :
    (LiteralExperiment.small (patternTemplate c (fun j => tag (low j,sign j))) : ℝ)-
      (∑ j ∈ support low \ finalSet (imbalance (upperSet low).card (positiveCount low sign)) ∅ path,
        exposure ξ b (bids b low B j))=
      rawDeficit ξ b c low B-selectedSum (hvector ξ b low B)
        (imbalance (upperSet low).card (positiveCount low sign)) path := by
  let E := finalSet (imbalance (upperSet low).card (positiveCount low sign)) ∅ path
  let p := fun j => exposure ξ b (bids b low B j)
  have hES : E ⊆ support low := sampled_subset_support ξ g b low B _ hW path hp
  have hc := finalSet_card (weights ξ g b low B) _ ∅ (by simpa using hW) path hp
  have hcard : (E.card : ℝ)=|(positiveCount low sign : ℝ)-
      (((upperSet low).card-positiveCount low sign : ℕ):ℝ)| := by
    dsimp [E]
    rw [hc]
    simpa using cast_imbalance (upperSet low).card (positiveCount low sign) (PiBinomial.count_le _ _ _)
  have hb := balanced_deficit_identity (c : ℝ) (positiveCount low sign)
    (((upperSet low).card-positiveCount low sign : ℕ):ℝ)
    (∑ j ∈ support low, p j) E p hcard
  have hs := Finset.sum_inter_add_sum_sdiff (support low) E p
  rw [Finset.inter_eq_right.mpr hES] at hs
  have hsum := selectedSum_eq_setSum (weights ξ g b low B) (hvector ξ b low B)
    _ ∅ (by simpa using hW) path hp
  simp only [Finset.sum_empty,sub_zero] at hsum
  have hcount : positiveCount low sign ≤ (upperSet low).card := PiBinomial.count_le _ _ _
  have hmax : max (positiveCount low sign) ((upperSet low).card-positiveCount low sign) ≤ c := by omega
  rw [small_template c low sign hH hL,Nat.cast_sub hmax,Nat.cast_max]
  rw [hsum]
  unfold postDeficit preDeficit at hb
  rw [Nat.cast_sub hcount] at hb ⊢
  dsimp [rawDeficit,hvector,p,E] at *
  nlinarith [hb,hs]

theorem literal_relative_moment_bound (ξ : ℝ) (g : LiteralExperiment.GuardData)
    (c : ℕ) (b : ℝ) (low : Fin N → Bool) (B : Fin N → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ j, hvector ξ b low B j ∈ Icc a A)
    {n J K k e : ℕ} (hH : (upperSet low).card=2*n+e)
    (hn : 0 < n) (he : e ≤ 1) (hk : k ≤ 2) (hJn : J ≤ n+1) (hK : 2*J+1 ≤ K)
    (hW : 0 < totalWeight (weights ξ g b low B))
    (hhalf : 2*(K : ℝ) ≤ totalWeight (weights ξ g b low B))
    (hsA : A < rawDeficit ξ b c low B) (hs : rawDeficit ξ b c low B ≤ 2*a*J)
    (hsmall : (J : ℝ)*((J : ℝ)+e)/n ≤ 1)
    (hdrift : 4*A*K/totalWeight (weights ξ g b low B) ≤ a/2) :
    |((CommonList.iid fairSign N).expect (fun sign =>
        (pathLaw (weights ξ g b low B) (imbalance (upperSet low).card (positiveCount low sign)) ∅).expect
          (fun path => deficitMoment k (rawDeficit ξ b c low B-selectedSum (hvector ξ b low B)
            (imbalance (upperSet low).card (positiveCount low sign)) path)))) /
      (PiBinomial.pmf (2*n+e) (1/2) (n+e)*potential k (rawDeficit ξ b c low B)/
        WeightedMoments.weightedMean (weights ξ g b low B) (hvector ξ b low B))-1| ≤
        (J : ℝ)*((J : ℝ)+e)/n+2*(4*A*K/totalWeight (weights ξ g b low B))/a+
          52*A/rawDeficit ξ b c low B := by
  rw [actual_sign_fiber_moment,hH]
  exact relative_error_bound (weights ξ g b low B) (hvector ξ b low B) ha hh
    hn he hk hJn hK hW hhalf hsA hs hsmall hdrift

theorem residuals_unclipped_of_route_counts (c : ℕ) (low sign : Fin N → Bool)
    (_h0 : positiveCount low sign ≤ c)
    (_h1 : (upperSet low).card-positiveCount low sign ≤ c)
    (hl0 : c-positiveCount low sign ≤ lowerCount low+1)
    (hl1 : c-((upperSet low).card-positiveCount low sign) ≤ lowerCount low+1) :
    (patternTemplate c (fun j => tag (low j,sign j))).residual₀=c-positiveCount low sign ∧
    (patternTemplate c (fun j => tag (low j,sign j))).residual₁=
      c-((upperSet low).card-positiveCount low sign) := by
  constructor
  · change min (1+classCount 0 (patternRow (fun j => tag (low j,sign j))))
      (c-classCount 1 (patternRow (fun j => tag (low j,sign j)))-
        classCount 2 (patternRow (fun j => tag (low j,sign j))))=_
    rw [classCount_zero,classCount_one,classCount_two,Nat.sub_zero,min_eq_right (by omega)]
  · change min (1+classCount 0 (patternRow (fun j => tag (low j,sign j))))
      (c-classCount 1 (patternRow (fun j => tag (low j,sign j)))-
        classCount 3 (patternRow (fun j => tag (low j,sign j))))=_
    rw [classCount_zero,classCount_one,classCount_three,Nat.sub_zero,min_eq_right (by omega)]

theorem small_template_of_route_counts (c : ℕ) (low sign : Fin N → Bool)
    (h0 : positiveCount low sign ≤ c)
    (h1 : (upperSet low).card-positiveCount low sign ≤ c)
    (hl0 : c-positiveCount low sign ≤ lowerCount low+1)
    (hl1 : c-((upperSet low).card-positiveCount low sign) ≤ lowerCount low+1) :
    LiteralExperiment.small (patternTemplate c (fun j => tag (low j,sign j)))=
      c-max (positiveCount low sign) ((upperSet low).card-positiveCount low sign) := by
  have hh := residuals_unclipped_of_route_counts c low sign h0 h1 hl0 hl1
  rw [LiteralExperiment.small,hh.1,hh.2]
  omega

theorem imbalance_template_of_route_counts (c : ℕ) (low sign : Fin N → Bool)
    (h0 : positiveCount low sign ≤ c)
    (h1 : (upperSet low).card-positiveCount low sign ≤ c)
    (hl0 : c-positiveCount low sign ≤ lowerCount low+1)
    (hl1 : c-((upperSet low).card-positiveCount low sign) ≤ lowerCount low+1) :
    LiteralExperiment.imbalance (patternTemplate c (fun j => tag (low j,sign j)))=
      imbalance (upperSet low).card (positiveCount low sign) := by
  have hh := residuals_unclipped_of_route_counts c low sign h0 h1 hl0 hl1
  have hr : positiveCount low sign ≤ (upperSet low).card := PiBinomial.count_le _ _ _
  rw [LiteralExperiment.imbalance,LiteralExperiment.small,hh.1,hh.2]
  unfold imbalance
  split_ifs <;> omega

theorem route_counts_of_imbalance_window {H r L c K : ℕ} (hr : r ≤ H)
    (hlower : H+K ≤ 2*c) (hupper : 2*c+K ≤ 2*(L+1)+H)
    (hwindow : imbalance H r ≤ K) :
    r ≤ c ∧ H-r ≤ c ∧ c-r ≤ L+1 ∧ c-(H-r) ≤ L+1 := by
  unfold imbalance at hwindow
  split_ifs at hwindow <;> omega

theorem exact_literal_deficit_of_route_counts (ξ : ℝ) (g : LiteralExperiment.GuardData)
    (c : ℕ) (b : ℝ) (low sign : Fin N → Bool) (B : Fin N → ℝ)
    (h0 : positiveCount low sign ≤ c)
    (h1 : (upperSet low).card-positiveCount low sign ≤ c)
    (hl0 : c-positiveCount low sign ≤ lowerCount low+1)
    (hl1 : c-((upperSet low).card-positiveCount low sign) ≤ lowerCount low+1)
    (hW : (imbalance (upperSet low).card (positiveCount low sign) : ℝ) <
      totalWeight (weights ξ g b low B))
    (path : Path (Fin (N+1)) (imbalance (upperSet low).card (positiveCount low sign)))
    (hp : 0 < (pathLaw (weights ξ g b low B)
      (imbalance (upperSet low).card (positiveCount low sign)) ∅).mass path) :
    (LiteralExperiment.small (patternTemplate c (fun j => tag (low j,sign j))) : ℝ)-
      (∑ j ∈ support low \ finalSet (imbalance (upperSet low).card (positiveCount low sign)) ∅ path,
        exposure ξ b (bids b low B j))=
      rawDeficit ξ b c low B-selectedSum (hvector ξ b low B)
        (imbalance (upperSet low).card (positiveCount low sign)) path := by
  let E := finalSet (imbalance (upperSet low).card (positiveCount low sign)) ∅ path
  let p := fun j => exposure ξ b (bids b low B j)
  have hES : E ⊆ support low := sampled_subset_support ξ g b low B _ hW path hp
  have hc := finalSet_card (weights ξ g b low B) _ ∅ (by simpa using hW) path hp
  have hcount : positiveCount low sign ≤ (upperSet low).card := PiBinomial.count_le _ _ _
  have hcard : (E.card : ℝ)=|(positiveCount low sign : ℝ)-
      (((upperSet low).card-positiveCount low sign : ℕ):ℝ)| := by
    dsimp [E]
    rw [hc]
    simpa using cast_imbalance (upperSet low).card (positiveCount low sign) hcount
  have hb := balanced_deficit_identity (c : ℝ) (positiveCount low sign)
    (((upperSet low).card-positiveCount low sign : ℕ):ℝ) (∑ j ∈ support low, p j) E p hcard
  have hs := Finset.sum_inter_add_sum_sdiff (support low) E p
  rw [Finset.inter_eq_right.mpr hES] at hs
  have hsum := selectedSum_eq_setSum (weights ξ g b low B) (hvector ξ b low B)
    _ ∅ (by simpa using hW) path hp
  simp only [Finset.sum_empty,sub_zero] at hsum
  have hmax : max (positiveCount low sign) ((upperSet low).card-positiveCount low sign) ≤ c :=
    max_le h0 h1
  rw [small_template_of_route_counts c low sign h0 h1 hl0 hl1,Nat.cast_sub hmax,Nat.cast_max,hsum]
  unfold postDeficit preDeficit at hb
  rw [Nat.cast_sub hcount] at hb ⊢
  dsimp [rawDeficit,hvector,p,E] at *
  nlinarith [hb,hs]

theorem moment_zero_outside_count_window (ξ : ℝ) (c : ℕ) (b : ℝ)
    (low sign : Fin N → Bool) (B : Fin N → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hh : ∀ j, a ≤ hvector ξ b low B j) (K k : ℕ)
    (hW : rawDeficit ξ b c low B ≤ a*K)
    (hd : K < imbalance (upperSet low).card (positiveCount low sign))
    (p : Path (Fin (N+1)) (imbalance (upperSet low).card (positiveCount low sign))) :
    deficitMoment k (rawDeficit ξ b c low B-selectedSum (hvector ξ b low B)
      (imbalance (upperSet low).card (positiveCount low sign)) p)=0 := by
  have hs := selectedSum_lower (hvector ξ b low B) hh _ p
  have hKr : (K:ℝ) ≤ imbalance (upperSet low).card (positiveCount low sign) := by
    exact_mod_cast hd.le
  have hnon : rawDeficit ξ b c low B-selectedSum (hvector ξ b low B)
      (imbalance (upperSet low).card (positiveCount low sign)) p ≤ 0 := by
    nlinarith [mul_le_mul_of_nonneg_left hKr ha]
  exact deficitMoment_eq_zero_of_nonpos k hnon

end FCAppendix.Affine.Uniform06.EntryLiteralDeficit
