import FCAppendix.Affine.Tail04.AllCountHighPolicy
import FCAppendix.Affine.Tail04.PrivatePayoffContinuity
import FCAppendix.Affine.Tail04.PrivateRowSorting
import FCAppendix.Affine.Tail04.JoinedPartialNoisy

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivatePartialSorting
open MeasureTheory ProbabilityTheory Set Classical
open scoped BigOperators
open EqualPrivateSignal EqualPrivateUpper PrivatePayoffContinuity

local instance (J : Type*) : TopologicalSpace (Finset J) := ⊥
local instance (J : Type*) : DiscreteTopology (Finset J) := ⟨rfl⟩
local instance (J : Type*) : MeasurableSpace (Finset J) := ⊤
local instance (J : Type*) : BorelSpace (Finset J) := ⟨borel_eq_top_of_discrete.symm⟩

def targetEquiv (N : ℕ) {H : ℕ} (σ : Equiv.Perm (Fin H)) :
    Target N H ≃ Target N H := Equiv.sumCongr (Equiv.refl _) σ

def reindexRow {H : ℕ} {R V Rm : ℝ} (σ : Equiv.Perm (Fin H))
    (row : Row H R V Rm) : Row H R V Rm := fun k => row (σ k)

@[simp] lemma targetEquiv_inl (N : ℕ) {H : ℕ} (σ : Equiv.Perm (Fin H))
    (i : Fin N) : targetEquiv N σ (Sum.inl i)=Sum.inl i := rfl

@[simp] lemma targetEquiv_inr (N : ℕ) {H : ℕ} (σ : Equiv.Perm (Fin H))
    (j : Fin H) : targetEquiv N σ (Sum.inr j)=Sum.inr (σ j) := rfl

lemma optimal_map_equiv {J K : Type*} (e : J ≃ K) (c : ℕ) (r : K → ℝ)
    (S : Finset J) (hS : Finite.Optimal c (r ∘ e) S) :
    Finite.Optimal c r (S.map e.toEmbedding) := by
  refine ⟨by simpa using hS.1,?_⟩
  intro T hT
  have hh := hS.2 (T.map e.symm.toEmbedding) (by simpa using hT)
  simpa [Function.comp_def] using hh

lemma receipt_reindex {N H : ℕ} {R V Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (σ : Equiv.Perm (Fin H))
    (row : Row H R V Rm) :
    receipt b q ξ (reindexRow σ row)=receipt b q ξ row ∘ targetEquiv N σ := by
  funext x
  cases x <;> rfl

lemma mem_map_private {N H : ℕ} (σ : Equiv.Perm (Fin H))
    (S : Finset (Target N H)) (j : Fin H) :
    Sum.inr j∈S.map (targetEquiv N σ).toEmbedding ↔ Sum.inr (σ.symm j)∈S := by
  constructor
  · intro hj
    obtain ⟨x,hx,he⟩ := Finset.mem_map.mp hj
    have hxj : x=Sum.inr (σ.symm j) := by
      apply (targetEquiv N σ).injective
      simpa using he
    simpa only [hxj] using hx
  · intro hj
    exact Finset.mem_map.mpr ⟨Sum.inr (σ.symm j),hj,by simp⟩

lemma restore_private_iff {N H c : ℕ} {R V Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R V Rm)
    (a : Action N H c) (j : Fin H) (price : Icc R V) (hj : row j=Sum.inr price) :
    Sum.inr j∈restore b q ξ row a ↔ Sum.inr j∈selected (signal row) a := by
  have hu : Sum.inr j∉upperSelection c b q ξ row := by
    intro h
    have hp := (AtypicalUnequal.topSelection_feasible (upperPool N row) c
      (receipt b q ξ row)).2 h
    simp [upperPool,signal,signalEntry,hj,isUpper] at hp
  simp only [restore,Finset.mem_union,hu,false_or]

lemma full_regular {N H : ℕ} {R V Rm : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (row : Row H R V Rm)
    (j : Fin H) (price : Icc R V) (hj : row j=Sum.inr price)
    (hfloor : V< Rm) (hreg : (b,q,signal row)∈Regular ξ j) :
    0< receipt b q ξ row (Sum.inr j) ∧
      ∀ x : Target N H,x≠Sum.inr j → receipt b q ξ row x≠receipt b q ξ row (Sum.inr j) := by
  have hprice : partialBid (signal row j)=(price:ℝ) := by
    simp [signal,signalEntry,hj,partialBid]
  refine ⟨by simpa [receipt,hj,numericalEntry,←hprice] using hreg.1,?_⟩
  intro x hx
  cases x with
  | inl i =>
    simpa [receipt,hj,numericalEntry,hprice,itemReceipt] using hreg.2 (Sum.inl i) hx
  | inr k =>
    cases hk : row k with
    | inl upper =>
      have hp : (price:ℝ)<(upper:ℝ) := price.2.2.trans_lt (hfloor.trans_le upper.2)
      simpa [receipt,hj,hk,numericalEntry] using hp.ne'
    | inr partialBidValue =>
      simpa [receipt,hj,hk,numericalEntry,itemReceipt,signal,signalEntry,partialBid]
        using hreg.2 (Sum.inr k) hx

theorem reindexed_optimum_privateValue {N H c : ℕ} {R V Rm B : ℝ}
    (b q : Fin N → ℝ) (ξ : ℝ) (σ : Equiv.Perm (Fin H))
    (row : Row H R V Rm) (S : Finset (Target N H))
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,b i∈Icc (0:ℝ) B)
    (hq : ∀ i,q i∈Icc (0:ℝ) 1) (hR : 0≤ R) (hVB : V≤ B)
    (hBRm : B< Rm) (hRm : 0< Rm)
    (hS : Finite.Optimal c (receipt b q ξ (reindexRow σ row)) S)
    (j : Fin H) (price : Icc R V) (hj : row j=Sum.inr price)
    (hreg : (b,q,signal row)∈Regular ξ j) :
    (if Sum.inr (σ.symm j)∈S then (1:ℝ) else 0)=
      privateValue (c:=c) ξ j (b,q,signal row) := by
  let a : Action N H c := chosen ξ (b,q,signal row)
  let T := restore b q ξ row a
  have hT : Finite.Optimal c (receipt b q ξ row) T := by
    apply restore_optimal b q ξ row a hξ hb hq hR hVB hBRm hRm
    exact residualOptimal_of_best ξ _ a (chosen_best ξ _)
  have hpull : Finite.Optimal c (receipt b q ξ row)
      (S.map (targetEquiv N σ).toEmbedding) := by
    apply optimal_map_equiv (targetEquiv N σ) c (receipt b q ξ row) S
    simpa only [←receipt_reindex] using hS
  have hr := full_regular b q ξ row j price hj (hVB.trans_lt hBRm) hreg
  have he : Sum.inr (σ.symm j)∈S ↔ Sum.inr j∈selected (signal row) a := by
    rw [←mem_map_private σ S j,
      membership_iff_strictRank_of_noTie c _ _ hpull _ hr.1 hr.2,
      ←membership_iff_strictRank_of_noTie c _ T hT _ hr.1 hr.2,
      restore_private_iff b q ξ row a j price hj]
  change (if Sum.inr (σ.symm j)∈S then (1:ℝ) else 0)=
    if Sum.inr j∈selected (signal row) a then 1 else 0
  simp only [he]

theorem equalBase_reindexed_privateValue (N H c : ℕ) {ξ B R V Rm : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0≤ R) (hVB : V≤ B)
    (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R V 1 B) (row : Row H R V Rm)
    (σ : Equiv.Perm (Fin H)) (j : Fin H) (price : Icc R V)
    (hj : row j=Sum.inr price)
    (hreg : policyInput (c:=c) (ξ:=ξ) p (signal row)∈Regular ξ j)
    (u : unitInterval) :
    (if Sum.inr (σ.symm j)∈AllCountHighPolicy.equalBase N H c ξ B R V Rm
      hξ hR hVB hBRm hRm (p,reindexRow σ row) u then (1:ℝ) else 0)=
      privateValue (c:=c) ξ j (policyInput (c:=c) (ξ:=ξ) p (signal row)) := by
  apply reindexed_optimum_privateValue (EqualPrivateMeasurable.bids p)
    (policyMean N H c R V ξ 1 B p) ξ σ row _ hξ
    (fun i => ⟨(by norm_num : (0:ℝ)≤1).trans (p.1 i).2.1,(p.1 i).2.2⟩)
    (policyMean_bounds N H c R V ξ 1 B p) hR hVB hBRm hRm
    ((Classical.choose_spec (exists_equal_upper_sampler N H c R V Rm ξ 1 B
      hξ (by norm_num) hR hVB hBRm hRm)).2.2.2.1 p (reindexRow σ row) u)
    j price hj hreg

theorem equalBase_sorted_privateValue (E : Observable.Regions) (N H c : ℕ) {ξ : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1)
    (p : PolicyParameters N H E.R E.Rp 1 E.U) (row : Row H E.R E.Rp E.H)
    (j : Fin H) (price : Icc E.R E.Rp) (hj : row j=Sum.inr price)
    (hreg : policyInput (c:=c) (ξ:=ξ) p (signal row)∈Regular ξ j)
    (u : unitInterval) :
    (if Sum.inr ((PrivateRowSorting.permutation (fun k => LocalCoordinates.signalKey E (signal row k))).symm j)
      ∈AllCountHighPolicy.equalBase N H c ξ E.U E.R E.Rp E.H hξ
        (E.d_nonneg.trans E.d_lt_R.le) (E.Rp_lt_one.le.trans E.one_le_U) E.U_lt_H
        ((by norm_num : (0:ℝ)<1).trans_le (E.one_le_U.trans E.U_lt_H.le))
        (p,PrivateRowSorting.sortRow E H row) u then (1:ℝ) else 0)=
      privateValue (c:=c) ξ j (policyInput (c:=c) (ξ:=ξ) p (signal row)) :=
  equalBase_reindexed_privateValue N H c hξ _ _ _ _ p row _ j price hj hreg u

theorem ae_equalBase_reindexed_privateValue (N H c : ℕ) {ξ B R U eps Rm : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (row : Row H R (U*(1+eps)) Rm) (j : Fin H) (price : Icc R U)
    (σ : unitInterval → Equiv.Perm (Fin H)) :
    ∀ᵐ z : unitInterval ∂volume, ∀ u : unitInterval,
      (if Sum.inr ((σ z).symm j)∈AllCountHighPolicy.equalBase N H c ξ B R (U*(1+eps)) Rm
        hξ hR.le hVB hBRm hRm
        (p,reindexRow (σ z) (AtypicalPartialNoisy.noisyRow hR heps.le j price row z)) u
        then (1:ℝ) else 0)=
      privateValue (c:=c) ξ j
        (noisyInput hR heps.le j (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)) z) := by
  filter_upwards [ae_noisyInput_regular hR heps ξ j
    (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row))] with z hz
  intro u
  let price' : Icc R (U*(1+eps)) :=
    ⟨Hybrid.activeNoisyRealBid eps price z,Hybrid.activeNoisyRealBid_mem hR heps.le price z⟩
  have hs : signal (AtypicalPartialNoisy.noisyRow hR heps.le j price row z)=
      (noisyInput hR heps.le j (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)) z).2.2 := by
    funext k
    by_cases hkj : k=j
    · subst k
      simp [AtypicalPartialNoisy.noisyRow,noisyInput,signal,signalEntry,focalPolicyInput]
    · simp [AtypicalPartialNoisy.noisyRow,noisyInput,signal,signalEntry,Function.update_of_ne hkj,focalPolicyInput]
  have hh := equalBase_reindexed_privateValue N H c hξ hR.le hVB hBRm hRm p
    (AtypicalPartialNoisy.noisyRow hR heps.le j price row z) (σ z) j price'
    (by simp [AtypicalPartialNoisy.noisyRow,price']) (by simpa [policyInput,hs,noisyInput,
      focalPolicyInput] using hz) u
  simpa [policyInput,hs,noisyInput,focalPolicyInput] using hh

theorem equalBase_reindexed_smoothedInclusion (N H c : ℕ) {ξ B R U eps Rm : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (row : Row H R (U*(1+eps)) Rm) (j : Fin H) (price : Icc R U)
    (σ : unitInterval → Equiv.Perm (Fin H)) :
    (∫ z : unitInterval, ∫ u : unitInterval,
      if Sum.inr ((σ z).symm j)∈AllCountHighPolicy.equalBase N H c ξ B R (U*(1+eps)) Rm
        hξ hR.le hVB hBRm hRm
        (p,reindexRow (σ z) (AtypicalPartialNoisy.noisyRow hR heps.le j price row z)) u
        then (1:ℝ) else 0)=
      smoothedInclusion (c:=c) hR heps.le ξ j (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)) := by
  apply integral_congr_ae
  filter_upwards [ae_equalBase_reindexed_privateValue N H c hξ hR heps hVB hBRm hRm
    p row j price σ] with z hz
  simp_rw [hz]
  simp

theorem equalBase_reindexed_smoothedPayment (N H c : ℕ) {ξ B R U eps Rm : ℝ}
    (hξ : ξ∈Icc (0:ℝ) 1) (hR : 0< R) (heps : 0< eps)
    (hVB : U*(1+eps)≤ B) (hBRm : B< Rm) (hRm : 0< Rm)
    (p : PolicyParameters N H R (U*(1+eps)) 1 B)
    (row : Row H R (U*(1+eps)) Rm) (j : Fin H) (price : Icc R U)
    (σ : unitInterval → Equiv.Perm (Fin H)) :
    (∫ z : unitInterval, ∫ u : unitInterval, Hybrid.activeNoisyRealBid eps price z*
      (if Sum.inr ((σ z).symm j)∈AllCountHighPolicy.equalBase N H c ξ B R (U*(1+eps)) Rm
        hξ hR.le hVB hBRm hRm
        (p,reindexRow (σ z) (AtypicalPartialNoisy.noisyRow hR heps.le j price row z)) u
        then (1:ℝ) else 0))=
      smoothedPayment (c:=c) hR heps.le ξ j (focalPolicyInput (c:=c) (ξ:=ξ) p price (signal row)) := by
  apply integral_congr_ae
  filter_upwards [ae_equalBase_reindexed_privateValue N H c hξ hR heps hVB hBRm hRm
    p row j price σ] with z hz
  simp_rw [hz]
  simp [focalPolicyInput]

lemma rivalsAbove_reindex {H : ℕ} {R V : ℝ} (σ : Equiv.Perm (Fin H))
    (s : Signal H R V) (j : Fin H) (price : ℝ) :
    (AtypicalPartialNoisy.rivalsAbove (σ.symm j) price (fun k => s (σ k))).map σ.toEmbedding=
      AtypicalPartialNoisy.rivalsAbove j price s := by
  ext k
  constructor
  · intro hk
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨hlj,hlt⟩ := Finset.mem_filter.mp hl
    have hn : l≠σ.symm j := (Finset.mem_erase.mp hlj).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩,hlt⟩
    intro he
    exact hn ((Equiv.eq_symm_apply σ).mpr he)
  · intro hk
    obtain ⟨hkj,hkt⟩ := Finset.mem_filter.mp hk
    have hn : k≠j := (Finset.mem_erase.mp hkj).1
    apply Finset.mem_map.mpr
    refine ⟨σ.symm k,Finset.mem_filter.mpr ⟨?_,?_⟩,by simp⟩
    · apply Finset.mem_erase.mpr
      exact ⟨fun he => hn (σ.symm.injective he),Finset.mem_univ _⟩
    · simpa using hkt

lemma rivalsAbove_reindex_card {H : ℕ} {R V : ℝ} (σ : Equiv.Perm (Fin H))
    (s : Signal H R V) (j : Fin H) (price : ℝ) :
    (AtypicalPartialNoisy.rivalsAbove (σ.symm j) price (fun k => s (σ k))).card=
      (AtypicalPartialNoisy.rivalsAbove j price s).card := by
  rw [←Finset.card_map σ.toEmbedding, rivalsAbove_reindex]

lemma rankInclusion_reindex (N H0 H1 c : ℕ) {R V : ℝ} (side : Bool)
    (σ : Equiv.Perm (Fin (AllCountAtypical.ownCount H0 H1 side)))
    (s : Signal (AllCountAtypical.ownCount H0 H1 side) R V)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : ℝ) :
    AtypicalPartialNoisy.rankInclusion N H0 H1 c side (σ.symm j) (price,fun k => s (σ k))=
      AtypicalPartialNoisy.rankInclusion N H0 H1 c side j (price,s) := by
  simp only [AtypicalPartialNoisy.rankInclusion,rivalsAbove_reindex_card]

theorem unequal_reindexed_rank (N H0 H1 c : ℕ) {ξ B R V Rm : ℝ}
    (side : Bool) (b : Fin N → ℝ)
    (row : Row (AllCountAtypical.ownCount H0 H1 side) R V Rm)
    (σ : Equiv.Perm (Fin (AllCountAtypical.ownCount H0 H1 side)))
    (hξ : ξ∈Icc (0:ℝ) 1) (hb : ∀ i,b i∈Icc (1:ℝ) B)
    (hR : 0< R) (hRRm : R≤ Rm) (hV : V<1) (hgap : (1-ξ)*B< R) (hfloor : V< Rm)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R V)
    (hj : row j=Sum.inr price)
    (hno : ∀ k,k≠j → numericalEntry (row k)≠(price:ℝ)) :
    (if Sum.inr (σ.symm j)∈AllCountAtypical.select N H0 H1 c ξ b side
      (reindexRow σ row) then (1:ℝ) else 0)=
      AtypicalPartialNoisy.rankInclusion N H0 H1 c side j ((price:ℝ),signal row) := by
  have hno' (k : Fin (AllCountAtypical.ownCount H0 H1 side)) (hk : k≠σ.symm j) :
      numericalEntry (reindexRow σ row k)≠(price:ℝ) := by
    apply hno (σ k)
    intro he
    exact hk ((Equiv.eq_symm_apply σ).mpr he)
  rw [AtypicalPartialNoisy.actual_inclusion_eq_rank N H0 H1 c side b (reindexRow σ row)
    hξ hb hR hRRm hV hgap (σ.symm j) price (by simpa [reindexRow] using hj) hfloor hno']
  exact rankInclusion_reindex N H0 H1 c side σ (signal row) j price

theorem joined_reindexed_rank (N H0 H1 c : ℕ) {ξ B R V Rm width : ℝ}
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (p : JoinedHighPolicy.Parameters N H0 R V B)
    (row : Row (AllCountAtypical.ownCount H0 H1 side) R V Rm)
    (σ : Equiv.Perm (Fin (AllCountAtypical.ownCount H0 H1 side)))
    (hR : 0< R) (hRRm : R≤ Rm) (hV : V<1) (hgap : (1-ξ)*B< R) (hfloor : V< Rm)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R V)
    (hj : row j=Sum.inr price)
    (hno : ∀ k,k≠j → numericalEntry (row k)≠(price:ℝ)) (u : unitInterval) :
    (if Sum.inr (σ.symm j)∈JoinedPartialNoisy.unequalSide N H0 H1 c ξ B R V Rm width
      ν0 ν1 side (p,reindexRow σ row) u then (1:ℝ) else 0)=
      if JoinedHighPolicy.UseTypical N H0 H1 c ξ B R V width ν0 ν1 p then
        (if JoinedHighPolicy.regime p.1.1 then 0 else 1)
      else AtypicalPartialNoisy.rankInclusion N H0 H1 c side j ((price:ℝ),signal row) := by
  simp only [JoinedPartialNoisy.unequalSide_private N H0 H1 c ν0 ν1 side hξ hξ1 hw p
    (reindexRow σ row) (σ.symm j) price (by simpa [reindexRow] using hj) u]
  by_cases hu : JoinedHighPolicy.UseTypical N H0 H1 c ξ B R V width ν0 ν1 p
  · simp only [hu,ite_true]
    cases JoinedHighPolicy.regime p.1.1 <;> norm_num
  · simp only [hu,ite_false]
    exact unequal_reindexed_rank N H0 H1 c side (JoinedHighPolicy.publicBids p)
      row σ ⟨hξ.le,hξ1⟩ (fun i => (p.1.2 i).2) hR hRRm hV hgap hfloor j price hj hno

theorem ae_joined_reindexed_rank (N H0 H1 c : ℕ) {ξ B R U eps Rm width : ℝ}
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (side : Bool)
    (hξ : 0< ξ) (hξ1 : ξ≤1) (hw : 0< width)
    (p : JoinedHighPolicy.Parameters N H0 R (U*(1+eps)) B)
    (row : Row (AllCountAtypical.ownCount H0 H1 side) R (U*(1+eps)) Rm)
    (hR : 0< R) (heps : 0< eps) (hRRm : R≤ Rm) (hV : U*(1+eps)<1)
    (hgap : (1-ξ)*B< R) (hfloor : U*(1+eps)< Rm)
    (j : Fin (AllCountAtypical.ownCount H0 H1 side)) (price : Icc R U) :
    ∀ᵐ z : unitInterval ∂volume, ∀ σ : Equiv.Perm (Fin (AllCountAtypical.ownCount H0 H1 side)),
      ∀ u : unitInterval,
      (if Sum.inr (σ.symm j)∈JoinedPartialNoisy.unequalSide N H0 H1 c ξ B R (U*(1+eps)) Rm width
        ν0 ν1 side (p,reindexRow σ (AtypicalPartialNoisy.noisyRow hR heps.le j price row z)) u
        then (1:ℝ) else 0)=
      if JoinedHighPolicy.UseTypical N H0 H1 c ξ B R (U*(1+eps)) width ν0 ν1 p then
        (if JoinedHighPolicy.regime p.1.1 then 0 else 1)
      else AtypicalPartialNoisy.rankInclusion N H0 H1 c side j
        (AtypicalPartialNoisy.inputAt (price,signal row) z) := by
  have hn (k : Fin (AllCountAtypical.ownCount H0 H1 side)) :
      ∀ᵐ z : unitInterval ∂volume,k≠j →
        numericalEntry (AtypicalPartialNoisy.noisyRow hR heps.le j price row z k)≠
          Hybrid.activeNoisyRealBid eps price z := by
    filter_upwards [Hybrid.ae_activeNoisyRealBid_ne eps price (numericalEntry (row k))
      heps.ne' (hR.trans_le price.2.1).ne'] with z hz hkj
    simpa [AtypicalPartialNoisy.noisyRow,Function.update_of_ne hkj] using hz.symm
  filter_upwards [ae_all_iff.mpr hn] with z hz
  intro σ u
  let price' : Icc R (U*(1+eps)) :=
    ⟨Hybrid.activeNoisyRealBid eps price z,Hybrid.activeNoisyRealBid_mem hR heps.le price z⟩
  have hh := joined_reindexed_rank N H0 H1 c ν0 ν1 side hξ hξ1 hw p
    (AtypicalPartialNoisy.noisyRow hR heps.le j price row z) σ hR hRRm hV hgap hfloor j price'
    (by simp [AtypicalPartialNoisy.noisyRow,price']) hz u
  have hr : AtypicalPartialNoisy.rivalsAbove j (Hybrid.activeNoisyRealBid eps price z)
      (signal (AtypicalPartialNoisy.noisyRow hR heps.le j price row z))=
      AtypicalPartialNoisy.rivalsAbove j (Hybrid.activeNoisyRealBid eps price z) (signal row) := by
    ext k
    by_cases hkj : k=j
    · subst k
      simp [AtypicalPartialNoisy.rivalsAbove]
    · simp [AtypicalPartialNoisy.rivalsAbove,AtypicalPartialNoisy.noisyRow,
        signal,Function.update_of_ne hkj]
  simp only [AtypicalPartialNoisy.rankInclusion,price',hr] at hh
  convert! hh using 1

end FCAppendix.Affine.Tail04.PrivatePartialSorting
