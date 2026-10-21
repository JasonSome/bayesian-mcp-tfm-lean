import FCAppendix.Affine.CompleteInformationPotential
import FCAppendix.Affine.Hybrid.FiniteSelector
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
namespace FCAppendix.Affine.LowBody.SortedPotential
open Set
open scoped BigOperators

def topSet (L k : ℕ) : Finset (Fin L) := Finset.univ.filter (fun i=>i.val<k)

@[simp] lemma mem_prefix {L k : ℕ} (i : Fin L) : i∈topSet L k ↔ i.val<k := by
  simp [topSet]

lemma card_prefix {L k : ℕ} (hk : k≤L) : (topSet L k).card=k := by
  rw [topSet,Fin.card_filter_val_lt,Nat.min_eq_right hk]

lemma prefix_mono {L j k : ℕ} (h : j≤k) : topSet L j⊆topSet L k :=
  fun _ hi=>(mem_prefix _).mpr (lt_of_lt_of_le ((mem_prefix _).mp hi) h)

lemma prefix_inter {L j k : ℕ} : topSet L j∩topSet L k=topSet L (min j k) := by
  ext i
  simp only [Finset.mem_inter,mem_prefix,lt_min_iff]

lemma prefix_union {L j k : ℕ} : topSet L j∪topSet L k=topSet L (max j k) := by
  ext i
  simp only [Finset.mem_union,mem_prefix,lt_max_iff]

def prefixSum {L : ℕ} (b : Fin L→ℝ) (k : ℕ) : ℝ := ∑i∈topSet L k,b i

lemma prefix_optimal {L k : ℕ} (hk : k≤L) (b : Fin L→ℝ)
    (hb : ∀i,0≤b i) (hs : Antitone b) :
    Finite.Optimal k b (topSet L k) := by
  classical
  by_cases hz : k=0
  · subst k
    refine ⟨by simp [topSet],?_⟩
    intro T hT
    have ht : T=∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hT)
    simp [ht,topSet]
  · let j : Fin L := ⟨k-1,by omega⟩
    refine ⟨(card_prefix hk).le,?_⟩
    intro T hT
    apply FCAppendix.Affine.Hybrid.threshold_optimal b (topSet L k) T (b j) (hb j)
      (by rw [card_prefix hk];exact hT)
    · intro i hi
      apply hs
      change i.val≤k-1
      have := (mem_prefix _).mp hi
      omega
    · intro i hi
      apply hs
      change (k-1:ℕ) ≤ i.val
      have hnot : ¬ i.val < k := by simpa only [mem_prefix] using hi
      omega

lemma sum_le_prefixSum {L k : ℕ} (hk : k≤L) (b : Fin L→ℝ)
    (hb : ∀i,0≤b i) (hs : Antitone b) (T : Finset (Fin L)) (hT : T.card≤k) :
    (∑i∈T,b i)≤prefixSum b k := (prefix_optimal hk b hb hs).2 T hT

def FeasibleZ (L r0 r1 z : ℕ) : Prop := z≤ min r0 r1 ∧ r0+r1≤L+z

def objective {L : ℕ} (κ : ℝ) (b : Fin L→ℝ) (R z : ℕ) : ℝ :=
  prefixSum b (R-z)+κ*prefixSum b z

def canonicalPair (L r0 r1 z : ℕ) : Finset (Fin L) × Finset (Fin L) :=
  (topSet L r0,topSet L z ∪ (topSet L (r0+r1-z) \ topSet L r0))

lemma canonical_union {L r0 r1 z : ℕ} (hz : FeasibleZ L r0 r1 z) :
    (canonicalPair L r0 r1 z).1∪(canonicalPair L r0 r1 z).2=
      topSet L (r0+r1-z) := by
  have hz0 : z≤r0 := hz.1.trans (min_le_left _ _)
  have hz1 : z≤r1 := hz.1.trans (min_le_right _ _)
  ext i
  simp only [canonicalPair,Finset.mem_union,Finset.mem_sdiff,mem_prefix]
  omega

lemma canonical_inter {L r0 r1 z : ℕ} (hz : FeasibleZ L r0 r1 z) :
    (canonicalPair L r0 r1 z).1∩(canonicalPair L r0 r1 z).2=topSet L z := by
  have hz0 : z≤r0 := hz.1.trans (min_le_left _ _)
  ext i
  simp only [canonicalPair,Finset.mem_inter,Finset.mem_union,Finset.mem_sdiff,mem_prefix]
  omega

lemma canonical_card {L r0 r1 z : ℕ} (h0 : r0≤L) (_h1 : r1≤L)
    (hz : FeasibleZ L r0 r1 z) :
    (canonicalPair L r0 r1 z).1.card=r0 ∧ (canonicalPair L r0 r1 z).2.card=r1 := by
  have hz0 : z≤r0 := hz.1.trans (min_le_left _ _)
  have hz1 : z≤r1 := hz.1.trans (min_le_right _ _)
  have hR : r0+r1-z≤L := by have := hz.2;omega
  have hd : Disjoint (topSet L z) (topSet L (r0+r1-z) \ topSet L r0) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 (prefix_mono hz0 hi)
  constructor
  · exact card_prefix h0
  · change (topSet L z ∪ (topSet L (r0+r1-z) \ topSet L r0)).card=r1
    rw [Finset.card_union_of_disjoint hd,Finset.card_sdiff_of_subset (prefix_mono (by omega)),
      card_prefix (hz0.trans h0),card_prefix hR,card_prefix h0]
    omega

lemma canonical_potential {L r0 r1 z : ℕ} (κ : ℝ) (b : Fin L→ℝ)
    (hz : FeasibleZ L r0 r1 z) :
    CompleteInformation.potential κ b (canonicalPair L r0 r1 z).1
      (canonicalPair L r0 r1 z).2=objective κ b (r0+r1) z := by
  rw [CompleteInformation.potential,canonical_union hz,canonical_inter hz]
  rfl

lemma actual_duplicate_count {L r0 r1 : ℕ} (S T : Finset (Fin L))
    (hS : S.card=r0) (hT : T.card=r1) : FeasibleZ L r0 r1 (S∩T).card := by
  constructor
  · exact le_min ((Finset.card_le_card Finset.inter_subset_left).trans_eq hS)
      ((Finset.card_le_card Finset.inter_subset_right).trans_eq hT)
  · have hu : (S∪T).card≤L := by simpa using Finset.card_le_univ (S∪T)
    have hc := Finset.card_union_add_card_inter S T
    rw [hS,hT] at hc
    omega

lemma potential_le_objective {L r0 r1 : ℕ} (κ : ℝ) (hκ : 0≤κ)
    (b : Fin L→ℝ) (hb : ∀i,0≤b i) (hs : Antitone b)
    (S T : Finset (Fin L)) (hS : S.card=r0) (hT : T.card=r1) :
    CompleteInformation.potential κ b S T≤objective κ b (r0+r1) (S∩T).card := by
  have hc := Finset.card_union_add_card_inter S T
  rw [hS,hT] at hc
  have hU : (S∪T).card=r0+r1-(S∩T).card := by omega
  have hu : r0+r1-(S∩T).card≤L := by rw [←hU];simpa only [Fintype.card_fin] using Finset.card_le_univ (S∪T)
  have hi : (S∩T).card≤L := by simpa only [Fintype.card_fin] using Finset.card_le_univ (S∩T)
  unfold CompleteInformation.potential objective
  exact add_le_add (sum_le_prefixSum hu b hb hs (S∪T) hU.le)
    (mul_le_mul_of_nonneg_left (sum_le_prefixSum hi b hb hs (S∩T) le_rfl) hκ)

def bidAt {L : ℕ} (b : Fin L→ℝ) (k : ℕ) : ℝ := if h : k<L then b ⟨k,h⟩ else 0

lemma topSet_succ {L k : ℕ} (hk : k<L) :
    topSet L (k+1)=insert (⟨k,hk⟩ : Fin L) (topSet L k) := by
  ext i
  simp only [mem_prefix,Finset.mem_insert,Fin.ext_iff]
  omega

lemma prefixSum_succ {L k : ℕ} (b : Fin L→ℝ) (hk : k<L) :
    prefixSum b (k+1)=prefixSum b k+bidAt b k := by
  have hn : (⟨k,hk⟩ : Fin L)∉topSet L k := by simp
  rw [prefixSum,topSet_succ hk,Finset.sum_insert hn]
  simp only [bidAt,dif_pos hk]
  exact add_comm _ _

lemma objective_increment {L R z : ℕ} (κ : ℝ) (b : Fin L→ℝ)
    (hz : z<L) (hzR : z<R) (hR : R-z≤L) :
    objective κ b R (z+1)-objective κ b R z=
      κ*bidAt b z-bidAt b (R-z-1) := by
  have hidx : R-z-1<L := by omega
  have hstep := prefixSum_succ b hidx
  have heq : R-z-1+1=R-z := by omega
  have heq' : R-z-1=R-(z+1) := by omega
  rw [heq,heq'] at hstep
  unfold objective
  rw [prefixSum_succ b hz,hstep,←heq']
  ring

lemma increment_antitone {L R j k : ℕ} (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ)
    (hs : Antitone b) (hjk : j≤k) (hkL : k<L) (hkR : k<R) (hR : R-j≤L) :
    κ*bidAt b k-bidAt b (R-k-1)≤κ*bidAt b j-bidAt b (R-j-1) := by
  have hjL : j<L := lt_of_le_of_lt hjk hkL
  have hjR : j<R := lt_of_le_of_lt hjk hkR
  have hidxj : R-j-1<L := by omega
  have hidxk : R-k-1<L := by omega
  have hfirst : b ⟨k,hkL⟩≤b ⟨j,hjL⟩ := hs (by exact hjk)
  have hsecond : b ⟨R-j-1,hidxj⟩≤b ⟨R-k-1,hidxk⟩ := hs (by change R-k-1≤R-j-1;omega)
  simp only [bidAt,dif_pos hkL,dif_pos hjL,dif_pos hidxj,dif_pos hidxk]
  exact sub_le_sub (mul_le_mul_of_nonneg_left hfirst hκ) hsecond

lemma objective_discrete_concave {L R j k : ℕ} (κ : ℝ) (hκ : 0≤κ)
    (b : Fin L→ℝ) (hs : Antitone b) (hjk : j≤k)
    (hkL : k<L) (hkR : k<R) (hR : R-j≤L) :
    objective κ b R (k+1)-objective κ b R k≤
      objective κ b R (j+1)-objective κ b R j := by
  rw [objective_increment κ b hkL hkR (by omega),
    objective_increment κ b (lt_of_le_of_lt hjk hkL) (lt_of_le_of_lt hjk hkR) hR]
  exact increment_antitone κ hκ b hs hjk hkL hkR hR

lemma feasible_min {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L) :
    FeasibleZ L r0 r1 (min r0 r1) := by
  constructor
  · exact le_rfl
  · omega

lemma objective_nonneg {L : ℕ} (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ)
    (hb : ∀i,0≤b i) (R z : ℕ) : 0≤objective κ b R z := by
  exact add_nonneg (Finset.sum_nonneg (fun i _=>hb i))
    (mul_nonneg hκ (Finset.sum_nonneg (fun i _=>hb i)))

def scalarScore {L : ℕ} (κ : ℝ) (b : Fin L→ℝ) (r0 r1 : ℕ) (z : Fin (L+1)) : ℝ :=
  by
    classical
    exact if FeasibleZ L r0 r1 z.val then objective κ b (r0+r1) z.val else -1

def maxZ {L : ℕ} (κ : ℝ) (b : Fin L→ℝ) (r0 r1 : ℕ) : ℕ :=
  (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)).val

lemma maxZ_le {L : ℕ} (κ : ℝ) (b : Fin L→ℝ) (r0 r1 : ℕ) : maxZ κ b r0 r1≤L :=
  Nat.le_of_lt_succ (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)).isLt

lemma maxZ_feasible {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L)
    (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i) :
    FeasibleZ L r0 r1 (maxZ κ b r0 r1) := by
  let z0 : Fin (L+1) := ⟨min r0 r1,by omega⟩
  have hfeas := feasible_min h0 h1
  have hh := FCAppendix.Affine.FiniteSelector.select_max (scalarScore κ b r0 r1) z0
  change scalarScore κ b r0 r1 z0≤
    scalarScore κ b r0 r1 (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)) at hh
  have hz0 : FeasibleZ L r0 r1 z0.val := hfeas
  rw [scalarScore,if_pos hz0] at hh
  by_contra hn
  change ¬FeasibleZ L r0 r1
    (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)).val at hn
  rw [scalarScore,if_neg hn] at hh
  have hp := objective_nonneg κ hκ b hb (r0+r1) z0.val
  linarith

lemma maxZ_maximal {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L)
    (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i)
    (z : ℕ) (hz : FeasibleZ L r0 r1 z) :
    objective κ b (r0+r1) z≤objective κ b (r0+r1) (maxZ κ b r0 r1) := by
  have hzL : z≤L := (hz.1.trans (min_le_left _ _)).trans h0
  have hh := FCAppendix.Affine.FiniteSelector.select_max (scalarScore κ b r0 r1)
    (⟨z,by omega⟩ : Fin (L+1))
  have hfeas := maxZ_feasible h0 h1 κ hκ b hb
  change FeasibleZ L r0 r1
    (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)).val at hfeas
  change scalarScore κ b r0 r1 ⟨z,by omega⟩≤
    scalarScore κ b r0 r1 (FCAppendix.Affine.FiniteSelector.select (scalarScore κ b r0 r1)) at hh
  simpa only [scalarScore,hz,hfeas,if_pos,maxZ] using hh

def selection {L : ℕ} (κ : ℝ) (b : Fin L→ℝ) (r0 r1 : ℕ) :
    Finset (Fin L) × Finset (Fin L) := canonicalPair L r0 r1 (maxZ κ b r0 r1)

lemma selection_card {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L)
    (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i) :
    (selection κ b r0 r1).1.card=r0 ∧ (selection κ b r0 r1).2.card=r1 :=
  canonical_card h0 h1 (maxZ_feasible h0 h1 κ hκ b hb)

lemma selection_potential_max {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L)
    (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i) (hs : Antitone b)
    (S T : Finset (Fin L)) (hS : S.card=r0) (hT : T.card=r1) :
    CompleteInformation.potential κ b S T≤
      CompleteInformation.potential κ b (selection κ b r0 r1).1 (selection κ b r0 r1).2 := by
  rw [selection,canonical_potential κ b (maxZ_feasible h0 h1 κ hκ b hb)]
  exact (potential_le_objective κ hκ b hb hs S T hS hT).trans
    (maxZ_maximal h0 h1 κ hκ b hb (S∩T).card (actual_duplicate_count S T hS hT))

lemma actual_maximum_value {L r0 r1 : ℕ} (h0 : r0≤L) (h1 : r1≤L)
    (κ : ℝ) (hκ : 0≤κ) (b : Fin L→ℝ) (hb : ∀i,0≤b i) (hs : Antitone b)
    (S T : Finset (Fin L)) (hS : S.card=r0) (hT : T.card=r1)
    (hmax : ∀S' T',S'.card=r0 → T'.card=r1 →
      CompleteInformation.potential κ b S' T'≤CompleteInformation.potential κ b S T) :
    CompleteInformation.potential κ b S T=objective κ b (r0+r1) (maxZ κ b r0 r1) := by
  have hc := selection_card h0 h1 κ hκ b hb
  have he := canonical_potential κ b (maxZ_feasible h0 h1 κ hκ b hb)
  apply le_antisymm
  · simpa only [selection,he] using selection_potential_max h0 h1 κ hκ b hb hs S T hS hT
  · rw [←he]
    exact hmax _ _ hc.1 hc.2

end FCAppendix.Affine.LowBody.SortedPotential
