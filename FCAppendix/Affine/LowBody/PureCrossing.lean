import FCAppendix.Affine.LowBody.SortedPotential

noncomputable section
namespace FCAppendix.Affine.LowBody.SortedPotential
open Set
open scoped BigOperators

theorem actual_maximum_component_optimal {L r0 r1 : ℕ} (h0 : r0 ≤ L) (h1 : r1 ≤ L)
    (κ : ℝ) (hκ : 0 < κ) (b : Fin L → ℝ) (hb : ∀i,0 ≤ b i) (hs : Antitone b)
    (S T : Finset (Fin L)) (hS : S.card=r0) (hT : T.card=r1)
    (hmax : ∀S' T',S'.card=r0  →  T'.card=r1  →
      CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S T) :
    Finite.Optimal (r0+r1-(S∩T).card) b (S∪T) ∧
      Finite.Optimal (S∩T).card b (S∩T) := by
  have hvalue := actual_maximum_value h0 h1 κ hκ.le b hb hs S T hS hT hmax
  have hbound := potential_le_objective κ hκ.le b hb hs S T hS hT
  have hscalar := maxZ_maximal h0 h1 κ hκ.le b hb (S∩T).card
    (actual_duplicate_count S T hS hT)
  have heq : CompleteInformation.potential κ b S T=
      objective κ b (r0+r1) (S∩T).card := by linarith
  have hc := Finset.card_union_add_card_inter S T
  rw [hS,hT] at hc
  have hU : (S∪T).card=r0+r1-(S∩T).card := by omega
  have hu : r0+r1-(S∩T).card ≤ L := by
    rw [←hU]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (S∪T)
  have hi : (S∩T).card ≤ L := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (S∩T)
  have hleU := sum_le_prefixSum hu b hb hs (S∪T) hU.le
  have hleI := sum_le_prefixSum hi b hb hs (S∩T) le_rfl
  unfold CompleteInformation.potential objective at heq
  have heqU : (∑i∈S∪T,b i)=prefixSum b (r0+r1-(S∩T).card) := by nlinarith
  have heqI : (∑i∈S∩T,b i)=prefixSum b (S∩T).card := by nlinarith
  constructor
  · refine ⟨hU.le,fun A hA=>?_⟩
    rw [heqU]
    exact sum_le_prefixSum hu b hb hs A hA
  · refine ⟨le_rfl,fun A hA=>?_⟩
    rw [heqI]
    exact sum_le_prefixSum hi b hb hs A hA

lemma unique_bid_mem_iff {L k : ℕ} (_hk : k ≤ L) (b : Fin L → ℝ) (hs : Antitone b)
    (t : Fin L) (ht : ∀i,i≠t  →  b i≠b t) (S : Finset (Fin L))
    (hcard : S.card=k) (hopt : Finite.Optimal k b S) : t∈S ↔ t.val < k := by
  classical
  have hgt : Finset.univ.filter (fun i : Fin L=>b t < b i)=topSet L t.val := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_prefix]
    constructor
    · intro h
      by_contra hn
      have hh := hs (show t ≤ i from le_of_not_gt hn)
      linarith
    · intro h
      have hle := hs (show i ≤ t from h.le)
      have hne : i≠t := by intro he;subst i;exact Nat.lt_irrefl _ h
      exact lt_of_le_of_ne hle (Ne.symm (ht i hne))
  have hge : Finset.univ.filter (fun i : Fin L=>i≠t ∧ b t ≤ b i)=topSet L t.val := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_prefix]
    constructor
    · rintro ⟨hne,hle⟩
      have hlt : b t < b i := lt_of_le_of_ne hle (Ne.symm (ht i hne))
      have hi : i∈Finset.univ.filter (fun i : Fin L=>b t < b i) := by simp [hlt]
      simpa only [hgt,mem_prefix] using hi
    · intro h
      have hh := hs (show i ≤ t from h.le)
      exact ⟨(by intro he;subst i;exact Nat.lt_irrefl _ h),hh⟩
  constructor
  · intro hmem
    by_contra hn
    have hm : k ≤ (Finset.univ.filter (fun i : Fin L=>b t < b i)).card := by
      rw [hgt,card_prefix (Nat.le_of_lt t.isLt)]
      exact le_of_not_gt hn
    exact Finite.excluded_of_many_better k b S hopt t hm hmem
  · intro htk
    by_contra hn
    have hsub : S⊆Finset.univ.filter (fun i : Fin L=>i≠t ∧ b t ≤ b i) := by
      intro i hiS
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,fun he=>hn (he ▸ hiS),
        Finite.optimal_swap k b S hopt i t hiS hn⟩
    have hc := Finset.card_le_card hsub
    rw [hcard,hge,card_prefix (Nat.le_of_lt t.isLt)] at hc
    omega

lemma le_of_steps {f : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀j,a ≤ j  →  j < b  →  f j ≤ f (j+1)) : f a ≤ f b := by
  have hall : ∀k,a ≤ k  →  k ≤ b  →  f a ≤ f k := by
    intro k hak
    induction k,hak using Nat.le_induction with
    | base=>intro _;exact le_rfl
    | succ k hk ih=>
      intro hkb
      exact (ih (by omega)).trans (hstep k hk (by omega))
  exact hall b hab le_rfl

lemma increment_eq_zero_between_max {f : ℕ → ℝ} {a b t : ℕ} (hat : a ≤ t) (htb : t < b)
    (hconc : ∀i j,a ≤ i  →  i ≤ j  →  j < b  →  f (j+1)-f j ≤ f (i+1)-f i)
    (hma : f (t+1) ≤ f a) (hmb : f t ≤ f b) : f (t+1)-f t=0 := by
  apply le_antisymm
  · by_contra h
    have hp : 0 < f (t+1)-f t := lt_of_not_ge h
    have hchain : f a ≤ f t := le_of_steps hat (fun j haj hjt=>by
      have hh := hconc j t haj (by omega) htb
      linarith)
    linarith
  · by_contra h
    have hn : f (t+1)-f t < 0 := lt_of_not_ge h
    have hchain : f b ≤ f (t+1) := by
      have hneg := le_of_steps (f:=fun k=> -f k) (show t+1 ≤ b by omega) (fun j htj hjb=>by
        have hh := hconc t j hat (by omega) hjb
        linarith)
      linarith
    linarith

theorem duplicate_change_scaled_tie {L r0 r1 : ℕ} (h0 : r0 ≤ L) (h1 : r1 ≤ L)
    (κ : ℝ) (hκ : 0 < κ) (b : Fin L → ℝ) (hb : ∀i,0 ≤ b i) (hs : Antitone b)
    (t : Fin L) (ht : ∀i,i≠t  →  b i≠b t)
    (S0 T0 S1 T1 : Finset (Fin L))
    (hS0 : S0.card=r0) (hT0 : T0.card=r1) (hS1 : S1.card=r0) (hT1 : T1.card=r1)
    (hm0 : ∀S' T',S'.card=r0  →  T'.card=r1  →
      CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S0 T0)
    (hm1 : ∀S' T',S'.card=r0  →  T'.card=r1  →
      CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S1 T1)
    (hnot : t∉S0∩T0) (hmem : t∈S1∩T1) :
    ∃j : Fin L,j≠t ∧ b j=κ*b t := by
  classical
  let z0 := (S0∩T0).card
  let z1 := (S1∩T1).card
  let R := r0+r1
  have hz0 := actual_duplicate_count S0 T0 hS0 hT0
  have hz1 := actual_duplicate_count S1 T1 hS1 hT1
  have hc0 := (actual_maximum_component_optimal h0 h1 κ hκ b hb hs S0 T0 hS0 hT0 hm0).2
  have hc1 := (actual_maximum_component_optimal h0 h1 κ hκ b hb hs S1 T1 hS1 hT1 hm1).2
  have hz0L : z0 ≤ L := by simpa only [z0,Fintype.card_fin] using Finset.card_le_univ (S0∩T0)
  have hz1L : z1 ≤ L := by simpa only [z1,Fintype.card_fin] using Finset.card_le_univ (S1∩T1)
  have hz0t : z0 ≤ t.val := le_of_not_gt (fun h=>hnot
    ((unique_bid_mem_iff hz0L b hs t ht (S0∩T0) rfl hc0).mpr h))
  have htz1 : t.val < z1 := (unique_bid_mem_iff hz1L b hs t ht (S1∩T1) rfl hc1).mp hmem
  have htz : FeasibleZ L r0 r1 t.val := by
    constructor
    · exact htz1.le.trans hz1.1
    · have hh := hz0.2
      change r0+r1 ≤ L+z0 at hh
      omega
  have htsucc : FeasibleZ L r0 r1 (t.val+1) := by
    constructor
    · exact (Nat.succ_le_of_lt htz1).trans hz1.1
    · have hh := hz0.2
      change r0+r1 ≤ L+z0 at hh
      omega
  have hscalar0 (z : ℕ) (hz : FeasibleZ L r0 r1 z) :
      objective κ b R z ≤ objective κ b R z0 := by
    have hcards := canonical_card h0 h1 hz
    have hm := hm0 _ _ hcards.1 hcards.2
    rw [canonical_potential κ b hz] at hm
    exact hm.trans (potential_le_objective κ hκ.le b hb hs S0 T0 hS0 hT0)
  have hscalar1 (z : ℕ) (hz : FeasibleZ L r0 r1 z) :
      objective κ b R z ≤ objective κ b R z1 := by
    have hcards := canonical_card h0 h1 hz
    have hm := hm1 _ _ hcards.1 hcards.2
    rw [canonical_potential κ b hz] at hm
    exact hm.trans (potential_le_objective κ hκ.le b hb hs S1 T1 hS1 hT1)
  have hR0 : R-z0 ≤ L := by have hh := hz0.2;change R ≤ L+z0 at hh;omega
  have hz1R : z1 ≤ R := hz1.1.trans ((min_le_left r0 r1).trans (Nat.le_add_right _ _))
  have hzero : objective κ b R (t.val+1)-objective κ b R t.val=0 :=
    increment_eq_zero_between_max hz0t htz1
      (fun i j hzi hij hjz=>objective_discrete_concave κ hκ.le b hs hij
        (lt_of_lt_of_le hjz hz1L) (lt_of_lt_of_le hjz hz1R) (by omega))
      (hscalar0 _ htsucc) (hscalar1 _ htz)
  have htR : t.val < R := lt_of_lt_of_le htz1 hz1R
  have hRt : R-t.val ≤ L := by have hh := htz.2;change R ≤ L+t.val at hh;omega
  rw [objective_increment κ b t.isLt htR hRt] at hzero
  have hjL : R-t.val-1 < L := by omega
  let j : Fin L := ⟨R-t.val-1,hjL⟩
  refine ⟨j,?_,?_⟩
  · intro he
    have hjt := congrArg Fin.val he
    have ha := hz1.1.trans (min_le_left _ _)
    have hb' := hz1.1.trans (min_le_right _ _)
    change z1 ≤ r0 at ha
    change z1 ≤ r1 at hb'
    change R-t.val-1=t.val at hjt
    dsimp only [R] at hjt
    omega
  · simp only [bidAt,dif_pos t.isLt,dif_pos hjL] at hzero
    exact (sub_eq_zero.mp hzero).symm

lemma potential_map {L : ℕ} (κ : ℝ) (b : Fin L → ℝ) (σ : Equiv.Perm (Fin L))
    (S T : Finset (Fin L)) :
    CompleteInformation.potential κ b (S.map σ.toEmbedding) (T.map σ.toEmbedding)=
      CompleteInformation.potential κ (fun i=>b (σ i)) S T := by
  rw [CompleteInformation.potential,←Finset.map_union,←Finset.map_inter]
  simp only [Finset.sum_map,Equiv.coe_toEmbedding,CompleteInformation.potential]

theorem duplicate_change_scaled_tie_unsorted {L r0 r1 : ℕ} (h0 : r0 ≤ L) (h1 : r1 ≤ L)
    (κ : ℝ) (hκ : 0 < κ) (b : Fin L → ℝ) (hb : ∀i,0 ≤ b i)
    (t : Fin L) (ht : ∀i,i≠t → b i≠b t)
    (S0 T0 S1 T1 : Finset (Fin L))
    (hS0 : S0.card=r0) (hT0 : T0.card=r1) (hS1 : S1.card=r0) (hT1 : T1.card=r1)
    (hm0 : ∀S' T',S'.card=r0 → T'.card=r1 →
      CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S0 T0)
    (hm1 : ∀S' T',S'.card=r0 → T'.card=r1 →
      CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S1 T1)
    (hnot : t∉S0∩T0) (hmem : t∈S1∩T1) :
    ∃j : Fin L,j≠t ∧ b j=κ*b t := by
  classical
  let σ := Tuple.sort (fun i=> -b i)
  let bs : Fin L → ℝ := fun i=>b (σ i)
  let reindex : Finset (Fin L) → Finset (Fin L) := fun S=>S.map σ.symm.toEmbedding
  have hs : Antitone bs := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i=> -b i) hij
    change -bs i ≤ -bs j at hh
    linarith
  have hr (S T : Finset (Fin L)) :
      CompleteInformation.potential κ bs (reindex S) (reindex T)=
        CompleteInformation.potential κ b S T := by
    have hh := potential_map κ b σ (reindex S) (reindex T)
    simpa only [reindex,Finset.map_map,Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,
      Finset.map_refl] using hh.symm
  have hm (S T : Finset (Fin L))
      (hmax : ∀S' T',S'.card=r0 → T'.card=r1 →
        CompleteInformation.potential κ b S' T' ≤ CompleteInformation.potential κ b S T) :
      ∀A B,A.card=r0 → B.card=r1 →
        CompleteInformation.potential κ bs A B ≤
          CompleteInformation.potential κ bs (reindex S) (reindex T) := by
    intro A B hA hB
    have hh := hmax (A.map σ.toEmbedding) (B.map σ.toEmbedding) (by simpa using hA)
      (by simpa using hB)
    rw [hr]
    simpa only [potential_map] using hh
  have ht' : ∀i,i≠σ.symm t → bs i≠bs (σ.symm t) := by
    intro i hi
    have hn : σ i≠t := by intro he;apply hi;exact σ.apply_eq_iff_eq_symm_apply.mp he
    simpa only [bs,Equiv.apply_symm_apply] using ht (σ i) hn
  have hn : σ.symm t∉reindex S0∩reindex T0 := by
    simpa only [reindex,Finset.mem_inter,Finset.mem_map_equiv,Equiv.symm_symm,
      Equiv.apply_symm_apply] using hnot
  have hy : σ.symm t∈reindex S1∩reindex T1 := by
    simpa only [reindex,Finset.mem_inter,Finset.mem_map_equiv,Equiv.symm_symm,
      Equiv.apply_symm_apply] using hmem
  obtain ⟨j,hjt,hbj⟩ := duplicate_change_scaled_tie h0 h1 κ hκ bs (fun i=>hb (σ i)) hs
    (σ.symm t) ht' (reindex S0) (reindex T0) (reindex S1) (reindex T1)
    (by simpa [reindex] using hS0) (by simpa [reindex] using hT0)
    (by simpa [reindex] using hS1) (by simpa [reindex] using hT1)
    (hm S0 T0 hm0) (hm S1 T1 hm1) hn hy
  refine ⟨σ j,?_,?_⟩
  · intro he
    exact hjt (σ.apply_eq_iff_eq_symm_apply.mp he)
  · simpa only [bs,Equiv.apply_symm_apply] using hbj

end FCAppendix.Affine.LowBody.SortedPotential
