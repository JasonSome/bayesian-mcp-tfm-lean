import FCAppendix.Affine.Hybrid.Native02.FullContextPolicy
import FCAppendix.Affine.Hybrid.EqualRelabel

set_option maxHeartbeats 1500000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Bayes Game Set Classical
open scoped BigOperators

section ClippedThreshold
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def clippedLaw (G : ClippedOwnerData ι) (j : Fin 2) : FiniteLaw (Finset ι) :=
  if j=0 then G.law₁ else G.law₂

def clippedCapacity (G : ClippedOwnerData ι) (j : Fin 2) : ℕ :=
  (if j=0 then G.owner₁.card else G.owner₂.card)+G.residual

def clippedReceipt (G : ClippedOwnerData ι) (j : Fin 2) : ι → ℝ :=
  if j=0 then G.receipt₁ else G.receipt₂

private lemma law_support_threshold {p w : ι → ℝ} {price : ℝ}
    (ν : FiniteLaw (Finset ι)) (c : ℕ) (hp : ExactCapacity.Implements p c ν)
    (hp0 : ∀ i,0≤ p i) (hp1 : ∀ i,p i≤1)
    (ht : Proposer.Threshold p w price) (S : Finset ι) (hS : ν.mass S≠0) :
    S.card=c ∧ (∀ i∈ S,price≤ w i) ∧ (∀ i∉S,w i≤ price) := by
  refine ⟨hp.1 S hS,?_,?_⟩
  · intro i hi
    have hpos := FiniteLaw.marginal_pos_of_support_mem ν S hS i hi
    rw [hp.2 i] at hpos
    by_cases hone : p i=1
    · exact ht.2.1 i hone
    · exact (ht.2.2 i hpos (lt_of_le_of_ne (hp1 i) hone)).ge
  · intro i hi
    have hone : p i≠1 := by
      intro he
      exact hi (GuardedData.support_mem_of_marginal_one ν i
        ((hp.2 i).trans he) S hS)
    by_cases hzero : p i=0
    · exact ht.1 i hzero
    · exact (ht.2.2 i (lt_of_le_of_ne (hp0 i) (Ne.symm hzero))
        (lt_of_le_of_ne (hp1 i) hone)).le

theorem clippedLaw_support_threshold (G : ClippedOwnerData ι) (j : Fin 2)
    (S : Finset ι) (hS : (clippedLaw G j).mass S≠0) :
    S.card=clippedCapacity G j ∧
      (∀ i∈ S,G.price≤ clippedReceipt G j i) ∧
      (∀ i∉S,clippedReceipt G j i≤ G.price) := by
  by_cases hj : j=0
  · simp only [clippedLaw,if_pos hj] at hS
    simpa only [clippedCapacity,clippedReceipt,if_pos hj] using
      law_support_threshold G.law₁ _ G.law₁_implements
        (fun i => (G.marginal_bounds₁ i).1) (fun i => (G.marginal_bounds₁ i).2)
        G.threshold₁ S hS
  · simp only [clippedLaw,if_neg hj] at hS
    simpa only [clippedCapacity,clippedReceipt,if_neg hj] using
      law_support_threshold G.law₂ _ G.law₂_implements
        (fun i => (G.marginal_bounds₂ i).1) (fun i => (G.marginal_bounds₂ i).2)
        G.threshold₂ S hS

lemma canonical_clipped_law (G : ClippedOwnerData ι) (j : Fin 2) :
    canonicalClippedOwnerLaw G.xi G.residual
      (if j=0 then G.owner₁ else G.owner₂)
      (if j=0 then G.owner₂ else G.owner₁) G.bid=clippedLaw G j := by
  by_cases hj : j=0
  · simp only [if_pos hj,clippedLaw]
    exact canonicalClippedOwnerLaw_eq G
  · simp only [if_neg hj,clippedLaw]
    have hs := canonicalClippedOwnerLaw_eq G.swap
    change canonicalClippedOwnerLaw G.xi G.residual G.owner₂ G.owner₁ G.bid=
      ExactCapacity.symmetricLottery G.swap.p₁ at hs
    rw [G.swap_p₁] at hs
    exact hs

lemma clippedLaw_opponent_marginal (G : ClippedOwnerData ι) (j : Fin 2) (i : ι) :
    G.bid i*(1-G.xi*(clippedLaw G (otherProposer j)).prob (fun S => i∈ S))=
      clippedReceipt G j i := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp only [otherProposer, clippedLaw, ite_true, show (1:Fin 2) ≠ 0 by decide,
      if_false, G.law₂_implements.2 i, clippedReceipt, ClippedOwnerData.receipt₁]
  · simp only [otherProposer, clippedLaw, show (1:Fin 2) ≠ 0 by decide,
      if_false, ite_true, G.law₁_implements.2 i, clippedReceipt, ClippedOwnerData.receipt₂]

lemma clippedLaw_mixed_marginal (G : ClippedOwnerData ι) (i : ι)
    (hi₁ : i∉G.owner₁) (hi₂ : i∉G.owner₂) (j : Fin 2) :
    (clippedLaw G j).prob (fun S => i∈ S)=G.mixedP i := by
  have hiM := (G.mixed_iff i).mpr ⟨hi₁,hi₂⟩
  by_cases hj : j=0
  · simp only [clippedLaw,if_pos hj,G.law₁_implements.2 i,
      ClippedOwnerData.p₁,if_neg hi₁,if_pos hiM]
  · simp only [clippedLaw,if_neg hj,G.law₂_implements.2 i,
      ClippedOwnerData.p₂,if_neg hi₂,if_pos hiM]

def omittedTargetQ (xi : ℝ) (r : ℕ) (b : ι → ℝ) (i : ι)
    (P : Finset ι × Finset ι) : ℝ :=
  EqualCapacity.positiveMarginal xi r (maskedMixedBids P.1 P.2 b) i

lemma omittedTargetQ_eq_mixed (G : ClippedOwnerData ι) (i : ι)
    (hi₁ : i∉G.owner₁) (hi₂ : i∉G.owner₂) :
    omittedTargetQ G.xi G.residual G.bid i (G.owner₁,G.owner₂)=G.mixedP i := by
  have h := congrFun (canonicalClippedOwnerP_eq G) i
  have hiM := (G.mixed_iff i).mpr ⟨hi₁,hi₂⟩
  simpa only [omittedTargetQ,canonicalClippedOwnerP,ClippedOwnerData.p₁,
    if_neg hi₁,if_pos hiM] using h

def omittedEquiv (C : Finset ι) (i : ι) (hC : ∀ j,j∈ C ↔ j≠i) : Option C ≃ ι where
  toFun := fun t => match t with | none => i | some j => j.val
  invFun := fun j => if hj : j=i then none else some ⟨j,(hC j).mpr hj⟩
  left_inv := by
    intro t
    cases t with
    | none => simp
    | some j => simp only [dif_neg ((hC j).mp j.property)]
  right_inv := by
    intro j
    by_cases hj : j=i <;> simp [hj]

lemma omittedTargetQ_reindex {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (C : Finset ι) (i : ι) (hC : ∀ j,j∈ C ↔ j≠i)
    (r : ℕ) (b : ι → ℝ) (AB : Finset C × Finset C) :
    omittedTargetQ xi r b i (embedOwnerPair C AB)=
      canonicalExceptionalQ xi r (b i) (fun j : C => b j) AB := by
  let e := omittedEquiv C i hC
  have hiC : i∉C := fun h => (hC i).mp h rfl
  have hi₁ : i∉embedSelection C AB.1 := fun h => hiC (embedSelection_subset C AB.1 h)
  have hi₂ : i∉embedSelection C AB.2 := fun h => hiC (embedSelection_subset C AB.2 h)
  have hmask : maskedMixedBids (embedSelection C AB.1) (embedSelection C AB.2) b ∘ e=
      maskedMixedBids (AB.1.map rivalEmbedding) (AB.2.map rivalEmbedding)
        (augmentedRivalBids (b i) (fun j : C => b j)) := by
    funext t
    cases t with
    | none => simp [Function.comp_apply,e,omittedEquiv,maskedMixedBids,
        hi₁,hi₂,rivalEmbedding,augmentedRivalBids]
    | some j => simp [Function.comp_apply,e,omittedEquiv,maskedMixedBids,
        mem_embedSelection,rivalEmbedding,augmentedRivalBids]
  have h := EqualCapacity.positiveMarginal_equiv e hxi hxi1 r
    (maskedMixedBids (embedSelection C AB.1) (embedSelection C AB.2) b) none
  rw [hmask] at h
  exact h.symm

theorem omitted_owner_expect_reindex {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (C : Finset ι) (i : ι) (hC : ∀ j,j∈ C ↔ j≠i)
    (K₀ K₁ r : ℕ) (b : ι → ℝ) (hN : 2≤ C.card) (hK : K₀+K₁≤ C.card)
    (F : ℝ → ℝ) :
    (ownerLawOnSubset C K₀ K₁ b).expect (fun P => F (omittedTargetQ xi r b i P))=
      letI : Nonempty C := by
        obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0< C.card by omega)
        exact ⟨⟨j,hj⟩⟩
      (sourceOwnersLaw (fun j : C => b j) K₀ K₁).expect
        (fun AB => F (canonicalExceptionalQ xi r (b i) (fun j : C => b j) AB)) := by
  rw [ownerLawOnSubset_valid C K₀ K₁ b hN hK,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro AB
  rw [omittedTargetQ_reindex hxi hxi1 C i hC]

theorem ownerPairOnSubset_expect (C : Finset ι) (K₀ K₁ : ℕ) (b : ι → ℝ)
    (F : Finset ι × Finset ι → ℝ) :
    (∫ u : unitInterval,F (ownerPairOnSubset C K₀ K₁ b u) ∂volume)=
      (ownerLawOnSubset C K₀ K₁ b).expect F := by
  have hm : Measurable (ownerPairOnSubset C K₀ K₁ b) := by
    simpa only [Function.comp_def, id_eq] using measurable_ownerPairOnSubset.comp
      ((measurable_const (a := ((C,K₀,K₁),b))).prodMk measurable_id)
  have hl := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure (volume : Measure unitInterval)
    (ownerPairOnSubset C K₀ K₁ b) hm (ownerLawOnSubset C K₀ K₁ b)
    (ownerPairOnSubset_law C K₀ K₁ b)
  have he := FiniteLaw.expect_ofMeasure (volume : Measure unitInterval)
    (ownerPairOnSubset C K₀ K₁ b) hm F
  rw [hl] at he
  exact he.symm

def reinsertBids (C : Finset ι) (b : ℝ) (x : C → ℝ) (j : ι) : ℝ :=
  if hj : j∈ C then x ⟨j,hj⟩ else b

omit [Fintype ι] in
lemma reinsertBids_on_rivals (C : Finset ι) (b : ℝ) (x : C → ℝ) :
    (fun j : C => reinsertBids C b x j)=x := by
  funext j
  simp only [reinsertBids,dif_pos j.property]

omit [Fintype ι] in
lemma reinsertBids_at_target (C : Finset ι) (b : ℝ) (x : C → ℝ) (i : ι) (hi : i∉C) :
    reinsertBids C b x i=b := by simp only [reinsertBids,dif_neg hi]

omit [Fintype ι] in
lemma measurable_reinsertBids (C : Finset ι) (b : ℝ) :
    Measurable (reinsertBids C b : (C → ℝ) → ι → ℝ) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j∈ C
  · simpa only [reinsertBids,dif_pos hj] using
      (measurable_pi_apply (⟨j,hj⟩ : C) : Measurable (fun x : C → ℝ => x ⟨j,hj⟩))
  · simp only [reinsertBids,dif_neg hj]
    exact measurable_const

theorem physical_omitted_owner_menus (C : Finset ι) [Nonempty C]
    (i : ι) (hC : ∀ j,j∈ C ↔ j≠i)
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi eta L U h0 v b M1 : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi) (hv : 0< v) (hb : 0< b)
    (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (hh0 : |h0|≤1)
    (K₀ K₁ r : ℕ) (hN : 2≤ C.card) (hK : K₀+K₁< C.card)
    (hguard : ClippedCountGuard xi L U (C.card-(K₀+K₁)+1) r)
    (hM1 : ∀ p∈ Icc (0:ℝ) 1,outsideOneAt xi v (h0/reciprocalMean G) p≤ M1) :
    let n := C.card-(K₀+K₁)
    let err := U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    (∫ x : C → ℝ,(ownerLawOnSubset C K₀ K₁ (reinsertBids C b x)).expect
      (fun P => omittedTargetQ xi r (reinsertBids C b x) i P*(v-b))
      ∂Measure.pi (fun _ : C => G))≤ M1+err/(1-xi) ∧
    (∫ x : C → ℝ,(ownerLawOnSubset C K₀ K₁ (reinsertBids C b x)).expect
      (fun P => independentTwo eta v b (omittedTargetQ xi r (reinsertBids C b x) i P))
      ∂Measure.pi (fun _ : C => G))≤ outsideTwo v (h0/reciprocalMean G)+2*err := by
  have hiC : i∉C := fun h => (hC i).mp h rfl
  have he (x : C → ℝ) (F : ℝ → ℝ) :
      (ownerLawOnSubset C K₀ K₁ (reinsertBids C b x)).expect
        (fun P => F (omittedTargetQ xi r (reinsertBids C b x) i P))=
      (sourceOwnersLaw x K₀ K₁).expect
        (fun AB => F (canonicalExceptionalQ xi r b x AB)) := by
    have h := omitted_owner_expect_reindex hxi hxi1 C i hC K₀ K₁ r
      (reinsertBids C b x) hN hK.le F
    simpa only [reinsertBids_on_rivals,reinsertBids_at_target C b x i hiC] using h
  have hs := primitive_excluded_owner_menus (ι:=C) G hxi hxi1 heta hv hb hL hLU hbox hh0
    K₀ K₁ r (by simpa only [Fintype.card_coe] using hN)
    (by simpa only [Fintype.card_coe] using hK)
    (by simpa only [Fintype.card_coe] using hguard) hM1
  have hs₁ (x : C → ℝ) := he x (fun q => q*(v-b))
  have hs₂ (x : C → ℝ) := he x (independentTwo eta v b)
  simp_rw [hs₁,hs₂]
  simpa only [Fintype.card_coe] using hs

end ClippedThreshold

theorem iid_coordinate_restriction_law {J K : Type*} [Fintype J] [Fintype K]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : K → J) (hf : Function.Injective f) :
    (Measure.pi (fun _ : J => μ)).map (fun x : J → ℝ => fun k : K => x (f k))=
      Measure.pi (fun _ : K => μ) := by
  classical
  let p : J → Prop := fun j => ∃ k,f k=j
  let e : K ≃ Subtype p := {
    toFun := fun k => ⟨f k,⟨k,rfl⟩⟩
    invFun := fun j => j.property.choose
    left_inv := fun k => hf (show f ((⟨f k,⟨k,rfl⟩⟩ : Subtype p).property.choose)=f k from
      (⟨f k,⟨k,rfl⟩⟩ : Subtype p).property.choose_spec)
    right_inv := fun j => Subtype.ext j.property.choose_spec }
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : J => ℝ) p
  have hs := (measurePreserving_piEquivPiSubtypeProd (fun _ : J => μ) p).map_eq
  have hr : (Measure.pi (fun _ : J => μ)).map (fun x : J → ℝ => fun j : Subtype p => x j)=
      Measure.pi (fun _ : Subtype p => μ) := by
    have h := congrArg (fun ν => ν.map Prod.fst) hs
    rw [Measure.map_map measurable_fst E.measurable,
      Measure.map_fst_prod,measure_univ,one_smul] at h
    exact h
  have he : (Measure.pi (fun _ : Subtype p => μ)).map
      (fun x : Subtype p → ℝ => fun k : K => x (e k))=
      Measure.pi (fun _ : K => μ) := by
    have h := (measurePreserving_piCongrLeft (fun _ : K => μ) e.symm).map_eq
    convert! h using 1
    congr 1
    funext x k
    simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']
  have hm₁ : Measurable (fun x : J → ℝ => fun j : Subtype p => x j) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (j : J))
  have hm₂ : Measurable (fun x : Subtype p → ℝ => fun k : K => x (e k)) :=
    measurable_pi_lambda _ (fun k => measurable_pi_apply (e k))
  calc
    _ = ((Measure.pi (fun _ : J => μ)).map
        (fun x : J → ℝ => fun j : Subtype p => x j)).map
        (fun x : Subtype p → ℝ => fun k : K => x (e k)) := by
      rw [Measure.map_map hm₂ hm₁]
      rfl
    _ = _ := by rw [hr,he]

namespace FullContext
variable {m : ℕ}

lemma ownerCount_sum (z : ℝ) (A : Finset (Fin m)) (d₀ d₁ : ℕ) :
    ownerCount z A d₀ d₁ 0+ownerCount z A d₀ d₁ 1=
      2*exclusiveQuota z A.card+residualDifference d₀ d₁ := by
  unfold ownerCount residualDifference
  simp only [ite_true, show (1:Fin 2)≠0 by decide,if_false]
  split_ifs <;> omega

lemma ownerCount_add_residual (z : ℝ) (A : Finset (Fin m)) (d₀ d₁ : ℕ)
    (hell : exclusiveQuota z A.card≤ min d₀ d₁) (j : Fin 2) :
    ownerCount z A d₀ d₁ j+(min d₀ d₁-exclusiveQuota z A.card)=
      if j=0 then d₀ else d₁ := by
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;>
    simp only [ownerCount, ite_true, show (1:Fin 2) ≠ 0 by decide, if_false] <;>
    unfold residualDifference <;> split_ifs <;> omega

lemma box_eligible_eq_erase (d L U : ℝ) (X : ClassifiedContext m)
    (i : Fin m) (hi : i∈ activeSet d X.1)
    (hout : entryBid (X.1 i)∉Icc L U)
    (hsmall : (activeSet d X.1\boxSet L U X.1).card≤1) :
    boxSet L U X.1∩activeSet d X.1=(activeSet d X.1).erase i := by
  let A := activeSet d X.1
  have hiB : i∉boxSet L U X.1 := fun h => hout (Finset.mem_filter.mp h).2.2
  have hibad : i∈ A\boxSet L U X.1 := Finset.mem_sdiff.mpr ⟨hi,hiB⟩
  ext j
  constructor
  · intro hj
    have hji : j≠i := by
      intro he
      exact hiB (he ▸ (Finset.mem_inter.mp hj).1)
    exact Finset.mem_erase.mpr ⟨hji,(Finset.mem_inter.mp hj).2⟩
  · intro hj
    obtain ⟨hji,hjA⟩ := Finset.mem_erase.mp hj
    have hjB : j∈ boxSet L U X.1 := by
      by_contra hn
      have hjbad : j∈ A\boxSet L U X.1 := Finset.mem_sdiff.mpr ⟨hjA,hn⟩
      exact hji ((Finset.card_le_one.mp hsmall) j hjbad i hibad)
    exact Finset.mem_inter.mpr ⟨hjB,hjA⟩

lemma eligibleOn_erase (A : Finset (Fin m)) (i : A) :
    eligibleOn A (A.erase i)=Finset.univ.erase i := by
  ext j
  simp only [eligibleOn,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_erase,j.property,and_true]
  exact not_congr Subtype.ext_iff.symm

lemma tableLaw_eq_clipped {xi : ℝ} (T : TableIndex m) (b : Fin m → ℝ)
    (u : unitInterval) (G : ClippedOwnerData T.1)
    (hx : G.xi=xi) (hb : G.bid=fun a : T.1 => b a)
    (ho₁ : G.owner₁=(tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u).1)
    (ho₂ : G.owner₂=(tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u).2)
    (hr : G.residual=T.2.2.2.2) (j : Fin 2) :
    tableLaw xi T j b u=(clippedLaw G j).map (embedSelection T.1) := by
  unfold tableLaw
  dsimp only
  rw [←hx,←hb,←ho₁,←ho₂,←hr,canonical_clipped_law]

theorem exists_clippedData_on_context {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : Fin m) (hi : i∈ activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (u : unitInterval) :
    ∃ G : ClippedOwnerData (activeSet d X.1),
      G.xi=xi ∧ G.bid=(fun a : activeSet d X.1 => entryBid (X.1 a)) ∧
      G.owner₁=(tableOwners (tableIndex d L U z c X).1
        (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 (fun a => entryBid (X.1 a)) u).1 ∧
      G.owner₂=(tableOwners (tableIndex d L U z c X).1
        (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
        (tableIndex d L U z c X).2.2.2.1 (fun a => entryBid (X.1 a)) u).2 ∧
      G.residual=(tableIndex d L U z c X).2.2.2.2 ∧
      (∀ j : Fin 2,clippedCapacity G j=c-contextUpper j X) ∧ d< G.price ∧
      (⟨i,hi⟩ : activeSet d X.1)∉G.owner₁ ∧ (⟨i,hi⟩ : activeSet d X.1)∉G.owner₂ := by
  let A := activeSet d X.1
  let a : A := ⟨i,hi⟩
  let B := boxSet L U X.1∩A
  let C := eligibleOn A B
  let d₀ := capacity c A X.2.1
  let d₁ := capacity c A X.2.2
  let ell := exclusiveQuota z A.card
  let K₀ := ownerCount z A d₀ d₁ 0
  let K₁ := ownerCount z A d₀ d₁ 1
  let r := min d₀ d₁-ell
  let bid : A → ℝ := fun j => entryBid (X.1 j)
  have hN : 2≤ A.card := hready.1
  have hB : B=A.erase i := box_eligible_eq_erase d L U X i hi hout hready.2.2.2.2.2.2.2
  have hC : C=Finset.univ.erase a := by rw [show C=eligibleOn A B from rfl,hB]; exact eligibleOn_erase A a
  have hCcard : C.card=A.card-1 := by rw [hC,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_coe]
  have hDguard : ClippedCountGuard xi L U (A.card-(K₀+K₁)) r := hguard
  have hCsize : 2≤ C.card := by rw [hCcard]; have := hDguard.1; have := hready.2.2.1; change 0< K₀+K₁ at this; omega
  have hKC : K₀+K₁≤ C.card := by rw [hCcard]; have := hDguard.1; omega
  have hBA : B≠A := by
    intro he
    have his : i∈ B := he.symm ▸ hi
    rw [hB] at his
    exact (Finset.notMem_erase i A) his
  let P := ownerPairOnSubset C K₀ K₁ bid u
  have hP : tableOwners (tableIndex d L U z c X).1
      (tableIndex d L U z c X).2.1 (tableIndex d L U z c X).2.2.1
      (tableIndex d L U z c X).2.2.2.1 (fun j => entryBid (X.1 j)) u=P := by
    change tableOwners A B K₀ K₁ (fun j => entryBid (X.1 j)) u = P
    rw [tableOwners, dif_pos hN, if_neg hBA]
  obtain ⟨hc₀,hc₁,hdis,hsub₀,hsub₁⟩ := ownerPairOnSubset_support C K₀ K₁ bid u hCsize hKC
  have hPc₀ : P.1.card = K₀ := hc₀
  have hPc₁ : P.2.card = K₁ := hc₁
  have haC : a∉C := by rw [hC]; exact Finset.notMem_erase _ _
  have ha₀ : a∉P.1 := fun h => haC (hsub₀ h)
  have ha₁ : a∉P.2 := fun h => haC (hsub₁ h)
  let D := Finset.univ\(P.1∪P.2)
  have hDcard : D.card=A.card-(K₀+K₁) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Fintype.card_coe,Finset.card_union_of_disjoint hdis,hc₀,hc₁]
  have hGD : ClippedCountGuard xi L U D.card r := by rw [hDcard]; exact hDguard
  let b₀ := Function.update bid a L
  have hb₀ : ∀ j : A,b₀ j∈ Icc L U := by
    intro j
    by_cases hja : j=a
    · simp only [b₀,hja,Function.update_self]
      exact ⟨le_rfl,hLU⟩
    · have hji : (j:Fin m)≠i := fun h => hja (Subtype.ext h)
      have hjB : (j:Fin m)∈ B := by rw [hB]; exact Finset.mem_erase.mpr ⟨hji,j.property⟩
      have hbox := (Finset.mem_filter.mp (Finset.mem_inter.mp hjB).1).2.2
      simpa only [b₀,Function.update_of_ne hja,bid] using hbox
  have hbidpos : 0< bid a := hd.trans_lt (Finset.mem_filter.mp hi).2.2
  obtain ⟨G,hx,hb,ho₀,ho₁,hr,hperturb⟩ := clipped_owner_of_box
    hxi hxi1 hL hLU b₀ hb₀ P.1 P.2 hdis r hGD a ha₀ ha₁ (bid a) hbidpos
  have hbactual : G.bid=bid := by
    rw [hb]
    funext j
    by_cases hj : j=a <;> simp [b₀,hj]
  have hD : D.Nonempty := Finset.card_pos.mp (by have := hGD.1; omega)
  have hmult := finiteMultiplier_box_bounds hL b₀ D hD r (fun j _ => hb₀ j) hGD.2.1
  have hprice : d< G.price := by
    have hdiff := (abs_le.mp hperturb).1
    have hg := hGD.2.2.1
    have hlU := mul_le_mul_of_nonneg_left hLU (sub_pos.mpr hxi1).le
    have hp : (1-xi)*U< G.price := by linarith [hmult.1]
    exact hgap.trans_le (hlU.trans hp.le)
  have hm : 0< m := by
    have hAm := Finset.card_le_univ A
    simp only [Fintype.card_fin] at hAm
    omega
  have hell : ell< min d₀ d₁ := (count_region_integer_tests m A.card
    (min d₀ d₁) ell (residualDifference d₀ d₁) hm hready.2.2.2.2.1).1
  have hraw₀ : d₀=c-X.2.1 := by
    have hs := hready.2.2.2.2.2.2.1.1
    change min A.card (c-X.2.1)< A.card at hs
    exact Nat.min_eq_right (by omega)
  have hraw₁ : d₁=c-X.2.2 := by
    have hs := hready.2.2.2.2.2.2.1.2
    change min A.card (c-X.2.2)< A.card at hs
    exact Nat.min_eq_right (by omega)
  refine ⟨G,hx,hbactual,by rw [hP]; exact ho₀,by rw [hP]; exact ho₁,hr,?_,
    hprice,by rw [ho₀]; exact ha₀,by rw [ho₁]; exact ha₁⟩
  intro j
  have hsum := ownerCount_add_residual z A d₀ d₁ hell.le j
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simpa only [clippedCapacity, ite_true, ho₀, hPc₀, hr, contextUpper,
      K₀, r, ell, ←hraw₀] using hsum
  · simpa only [clippedCapacity, show (1:Fin 2) ≠ 0 by decide, if_false, ho₁, hPc₁, hr,
      contextUpper, K₁, r, ell, ←hraw₁] using hsum

theorem proposalValid_of_clipped {xi : ℝ} (_hxi : 0< xi) (_hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0≤ d)
    (X : ClassifiedContext m) (G : ClippedOwnerData (activeSet d X.1))
    (hx : G.xi=xi) (hb : G.bid=fun i : activeSet d X.1 => entryBid (X.1 i))
    (hcap : ∀ j : Fin 2,clippedCapacity G j=c-contextUpper j X) (hprice : d< G.price)
    (hlaw : ∀ j : Fin 2,proposalLaw xi d L U z c μ j X=
      (clippedLaw G j).map (embedSelection (activeSet d X.1))) :
    proposalValid xi d L U z c μ X := by
  let A := activeSet d X.1
  have hreceipt (j : Fin 2) (i : A) :
      proposalReceipt xi d L U z c μ j X i=clippedReceipt G j i := by
    rw [proposalReceipt, hlaw, prob_map_embed_active, ←hx]
    convert! clippedLaw_opponent_marginal G j i using 1
    rw [congrFun hb i]
  have houtside (j : Fin 2) (i : Fin m) (hi : i∉A) :
      proposalReceipt xi d L U z c μ j X i≤ d := by
    rw [proposalReceipt,hlaw,prob_map_embed_inactive A _ i hi]
    simp only [mul_zero,sub_zero,mul_one]
    by_cases hvis : X.1 i=none
    · simpa only [hvis,entryBid] using hd
    · exact le_of_not_gt (fun ht => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvis,ht⟩))
  intro j S hS
  rw [hlaw j] at hS
  obtain ⟨Q,hQ,rfl⟩ := finiteMap_support _ (embedSelection A) S hS
  obtain ⟨hc,hs,hn⟩ := clippedLaw_support_threshold G j Q hQ
  have hcard : (embedSelection A Q).card=c-contextUpper j X := by rw [embedSelection_card,hc,hcap]
  have hselected : ∀ i∈ embedSelection A Q,G.price≤ proposalReceipt xi d L U z c μ j X i := by
    intro i hi
    have hiA := embedSelection_subset A Q hi
    have hiQ : (⟨i,hiA⟩ : A)∈ Q := (mem_embedSelection A Q ⟨i,hiA⟩).mp hi
    rw [show proposalReceipt xi d L U z c μ j X i=clippedReceipt G j ⟨i,hiA⟩ from hreceipt j ⟨i,hiA⟩]
    exact hs ⟨i,hiA⟩ hiQ
  have hunselected : ∀ i∉embedSelection A Q,proposalReceipt xi d L U z c μ j X i≤ G.price := by
    intro i hi
    by_cases hiA : i∈ A
    · have hiQ : (⟨i,hiA⟩ : A)∉Q := fun h => hi ((mem_embedSelection A Q ⟨i,hiA⟩).mpr h)
      rw [show proposalReceipt xi d L U z c μ j X i=clippedReceipt G j ⟨i,hiA⟩ from hreceipt j ⟨i,hiA⟩]
      exact hn ⟨i,hiA⟩ hiQ
    · exact (houtside j i hiA).trans hprice.le
  refine ⟨⟨hcard.le,?_⟩,hcard.le,?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp (embedSelection_subset A Q hi)).2.1
  · intro T hT
    exact threshold_optimal _ _ T G.price G.price_pos.le
      (by simpa only [hcard] using hT) hselected hunselected

theorem validation_accepts_exceptional {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : Fin m) (hi : i∈ activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) :
    useProposal xi d L U z c μ X := by
  let u := (observedLowMinimumSeed d μ X.1).getD 0
  obtain ⟨G,hx,hb,ho₀,ho₁,hr,hcap,hprice,_,_⟩ :=
    exists_clippedData_on_context hxi hxi1 d L U z c hd hL hLU hgap X hready i hi hout hguard u
  refine ⟨hready,proposalValid_of_clipped hxi hxi1 d L U z c μ hd X G hx hb hcap hprice ?_⟩
  intro j
  convert! tableLaw_eq_clipped (tableIndex d L U z c X)
    (fun a => entryBid (X.1 a)) u G hx hb ho₀ ho₁ hr j using 1

theorem contextPolicy_law_on_exceptional {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : Fin m) (hi : i∈ activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (j : Fin 2) :
    volume.map ((contextPolicy hxi hxi1 d L U z c μ).select j X)=
      FiniteLaw.probabilityMeasure (proposalLaw xi d L U z c μ j X) := by
  have hp := validation_accepts_exceptional hxi hxi1 d L U z c μ hd hL hLU hgap X hready i hi hout hguard
  change volume.map (select (m := m) hxi hxi1 d L U z c μ j X) = _
  have heq : select (m := m) hxi hxi1 d L U z c μ j X =
      proposalSample (m := m) hxi hxi1 d L U z c μ j X := by
    funext s
    exact if_pos hp
  rw [heq]
  exact (proposalSample_spec (m := m) hxi hxi1 d L U z c μ j).2.2 X

def tableTargetQ (xi : ℝ) (T : TableIndex m) (b : Fin m → ℝ)
    (u : unitInterval) (i : T.1) : ℝ :=
  omittedTargetQ xi T.2.2.2.2 (fun a : T.1 => b a) i
    (tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u)

theorem tableLaw_exceptional_target_marginal {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (u : unitInterval) (j : Fin 2) :
    (tableLaw xi (tableIndex d L U z c X) j (fun a => entryBid (X.1 a)) u).prob
      (fun S => (i:Fin m)∈ S)=
      tableTargetQ xi (tableIndex d L U z c X) (fun a => entryBid (X.1 a)) u i := by
  obtain ⟨G,hx,hb,ho₀,ho₁,hr,hcap,hprice,hi₀,hi₁⟩ :=
    exists_clippedData_on_context hxi hxi1 d L U z c hd hL hLU hgap X hready
      i i.property hout hguard u
  rw [tableLaw_eq_clipped _ _ u G hx hb ho₀ ho₁ hr j,prob_map_embed_active]
  change (clippedLaw G j).prob (fun S => i ∈ S) = _
  rw [clippedLaw_mixed_marginal G i hi₀ hi₁]
  have hq := omittedTargetQ_eq_mixed G i hi₀ hi₁
  rw [hx,hb,ho₀,ho₁,hr] at hq
  exact hq.symm

theorem tableLaw_exceptional_broadcast_payoff {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (u : unitInterval) (eta v : ℝ) :
    ((tableLaw xi (tableIndex d L U z c X) 0 (fun a => entryBid (X.1 a)) u).prod
      (tableLaw xi (tableIndex d L U z c X) 1 (fun a => entryBid (X.1 a)) u)).expect
      (broadcastPayoff eta v (entryBid (X.1 i)) (i:Fin m))=
      independentTwo eta v (entryBid (X.1 i))
        (tableTargetQ xi (tableIndex d L U z c X) (fun a => entryBid (X.1 a)) u i) := by
  rw [expect_product_broadcastPayoff,
    tableLaw_exceptional_target_marginal hxi hxi1 d L U z c hd hL hLU hgap X hready i hout hguard u 0,
    tableLaw_exceptional_target_marginal hxi hxi1 d L U z c hd hL hLU hgap X hready i hout hguard u 1]
  unfold independentTwo
  ring

theorem tableLaw_exceptional_singleton_payoff {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (u : unitInterval) (v : ℝ) :
    ((tableLaw xi (tableIndex d L U z c X) 0 (fun a => entryBid (X.1 a)) u).prod
      (tableLaw xi (tableIndex d L U z c X) 1 (fun a => entryBid (X.1 a)) u)).expect
      (singletonPayoff v (entryBid (X.1 i)) (i:Fin m))=
      tableTargetQ xi (tableIndex d L U z c X) (fun a => entryBid (X.1 a)) u i*
        (v-entryBid (X.1 i)) := by
  rw [expect_product_singletonPayoff,
    tableLaw_exceptional_target_marginal hxi hxi1 d L U z c hd hL hLU hgap X hready i hout hguard u 0,
    tableLaw_exceptional_target_marginal hxi hxi1 d L U z c hd hL hLU hgap X hready i hout hguard u 1]
  ring

theorem contextPolicy_private_payoff_exceptional {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (X : ClassifiedContext m)
    (hready : countReady xi d L U z c X)
    (i : activeSet d X.1) (hout : entryBid (X.1 i)∉Icc L U)
    (hguard : ClippedCountGuard xi L U
      ((tableIndex d L U z c X).1.card-
        ((tableIndex d L U z c X).2.2.1+(tableIndex d L U z c X).2.2.2.1))
      (tableIndex d L U z c X).2.2.2.2) (eta v : ℝ) :
    (∫ s : unitInterval×unitInterval,
      broadcastPayoff eta v (entryBid (X.1 i)) (i:Fin m)
        ((contextPolicy hxi hxi1 d L U z c μ).select 0 X s.1,
          (contextPolicy hxi hxi1 d L U z c μ).select 1 X s.2)
      ∂((volume : Measure unitInterval).prod volume))=
      independentTwo eta v (entryBid (X.1 i))
        (tableTargetQ xi (tableIndex d L U z c X) (fun a => entryBid (X.1 a))
          ((observedLowMinimumSeed d μ X.1).getD 0) i) := by
  let C := contextPolicy (m := m) hxi hxi1 d L U z c μ
  let f := fun s : unitInterval×unitInterval => (C.select 0 X s.1,C.select 1 X s.2)
  have hm : Measurable f :=
    ((C.measurable 0).comp (measurable_const.prodMk measurable_fst)).prodMk
      ((C.measurable 1).comp (measurable_const.prodMk measurable_snd))
  have hp := validation_accepts_exceptional hxi hxi1 d L U z c μ hd hL hLU hgap X hready
    i i.property hout hguard
  have hl := contextPolicy_private_pair_law hxi hxi1 d L U z c μ X hp
  have heq := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    ((volume : Measure unitInterval).prod volume) f hm
    ((proposalLaw xi d L U z c μ 0 X).prod (proposalLaw xi d L U z c μ 1 X)) hl
  have he := FiniteLaw.expect_ofMeasure ((volume : Measure unitInterval).prod volume) f hm
    (broadcastPayoff eta v (entryBid (X.1 i)) (i:Fin m))
  rw [heq] at he
  rw [←he]
  exact tableLaw_exceptional_broadcast_payoff hxi hxi1 d L U z c hd hL hLU hgap X hready
    i hout hguard _ eta v

theorem tableTargetQ_uniform_common_reindex {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (T : TableIndex m) (b : Fin m → ℝ) (i : T.1)
    (hN : 2≤ T.1.card) (hB : T.2.1=T.1.erase i)
    (hCsize : 2≤(eligibleOn T.1 T.2.1).card)
    (hK : T.2.2.1+T.2.2.2.1≤(eligibleOn T.1 T.2.1).card) (F : ℝ → ℝ) :
    (∫ u : unitInterval,F (tableTargetQ xi T b u i) ∂volume)=
      let C := eligibleOn T.1 T.2.1
      letI : Nonempty C := by
        obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0< C.card from lt_of_lt_of_le (by decide : 0<2) hCsize)
        exact ⟨⟨j,hj⟩⟩
      (sourceOwnersLaw (fun j : C => b j.val) T.2.2.1 T.2.2.2.1).expect
        (fun AB => F (canonicalExceptionalQ xi T.2.2.2.2 (b i)
          (fun j : C => b j.val) AB)) := by
  let A := T.1
  let C := eligibleOn T.1 T.2.1
  have hBA : T.2.1≠T.1 := by
    intro he
    have hi : (i:Fin m)∈ T.2.1 := he.symm ▸ i.property
    rw [hB] at hi
    exact (Finset.notMem_erase _ _) hi
  have hC : ∀ j : A,j∈ C ↔ j≠i := by
    intro j
    have he : C=Finset.univ.erase i := by rw [show C=eligibleOn A T.2.1 from rfl,hB]; exact eligibleOn_erase A i
    rw [he]
    simp only [Finset.mem_erase,Finset.mem_univ,and_true]
  have htable (u : unitInterval) :
      tableOwners T.1 T.2.1 T.2.2.1 T.2.2.2.1 b u=
        ownerPairOnSubset C T.2.2.1 T.2.2.2.1 (fun a : A => b a) u := by
    simp only [tableOwners,dif_pos hN,if_neg hBA]
    rfl
  simp only [tableTargetQ,htable]
  have he := ownerPairOnSubset_expect C T.2.2.1 T.2.2.2.1 (fun a : A => b a)
    (fun P => F (omittedTargetQ xi T.2.2.2.2 (fun a : A => b a) i P))
  have howner := omitted_owner_expect_reindex hxi hxi1 C i hC T.2.2.1 T.2.2.2.1
    T.2.2.2.2 (fun a : A => b a) hCsize hK F
  convert! he.trans howner using 1

end FullContext
end FCAppendix.Affine.Hybrid.Native02
