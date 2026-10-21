import FCAppendix.Affine.Uniform07Finishing.Native.SourceSeedCorrection
import FCAppendix.Affine.Uniform07Finishing.Native.FocalCopyGeneric

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Weighted
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open Existence.PayOnceBounded (listBids positiveSupport mem_positiveSupport)
open scoped BigOperators
variable {m : ℕ} [Nonempty (Fin m)]

omit [Nonempty (Fin m)] in
theorem residual_feasible_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m)
    (d₀ d₁ : ℕ) (P : ResidualPotential.Pair m) :
    ResidualPotential.Feasible (L ∘ e.symm) d₀ d₁ (relabelPair e P) ↔
      ResidualPotential.Feasible L d₀ d₁ P := by
  simp only [ResidualPotential.Feasible,LocallyFeasible,relabelPair,Finset.card_map]
  constructor
  · rintro ⟨⟨h0,hp0⟩,⟨h1,hp1⟩⟩
    refine ⟨⟨h0,?_⟩,⟨h1,?_⟩⟩
    · intro i hi
      simpa using hp0 (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    · intro i hi
      simpa using hp1 (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · rintro ⟨⟨h0,hp0⟩,⟨h1,hp1⟩⟩
    refine ⟨⟨h0,?_⟩,⟨h1,?_⟩⟩
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
      simpa using hp0 k hk
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
      simpa using hp1 k hk

omit [Nonempty (Fin m)] in
theorem residual_bid_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    ResidualPotential.bid (L ∘ e.symm) = ResidualPotential.bid L ∘ e.symm := rfl

theorem residual_selection_focalCopy_relabel {κ : ℝ} (hκ : 0 ≤ κ)
    (e : Equiv.Perm (Fin m)) (L : LocalList m) (d₀ d₁ : ℕ) (i : Fin m)
    (hgeneric : ∀P Q : ResidualPotential.Pair m,
      ResidualPotential.Feasible L d₀ d₁ P → ResidualPotential.Feasible L d₀ d₁ Q →
      CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 =
        CompleteInformation.potential κ (ResidualPotential.bid L) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    focalCopy (ResidualPotential.selection κ (L ∘ e.symm) d₀ d₁) (e i) =
      focalCopy (ResidualPotential.selection κ L d₀ d₁) i := by
  let P := ResidualPotential.selection κ L d₀ d₁
  let S := ResidualPotential.selection κ (L ∘ e.symm) d₀ d₁
  let Q := relabelPair e.symm S
  have hP := ResidualPotential.selection_feasible κ hκ L d₀ d₁
  have hS := ResidualPotential.selection_feasible κ hκ (L ∘ e.symm) d₀ d₁
  have hQ : ResidualPotential.Feasible L d₀ d₁ Q := by
    simpa only [Q,Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply] using
      (residual_feasible_relabel e.symm (L ∘ e.symm) d₀ d₁ S).mpr hS
  have hPe : ResidualPotential.Feasible (L ∘ e.symm) d₀ d₁ (relabelPair e P) :=
    (residual_feasible_relabel e L d₀ d₁ P).mpr hP
  have heP := potential_relabel κ (ResidualPotential.bid L) e P
  have heQ := potential_relabel κ (ResidualPotential.bid (L ∘ e.symm)) e.symm S
  have hback : ResidualPotential.bid (L ∘ e.symm) ∘ e = ResidualPotential.bid L := by
    funext k
    simp only [residual_bid_relabel,Function.comp_apply,Equiv.symm_apply_apply]
  rw [show e.symm.symm = e from rfl,hback] at heQ
  have hPS := residual_selection_max hκ (L ∘ e.symm) d₀ d₁ (relabelPair e P) hPe
  rw [residual_bid_relabel] at hPS
  rw [heP] at hPS
  have hQP := residual_selection_max hκ L d₀ d₁ Q hQ
  have hPQ : CompleteInformation.potential κ (ResidualPotential.bid L) P.1 P.2 ≤
      CompleteInformation.potential κ (ResidualPotential.bid L) Q.1 Q.2 :=
    hPS.trans_eq heQ.symm
  have hc := hgeneric P Q hP hQ (le_antisymm hPQ hQP)
  have hQr : focalCopy Q i = focalCopy S (e i) := by
    simpa only [Q,Equiv.symm_apply_apply] using focalCopy_relabel e.symm S (e i)
  exact (hc.trans hQr).symm

omit [Nonempty (Fin m)] in
theorem listBids_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) :
    listBids (L ∘ e.symm) = listBids L ∘ e.symm := rfl

omit [Nonempty (Fin m)] in
theorem remainder_relabel (e : Equiv.Perm (Fin m)) (L : LocalList m) (E : Finset (Fin m)) :
    remainder (L ∘ e.symm) (E.map e.toEmbedding) = remainder L E ∘ e.symm := by
  funext i
  simp only [remainder,Function.comp_apply,Finset.mem_map_equiv]

theorem threshold_relabel {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (e : Equiv.Perm (Fin m)) (d : ℕ) (b : Fin m → ℝ) :
    threshold ξ d (b ∘ e.symm) = threshold ξ d b := by
  unfold threshold
  congr 1
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    simpa only [EqualCapacity.positiveMarginal_equiv e.symm hξ hξ1,
      Function.comp_apply] using Finset.le_sup'
      (fun k => if EqualCapacity.positiveMarginal ξ d b k < 1 then
        b k*(1-ξ*EqualCapacity.positiveMarginal ξ d b k) else 0) (Finset.mem_univ (e.symm i))
  · apply Finset.sup'_le
    intro i _
    simpa only [EqualCapacity.positiveMarginal_equiv e.symm hξ hξ1,
      Function.comp_apply,Equiv.symm_apply_apply] using Finset.le_sup'
      (fun k => if EqualCapacity.positiveMarginal ξ d (b ∘ e.symm) k < 1 then
        (b ∘ e.symm) k*(1-ξ*EqualCapacity.positiveMarginal ξ d (b ∘ e.symm) k) else 0)
      (Finset.mem_univ (e i))

theorem validExclusive_relabel_iff {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (e : Equiv.Perm (Fin m)) (L : LocalList m) (d₀ d₁ : ℕ) (E : Finset (Fin m)) :
    ValidExclusive ξ (L ∘ e.symm) d₀ d₁ (E.map e.toEmbedding) ↔
      ValidExclusive ξ L d₀ d₁ E := by
  have hb : listBids (remainder (L ∘ e.symm) (E.map e.toEmbedding)) =
      listBids (remainder L E) ∘ e.symm := by rw [remainder_relabel,listBids_relabel]
  have hs : positiveSupport (listBids (remainder L E) ∘ e.symm) =
      (positiveSupport (listBids (remainder L E))).map e.toEmbedding := by
    ext i
    simp only [mem_positiveSupport,Function.comp_apply,Finset.mem_map_equiv]
  simp only [ValidExclusive,Finset.card_map,hb,hs,threshold_relabel hξ hξ1]
  constructor
  · rintro ⟨hc,hpres,hfill,hr⟩
    refine ⟨hc,?_,hfill,?_⟩
    · intro i hi
      simpa using
        hpres (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
    · intro i hi
      simpa using
        hr (e i) (Finset.mem_map.mpr ⟨i,hi,rfl⟩)
  · rintro ⟨hc,hpres,hfill,hr⟩
    refine ⟨hc,?_,hfill,?_⟩
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
      simpa using hpres k hk
    · intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hi
      simpa using hr k hk

theorem privateCountMoment_unusable (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (E : Option (Finset (Fin m)))
    (he : budget c 0 X ≠ budget c 1 X)
    (hn : ¬usable ξ c (fun _ : ClassifiedContext m => E) X)
    (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X E i q = q (focalCopy (purePair ξ c X) i) := by
  simp only [privateCountMoment,select,if_neg he,if_neg hn,if_true,
    if_neg (by decide : (1 : Fin 2) ≠ 0),integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem privateCountMoment_relabel {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (e : Equiv.Perm (Fin m)) (X : ClassifiedContext m)
    (E : Option (Finset (Fin m))) (i : Fin m) (q : Fin 3 → ℝ)
    (hgeneric : ∀P Q : ResidualPotential.Pair m,
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P →
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) Q →
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) P.1 P.2 =
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    privateCountMoment ξ hξ hξ1 c (relabelContext e X)
      (E.map (fun S => S.map e.toEmbedding)) (e i) q =
      privateCountMoment ξ hξ hξ1 c X E i q := by
  have hpure : focalCopy (purePair ξ c (relabelContext e X)) (e i) =
      focalCopy (purePair ξ c X) i := by
    have hleft := congrArg₂
      (fun d₀ d₁ : ℕ => focalCopy
        (ResidualPotential.selection (1-ξ) (X.1 ∘ e.symm) d₀ d₁) (e i))
      (budget_relabel c 0 X e) (budget_relabel c 1 X e)
    exact hleft.trans (residual_selection_focalCopy_relabel
      (κ := 1-ξ) (by linarith) e X.1 (budget c 0 X) (budget c 1 X) i hgeneric)
  by_cases he : budget c 0 X = budget c 1 X
  · have he' : budget c 0 (relabelContext e X) = budget c 1 (relabelContext e X) := by
      simpa only [budget_relabel] using he
    rw [privateCountMoment_equal _ _ _ _ _ _ he',privateCountMoment_equal _ _ _ _ _ _ he]
    simp only [budget_relabel]
    simp only [relabelContext,listBids_relabel,
      EqualCapacity.positiveMarginal_equiv e.symm hξ hξ1,Equiv.symm_apply_apply]
  have he' : budget c 0 (relabelContext e X) ≠ budget c 1 (relabelContext e X) := by
    simpa only [budget_relabel] using he
  cases E with
  | none => rw [Option.map_none,privateCountMoment_none _ _ _ _ _ he',
      privateCountMoment_none _ _ _ _ _ he,hpure]
  | some E =>
      simp only [Option.map_some]
      by_cases hv : ValidExclusive ξ X.1 (budget c 0 X) (budget c 1 X) E
      · have hv' : ValidExclusive ξ (relabelContext e X).1
            (budget c 0 (relabelContext e X)) (budget c 1 (relabelContext e X))
            (E.map e.toEmbedding) := by
          rw [budget_relabel,budget_relabel]
          exact (validExclusive_relabel_iff hξ hξ1 e X.1 _ _ E).mpr hv
        rw [privateCountMoment_weighted _ _ _ _ _ _ he' hv',
          privateCountMoment_weighted _ _ _ _ _ _ he hv]
        dsimp only
        have hl : larger c (relabelContext e X) = larger c X := by simp only [larger,budget_relabel]
        simp only [hl,commonBudget_relabel]
        simp only [relabelContext,remainder_relabel,listBids_relabel,
          EqualCapacity.positiveMarginal_equiv e.symm hξ hξ1,Equiv.symm_apply_apply,
          Finset.mem_map_equiv]
      · have hn : ¬usable ξ c (fun _ : ClassifiedContext m => some E) X := by
          intro h
          exact hv (by simpa only [candidate,Option.getD_some] using h.2)
        have hn' : ¬usable ξ c (fun _ : ClassifiedContext m => some (E.map e.toEmbedding))
            (relabelContext e X) := by
          intro h
          have hh := h.2
          simp only [candidate,Option.getD_some] at hh
          rw [budget_relabel,budget_relabel] at hh
          change ValidExclusive ξ (X.1 ∘ e.symm) (budget c 0 X) (budget c 1 X)
            (E.map e.toEmbedding) at hh
          exact hv ((validExclusive_relabel_iff hξ hξ1 e X.1 _ _ E).mp hh)
        rw [privateCountMoment_unusable _ _ _ _ _ _ he' hn',
          privateCountMoment_unusable _ _ _ _ _ _ he hn,hpure]

omit [Nonempty (Fin m)] in
theorem exceptionalSet_relabel (U : ℝ) (X : ClassifiedContext m) (e : Equiv.Perm (Fin m)) :
    exceptionalSet U (relabelContext e X).1 = (exceptionalSet U X.1).map e.toEmbedding := by
  ext i
  simp only [exceptionalSet,Finset.mem_filter,Finset.mem_univ,true_and,relabelContext,
    Function.comp_apply,Finset.mem_map_equiv]

theorem finitePathCountCorrection_relabel {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (Λ a r U d₀ z t width ε : ℝ) (c : ℕ)
    (e : Equiv.Perm (Fin m)) (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ)
    (hgeneric : ∀P Q : ResidualPotential.Pair m,
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) P →
      ResidualPotential.Feasible X.1 (budget c 0 X) (budget c 1 X) Q →
      CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) P.1 P.2 =
        CompleteInformation.potential (1-ξ) (ResidualPotential.bid X.1) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    finitePathCountCorrection ξ hξ hξ1 Λ r U c
      (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c) (relabelContext e X) (e i) q =
      finitePathCountCorrection ξ hξ hξ1 Λ r U c
        (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c) X i q := by
  let Δ := max (budget c 0 X) (budget c 1 X)-commonBudget c X
  let Δe := max (budget c 0 (relabelContext e X)) (budget c 1 (relabelContext e X))-
    commonBudget c (relabelContext e X)
  let w := sourceWeights ξ Λ r U X.1
  let we := sourceWeights ξ Λ r U (relabelContext e X).1
  let raw (Y : ClassifiedContext m) (weights : WeightedSampling.Weights (Fin m))
      (n : ℕ) (j : Fin m) : ℝ :=
    (WeightedSampling.pathLaw weights n ∅).expect (fun path =>
      privateCountMoment ξ hξ hξ1 c Y
        (some (WeightedSampling.finalSet n ∅ path)) j q)
  have hn : Δe = Δ := by
    simp only [Δe,Δ,budget_relabel,commonBudget_relabel]
  have hw : we = WeightedSampling.relabelWeights w e :=
    sourceWeights_relabel ξ Λ r U X.1 e
  have hB := privateCountMoment_relabel hξ hξ1 c e X none i q hgeneric
  simp only [Option.map_none] at hB
  change (if (exceptionalSet U (relabelContext e X).1).card ≤ 1 ∧
      (Δe : ℝ) < WeightedSampling.totalWeight we then
    (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c (relabelContext e X) : ℝ) *
      (raw (relabelContext e X) we Δe (e i) -
        privateCountMoment ξ hξ hξ1 c (relabelContext e X) none (e i) q) else 0) =
    (if (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) < WeightedSampling.totalWeight w then
      (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X : ℝ) *
        (raw X w Δ i - privateCountMoment ξ hξ hξ1 c X none i q) else 0)
  rw [exceptionalSet_relabel,Finset.card_map,hn,hw,
    WeightedSampling.totalWeight_relabel,sourceGuardAlpha_relabel,hB]
  by_cases hg : (exceptionalSet U X.1).card ≤ 1 ∧ (Δ : ℝ) < WeightedSampling.totalWeight w
  · rw [if_pos hg,if_pos hg]
    apply congrArg (fun y : ℝ =>
      (sourceGuardAlpha ξ Λ a r U d₀ z t width ε c X : ℝ) *
        (y-privateCountMoment ξ hξ hξ1 c X none i q))
    dsimp only [raw]
    have hp := WeightedSampling.pathLaw_relabel w Δ ∅ e (by simpa using hg.2)
    simp only [Finset.map_empty] at hp
    rw [hp,FiniteLaw.expect_map]
    apply FiniteLaw.expect_congr
    intro path
    have hset := WeightedSampling.finalSet_relabel e Δ ∅ path
    simp only [Finset.map_empty] at hset
    rw [hset]
    simpa only [Option.map_some] using privateCountMoment_relabel hξ hξ1 c e X
      (some (WeightedSampling.finalSet Δ ∅ path)) i q hgeneric
  · rw [if_neg hg,if_neg hg]

end FCAppendix.Affine.Uniform07Finishing.Weighted
