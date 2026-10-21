import FCAppendix.Affine.Hybrid.Finishing01ClearingCounts
import FCAppendix.Affine.Hybrid.PureRelabel

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finish01
open Set MeasureTheory Classical
open scoped BigOperators

section FiniteTransport
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def embedPair (e : ι ↪ κ) (AB : Finset ι × Finset ι) : Finset κ × Finset κ :=
  (AB.1.map e,AB.2.map e)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma mem_embed_set (e : ι ↪ κ) (S : Finset ι) (i : ι) :
    e i ∈ S.map e ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j,hj,he⟩ := Finset.mem_map.mp h
    exact e.injective he ▸ hj
  · intro h
    exact Finset.mem_map.mpr ⟨i,h,rfl⟩

omit [Fintype ι] [Fintype κ] in
lemma focalCopy_embedPair (e : ι ↪ κ) (AB : Finset ι × Finset ι) (i : ι) :
    LowBody.focalCopy (embedPair e AB) (e i) = LowBody.focalCopy AB i := by
  simp only [LowBody.focalCopy,embedPair,Finset.mem_inter,Finset.mem_union,mem_embed_set]

lemma pairCountMass_embed (Q : FiniteLaw (Finset ι × Finset ι)) (e : ι ↪ κ)
    (i : ι) (j : Fin 3) :
    pairCountMass (Q.map (embedPair e)) (e i) j = pairCountMass Q i j := by
  unfold pairCountMass
  rw [FiniteLaw.prob_eq_expect,FiniteLaw.expect_map,FiniteLaw.prob_eq_expect]
  exact FiniteLaw.expect_congr _ (fun AB => by rw [focalCopy_embedPair])

lemma finiteLaw_map_prod {A B C D : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (mu : FiniteLaw A) (nu : FiniteLaw B) (f : A → C) (g : B → D) :
    (mu.map f).prod (nu.map g) = (mu.prod nu).map (Prod.map f g) := by
  apply FiniteLaw.ext_expect
  intro H
  simp only [FiniteLaw.expect_prod,FiniteLaw.expect_map,Prod.map_apply]

omit [DecidableEq ι] [DecidableEq κ] in

lemma kernelMarginal_equiv {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (c : ℕ) (b : ι → ℝ) (hb : ∀ i,0 < b i) (e : ι ≃ κ) :
    EqualCapacity.kernelMarginal xi c (b ∘ e.symm) =
      EqualCapacity.kernelMarginal xi c b ∘ e.symm := by
  obtain ⟨h0,h1,hs,z,hz,ht⟩ := EqualCapacity.kernelMarginal_spec hxi hxi1 c b hb
  apply EqualCapacity.isKernel_unique hxi c (b ∘ e.symm)
    (fun i => hb (e.symm i)) _ _
    (EqualCapacity.kernelMarginal_spec hxi hxi1 c _ (fun i => hb (e.symm i)))
  refine ⟨(fun i => h0 (e.symm i)),(fun i => h1 (e.symm i)),?_,z,hz,?_,?_,?_⟩
  · change (∑ i : κ,EqualCapacity.kernelMarginal xi c b (e.symm i)) = _
    rw [Equiv.sum_comp e.symm,hs,Fintype.card_congr e]
  · intro i hi
    exact ht.1 (e.symm i) hi
  · intro i hi
    exact ht.2.1 (e.symm i) hi
  · intro i hi hj
    exact ht.2.2 (e.symm i) hi hj

def positiveSupportEquiv (b : ι → ℝ) (e : Equiv.Perm ι) :
    Existence.PayOnceBounded.positiveSupport b ≃
      Existence.PayOnceBounded.positiveSupport (b ∘ e.symm) where
  toFun i := ⟨e i,by
    rw [Existence.PayOnceBounded.mem_positiveSupport]
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using
      (Existence.PayOnceBounded.mem_positiveSupport b i).mp i.property⟩
  invFun i := ⟨e.symm i,by
    exact (Existence.PayOnceBounded.mem_positiveSupport b (e.symm i)).mpr
      ((Existence.PayOnceBounded.mem_positiveSupport (b ∘ e.symm) i).mp i.property)⟩
  left_inv i := by apply Subtype.ext; exact e.symm_apply_apply i
  right_inv i := by apply Subtype.ext; exact e.apply_symm_apply i

lemma positiveMarginal_relabel {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (c : ℕ) (b : ι → ℝ) (e : Equiv.Perm ι) :
    EqualCapacity.positiveMarginal xi c (b ∘ e.symm) =
      EqualCapacity.positiveMarginal xi c b ∘ e.symm := by
  let S := Existence.PayOnceBounded.positiveSupport b
  let T := Existence.PayOnceBounded.positiveSupport (b ∘ e.symm)
  let E : S ≃ T := positiveSupportEquiv b e
  have hk := kernelMarginal_equiv hxi hxi1 c (fun i : S => b i)
    (fun i => (Existence.PayOnceBounded.mem_positiveSupport b i).mp i.property) E
  funext i
  by_cases hi : 0 < b (e.symm i)
  · have hS : e.symm i ∈ S :=
      (Existence.PayOnceBounded.mem_positiveSupport b (e.symm i)).mpr hi
    have hT : i ∈ T :=
      (Existence.PayOnceBounded.mem_positiveSupport (b ∘ e.symm) i).mpr hi
    change EqualCapacity.onSupport xi c T (b ∘ e.symm) i =
      EqualCapacity.onSupport xi c S b (e.symm i)
    rw [EqualCapacity.onSupport,dif_pos hT,EqualCapacity.onSupport,dif_pos hS]
    have he : (fun j : T => (b ∘ e.symm) j) = (fun j : S => b j) ∘ E.symm := rfl
    rw [he,hk]
    rfl
  · have hS : e.symm i ∉ S := fun h =>
      hi ((Existence.PayOnceBounded.mem_positiveSupport b (e.symm i)).mp h)
    have hT : i ∉ T := fun h =>
      hi ((Existence.PayOnceBounded.mem_positiveSupport (b ∘ e.symm) i).mp h)
    change EqualCapacity.onSupport xi c T (b ∘ e.symm) i =
      EqualCapacity.onSupport xi c S b (e.symm i)
    rw [EqualCapacity.onSupport_outside _ _ _ _ _ hT,
      EqualCapacity.onSupport_outside _ _ _ _ _ hS]

lemma canonicalLottery_relabel {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (c : ℕ) (b : ι → ℝ) (e : Equiv.Perm ι) :
    EqualCapacity.canonicalLottery xi c (b ∘ e.symm) =
      (EqualCapacity.canonicalLottery xi c b).map (fun S => S.map e.toEmbedding) := by
  unfold EqualCapacity.canonicalLottery
  rw [positiveMarginal_relabel hxi hxi1,ExactCapacity.symmetricLottery_equivariant]

lemma equal_pair_law_relabel {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (c : ℕ) (b : ι → ℝ) (e : Equiv.Perm ι) :
    (EqualCapacity.canonicalLottery xi c (b ∘ e.symm)).prod
        (EqualCapacity.canonicalLottery xi c (b ∘ e.symm)) =
      ((EqualCapacity.canonicalLottery xi c b).prod
        (EqualCapacity.canonicalLottery xi c b)).map (embedPair e.toEmbedding) := by
  simp only [canonicalLottery_relabel hxi hxi1 c b e]
  rw [finiteLaw_map_prod]
  rfl

def guardedPairLaw (xi : ℝ) (b : ι → ℝ) (r : ℕ)
    (AB : Finset ι × Finset ι) : FiniteLaw (Finset ι × Finset ι) :=
  let D := Finset.univ \ (AB.1 ∪ AB.2)
  let lam := finiteMultiplier xi b D r
  (ExactCapacity.symmetricLottery (ownerMixedMarginal AB.1 D xi lam b)).prod
    (ExactCapacity.symmetricLottery (ownerMixedMarginal AB.2 D xi lam b))

lemma guardedPairLaw_eq (G : GuardedData ι) :
    guardedPairLaw G.xi G.bid G.residual (G.owner₁,G.owner₂) = G.jointLaw := rfl

omit [Fintype ι] in
lemma guarded_marginal_relabel (xi : ℝ) (b : ι → ℝ) (r : ℕ)
    (E D : Finset ι) (e : Equiv.Perm ι) :
    ownerMixedMarginal (E.map e.toEmbedding) (D.map e.toEmbedding) xi
      (finiteMultiplier xi (b ∘ e.symm) (D.map e.toEmbedding) r) (b ∘ e.symm) =
      ownerMixedMarginal E D xi (finiteMultiplier xi b D r) b ∘ e.symm := by
  have hb : (b ∘ e.symm) ∘ e = b := by funext i; simp
  rw [finiteMultiplier_map,hb]
  funext i
  simp only [ownerMixedMarginal,Finset.mem_map_equiv,Function.comp_apply]

lemma guardedPairLaw_relabel (xi : ℝ) (b : ι → ℝ) (r : ℕ)
    (AB : Finset ι × Finset ι) (e : Equiv.Perm ι) :
    guardedPairLaw xi (b ∘ e.symm) r (embedPair e.toEmbedding AB) =
      (guardedPairLaw xi b r AB).map (embedPair e.toEmbedding) := by
  have hD : Finset.univ \ ((AB.1.map e.toEmbedding) ∪ (AB.2.map e.toEmbedding)) =
      (Finset.univ \ (AB.1 ∪ AB.2)).map e.toEmbedding := by
    rw [Finset.map_sdiff,Finset.map_univ_equiv,Finset.map_union]
  unfold guardedPairLaw embedPair
  dsimp only
  rw [hD,guarded_marginal_relabel,guarded_marginal_relabel,
    ExactCapacity.symmetricLottery_equivariant,ExactCapacity.symmetricLottery_equivariant,
    finiteLaw_map_prod]
  rfl

def sourceGuardedPairLaw [Nonempty ι] (xi : ℝ) (b : ι → ℝ) (r K0 K1 : ℕ) :
    FiniteLaw (Finset ι × Finset ι) :=
  FiniteLaw.finiteMix (sourceOwnersLaw b K0 K1) (guardedPairLaw xi b r)

lemma sourceGuardedPairLaw_relabel [Nonempty ι]
    (xi : ℝ) (b : ι → ℝ) (r K0 K1 : ℕ) (e : Equiv.Perm ι) :
    sourceGuardedPairLaw xi (b ∘ e.symm) r K0 K1 =
      (sourceGuardedPairLaw xi b r K0 K1).map (embedPair e.toEmbedding) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [sourceGuardedPairLaw,FiniteLaw.expect_finiteMix,sourceOwnersLaw_relabel,
    FiniteLaw.expect_map,FiniteLaw.expect_map,sourceGuardedPairLaw,FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro AB
  rw [show (AB.1.map e.toEmbedding,AB.2.map e.toEmbedding) =
    embedPair e.toEmbedding AB from rfl,guardedPairLaw_relabel,FiniteLaw.expect_map]

end FiniteTransport

section Physical
variable {N : ℕ}

def activeNameEmbedding (kind : Fin N → Fin 4) (e : Equiv.Perm (Fin (N+1))) :
    ActivePatternIndex kind ↪ Fin (N+1) where
  toFun i := e i.val
  inj' := fun _ _ h => Subtype.ext (e.injective h)

lemma activeNameEmbedding_focal (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) :
    activeNameEmbedding kind e (activePatternFocal kind) = e 0 := rfl

def namedPhysicalAllocationLaw (xi z L W : ℝ) (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (bid : ℝ) (rows : ActiveCountRows N) :
    FiniteLaw (Finset (Fin (N+1)) × Finset (Fin (N+1))) :=
  let t : ActivePhysicalData N := (0,bid,rows)
  let T := activePatternTemplate c kind
  let b := activePhysicalBids kind t
  if activePatternGuarded xi L W c z kind then
    (sourceGuardedPairLaw xi (activePhysicalActiveBids kind t)
      (activePatternResidual c z kind) (activePatternOwner c z kind 0)
      (activePatternOwner c z kind 1)).map (embedPair (activeNameEmbedding kind e))
  else if T.residual₀ = T.residual₁ then
    (EqualCapacity.canonicalLottery xi T.residual₀ (b ∘ e.symm)).prod
      (EqualCapacity.canonicalLottery xi T.residual₀ (b ∘ e.symm))
  else FiniteLaw.dirac ((T.relabel e).selection (1-xi) (b ∘ e.symm))

lemma sourceGuardedPairLaw_active_count {xi L W : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (c : ℕ) (z : ℝ) (kind : Fin N → Fin 4)
    (hg : activePatternGuarded xi L W c z kind)
    (b : ActivePatternIndex kind → ℝ) (hb : ∀ i,b i ∈ Icc L W)
    (i : ActivePatternIndex kind) (j : Fin 3) :
    pairCountMass (sourceGuardedPairLaw xi b (activePatternResidual c z kind)
      (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)) i j =
      sourceCountMass xi b (activePatternResidual c z kind)
        (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) i j := by
  unfold pairCountMass sourceGuardedPairLaw sourceCountMass
  rw [FiniteLaw.prob_eq_expect,FiniteLaw.expect_finiteMix]
  apply expect_congr_on_support
  intro AB hAB
  obtain ⟨G,hxiG,hbid,h0,h1,hr,_,_⟩ :=
    activePattern_guardedData hxi hxi1 hL c z kind hg b hb AB.1 AB.2 hAB
  have he : guardedPairLaw xi b (activePatternResidual c z kind) AB = G.jointLaw := by
    rw [←hxiG,←hbid,←hr,show AB=(G.owner₁,G.owner₂) from (Prod.ext h0 h1).symm]
    rfl
  rw [he,←FiniteLaw.prob_eq_expect]
  have hh := congrFun (guarded_actual_count_mass G i) j
  simpa only [pairCountMass,hxiG,hbid,h0,h1,hr] using hh

theorem namedPhysicalAllocationLaw_count {xi L W : ℝ}
    (hxi : 0 < xi) (hxi1 : xi < 1) (hL : 0 < L)
    (z : ℝ) (c : ℕ) (kind : Fin N → Fin 4)
    (e : Equiv.Perm (Fin (N+1))) (bid : ℝ) (rows : ActiveCountRows N)
    (hb : bid ∈ Icc L W) (hrows : ∀ i,rows.2 i ∈ Icc L W)
    (hcopy : ∀ A B : Finset (Fin (N+1)) × Finset (Fin (N+1)),
      LowBody.CompleteInformation.potential (1-xi)
          (activePhysicalBids kind (0,bid,rows)) A.1 A.2 =
        LowBody.CompleteInformation.potential (1-xi)
          (activePhysicalBids kind (0,bid,rows)) B.1 B.2 →
        LowBody.focalCopy A 0 = LowBody.focalCopy B 0) (j : Fin 3) :
    pairCountMass (namedPhysicalAllocationLaw xi z L W c kind e bid rows) (e 0) j =
      activePhysicalPatternCountMass xi z L W c kind bid rows j := by
  unfold namedPhysicalAllocationLaw activePhysicalPatternCountMass
  dsimp only
  split_ifs with hg he
  · rw [←activeNameEmbedding_focal kind e,pairCountMass_embed]
    exact sourceGuardedPairLaw_active_count hxi hxi1 hL c z kind hg _
      (fun i => by
        rcases Fin.eq_zero_or_eq_succ i.val with hi | ⟨k, hk⟩
        · simpa only [activePhysicalActiveBids, hi, Fin.cases_zero] using hb
        · simpa only [activePhysicalActiveBids, hk, Fin.cases_succ] using hrows k) _ j
  · rw [equal_pair_law_relabel hxi hxi1]
    exact (pairCountMass_embed _ e.toEmbedding 0 j).trans
      (equal_actual_count_mass hxi hxi1 _ _ 0 j)
  · rw [pairCountMass,FiniteLaw.prob_eq_expect,FiniteLaw.expect_dirac]
    have hc := (activePatternTemplate c kind).selection_focalCopy_relabel e (1-xi)
      (activePhysicalBids kind (0,bid,rows)) 0
      (fun A B _ _ h => hcopy A B h)
    rw [hc]
    simp only [pointMass,eq_comm]

end Physical
end FCAppendix.Affine.Hybrid.Finish01
