import FCAppendix.Affine.Hybrid.Native02.FullContextRows
import FCAppendix.Affine.Hybrid.Native02.PhysicalRowIntegration
import FCAppendix.Affine.Hybrid.Native02.OwnerEquivalence

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open scoped BigOperators

section PrivateLaw
variable {m c : ℕ}

theorem privateContextLaw_expect_pair (C : ContextPolicy m c unitInterval)
    (X : ClassifiedContext m) (i : Fin m) (f : Fin 3 → ℝ) :
    (privateContextLaw C X i).expect f =
      ∫ s : unitInterval × unitInterval,
        f (focalCopy (C.select 0 X s.1, C.select 1 X s.2) i)
        ∂((volume : Measure unitInterval).prod volume) := by
  rw [privateContextLaw, CountLaw.expect_ofMeasure]
  let H : unitInterval × unitInterval → ℝ :=
    fun s => f (focalCopy (C.select 0 X s.1, C.select 1 X s.2) i)
  have hH : Measurable H :=
    (measurable_of_countable (fun ST : Finset (Fin m) × Finset (Fin m) =>
      f (focalCopy ST i))).comp
      (((C.measurable 0).comp (measurable_const.prodMk measurable_fst)).prodMk
        ((C.measurable 1).comp (measurable_const.prodMk measurable_snd)))
  have hp := measurePreserving_piFinTwo
    (fun _ : Fin 2 => (volume : Measure unitInterval))
  have hi := integral_map (μ := Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))
    hp.measurable.aemeasurable hH.aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

lemma realizedPayoff_focalCopy (eta v b : ℝ) (i : Fin m)
    (ST : Finset (Fin m) × Finset (Fin m)) :
    realizedPayoff eta v b (focalCopy ST i).val = broadcastPayoff eta v b i ST := by
  by_cases h0 : i ∈ ST.1 <;> by_cases h1 : i ∈ ST.2 <;>
    simp [realizedPayoff, focalCopy, broadcastPayoff, h0, h1]
  ring

lemma singleton_focalCopy (v b : ℝ) (i : Fin m)
    (ST : Finset (Fin m) × Finset (Fin m)) :
    ((v-b)/2)*((focalCopy ST i).val : ℝ) = singletonPayoff v b i ST := by
  by_cases h0 : i ∈ ST.1 <;> by_cases h1 : i ∈ ST.2 <;>
    simp [focalCopy, singletonPayoff, h0, h1]
  ring

end PrivateLaw

namespace FullContext
variable {N m : ℕ}

theorem privateContextLaw_expect_proposal {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (d L U z : ℝ) (c : ℕ) (μ : Measure ℝ) (X : ClassifiedContext m)
    (hp : useProposal xi d L U z c μ X) (i : Fin m) (f : Fin 3 → ℝ) :
    (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ) X i).expect f =
      ((proposalLaw xi d L U z c μ 0 X).prod
        (proposalLaw xi d L U z c μ 1 X)).expect (fun ST => f (focalCopy ST i)) := by
  rw [privateContextLaw_expect_pair]
  let C := contextPolicy (m := m) hxi hxi1 d L U z c μ
  let F : unitInterval × unitInterval → Finset (Fin m) × Finset (Fin m) :=
    fun s => (C.select 0 X s.1, C.select 1 X s.2)
  have hm : Measurable F :=
    ((C.measurable 0).comp (measurable_const.prodMk measurable_fst)).prodMk
      ((C.measurable 1).comp (measurable_const.prodMk measurable_snd))
  have he := FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure
    ((volume : Measure unitInterval).prod volume) F hm
    ((proposalLaw xi d L U z c μ 0 X).prod (proposalLaw xi d L U z c μ 1 X))
    (contextPolicy_private_pair_law hxi hxi1 d L U z c μ X hp)
  have hi := FiniteLaw.expect_ofMeasure ((volume : Measure unitInterval).prod volume)
    F hm (fun ST => f (focalCopy ST i))
  rw [he] at hi
  exact hi.symm

lemma measurable_table_pair_expect {xi : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (T : TableIndex m) (b : Fin m → ℝ)
    (f : (Finset (Fin m) × Finset (Fin m)) → ℝ) :
    Measurable (fun u : unitInterval =>
      ((tableLaw xi T 0 b u).prod (tableLaw xi T 1 b u)).expect f) := by
  dsimp only [FiniteLaw.expect, FiniteLaw.prod]
  apply Finset.measurable_sum
  intro ST _
  exact (((measurable_tableLaw_mass_fixed hxi hxi1 T 0 ST.1).comp
    (measurable_const.prodMk measurable_id)).mul
      ((measurable_tableLaw_mass_fixed hxi hxi1 T 1 ST.2).comp
        (measurable_const.prodMk measurable_id))).mul measurable_const

lemma sourceRow_active_entry (kind : Fin N → Fin 4) (low active : Fin N → ℝ)
    (v b : ℝ) (i : ActivePatternIndex kind) :
    entryBid ((sourceRowContext kind low active b).1 i) =
      activePhysicalActiveBids kind (v, b, (fun _ => 0), active) i := by
  have hh : ∀ (k : Fin (N+1)) (hk : activePatternPred kind k),
      entryBid ((sourceRowContext kind low active b).1 k) =
        activePhysicalActiveBids kind (v, b, (fun _ => 0), active) ⟨k, hk⟩ := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · intro hk
      rfl
    · intro hk
      change kind j = 1 at hk
      have h0 : kind j ≠ 0 := by simpa only [hk] using (show (1 : Fin 4) ≠ 0 by decide)
      simp only [sourceRowContext_succ, if_neg h0, if_pos hk, entryBid,
        activePhysicalActiveBids, Fin.cases_succ]
  exact hh i.val i.property

lemma sourceRow_active_mem_iff {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1))) (i : Fin (N+1)) :
    i ∈ activeSet d (NativeContinuation.reindexContext e
      (sourceRowContext kind low active b)).1 ↔ activePatternPred kind (e i) := by
  change i ∈ activeSet d ((sourceRowContext kind low active b).1 ∘ e) ↔ _
  rw [activeSet_reindex, activeSet_sourceRow hsep kind low active b hlow hactive hb]
  simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_filter,
    Finset.mem_univ, true_and]

def sourceRowActiveEquiv {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1))) :
    ActivePatternIndex kind ≃ activeSet d (NativeContinuation.reindexContext e
      (sourceRowContext kind low active b)).1 where
  toFun i := ⟨e.symm i, (sourceRow_active_mem_iff hsep kind low active b hlow hactive hb e _).mpr
    (by simpa only [Equiv.apply_symm_apply] using i.property)⟩
  invFun i := ⟨e i, (sourceRow_active_mem_iff hsep kind low active b hlow hactive hb e _).mp
    i.property⟩
  left_inv i := Subtype.ext (e.apply_symm_apply i)
  right_inv i := Subtype.ext (e.symm_apply_apply i)

lemma sourceRowActiveEquiv_bid {d L U : ℝ} (hsep : d < L)
    (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (v b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1))) :
    let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
    let E := sourceRowActiveEquiv hsep kind low active b hlow hactive hb e
    (fun i : activeSet d X.1 => entryBid (X.1 i)) =
      activePhysicalActiveBids kind (v, b, (fun _ => 0), active) ∘ E.symm := by
  funext i
  exact sourceRow_active_entry kind low active v b
    ⟨e i, (sourceRow_active_mem_iff hsep kind low active b hlow hactive hb e i).mp i.property⟩

theorem sourceRow_low_integral_table {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnoatoms : ∀ b, μ {b} = 0) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (b : ℝ)
    (hactive : ∀ j, active j ∈ Icc L U) (hb : b ∈ Icc L U)
    (hguard : activePatternGuarded xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) (f : Fin 3 → ℝ) :
    let C := contextPolicy (m := N+1) hxi hxi1 d L U z c μ
    let X0 := NativeContinuation.reindexContext e
      (sourceRowContext kind (fun _ => 0) active b)
    (∫ low : Fin N → ℝ, (privateContextLaw C
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
      (e.symm 0)).expect f ∂Measure.pi (fun _ : Fin N => μ)) =
      ∫ u : unitInterval,
        ((tableLaw xi (tableIndex d L U z c X0) 0 (fun i => entryBid (X0.1 i)) u).prod
          (tableLaw xi (tableIndex d L U z c X0) 1 (fun i => entryBid (X0.1 i)) u)).expect
          (fun ST => f (focalCopy ST (e.symm 0))) ∂volume := by
  dsimp only
  let X := fun low : Fin N → ℝ => NativeContinuation.reindexContext e
    (sourceRowContext kind low active b)
  let X0 := X (fun _ => 0)
  let T := tableIndex d L U z c X0
  let F := fun u : unitInterval =>
    ((tableLaw xi T 0 (fun i => entryBid (X0.1 i)) u).prod
      (tableLaw xi T 1 (fun i => entryBid (X0.1 i)) u)).expect
      (fun ST => f (focalCopy ST (e.symm 0)))
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hzero : ∀ _ : Fin N, (0 : ℝ) ∈ Icc 0 d := fun _ => ⟨le_rfl, hd⟩
  have hlowcount := hguard.2.2.2.2.2
  have hlows : ∀ᵐ low ∂Measure.pi (fun _ : Fin N => μ), ∀ j, low j ∈ Icc 0 d :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hμ)
  have hF : Measurable F := measurable_table_pair_expect hxi hxi1 T _ _
  have he : ∀ᵐ low ∂Measure.pi (fun _ : Fin N => μ),
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ) (X low) (e.symm 0)).expect f =
        F (maskedLowSeed μ kind hlowcount low) := by
    filter_upwards [hlows] with low hlow
    have hp := (useProposal_sourceRow_iff hxi hxi1 z c μ hd hL hgap
      kind low active b hlow hactive hb e).mpr hguard
    have hA : activeSet d (X low).1 = activeSet d X0.1 := by
      change activeSet d ((sourceRowContext kind low active b).1 ∘ e) =
        activeSet d ((sourceRowContext kind (fun _ => 0) active b).1 ∘ e)
      rw [activeSet_reindex, activeSet_reindex,
        activeSet_sourceRow hsep kind low active b hlow hactive hb,
        activeSet_sourceRow hsep kind (fun _ => 0) active b hzero hactive hb]
    have hT : tableIndex d L U z c (X low) = T := by
      rw [tableIndex_sourceRow hsep z c kind low active b hlow hactive hb e,
        show T = tableIndex d L U z c X0 from rfl,
        tableIndex_sourceRow hsep z c kind (fun _ => 0) active b hzero hactive hb e, hA]
    have hseed : (observedLowMinimumSeed d μ (X low).1).getD 0 =
        maskedLowSeed μ kind hlowcount low := by
      change (seedOnList μ (lowOnlyList d
        ((sourceRowContext kind low active b).1 ∘ e))).getD 0 = _
      rw [lowOnlyList_reindex, lowOnlyList_sourceRow hsep kind low active b hlow hactive hb]
      exact congrArg (fun o : Option unitInterval => o.getD 0)
        (maskedLowSeed_formula μ kind hlowcount e low)
    have hbid : ∀ i ∈ T.1, entryBid ((X low).1 i) = entryBid (X0.1 i) := by
      intro i hi
      have hp0 : activePatternPred kind (e i) :=
        (sourceRow_active_mem_iff hsep kind (fun _ => 0) active b hzero hactive hb e i).mp hi
      exact (sourceRow_active_entry kind low active 0 b ⟨e i, hp0⟩).trans
        (sourceRow_active_entry kind (fun _ => 0) active 0 b ⟨e i, hp0⟩).symm
    have hlaw (j : Fin 2) : proposalLaw xi d L U z c μ j (X low) =
        tableLaw xi T j (fun i => entryBid (X0.1 i)) (maskedLowSeed μ kind hlowcount low) := by
      unfold proposalLaw
      rw [hT, hseed]
      exact tableLaw_congr_active xi T j _ _ _ hbid
    rw [privateContextLaw_expect_proposal hxi hxi1 d L U z c μ (X low) hp]
    rw [hlaw 0, hlaw 1]
  calc
    _ = ∫ low : Fin N → ℝ, F (maskedLowSeed μ kind hlowcount low)
        ∂Measure.pi (fun _ : Fin N => μ) := integral_congr_ae he
    _ = ∫ u : unitInterval, F u ∂volume := by
      rw [← maskedLowSeed_law μ hnoatoms kind hlowcount]
      exact (integral_map (measurable_maskedLowSeed μ kind hlowcount).aemeasurable
        hF.aestronglyMeasurable).symm

theorem sourceRow_private_payoff_guarded {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnoatoms : ∀ b, μ {b} = 0) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (eta v b : ℝ)
    (hactive : ∀ j, active j ∈ Icc L U) (hb : b ∈ Icc L U)
    (hguard : activePatternGuarded xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    (∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect (fun k => realizedPayoff eta v b k.val)
      ∂Measure.pi (fun _ : Fin N => μ)) =
      sourceOwnerPayoff xi eta v
        (activePhysicalActiveBids kind (v, b, (fun _ => 0), active))
        (activePatternResidual c z kind) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1) (activePatternFocal kind) := by
  rw [sourceRow_low_integral_table hxi hxi1 z c μ hnoatoms hd hL hgap hμ
    kind active b hactive hb hguard e]
  simp_rw [realizedPayoff_focalCopy]
  let X := NativeContinuation.reindexContext e
    (sourceRowContext kind (fun _ => 0) active b)
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hzero : ∀ _ : Fin N, (0 : ℝ) ∈ Icc 0 d := fun _ => ⟨le_rfl, hd⟩
  let E := sourceRowActiveEquiv hsep kind (fun _ => 0) active b hzero hactive hb e
  let i := E (activePatternFocal kind)
  letI : Nonempty (activeSet d X.1) := ⟨i⟩
  have hi : (i : Fin (N+1)) = e.symm 0 := rfl
  have hbi : entryBid (X.1 i) = b := by
    change entryBid ((sourceRowContext kind (fun _ => 0) active b).1 (e (e.symm 0))) = b
    simp only [Equiv.apply_symm_apply, sourceRowContext_zero, entryBid]
  have hp := (useProposal_sourceRow_iff hxi hxi1 z c μ hd hL hgap
    kind (fun _ => 0) active b hzero hactive hb e).mpr hguard
  have hbox : ∀ j ∈ activeSet d X.1, entryBid (X.1 j) ∈ Icc L U := by
    intro j hj
    exact sourceRow_active_box hsep kind (fun _ => 0) active b hzero hactive hb (e j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩)
  have hav := tableLaw_uniform_common_payoff hxi hxi1 d L U z c hL X hp.1 hbox eta v i
  rw [hbi, hi] at hav
  rw [hav, tableIndex_sourceRow hsep z c kind (fun _ => 0) active b hzero hactive hb e]
  dsimp only
  rw [sourceRowActiveEquiv_bid hsep kind (fun _ => 0) active v b hzero hactive hb e]
  exact sourceOwnerPayoff_equiv E xi eta v _ _ _ _ (activePatternFocal kind)
    hguard.1 hguard.2.2.1 hguard.2.2.2.1.le

theorem sourceRow_private_singleton_guarded {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnoatoms : ∀ b, μ {b} = 0) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d)
    (kind : Fin N → Fin 4) (active : Fin N → ℝ) (v b : ℝ)
    (hactive : ∀ j, active j ∈ Icc L U) (hb : b ∈ Icc L U)
    (hguard : activePatternGuarded xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    (∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect (fun k => ((v-b)/2)*(k.val : ℝ))
      ∂Measure.pi (fun _ : Fin N => μ)) =
      sourceSingletonPayoff xi v
        (activePhysicalActiveBids kind (v, b, (fun _ => 0), active))
        (activePatternResidual c z kind) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1) (activePatternFocal kind) := by
  rw [sourceRow_low_integral_table hxi hxi1 z c μ hnoatoms hd hL hgap hμ
    kind active b hactive hb hguard e]
  simp_rw [singleton_focalCopy]
  let X := NativeContinuation.reindexContext e
    (sourceRowContext kind (fun _ => 0) active b)
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hzero : ∀ _ : Fin N, (0 : ℝ) ∈ Icc 0 d := fun _ => ⟨le_rfl, hd⟩
  let E := sourceRowActiveEquiv hsep kind (fun _ => 0) active b hzero hactive hb e
  let i := E (activePatternFocal kind)
  letI : Nonempty (activeSet d X.1) := ⟨i⟩
  have hi : (i : Fin (N+1)) = e.symm 0 := rfl
  have hbi : entryBid (X.1 i) = b := by
    change entryBid ((sourceRowContext kind (fun _ => 0) active b).1 (e (e.symm 0))) = b
    simp only [Equiv.apply_symm_apply, sourceRowContext_zero, entryBid]
  have hp := (useProposal_sourceRow_iff hxi hxi1 z c μ hd hL hgap
    kind (fun _ => 0) active b hzero hactive hb e).mpr hguard
  have hbox : ∀ j ∈ activeSet d X.1, entryBid (X.1 j) ∈ Icc L U := by
    intro j hj
    exact sourceRow_active_box hsep kind (fun _ => 0) active b hzero hactive hb (e j)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩)
  have hav := tableLaw_uniform_common_singleton hxi hxi1 d L U z c hL X hp.1 hbox v i
  rw [hbi, hi] at hav
  rw [hav, tableIndex_sourceRow hsep z c kind (fun _ => 0) active b hzero hactive hb e]
  dsimp only
  rw [sourceRowActiveEquiv_bid hsep kind (fun _ => 0) active v b hzero hactive hb e]
  exact sourceSingletonPayoff_equiv E xi v _ _ _ _ (activePatternFocal kind)
    hguard.1 hguard.2.2.1 hguard.2.2.2.1.le

end FullContext
end FCAppendix.Affine.Hybrid.Native02
