import FCAppendix.Affine.Hybrid.Native02.SourceRowPayoff
import FCAppendix.Affine.Hybrid.NativeLowContextPayoff

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Classical
open scoped BigOperators

section FiniteTies
variable {N : ℕ}

theorem ae_iid_real_linear_ne (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hnoatoms : ∀ b, μ {b} = 0) (a : Fin N → ℝ) (j : Fin N)
    (hj : a j ≠ 0) (t : ℝ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ), (∑ i, a i*x i) ≠ t := by
  letI : NullSingletonClass μ := ⟨hnoatoms⟩
  cases N with
  | zero => exact Fin.elim0 j
  | succ M =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M+1) => ℝ) j
    let f := fun x : Fin (M+1) → ℝ => ∑ i, a i*x i
    have hfm : Measurable f := by dsimp [f]; fun_prop
    have hS : MeasurableSet {y : ℝ × (Fin M → ℝ) | f (e.symm y) ≠ t} :=
      (measurableSet_eq_fun (hfm.comp e.symm.measurable) measurable_const).compl
    have he (x : ℝ) (r : Fin M → ℝ) :
        f (e.symm (x,r)) = a j*x + ∑ k, a (j.succAbove k)*r k := by
      dsimp only [f]
      rw [Fin.sum_univ_succAbove _ j]
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    have hprod : ∀ᵐ y ∂μ.prod (Measure.pi (fun _ : Fin M => μ)), f (e.symm y) ≠ t := by
      apply (Measure.ae_prod_iff_ae_ae hS).mpr
      apply (Measure.ae_ae_comm hS).mpr
      apply ae_of_all
      intro r
      filter_upwards [LowBody.ae_affine_ne μ (a j) (∑ k, a (j.succAbove k)*r k) t hj]
        with x hx
      rwa [he]
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (M+1) => μ) j
    have hh := hp.quasiMeasurePreserving.ae hprod
    simpa only [e, MeasurableEquiv.symm_apply_apply] using hh

lemma physical_potential_difference (kind : Fin N → Fin 4) (κ v b : ℝ)
    (low active : Fin N → ℝ) (P Q : Finset (Fin (N+1)) × Finset (Fin (N+1))) :
    CompleteInformation.potential κ (activePhysicalBids kind (v,b,low,active)) P.1 P.2 -
      CompleteInformation.potential κ (activePhysicalBids kind (v,b,low,active)) Q.1 Q.2 =
      (copyCoefficient κ P 0-copyCoefficient κ Q 0)*b +
        (∑ j, (if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*low j) +
        ∑ j, (if kind j=1 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*active j := by
  rw [potential_eq_copyCoefficient, potential_eq_copyCoefficient,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [activePhysicalBids, Fin.cons_zero, Fin.cons_succ]
  have hS :
      (∑ j, copyCoefficient κ P j.succ*(if kind j=0 then low j else if kind j=1 then active j else 0)) -
        (∑ j, copyCoefficient κ Q j.succ*(if kind j=0 then low j else if kind j=1 then active j else 0)) =
      (∑ j, (if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*low j) +
        ∑ j, (if kind j=1 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0)*active j := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h0 : kind j = 0
    · have h1 : kind j ≠ 1 := by simpa only [h0] using (show (0 : Fin 4) ≠ 1 by decide)
      simp only [if_pos h0, if_neg h1]
      ring
    · by_cases h1 : kind j = 1
      · simp [h1]
        ring
      · simp [h0,h1]
  linear_combination hS

theorem ae_physical_ties_same_focalCopy {κ b : ℝ} (hκ : 0 < κ) (hb : b ≠ 0)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hμnull : ∀ y, μ {y} = 0) (hBnull : ∀ y, B {y} = 0)
    (kind : Fin N → Fin 4) (v : ℝ) :
    ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => B)),
      ∀ P Q : Finset (Fin (N+1)) × Finset (Fin (N+1)),
      CompleteInformation.potential κ (activePhysicalBids kind (v,b,r.1,r.2)) P.1 P.2 =
        CompleteInformation.potential κ (activePhysicalBids kind (v,b,r.1,r.2)) Q.1 Q.2 →
      focalCopy P 0 = focalCopy Q 0 := by
  apply ae_all_iff.mpr
  intro P
  apply ae_all_iff.mpr
  intro Q
  by_cases hcopy : focalCopy P 0 = focalCopy Q 0
  · exact ae_of_all _ (fun _ _ => hcopy)
  · let aL := fun j : Fin N =>
      if kind j=0 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0
    let aA := fun j : Fin N =>
      if kind j=1 then copyCoefficient κ P j.succ-copyCoefficient κ Q j.succ else 0
    let a0 := copyCoefficient κ P 0-copyCoefficient κ Q 0
    have h0 : a0 ≠ 0 := sub_ne_zero.mpr (copyCoefficient_ne_of_focalCopy_ne hκ P Q 0 hcopy)
    have hS : MeasurableSet {r : (Fin N → ℝ) × (Fin N → ℝ) |
        a0*b + (∑ j, aL j*r.1 j) + (∑ j, aA j*r.2 j) ≠ 0} := by
      apply (measurableSet_eq_fun ?_ measurable_const).compl
      fun_prop
    have hn : ∀ᵐ r ∂(Measure.pi (fun _ : Fin N => μ)).prod (Measure.pi (fun _ : Fin N => B)),
        a0*b + (∑ j, aL j*r.1 j) + (∑ j, aA j*r.2 j) ≠ 0 := by
      by_cases hL : ∃ j, aL j ≠ 0
      · obtain ⟨j,hj⟩ := hL
        apply (Measure.ae_prod_iff_ae_ae hS).mpr
        apply (Measure.ae_ae_comm hS).mpr
        apply ae_of_all
        intro active
        filter_upwards [ae_iid_real_linear_ne μ hμnull aL j hj
          (-a0*b-∑ k, aA k*active k)] with low hl he
        apply hl
        linarith
      · by_cases hA : ∃ j, aA j ≠ 0
        · obtain ⟨j,hj⟩ := hA
          apply (Measure.ae_prod_iff_ae_ae hS).mpr
          apply ae_of_all
          intro low
          filter_upwards [ae_iid_real_linear_ne B hBnull aA j hj
            (-a0*b-∑ k, aL k*low k)] with active ha he
          apply ha
          linarith
        · have hL0 : ∀ j, aL j = 0 := by simpa only [not_exists, not_not] using hL
          have hA0 : ∀ j, aA j = 0 := by simpa only [not_exists, not_not] using hA
          apply ae_of_all
          intro r
          simpa only [hL0, hA0, zero_mul, Finset.sum_const_zero, add_zero] using mul_ne_zero h0 hb
    filter_upwards [hn] with r hr he
    apply False.elim (hr ?_)
    have hh := physical_potential_difference kind κ v b r.1 r.2 P Q
    rw [he, sub_self] at hh
    exact hh.symm

end FiniteTies

namespace FullContext
variable {N : ℕ}

lemma sourceRow_entryBid (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (v b : ℝ) :
    (fun i => entryBid ((sourceRowContext kind low active b).1 i)) =
      activePhysicalBids kind (v,b,low,active) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rw [sourceRowContext_succ]
    by_cases h0 : kind j = 0 <;> by_cases h1 : kind j = 1 <;>
      simp [activePhysicalBids, h0, h1, entryBid]

lemma sourceRow_entry_bounds {d L U : ℝ} (hd : 0 ≤ d) (hL : 0 < L)
    (hdU : d ≤ U) (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (i : Fin (N+1)) :
    entryBid ((sourceRowContext kind low active b).1 i) ∈ Icc 0 U := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨hL.le.trans hb.1, hb.2⟩
  · rw [sourceRowContext_succ]
    by_cases h0 : kind j = 0
    · simp only [if_pos h0, entryBid]
      exact ⟨(hlow j).1, (hlow j).2.trans hdU⟩
    · by_cases h1 : kind j = 1
      · simp only [if_neg h0, if_pos h1, entryBid]
        exact ⟨hL.le.trans (hactive j).1, (hactive j).2⟩
      · simp only [if_neg h0, if_neg h1, entryBid]
        exact ⟨le_rfl, hd.trans hdU⟩

lemma sourceRow_support (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (b : ℝ) :
    Finset.univ.filter (fun i => (sourceRowContext kind low active b).1 i ≠ none) =
      Finset.univ.filter (lowerPatternPred kind) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sourceRowContext_zero, lowerPatternPred]
  · rw [sourceRowContext_succ]
    by_cases h0 : kind j = 0 <;> by_cases h1 : kind j = 1 <;>
      simp [lowerPatternPred, h0, h1]

lemma sourceRow_clipped_template (kind : Fin N → Fin 4) (low active : Fin N → ℝ)
    (b : ℝ) (c : ℕ) (e : Equiv.Perm (Fin (N+1))) :
    let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
    (NativeContinuation.receivedTemplate X.1 (NativeContinuation.residual c 0 X)
      (NativeContinuation.residual c 1 X)).clipped =
        (activePatternTemplate c kind).relabel e.symm := by
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  have hs : Finset.univ.filter (fun i => X.1 i ≠ none) =
      (Finset.univ.filter (lowerPatternPred kind)).map e.symm.toEmbedding := by
    have he : Finset.univ.filter (fun i => X.1 i ≠ none) =
        (Finset.univ.filter (fun i => (sourceRowContext kind low active b).1 i ≠ none)).map
          e.symm.toEmbedding := by
      ext i
      simp [X, NativeContinuation.reindexContext]
    rw [he, sourceRow_support]
  have hext (T S : PureTemplate (Fin (N+1))) (hs : T.support=S.support)
      (h0 : T.residual₀=S.residual₀) (h1 : T.residual₁=S.residual₁) : T=S := by
    cases T
    cases S
    simp_all
  apply hext
  · exact hs
  · simp only [PureTemplate.clipped, NativeContinuation.receivedTemplate,
      PureTemplate.relabel, activePatternTemplate]
    rw [hs, Finset.card_map]
    change min _ (c-contextUpper 0 (sourceRowContext kind low active b)) = _
    rw [sourceRow_upper]
  · simp only [PureTemplate.clipped, NativeContinuation.receivedTemplate,
      PureTemplate.relabel, activePatternTemplate]
    rw [hs, Finset.card_map]
    change min _ (c-contextUpper 1 (sourceRowContext kind low active b)) = _
    rw [sourceRow_upper]

lemma all_focal_ties_relabel {m : ℕ} (κ : ℝ) (b : Fin m → ℝ)
    (i : Fin m) (e : Equiv.Perm (Fin m))
    (hg : ∀ P Q : Finset (Fin m) × Finset (Fin m),
      CompleteInformation.potential κ b P.1 P.2 = CompleteInformation.potential κ b Q.1 Q.2 →
      focalCopy P i = focalCopy Q i) :
    ∀ P Q : Finset (Fin m) × Finset (Fin m),
      CompleteInformation.potential κ (b ∘ e.symm) P.1 P.2 =
        CompleteInformation.potential κ (b ∘ e.symm) Q.1 Q.2 →
      focalCopy P (e i) = focalCopy Q (e i) := by
  have hb : (b ∘ e.symm) ∘ e = b := by funext k; simp
  have hp (P : Finset (Fin m) × Finset (Fin m)) :
      CompleteInformation.potential κ b (relabelPair e.symm P).1 (relabelPair e.symm P).2 =
        CompleteInformation.potential κ (b ∘ e.symm) P.1 P.2 := by
    simpa only [Equiv.symm_symm, hb] using potential_relabel κ (b ∘ e.symm) e.symm P
  intro P Q hPQ
  have hh := hg (relabelPair e.symm P) (relabelPair e.symm Q)
    ((hp P).trans (hPQ.trans (hp Q).symm))
  have hP := focalCopy_relabel e.symm P (e i)
  have hQ := focalCopy_relabel e.symm Q (e i)
  simp only [Equiv.symm_apply_apply] at hP hQ
  rwa [hP, hQ] at hh

theorem sourceRow_private_payoff_fallback {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ : Measure ℝ) (hd : 0 ≤ d) (hL : 0 < L)
    (hgap : d < (1-xi)*L) (kind : Fin N → Fin 4) (low active : Fin N → ℝ) (v b : ℝ)
    (hlow : ∀ j, low j ∈ Icc 0 d) (hactive : ∀ j, active j ∈ Icc L U)
    (hb : b ∈ Icc L U) (e : Equiv.Perm (Fin (N+1)))
    (hguard : ¬ activePatternGuarded xi L U c z kind)
    (hgeneric : ∀ P Q : Finset (Fin (N+1)) × Finset (Fin (N+1)),
      CompleteInformation.potential (1-xi) (activePhysicalBids kind (v,b,low,active)) P.1 P.2 =
        CompleteInformation.potential (1-xi) (activePhysicalBids kind (v,b,low,active)) Q.1 Q.2 →
      focalCopy P 0 = focalCopy Q 0) :
    (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
      (e.symm 0)).expect (fun k => realizedPayoff (1-2*xi) v b k.val) =
      activePhysicalPatternPayoff xi z L U c kind (v,b,low,active) := by
  let X := NativeContinuation.reindexContext e (sourceRowContext kind low active b)
  let bids := activePhysicalBids kind (v,b,low,active)
  let T := activePatternTemplate c kind
  have hsep : d < L := hgap.trans (by nlinarith [mul_pos hxi hL])
  have hdU : d ≤ U := hsep.le.trans (hb.1.trans hb.2)
  have hX : NonnegativeList X.1 := fun i =>
    (sourceRow_entry_bounds hd hL hdU kind low active b hlow hactive hb (e i)).1
  have hXU : ∀ i, entryBid (X.1 i) ≤ U := fun i =>
    (sourceRow_entry_bounds hd hL hdU kind low active b hlow hactive hb (e i)).2
  have hentry : (fun i => entryBid (X.1 i)) = bids ∘ e := by
    funext i
    exact congrFun (sourceRow_entryBid kind low active v b) (e i)
  have hbid : ResidualPotential.bid X.1 = bids ∘ e := by
    funext i
    change max (entryBid (X.1 i)) 0 = _
    rw [max_eq_left (hX i)]
    exact congrFun hentry i
  have hbi : entryBid (X.1 (e.symm 0)) = b := by
    simpa only [Function.comp_apply,Equiv.apply_symm_apply,bids,activePhysicalBids,Fin.cons_zero]
      using congrFun hentry (e.symm 0)
  have herase : NativeContinuation.eraseActiveList (∅ : Finset (Fin (N+1))) X.1 = X.1 := by
    funext i
    simp [NativeContinuation.eraseActiveList]
  have htemplate : (NativeContinuation.receivedTemplate X.1 (NativeContinuation.residual c 0 X)
      (NativeContinuation.residual c 1 X)).clipped = T.relabel e.symm :=
    sourceRow_clipped_template kind low active b c e
  have hrel := all_focal_ties_relabel (1-xi) bids 0 e.symm hgeneric
  have hg :
      let low := NativeContinuation.eraseActiveList (∅ : Finset (Fin (N+1))) X.1
      let S := (NativeContinuation.receivedTemplate low
        (NativeContinuation.residual c 0 X-(∅ : Finset (Fin (N+1))).card)
        (NativeContinuation.residual c 1 X-(∅ : Finset (Fin (N+1))).card)).clipped
      ∀ P Q, S.Feasible P → S.Feasible Q →
        CompleteInformation.potential (1-xi) (ResidualPotential.bid low) P.1 P.2 =
          CompleteInformation.potential (1-xi) (ResidualPotential.bid low) Q.1 Q.2 →
        focalCopy P (e.symm 0) = focalCopy Q (e.symm 0) := by
    dsimp only
    simp only [herase, Finset.card_empty, Nat.sub_zero]
    rw [htemplate, hbid]
    exact fun P Q _ _ he => hrel P Q he
  have hc := NativeContinuation.context_low_payoff xi hxi hxi1 c X hX U
    ((hL.le.trans hb.1).trans hb.2) ∅ (by simp) (fun i _ => hXU i)
    (e.symm 0) (by simp) (by rw [hbi]; exact hL.trans_le hb.1) v hg
  simp only [herase,Finset.card_empty,Nat.sub_zero,NativeContinuation.residualPayoff,hbid] at hc
  rw [htemplate] at hc
  have hpay := T.userPayoff_relabel e.symm hxi hxi1 v bids 0
    (fun P Q _ _ he => hgeneric P Q he)
  simp only [Equiv.symm_symm] at hpay
  have hr : (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ) X (e.symm 0)).expect
      (fun k => realizedPayoff (1-2*xi) v b k.val) =
      ∫ s : Fin 2 → unitInterval,
        purePayoff (1-xi) v (fun i => entryBid (X.1 i))
          (NativeContinuation.select xi hxi hxi1 c 0 X (s 0),
            NativeContinuation.select xi hxi hxi1 c 1 X (s 1)) (e.symm 0)
        ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)) := by
    rw [privateContextLaw, CountLaw.expect_ofMeasure]
    apply integral_congr_ae
    apply ae_of_all
    intro s
    have hs (j : Fin 2) := sourceRow_fallback hxi hxi1 z c μ hd hL hgap
      kind low active b hlow hactive hb e hguard j (s j)
    change realizedPayoff (1-2*xi) v b
      (focalCopy (((contextPolicy hxi hxi1 d L U z c μ).select 0 X (s 0)),
        ((contextPolicy hxi hxi1 d L U z c μ).select 1 X (s 1))) (e.symm 0)).val = _
    rw [hs 0,hs 1,realizedPayoff_focalCopy]
    dsimp only
    rw [purePayoff_outcomes,hbi]
    rfl
  rw [hr, hc]
  change (T.relabel e.symm).userPayoff xi v (bids ∘ e) (e.symm 0) = _
  rw [hpay]
  exact (if_neg hguard).symm

theorem sourceRow_payoff_physical {xi d L U : ℝ} (hxi : 0 < xi) (hxi1 : xi < 1)
    (z : ℝ) (c : ℕ) (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hμnull : ∀ y, μ {y} = 0) (hBnull : ∀ y, B {y} = 0)
    (hd : 0 ≤ d) (hL : 0 < L) (hgap : d < (1-xi)*L)
    (hμ : ∀ᵐ y ∂μ, y ∈ Icc 0 d) (hB : ∀ᵐ y ∂B, y ∈ Icc L U)
    (kind : Fin N → Fin 4) (v b : ℝ) (hb : b ∈ Icc L U)
    (e : Equiv.Perm (Fin (N+1))) :
    (∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).expect (fun k => realizedPayoff (1-2*xi) v b k.val)
      ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B)) =
      ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ,
        activePhysicalPatternPayoff xi z L U c kind (v,b,low,active)
        ∂Measure.pi (fun _ : Fin N => μ) ∂Measure.pi (fun _ : Fin N => B) := by
  have hlows : ∀ᵐ low ∂Measure.pi (fun _ : Fin N => μ), ∀ j, low j ∈ Icc 0 d :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => μ) j).quasiMeasurePreserving.ae hμ)
  have hactives : ∀ᵐ active ∂Measure.pi (fun _ : Fin N => B), ∀ j, active j ∈ Icc L U :=
    ae_all_iff.mpr (fun j => (measurePreserving_eval (fun _ : Fin N => B) j).quasiMeasurePreserving.ae hB)
  by_cases hguard : activePatternGuarded xi L U c z kind
  · apply integral_congr_ae
    filter_upwards [hactives] with active ha
    rw [sourceRow_private_payoff_guarded hxi hxi1 z c μ hμnull hd hL hgap hμ
      kind active (1-2*xi) v b ha hb hguard e]
    simp only [activePhysicalPatternPayoff,if_pos hguard]
    have he : ∀ low : Fin N → ℝ,
        activePhysicalActiveBids kind (v,b,low,active) =
          activePhysicalActiveBids kind (v,b,(fun _ => 0),active) := by
      intro low
      rfl
    simp_rw [he]
    simp only [integral_const,probReal_univ,one_smul]
  · have hg := ae_physical_ties_same_focalCopy (sub_pos.mpr hxi1)
      (hL.trans_le hb.1).ne' μ B hμnull hBnull kind v
    have hs := (Measure.measurePreserving_swap
      (μ := Measure.pi (fun _ : Fin N => B))
      (ν := Measure.pi (fun _ : Fin N => μ))).quasiMeasurePreserving.ae hg
    have hgg := Measure.ae_ae_of_ae_prod hs
    apply integral_congr_ae
    filter_upwards [hactives, hgg] with active ha hga
    apply integral_congr_ae
    filter_upwards [hlows, hga] with low hl hgl
    exact sourceRow_private_payoff_fallback hxi hxi1 z c μ hd hL hgap
      kind low active v b hl ha hb e hguard hgl

end FullContext
end FCAppendix.Affine.Hybrid.Native02
