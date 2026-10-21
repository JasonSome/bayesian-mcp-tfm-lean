import FCAppendix.Affine.Uniform07Finishing.Native.NativeSeedLaw
import FCAppendix.Affine.Uniform07Finishing.Native.GuardedSeedErasure
import FCAppendix.Affine.Uniform07Finishing.Native.ForcedFocalSeed
import FCAppendix.Affine.LowBody.NullHyperplanes

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody StrictNative
open scoped BigOperators

theorem ae_mul_ne_nonzero_of_zero_only_atoms (μ : Measure ℝ)
    (hμ : ∀x : ℝ, x ≠ 0 → μ {x} = 0) (a t : ℝ) (ht : t ≠ 0) :
    ∀ᵐx ∂μ, a*x ≠ t := by
  by_cases ha : a = 0
  · exact ae_of_all _ (fun x => by simpa only [ha,zero_mul] using ht.symm)
  · have hpoint : t/a ≠ 0 := div_ne_zero ht ha
    have hx : ∀ᵐx ∂μ, x ≠ t/a := by
      rw [ae_iff]
      simpa only [not_not,Set.setOf_eq_eq_singleton] using hμ (t/a) hpoint
    filter_upwards [hx] with x hx he
    apply hx
    apply (eq_div_iff ha).mpr
    simpa only [mul_comm] using he

theorem ae_iid_linear_ne_nonzero_of_zero_only_atoms
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀x : ℝ, x ≠ 0 → μ {x} = 0) (N : ℕ) (a : Fin N → ℝ)
    (t : ℝ) (ht : t ≠ 0) :
    ∀ᵐx ∂Measure.pi (fun _ : Fin N => μ), (∑i,a i*x i) ≠ t := by
  induction N generalizing t with
  | zero => exact ae_of_all _ (fun x => by simpa using ht.symm)
  | succ N ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => ℝ) 0
      let f : (Fin (N+1) → ℝ) → ℝ := fun x => ∑i,a i*x i
      have hf : Measurable f := by dsimp only [f]; fun_prop
      have hS : MeasurableSet {y : ℝ × (Fin N → ℝ) | f (e.symm y) ≠ t} :=
        (measurableSet_eq_fun (hf.comp e.symm.measurable) measurable_const).compl
      have he (x : ℝ) (r : Fin N → ℝ) :
          f (e.symm (x,r)) = a 0*x + ∑j,a j.succ*r j := by
        dsimp only [f]
        rw [Fin.sum_univ_succAbove _ (0 : Fin (N+1))]
        simp [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
      have hp : ∀ᵐy ∂μ.prod (Measure.pi (fun _ : Fin N => μ)), f (e.symm y) ≠ t := by
        apply (Measure.ae_prod_iff_ae_ae hS).mpr
        filter_upwards [ae_mul_ne_nonzero_of_zero_only_atoms μ hμ (a 0) t ht] with x hx
        have ht' : t-a 0*x ≠ 0 := sub_ne_zero.mpr hx.symm
        filter_upwards [ih (fun j => a j.succ) (t-a 0*x) ht'] with r hr
        rw [he]
        intro hh
        apply hr
        linarith
      have hh := (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) 0).quasiMeasurePreserving.ae hp
      simpa only [e,MeasurableEquiv.symm_apply_apply] using hh

theorem ae_updated_potential_ties_same_focalCopy {m : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀x : ℝ, x ≠ 0 → μ {x} = 0)
    {κ b : ℝ} (hκ : 0 < κ) (hb : b ≠ 0) (i : Fin m) :
    ∀ᵐx ∂Measure.pi (fun _ : Fin m => μ),
      ∀P Q : ResidualPotential.Pair m,
        CompleteInformation.potential κ (Function.update x i b) P.1 P.2 =
          CompleteInformation.potential κ (Function.update x i b) Q.1 Q.2 →
        focalCopy P i = focalCopy Q i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ N =>
      apply ae_all_iff.mpr
      intro P
      apply ae_all_iff.mpr
      intro Q
      by_cases hcopy : focalCopy P i = focalCopy Q i
      · exact ae_of_all _ (fun _ _ => hcopy)
      · let A : Fin (N+1) → ℝ := fun k => copyCoefficient κ P k-copyCoefficient κ Q k
        have hA : A i ≠ 0 := sub_ne_zero.mpr
          (copyCoefficient_ne_of_focalCopy_ne hκ P Q i hcopy)
        have ht : -(A i*b) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hA hb)
        have hr := ae_iid_linear_ne_nonzero_of_zero_only_atoms μ hμ N
          (fun j => A (i.succAbove j)) (-(A i*b)) ht
        have hdelete : MeasurePreserving
            (fun x : Fin (N+1) → ℝ => fun j => x (i.succAbove j))
            (Measure.pi (fun _ : Fin (N+1) => μ)) (Measure.pi (fun _ : Fin N => μ)) :=
          (measurePreserving_snd (μ := μ) (ν := Measure.pi (fun _ : Fin N => μ))).comp
            (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i)
        filter_upwards [hdelete.quasiMeasurePreserving.ae hr] with x hx he
        have hd : CompleteInformation.potential κ (Function.update x i b) P.1 P.2 -
            CompleteInformation.potential κ (Function.update x i b) Q.1 Q.2 =
            A i*b+∑j,A (i.succAbove j)*x (i.succAbove j) := by
          rw [potential_eq_copyCoefficient,potential_eq_copyCoefficient,
            ←Finset.sum_sub_distrib]
          have hs : (∑k,(copyCoefficient κ P k*Function.update x i b k-
              copyCoefficient κ Q k*Function.update x i b k)) =
              ∑k,A k*Function.update x i b k := by
            apply Finset.sum_congr rfl
            intro k _
            dsimp only [A]
            ring
          rw [hs,Fin.sum_univ_succAbove _ i]
          simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne i _)]
        rw [he,sub_self] at hd
        exact False.elim (hx (by linarith))

def maskedLowerDrawBid (R : ℝ) (u : UserDraw 2) : ℝ :=
  if u.1.2.bid < R then u.1.2.bid else 0

theorem measurable_maskedLowerDrawBid (R : ℝ) : Measurable (maskedLowerDrawBid R) :=
  Measurable.ite (measurableSet_lt measurable_draw_bid measurable_const)
    measurable_draw_bid measurable_const

theorem native_masked_bid_zero_only_atoms {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) [NullSingletonClass (submittedBidMeasure Γ)]
    (R x : ℝ) (hx : x ≠ 0) :
    ((userLaw Γ).map (maskedLowerDrawBid R)) {x} = 0 := by
  rw [Measure.map_apply (measurable_maskedLowerDrawBid R) (measurableSet_singleton x)]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [actual_draw_bid_ne Γ x] with u hu
  change maskedLowerDrawBid R u ≠ x
  unfold maskedLowerDrawBid
  split_ifs
  · exact hu
  · exact hx.symm

theorem ae_native_updated_potential_ties_same_focalCopy
    {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) [NullSingletonClass (submittedBidMeasure Γ)]
    {κ b : ℝ} (hκ : 0 < κ) (hb : b ≠ 0) (R : ℝ) (i : Fin m) :
    ∀ᵐd ∂userProfileLaw Γ, ∀P Q : ResidualPotential.Pair m,
      CompleteInformation.potential κ
          (Function.update (fun k => maskedLowerDrawBid R (d k)) i b) P.1 P.2 =
        CompleteInformation.potential κ
          (Function.update (fun k => maskedLowerDrawBid R (d k)) i b) Q.1 Q.2 →
      focalCopy P i = focalCopy Q i := by
  let ν := (userLaw Γ).map (maskedLowerDrawBid R)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (measurable_maskedLowerDrawBid R).aemeasurable
  have hg := ae_updated_potential_ties_same_focalCopy ν
    (native_masked_bid_zero_only_atoms Γ R) hκ hb i
  have hp : MeasurePreserving (fun d : UserProfile m 2 => fun k => maskedLowerDrawBid R (d k))
      (userProfileLaw Γ) (Measure.pi (fun _ : Fin m => ν)) :=
    ⟨measurable_pi_lambda _ (fun k =>
      (measurable_maskedLowerDrawBid R).comp (measurable_pi_apply k)),
      Measure.pi_map_pi (fun _ => (measurable_maskedLowerDrawBid R).aemeasurable)⟩
  exact hp.quasiMeasurePreserving.ae hg

theorem actualContext_updated_bid_vector {m : ℕ} (R : ℝ)
    (d : UserProfile m 2) (i : Fin m) (v : ℝ) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (ha : a.bid < R)
    (hd : Function.update d i ((v,a),τ) ∈ classifiedProfiles m R) :
    ResidualPotential.bid (actualContext R (Function.update d i ((v,a),τ))).1 =
      Function.update (fun k => maskedLowerDrawBid R (d k)) i a.bid := by
  have hl := broadcastPart_observe (Function.update d i ((v,a),τ)) hd 0
  funext k
  change max (entryBid ((actualContext R (Function.update d i ((v,a),τ))).1 k)) 0 = _
  change max (entryBid (broadcastPart R
    (observe (drawsRealization (Function.update d i ((v,a),τ))) 0) k)) 0 = _
  rw [hl]
  by_cases hk : k = i
  · subst k
    simp only [Function.update_self,if_pos ha,entryBid,max_eq_left a.bid_nonneg]
  · simp only [Function.update_of_ne hk,maskedLowerDrawBid]
    by_cases hb : (d k).1.2.bid < R
    · simp only [if_pos hb,entryBid,max_eq_left (d k).1.2.bid_nonneg]
    · simp only [if_neg hb,entryBid,max_self]

def contextCopyGeneric {m : ℕ} (κ : ℝ) (i : Fin m) (X : ClassifiedContext m) : Prop :=
  ∀P Q : ResidualPotential.Pair m,
    CompleteInformation.potential κ (ResidualPotential.bid X.1) P.1 P.2 =
      CompleteInformation.potential κ (ResidualPotential.bid X.1) Q.1 Q.2 →
    focalCopy P i = focalCopy Q i

theorem measurableSet_contextCopyGeneric {m : ℕ} (κ : ℝ) (i : Fin m) :
    MeasurableSet {X : ClassifiedContext m | contextCopyGeneric κ i X} := by
  simp only [contextCopyGeneric,setOf_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro Q
  by_cases hc : focalCopy P i = focalCopy Q i
  · simp only [hc,implies_true,setOf_true,MeasurableSet.univ]
  · simp only [hc,imp_false]
    have hb : Measurable (fun X : ClassifiedContext m => ResidualPotential.bid X.1) := by
      apply measurable_pi_lambda
      intro k
      exact ((measurable_entryBid.comp ((measurable_pi_apply k).comp measurable_fst)).max measurable_const)
    exact (measurableSet_eq_fun ((continuous_potential κ P).measurable.comp hb)
      ((continuous_potential κ Q).measurable.comp hb)).compl

theorem insert_deleteFocal {m : ℕ} (i : Fin m) (v : ℝ) (a : JointAction 2)
    (τ : Equiv.Perm (Fin 2)) (d : UserProfile m 2) :
    insertFocalProfile i v a τ (deleteFocal i d) = Function.update d i ((v,a),τ) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [insertFocalProfile]
  · simp only [insertFocalProfile,dif_neg hk,deleteFocal,Function.update_of_ne hk]

theorem updated_broadcast_classified {m : ℕ} {R : ℝ}
    (d : UserProfile m 2) (hd : d ∈ classifiedProfiles m R) (i : Fin m)
    (v : ℝ) (a : JointAction 2) (ha : a.bid < R) (ha2 : a.routeCount = 2)
    (τ : Equiv.Perm (Fin 2)) :
    Function.update d i ((v,a),τ) ∈ classifiedProfiles m R := by
  intro k
  by_cases hk : k = i
  · subst k
    simpa only [Function.update_self] using (Or.inl ⟨ha,ha2⟩ :
      (a.bid < R ∧ a.routeCount = 2) ∨ (R ≤ a.bid ∧ a.routeCount = 1))
  · simpa only [Function.update_of_ne hk] using hd k

theorem ae_native_focal_context_generic {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) [NullSingletonClass (submittedBidMeasure Γ)]
    {κ R : ℝ} (hκ : 0 < κ)
    (hfull : ∀ᵐd ∂userProfileLaw Γ, d ∈ classifiedProfiles m R)
    (i : Fin m) (a : JointAction 2) (ha0 : 0 < a.bid) (haR : a.bid < R)
    (ha2 : a.routeCount = 2) (τ : Equiv.Perm (Fin 2)) (j : Fin 2) :
    ∀ᵐd ∂Measure.pi (fun _ : RivalIndex i => userLaw Γ),
      contextCopyGeneric κ i (observedContext R j (focalLocalList i a τ j d)) := by
  have hC : Measurable (fun d : RivalIndex i → UserDraw 2 =>
      observedContext R j (focalLocalList i a τ j d)) :=
    (measurable_observedContext R j).comp (measurable_focalLocalList i a τ j)
  have hp := deleteFocal_preserves_iid i (userLaw Γ)
  rw [←hp.map_eq]
  apply (ae_map_iff hp.measurable.aemeasurable
    ((measurableSet_contextCopyGeneric κ i).preimage hC)).mpr
  filter_upwards [hfull,ae_native_updated_potential_ties_same_focalCopy Γ
    hκ ha0.ne' R i] with d hd hg
  have hz := updated_broadcast_classified d hd i 0 a haR ha2 τ
  have hlist : focalLocalList i a τ j (deleteFocal i d) =
      observe (drawsRealization (Function.update d i ((0,a),τ))) j := by
    simp only [focalLocalList,insert_deleteFocal]
  rw [hlist,observedContext_eq_actual _ hz j]
  unfold contextCopyGeneric
  rw [actualContext_updated_bid_vector R d i 0 a τ haR hz]
  exact hg

end FCAppendix.Affine.Uniform07Finishing
