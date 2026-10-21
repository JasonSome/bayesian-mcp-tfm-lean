import FCAppendix.Affine.Tail04.NativeExceptionalFailure
import FCAppendix.Affine.Hybrid.Native02.ExceptionalOriginalRows

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeExceptionalCounts
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes Classical
open Hybrid Hybrid.Native02 Hybrid.Native02.FullContext
open NativeExceptionalFailure LowBody
open scoped BigOperators

private lemma zero_test_identity (b : ℝ) (k : Fin 3) :
    (if k=0 then (1:ℝ) else 0)=
      1-realizedPayoff 0 1 b k.val+realizedPayoff 0 0 b k.val := by
  fin_cases k <;> simp [realizedPayoff]

variable {N c : ℕ}

def patternFailure (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ) (b : ℝ)
    (kind : Fin N→ Fin 4) : ℝ :=
  ∫active : Fin N→ℝ,∫low : Fin N→ℝ,
    (privateContextLaw C
      (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
      (e.symm 0)).mass 0
    ∂Measure.pi (fun _ : Fin N=>μ) ∂Measure.pi (fun _ : Fin N=> B)

theorem exceptionalTable_pair_failure {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ) (hd : 0≤ d)
    (hL : 0< L) (hLU : L≤ U) (hgap : d<(1-xi)*L)
    (kind : Fin N→ Fin 4) (active : Fin N→ℝ) (b : ℝ)
    (hactive : ∀j,active j∈Icc L U) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) (u : unitInterval) :
    let T:=exceptionalTable z c kind e
    let P:=(tableLaw xi T 0 (originalActiveBids kind e b active) u).prod
      (tableLaw xi T 1 (originalActiveBids kind e b active) u)
    P.expect (fun ST=> if focalCopy ST (e.symm 0)=0 then (1:ℝ) else 0)=
      (1-tableTargetQ xi T (originalActiveBids kind e b active) u (originalFocal kind e))^2 := by
  dsimp only
  let T:=exceptionalTable z c kind e
  let P:=(tableLaw xi T 0 (originalActiveBids kind e b active) u).prod
    (tableLaw xi T 1 (originalActiveBids kind e b active) u)
  have h1:=(exceptionalTable_pair_payoffs hxi hxi1 z c hd hL hLU hgap
    kind active b hactive hb hout hguard e u 0 1).2
  have h0:=(exceptionalTable_pair_payoffs hxi hxi1 z c hd hL hLU hgap
    kind active b hactive hb hout hguard e u 0 0).2
  calc
    _=P.expect (fun ST=>1-broadcastPayoff 0 1 b (e.symm 0) ST+
      broadcastPayoff 0 0 b (e.symm 0) ST) := by
      apply FiniteLaw.expect_congr
      intro ST
      have hh:=zero_test_identity b (focalCopy ST (e.symm 0))
      simpa only [realizedPayoff_focalCopy] using hh
    _=1-P.expect (broadcastPayoff 0 1 b (e.symm 0))+
        P.expect (broadcastPayoff 0 0 b (e.symm 0)) := by
      rw [FiniteLaw.expect_add,FiniteLaw.expect_sub,FiniteLaw.expect_const]
    _=_ := by rw [h1,h0];unfold independentTwo;ring

theorem sourceRow_low_failure_eq {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hnoatoms : ∀b,μ {b}=0)
    (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U) (hgap : d<(1-xi)*L)
    (hμ : ∀ᵐb ∂μ,b∈Icc 0 d)
    (kind : Fin N→ Fin 4) (active : Fin N→ℝ) (b : ℝ)
    (hactive : ∀j,active j∈Icc L U) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    let C:=originalEligible kind e
    letI : Nonempty C:=by
      have hpos:=hguard.1.2.2.1
      have hD:=hguard.2.1
      obtain ⟨j,hj⟩:=Finset.card_pos.mp
        (show 0< C.card by dsimp [C];rw [originalEligible_card];omega)
      exact ⟨⟨j,hj⟩⟩
    (∫low : Fin N→ℝ,
      (privateContextLaw (contextPolicy hxi hxi1 d L U z c μ)
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
        (e.symm 0)).mass 0 ∂Measure.pi (fun _ : Fin N=>μ))=
      (sourceOwnersLaw (fun j : C=> active (originalRivalCoordinate kind e j))
        (activePatternOwner c z kind 0) (activePatternOwner c z kind 1)).expect
        (fun AB=>(1-canonicalExceptionalQ xi (activePatternResidual c z kind) b
          (fun j : C=> active (originalRivalCoordinate kind e j)) AB)^2) := by
  dsimp only
  have hlow:=sourceRow_low_integral_exceptional_table hxi hxi1 z c μ hnoatoms
    hd hL hLU hgap hμ kind active b hactive hb hout hguard e
    (fun k=> if k=0 then (1:ℝ) else 0)
  simp only [FiniteLaw.expect_singleton] at hlow
  rw [hlow]
  calc
    _=∫u : unitInterval,
      (1-tableTargetQ xi (exceptionalTable z c kind e) (originalActiveBids kind e b active)
        u (originalFocal kind e))^2 ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u=> exceptionalTable_pair_failure hxi hxi1 z c hd hL hLU hgap
        kind active b hactive hb hout hguard e u)
    _=_:=exceptionalTable_common_owner_test hxi hxi1 z c hd hL hLU hgap
      kind active b hactive hb hout hguard e (fun q=>(1-q)^2)

theorem patternFailure_eq {xi d L U : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (z : ℝ) (c : ℕ)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀b,μ {b}=0) (hd : 0≤ d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (hμ : ∀ᵐb ∂μ,b∈Icc 0 d) (hB : ∀ᵐb ∂B,b∈Icc L U)
    (kind : Fin N→ Fin 4) (b : ℝ) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    let C:=originalEligible kind e
    letI : Nonempty C:=by
      have hpos:=hguard.1.2.2.1
      have hD:=hguard.2.1
      obtain ⟨j,hj⟩:=Finset.card_pos.mp
        (show 0< C.card by dsimp [C];rw [originalEligible_card];omega)
      exact ⟨⟨j,hj⟩⟩
    patternFailure (contextPolicy hxi hxi1 d L U z c μ) e μ B b kind=
      ∫x : C→ℝ,(sourceOwnersLaw x (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect
        (fun AB=>(1-canonicalExceptionalQ xi (activePatternResidual c z kind) b x AB)^2)
        ∂Measure.pi (fun _ : C=> B) := by
  dsimp only
  let C:=originalEligible kind e
  letI : Nonempty C:=by
    have hpos:=hguard.1.2.2.1
    have hD:=hguard.2.1
    obtain ⟨j,hj⟩:=Finset.card_pos.mp
      (show 0< C.card by dsimp [C];rw [originalEligible_card];omega)
    exact ⟨⟨j,hj⟩⟩
  let proj:=fun active : Fin N→ℝ=> fun j : C=> active (originalRivalCoordinate kind e j)
  have hmproj : Measurable proj:=measurable_pi_lambda _
    (fun j=> measurable_pi_apply (originalRivalCoordinate kind e j))
  have hproj:=iid_coordinate_restriction_law B (originalRivalCoordinate kind e)
    (originalRivalCoordinate_injective kind e)
  have hvec : ∀ᵐactive : Fin N→ℝ ∂Measure.pi (fun _ : Fin N=> B),∀j,active j∈Icc L U :=
    ae_all_iff.mpr (fun j=>(measurePreserving_eval (fun _ : Fin N=> B) j).quasiMeasurePreserving.ae hB)
  unfold patternFailure
  calc
    _=∫active : Fin N→ℝ,
      (sourceOwnersLaw (proj active) (activePatternOwner c z kind 0)
        (activePatternOwner c z kind 1)).expect
        (fun AB=>(1-canonicalExceptionalQ xi (activePatternResidual c z kind) b (proj active) AB)^2)
      ∂Measure.pi (fun _ : Fin N=> B) := by
      apply integral_congr_ae
      filter_upwards [hvec] with active ha
      exact sourceRow_low_failure_eq hxi hxi1 z c μ hnoatoms hd hL hLU hgap hμ
        kind active b ha hb hout hguard e
    _=_:=by
      rw [←hproj]
      exact (integral_map hmproj.aemeasurable
        (measurable_exceptional_owner_test hxi hxi1 _ _ _ b (fun q=>(1-q)^2)
          (by fun_prop)).aestronglyMeasurable).symm

theorem patternFailure_error {xi d L U h0 b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hd : 0< d) (hL : 0< L) (hLU : L≤ U)
    (z : ℝ) (c : ℕ) (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hnoatoms : ∀b,μ {b}=0) (hgap : d<(1-xi)*L)
    (hμ : ∀ᵐb ∂μ,b∈Icc 0 d) (hB : ∀ᵐb ∂B,b∈Icc L U) (hh0 : |h0|≤1)
    (kind : Fin N→ Fin 4) (hb : d< b) (hout : b∉Icc L U)
    (hguard : exceptionalPatternGuard xi L U c z kind)
    (e : Equiv.Perm (Fin (N+1))) :
    |patternFailure (contextPolicy hxi hxi1 d L U z c μ) e μ B b kind-
      (1-EqualCapacity.demand xi b (h0/reciprocalMean B))^2|≤
      (2/(xi*d))*exceptionalPatternMenuError xi L U h0 c z kind := by
  let C:=originalEligible kind e
  have hKpos:=hguard.1.2.2.1
  have hD:=hguard.2.1
  have hCcard : C.card=Fintype.card (ActivePatternIndex kind)-1:=originalEligible_card kind e
  have hN : 2≤ C.card:=by rw [hCcard];omega
  letI : Nonempty C:=by
    obtain ⟨j,hj⟩:=Finset.card_pos.mp (show 0< C.card by omega)
    exact ⟨⟨j,hj⟩⟩
  have hK : activePatternOwner c z kind 0+activePatternOwner c z kind 1< C.card:=by
    rw [hCcard];omega
  have hn : C.card-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)=
      Fintype.card (ActivePatternIndex kind)-
        (activePatternOwner c z kind 0+activePatternOwner c z kind 1)-1:=by omega
  have hg : ClippedCountGuard xi L U
      (Fintype.card C-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)+1)
      (activePatternResidual c z kind):=by
    have he : Fintype.card C-(activePatternOwner c z kind 0+activePatternOwner c z kind 1)+1=
        Fintype.card (ActivePatternIndex kind)-
          (activePatternOwner c z kind 0+activePatternOwner c z kind 1):=by
      rw [Fintype.card_coe,hCcard];omega
    rw [he]
    exact hguard.2
  rw [patternFailure_eq hxi hxi1 z c μ B hnoatoms hd.le hL hLU hgap hμ hB kind b hb hout hguard e]
  have hh:=primitive_excluded_owner_failure (ι:=C) B hxi hxi1 hd hb.le hL hLU hB hh0
    (activePatternOwner c z kind 0) (activePatternOwner c z kind 1) (activePatternResidual c z kind)
    (by simpa only [Fintype.card_coe] using hN) (by simpa only [Fintype.card_coe] using hK) hg
  simpa only [Fintype.card_coe,hn,exceptionalPatternMenuError] using hh

lemma patternFailure_mem (C : ContextPolicy (N+1) c unitInterval)
    (e : Equiv.Perm (Fin (N+1))) (μ B : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure B] (b : ℝ) (kind : Fin N→ Fin 4) :
    patternFailure C e μ B b kind∈Icc (0:ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun _=> integral_nonneg (fun _=> FiniteLaw.nonneg _ _))
  · have hlow (active : Fin N→ℝ) :
        |∫low : Fin N→ℝ,(privateContextLaw C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b))
          (e.symm 0)).mass 0 ∂Measure.pi (fun _ : Fin N=>μ)|≤1 := by
      have h:=norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin N=>μ))
        (f:=fun low : Fin N→ℝ=>(privateContextLaw C
          (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).mass 0)
        (C:=1) (ae_of_all _ (fun _=> by
          rw [Real.norm_eq_abs,abs_of_nonneg (FiniteLaw.nonneg _ _)]
          exact FiniteLaw.mass_le_one _ _))
      simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h
    have h:=norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : Fin N=> B))
      (f:=fun active : Fin N→ℝ=>∫low : Fin N→ℝ,(privateContextLaw C
        (NativeContinuation.reindexContext e (sourceRowContext kind low active b)) (e.symm 0)).mass 0
        ∂Measure.pi (fun _ : Fin N=>μ))
      (C:=1) (ae_of_all _ (fun active=> by
        simpa only [Real.norm_eq_abs] using hlow active))
    have habs : |patternFailure C e μ B b kind|≤1:=by
      simpa only [patternFailure,Real.norm_eq_abs,probReal_univ,mul_one] using h
    exact (le_abs_self _).trans habs

theorem eventually_exceptional_fullrow_failure
    (s a h rho z xi d L U : ℝ)
    (hs : 0< s) (ha : 0< a) (hh : 0< h) (hsum : s+a+h=1)
    (hz0 : 0≤ z) (hz1 : z<1) (hxi : 0< xi) (hxi1 : xi<1)
    (hd : 0< d) (hL : 0< L) (hLU : L≤ U)
    (hgap : d<(1-xi)*L) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho z) (hq1 : sourceExposure a h rho z<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U< L)
    (cap : ℕ→ℕ) (hcap : Tendsto (fun M=>(cap M:ℝ)/(M:ℝ)) atTop (nhds rho))
    (eps : ℝ) (heps : 0< eps) :
    ∀ᶠN : ℕ in atTop,∀(μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B],
      (∀b,μ {b}=0)→(∀ᵐb ∂μ,b∈Icc 0 d)→(∀ᵐb ∂B,b∈Icc L U)→
      ∀(e : Equiv.Perm (Fin (N+1))) (b : ℝ),d< b→ b∉Icc L U→
      let C : ContextPolicy (N+1) (cap (N+1)) unitInterval:=
    contextPolicy hxi hxi1 d L U z (cap (N+1)) μ
      let P:=CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
      let lam:=(1-xi*sourceExposure a h rho z)/reciprocalMean B
      |P.expect (patternFailure C e μ B b)-(1-EqualCapacity.demand xi b lam)^2|< eps := by
  let K:=2/(xi*d)
  have hK : 0< K:=by dsimp [K];positivity
  let tau:=eps/(2*K)
  have htau : 0< tau:=by dsimp [tau];positivity
  obtain ⟨delta,deq,dclip,hdelt,hdeq,hdclip,hcount⟩:=
    exists_eventual_exceptional_pattern_bound s a h rho z xi L U hs ha hh hsum
      hz0 hz1 hxi hxi1 hL hLU hlower hupper hq0 hq1 hboxlo hboxhi cap hcap tau htau
  have htail:=(exceptionalGuardError_tendsto_zero hh hdelt hdeq hdclip).eventually
    (Iio_mem_nhds (half_pos heps))
  filter_upwards [hcount,htail] with N hN htailN
  intro μ B _ _ hnoatoms hμ hB e b hb hout
  dsimp only
  let C : ContextPolicy (N+1) (cap (N+1)) unitInterval:=
    contextPolicy hxi hxi1 d L U z (cap (N+1)) μ
  let P:=CommonList.iid (categoryLaw s a h hs.le ha.le hh.le hsum B) N
  let h0:=1-xi*sourceExposure a h rho z
  let lam:=h0/reciprocalMean B
  let target:=(1-EqualCapacity.demand xi b lam)^2
  let good:=fun kind : Fin N→ Fin 4=>
    exceptionalPatternGuard xi L U (cap (N+1)) z kind∧
      exceptionalPatternMenuError xi L U h0 (cap (N+1)) z kind< tau
  have hprob : P.prob (fun kind=>¬good kind)≤ exceptionalGuardError h delta deq dclip N:=
    hN B inferInstance
  have h0abs : |h0|≤1:=by rw [abs_le];dsimp [h0];constructor <;> nlinarith
  have htarget : target∈Icc (0:ℝ) 1:=by
    have hq:=EqualCapacity.demand_bounds xi b lam
    exact ⟨sq_nonneg _,by nlinarith [hq.1,hq.2]⟩
  have hbound (kind : Fin N→ Fin 4) : |patternFailure C e μ B b kind-target|≤1:=by
    have hp:=patternFailure_mem C e μ B b kind
    rw [abs_le];constructor <;> linarith [hp.1,hp.2,htarget.1,htarget.2]
  have hgood (kind : Fin N→ Fin 4) (hk : good kind) :
      |patternFailure C e μ B b kind-target|≤ eps/2:=by
    have hm:=patternFailure_error hxi hxi1 hd hL hLU z (cap (N+1)) μ B
      hnoatoms hgap hμ hB h0abs kind hb hout hk.1 e
    have he : K*exceptionalPatternMenuError xi L U h0 (cap (N+1)) z kind< eps/2:=by
      have hh:=mul_lt_mul_of_pos_left hk.2 hK
      dsimp [tau] at hh
      have hid : K*(eps/(2*K))=eps/2:=by field_simp
      rwa [hid] at hh
    exact hm.trans he.le
  have he:=finite_menu_upper P good (fun kind=>|patternFailure C e μ B b kind-target|)
    0 1 (eps/2) le_rfl (half_pos heps).le hbound
      (fun kind hk=> by simpa only [zero_add] using hgood kind hk)
  have habs:=P.abs_expect_le (fun kind=> patternFailure C e μ B b kind-target)
  rw [FiniteLaw.expect_sub,FiniteLaw.expect_const] at habs
  have herr:=hprob.trans_lt htailN
  simp only [zero_add,one_mul] at he
  exact (habs.trans he).trans_lt (by linarith only [herr])

theorem closed_broadcast_failure_fullrows
    (C : ContextPolicy (N+1) c unitInterval) (Γ : FiniteGame (N+1) 2 c unitInterval)
    {d U R : ℝ} (hdU : d≤ U) (hUR : U< R) (hseed : Γ.seedLaw=volume)
    (hfull : ∀ᵐx ∂userProfileLaw Γ,x∈closedProfiles (N+1) R)
    (hgap : ∀ᵐx ∂Γ.F⊗ₘΓ.σ,x.2.bid≤ U∨R≤ x.2.bid)
    (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hrow : (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B)
    (i : Fin (N+1)) (act : JointAction 2) (hb : act.bid< R) (hk : act.routeCount=2) :
    ((problem (ClosedPolicy.nativeGame C Γ R) i).outcome act).mass 0=
      (CommonList.iid (categoryLaw s a h hs ha hh hsum B) N).expect
        (patternFailure C (NativeContinuation.focalIndex i).symm μ B act.bid) := by
  have he:=closed_broadcast_count_physicalRows_all_lower C Γ hdU hUR hseed hfull hgap
    (physicalRivalLaw s a h μ B) hrow i act hb hk (fun k=> if k=0 then (1:ℝ) else 0)
  simp only [FiniteLaw.expect_singleton] at he
  have he2:=integral_physicalRows_eq_patternMenus s a h hs ha hh hsum μ B C i act.bid
    (fun k=> if k=0 then (1:ℝ) else 0) 1 (fun k=> by split_ifs <;> norm_num)
  simp only [FiniteLaw.expect_singleton] at he2
  rw [he,he2]
  rw [categoryLaw_eq_low_law s a h hs ha hh hsum μ B]
  apply FiniteLaw.expect_congr
  intro kind
  simp only [patternFailure,Equiv.symm_symm,NativeContinuation.focalIndex_zero]

end FCAppendix.Affine.Tail04.NativeExceptionalCounts
