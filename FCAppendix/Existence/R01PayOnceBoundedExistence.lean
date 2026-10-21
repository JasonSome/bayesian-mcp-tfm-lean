import FCAppendix.Existence.R01PayOnceNativePurity

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

structure BoundedPayOnceEquilibrium (m n c : ℕ) (F : Measure ℝ) (g : ℝ) where
  game : FiniteGame m n c unitInterval
  posterior : PosteriorSystem game
  values : game.F=F
  bid_rule : game.A=Schedule.once n
  base_rule : game.G=Schedule.once n
  fee : game.g=g
  users : UsersOptimal game
  proposers : PosteriorProposerOptimalAE game posterior
  symmetric : SymmetricProposersOnPath game
  equivariant : PolicyLawEquivariant game
  inactive : ∀ᵐv ∂F,∀ᵐa ∂game.σ v,v ≤ g → a=Interim.abstain n
  positive : ∀i : Fin m,∀ᵐv ∂F,∀ᵐa ∂game.σ v,g < v →
    0 < a.bid ∧ a.bid < v-g ∧ 0 < (problem game i).payoff v a ∧ a.routeCount=n
  pure : (∀v,g < v → F {v}=0) → ∃(b : ℝ → ℝ)(hb : ∀v,0 ≤ b v),Measurable b ∧ Monotone b ∧
    (∀ᵐv ∂F,g < v → game.σ v=Measure.dirac (fullBid n (b v) (hb v)))

theorem bounded_payOnce_exists_succ (N k c : ℕ) (hN : 0 < N) (hn : 2 ≤ k+1)
    (hc : 1 ≤ c) (hcm : c < N+1) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0 ≤ g) (Wbar : ℝ) (hbounded : ∀ᵐv ∂F,max 0 (v-g) ≤ Wbar) :
    Nonempty (BoundedPayOnceEquilibrium (N+1) (k+1) c F g) := by
  let W := max Wbar 1
  have hW : 0 < W := lt_of_lt_of_le (by norm_num) (le_max_right Wbar 1)
  have hboundW : ∀ᵐv ∂F,max 0 (v-g) ≤ W :=
    hbounded.mono (fun _ hv=>hv.trans (le_max_left Wbar 1))
  let μ := physicalNetLaw W g hW.le F
  obtain ⟨π,σ,hσ,hdis,hπIC,hσIC,hσsupport,hzero⟩ :=
    exists_bounded_broadcast_law W hW N (k+1) c hN hn hc hcm μ
  letI : IsMarkovKernel σ := hσ
  let κ := physicalKernel W g hW.le σ
  let Γ := mixedGame (N+1) (k+1) c hn F κ (Schedule.once (k+1)) g hg
  have hICphysical : ∀ᵐv ∂F,∀ᵐa ∂κ v,∀a' : FloorAction 0 W,
      positivePayoff N (k+1) c π.1 (physicalNetType W g hW.le v,a') ≤
        positivePayoff N (k+1) c π.1 (physicalNetType W g hW.le v,a) :=
    ae_of_ae_map (continuous_physicalNetType W g hW.le).measurable.aemeasurable hσIC
  have hsupport : ∀ᵐv ∂F,∀ᵐa ∂κ v,
      (v ≤ g ↔ present a=false) ∧ (present a=true → 0 < bid a) := by
    have hs := ae_of_ae_map (continuous_physicalNetType W g hW.le).measurable.aemeasurable hσsupport
    filter_upwards [hs] with v hv
    filter_upwards [hv] with a ha
    exact ⟨(physicalNetType_eq_zero_iff W g hW v).symm.trans ha.1,ha.2⟩
  have hneteq : ∀ᵐv ∂F,g < v → (physicalNetType W g hW.le v).1=v-g := by
    filter_upwards [hboundW] with v hv hvpos
    exact physicalNetType_eq_sub_of_positive W g hW.le v hvpos hv
  have hjoint : (F ⊗ₘ κ).map (fun z : ℝ×FloorAction 0 W=>
      (physicalNetType W g hW.le z.1,z.2))=(π.1 : Measure (Value W × FloorAction 0 W)) :=
    (physicalKernel_jointLaw W g hW.le F σ).trans hdis
  have hinactive : ∀ᵐv ∂F,∀ᵐa ∂κ v,v ≤ g → present a=false := by
    filter_upwards [hsupport] with v hv
    exact hv.mono (fun _ ha=>ha.1.mp)
  have hu : UsersOptimal Γ := mixedGame_usersOptimal_of_net_IC hn F κ g hg
    (physicalNetType W g hW.le) (continuous_physicalNetType W g hW.le).measurable
    π.1 hjoint hneteq hICphysical hinactive
  have hbid := mixedGame_bid_law_of_joint_law (N:=N) (c:=c) hn F κ g hg
    (physicalNetType W g hW.le) (continuous_physicalNetType W g hW.le).measurable π.1 hjoint
  have hQphysical := mixedGame_positiveQ_ae hn F κ g hg hc hcm.le π.1 hbid hsupport
  have hQideal := bounded_positiveQ_of_physical g hW N (k+1) c hn F π.1 σ hQphysical
  have hpositiveIdeal : ∀ᵐw ∂μ,∀ᵐa ∂σ w,0 < w.1 → 0 < bid a := by
    filter_upwards [hσsupport] with w hw
    filter_upwards [hw] with a ha hwp
    apply ha.2
    cases hp : present a with
    | false=>exact False.elim ((ne_of_gt hwp) (ha.1.mpr hp))
    | true=>rfl
  refine ⟨{
    game := Γ
    posterior := mixedPosterior (m:=N+1) (c:=c) hn F κ (Schedule.once (k+1)) g hg
    values := rfl
    bid_rule := rfl
    base_rule := rfl
    fee := rfl
    users := hu
    proposers := mixedGame_proposer_optimal hn F κ (Schedule.once (k+1)) g hg
    symmetric := mixedGame_symmetric hn F κ (Schedule.once (k+1)) g hg
    equivariant := mixedGame_equivariant hn F κ (Schedule.once (k+1)) g hg
    inactive := ?_
    positive := ?_
    pure := ?_ }⟩
  · have hs := mixedGame_native_support (m:=N+1) (c:=c) hn F κ g hg hsupport
    exact hs.mono (fun _ hv=>hv.mono (fun _ ha=>ha.1))
  · intro i
    filter_upwards [hneteq,hICphysical,hsupport,hQphysical] with v hnet hICv hsv hQv
    change ∀ᵐa ∂(κ.map (nativeAction (k+1))) v,g < v → _
    rw [Kernel.map_apply _ (measurable_nativeAction (k+1) W),
      (measurableEmbedding_nativeAction hn).ae_map_iff]
    filter_upwards [hICv,hsv,hQv] with a ha hsa hQa
    intro hvpos
    have hp : present a=true := by
      cases hp : present a with
      | false=>exact False.elim (not_le_of_gt hvpos (hsa.1.mpr hp))
      | true=>rfl
    have hbpos := hsa.2 hp
    cases a with
    | inl u=>simp [present] at hp
    | inr b=>
      let bp : PositiveBid W := ⟨b.1,hbpos,b.2.2⟩
      have hsur := positive_bid_bestResponse_strict_surplus N (k+1) c hn π.1
        (physicalNetType W g hW.le v) bp ha (hQa hvpos)
      have hval:=hnet hvpos
      have hpay : 0 < (problem Γ i).payoff v (nativeAction (k+1) (.inr b)) := by
        rw [mixedGame_native_payoff hn F κ g hg π.1 hbid]
        rw [←hval]
        exact hsur.2
      exact ⟨hbpos,by simpa only [hval,nativeAction] using hsur.1,hpay,rfl⟩
  · intro hatom
    exact mixedGame_physical_monotone_purity hW N (k+1) c hn F g hg hboundW
      π.1 σ hσIC hpositiveIdeal hQideal hatom

theorem bounded_payOnce_exists (m n c : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hc : 1 ≤ c) (hcm : c < m) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0 ≤ g) (Wbar : ℝ) (hbounded : ∀ᵐv ∂F,max 0 (v-g) ≤ Wbar) :
    Nonempty (BoundedPayOnceEquilibrium m n c F g) := by
  cases m with
  | zero=>omega
  | succ N=>
    cases n with
    | zero=>omega
    | succ k=>exact bounded_payOnce_exists_succ N k c (by omega) hn hc hcm F g hg Wbar hbounded

end FCAppendix.Bayes.PayOnceConstruction
