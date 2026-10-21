import FCAppendix.Affine.Hybrid.Native02.Implementation
import FCAppendix.Affine.Multiple07.Native01Adapter
import FCAppendix.Affine.Multiple07.FiniteFamilyAdapter
import FCAppendix.Affine.Uniform07Finishing.Native.AllLists

noncomputable section
namespace FCAppendix.Affine.Multiple07
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology Classical
open Hybrid.Native02

theorem physicalBidLaw_eq_joint_bid {m n c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : FiniteGame m n c Seed) :
    physicalBidLaw Γ = (Γ.F ⊗ₘ Γ.σ).map (fun x => x.2.bid) := by
  have hb : Measurable (fun x : ℝ × JointAction n => x.2.bid) :=
    (measurable_bid n).comp measurable_snd
  unfold physicalBidLaw userLaw
  change Measure.map ((fun x : ℝ × JointAction n => x.2.bid) ∘ Prod.fst)
    ((Γ.F ⊗ₘ Γ.σ).prod (permLaw n)) = _
  rw [← Measure.map_map hb measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]

theorem source_band_trichotomy (r : Partition) (b : Band) {v : ℝ}
    (hv : v ∈ Icc (bandLower b) (bandUpper b)) :
    v ∈ Icc (0:ℝ) lowCeiling ∨ v ∈ activeSet r ∨ v ∈ upperSet r := by
  rcases hv with ⟨hvl,hvu⟩
  cases r <;> cases b <;>
    norm_num [bandLower,bandUpper,activeSet,activeLower,activeUpper,
      upperSet,upperLower,lowCeiling] at hvl hvu ⊢ <;>
    first
    | exact Or.inl ⟨by linarith,by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith,by linarith⟩)

theorem sourceNative02_activeCount (r : Partition)
    (v : Hybrid.ActiveValue (activeLower r) (activeUpper r)) :
    (sourceNative02Input r).activeCount v = limitingLaw r v.1 := by
  rw [limitingLaw_active r v.property]
  apply FiniteLaw.ext
  intro j
  simp only [Hybrid.Native02.PrimitiveInput.activeCount,
    Hybrid.Native02.activeLimitLaw, FiniteLaw.mixture,
    sourceNative02Input_z, sourceNative02Input_q, zero_mul,
    zero_add, sub_zero, one_mul]

def recastSourceGame {M M' : ℕ} (h : M=M')
    (Γ : FiniteGame M 2 (marketCapacity M) unitInterval) :
    FiniteGame M' 2 (marketCapacity M') unitInterval := h ▸ Γ

theorem recastSourceGame_parameters {M M' : ℕ} (h : M=M')
    (Γ : FiniteGame M 2 (marketCapacity M) unitInterval) :
    (recastSourceGame h Γ).F=Γ.F ∧ (recastSourceGame h Γ).A=Γ.A ∧
    (recastSourceGame h Γ).g=Γ.g ∧ (recastSourceGame h Γ).seedLaw=Γ.seedLaw := by
  cases h
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem recastSourceGame_native (r : Partition) {M M' : ℕ} (h : M=M')
    (Γ : FiniteGame M 2 (marketCapacity M) unitInterval)
    (hΓ : IsBayesianEquilibrium Γ ∧ NullSingletonClass (physicalBidLaw Γ) ∧
      (∀ᵐ x ∂(Γ.F ⊗ₘ Γ.σ), x.2.routeCount=if x.1∈upperSet r then 1 else 2)) :
    IsBayesianEquilibrium (recastSourceGame h Γ) ∧
      NullSingletonClass (physicalBidLaw (recastSourceGame h Γ)) ∧
      (∀ᵐ x ∂((recastSourceGame h Γ).F ⊗ₘ (recastSourceGame h Γ).σ),
        x.2.routeCount=if x.1∈upperSet r then 1 else 2) := by
  cases h
  exact hΓ

theorem recastSourceGame_conditional {M M' : ℕ} (h : M=M')
    (Γ : FiniteGame M 2 (marketCapacity M) unitInterval)
    (hm : 0< M) (hm' : 0< M') (v : ℝ) :
    conditionalTypeCountLaw (recastSourceGame h Γ) hm' v =
      conditionalTypeCountLaw Γ hm v := by
  cases h
  rfl

namespace Native02Source

variable (r : Partition) (I : NativeImplementation (sourceNative02Input r))

def completedGame (k : ℕ) :
    FiniteGame (I.toNativeFamilyData.M k) 2
      (marketCapacity (I.toNativeFamilyData.M k)) unitInterval :=
  Uniform07Finishing.AllLists.game (I.toNativeFamilyData.game k)

theorem completed_parameters (k : ℕ) :
    (completedGame r I k).F=sourceValueLaw ∧
    (completedGame r I k).A=affineSchedule ∧
    (completedGame r I k).g=0 ∧ (completedGame r I k).seedLaw=volume := by
  have h := I.toNativeFamilyData.original_tariffs_seed k
  refine ⟨?_,?_,h.1,h.2.2.2⟩
  · change (I.toNativeFamilyData.game k).F = sourceValueLaw
    simpa only [sourceNative02Input_originalValues] using I.toNativeFamilyData.original_F k
  · change (I.toNativeFamilyData.game k).A = affineSchedule
    simpa only [sourceNative02Input_eta,affineSchedule] using h.2.1

theorem original_routes (k : ℕ) :
    ∀ᵐ x ∂((I.toNativeFamilyData.game k).F ⊗ₘ (I.toNativeFamilyData.game k).σ),
      x.2.routeCount=if x.1∈upperSet r then 1 else 2 := by
  let D := I.toNativeFamilyData
  let p := sourceNative02Input r
  rw [D.joint_original k]
  apply original_population_mixture_ae p.s p.a p.h
    (D.source.PL (D.index k)) (D.source.PA (D.index k)) (D.source.PH (D.index k))
  · filter_upwards [D.source.PL_support (D.index k)] with x hx
    have hn : x.1∉upperSet r := by
      intro hu
      have hv : x.1≤ lowCeiling := hx.1.2
      have hh := hu.1
      cases r <;> norm_num [lowCeiling,upperSet,upperLower] at hv hh <;> linarith
    simpa only [if_neg hn] using hx.2.2
  · filter_upwards [D.source.PA_support (D.index k)] with x hx
    have hn : x.1∉upperSet r := by
      intro hu
      have hv : x.1≤ activeUpper r := hx.1.2
      have hh := hu.1
      cases r <;> norm_num [activeUpper,upperSet,upperLower] at hv hh <;> linarith
    simpa only [if_neg hn] using hx.2.2
  · filter_upwards [D.source.PH_support (D.index k),
      D.source.PH_source_support (D.index k)] with x hx hs
    have hu : x.1∈upperSet r := hs
    simpa only [if_pos hu] using hx.2

theorem completed_native (k : ℕ) :
    IsBayesianEquilibrium (completedGame r I k) ∧
    NullSingletonClass (physicalBidLaw (completedGame r I k)) ∧
    (∀ᵐ x ∂((completedGame r I k).F ⊗ₘ (completedGame r I k).σ),
      x.2.routeCount=if x.1∈upperSet r then 1 else 2) := by
  refine ⟨Uniform07Finishing.AllLists.equilibrium_of_feasible
    (I.toNativeFamilyData.game k) (I.toNativeFamilyData.posterior k)
    (I.users_optimal k) (I.toNativeFamilyData.proposer_all_lists_seeds k),?_,
    original_routes r I k⟩
  rw [physicalBidLaw_eq_joint_bid]
  exact I.toNativeFamilyData.bid_atomless k

theorem original_conditional_limit (b : Band) (v : ℝ)
    (hv : v∈Icc (bandLower b) (bandUpper b)) : ∀j : Fin 3,
    Tendsto (fun k => (conditionalTypeCountLaw (I.toNativeFamilyData.game k)
      (lt_of_lt_of_le (by decide : 0<2) (I.toNativeFamilyData.market_valid k).1) v).mass j)
      atTop (𝓝 ((limitingLaw r v).mass j)) := by
  apply conditional_average_mass_tendsto
  intro i j
  rcases source_band_trichotomy r b hv with hL|hA|hH
  · rw [limitingLaw_low hL]
    exact I.low_count_limit v hL i j
  · let w : (sourceNative02Input r).Value := ⟨v,hA⟩
    simpa only [sourceNative02_activeCount r w] using I.active_count_limit w i j
  · rw [limitingLaw_upper r hH]
    have hh : activeUpper r< v :=
      (show activeUpper r< upperLower r by cases r <;>
        norm_num [activeUpper,upperLower]).trans_le hH.1
    exact I.upper_count_limit v hh i j

theorem completed_conditional_limit (b : Band) (v : ℝ)
    (hv : v∈Icc (bandLower b) (bandUpper b)) (j : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw (completedGame r I k)
      (lt_of_lt_of_le (by decide : 0<2) (I.toNativeFamilyData.market_valid k).1) v).mass j)
      atTop (𝓝 ((limitingLaw r v).mass j)) := by
  apply (original_conditional_limit r I b v hv j).congr'
  apply Eventually.of_forall
  intro k
  dsimp only
  change _ = (conditionalTypeCountLaw (Uniform07Finishing.AllLists.game _) _ v).mass j
  rw [Uniform07Finishing.AllLists.conditional_count_eq]
  rfl

def tailGame (M : ℕ) (hM : I.toNativeFamilyData.offset≤ M) :
    FiniteGame M 2 (marketCapacity M) unitInterval :=
  recastSourceGame (show I.toNativeFamilyData.M (M-I.toNativeFamilyData.offset)=M by
    rw [I.toNativeFamilyData.M_eq]
    omega) (completedGame r I (M-I.toNativeFamilyData.offset))

theorem tail_parameters (M : ℕ) (hM : I.toNativeFamilyData.offset≤ M) :
    (tailGame r I M hM).F=sourceValueLaw ∧ (tailGame r I M hM).A=affineSchedule ∧
    (tailGame r I M hM).g=0 ∧ (tailGame r I M hM).seedLaw=volume := by
  have h := completed_parameters r I (M-I.toNativeFamilyData.offset)
  have ht := recastSourceGame_parameters
    (show I.toNativeFamilyData.M (M-I.toNativeFamilyData.offset)=M by
      rw [I.toNativeFamilyData.M_eq]; omega)
    (completedGame r I (M-I.toNativeFamilyData.offset))
  exact ⟨ht.1.trans h.1,ht.2.1.trans h.2.1,ht.2.2.1.trans h.2.2.1,
    ht.2.2.2.trans h.2.2.2⟩

theorem tail_native (M : ℕ) (hM : I.toNativeFamilyData.offset≤ M) :
    IsBayesianEquilibrium (tailGame r I M hM) ∧
      NullSingletonClass (physicalBidLaw (tailGame r I M hM)) ∧
      (∀ᵐ x ∂((tailGame r I M hM).F ⊗ₘ (tailGame r I M hM).σ),
        x.2.routeCount=if x.1∈upperSet r then 1 else 2) :=
  recastSourceGame_native r _ _ (completed_native r I _)

theorem tail_conditional (b : Band) (v : ℝ)
    (hv : v∈Icc (bandLower b) (bandUpper b)) (j : Fin 3) :
    Tendsto (fun k => (conditionalTypeCountLaw
      (tailGame r I (I.toNativeFamilyData.offset+k) (by omega))
      (by dsimp [NativeFamilyData.offset]; omega) v).mass j)
      atTop (𝓝 ((limitingLaw r v).mass j)) := by
  have hindex (k k' : ℕ) (he : k=k')
      (hk : 0<I.toNativeFamilyData.M k) (hk' : 0<I.toNativeFamilyData.M k') :
      (conditionalTypeCountLaw (completedGame r I k) hk v).mass j =
        (conditionalTypeCountLaw (completedGame r I k') hk' v).mass j := by
    subst k'
    rfl
  apply (completed_conditional_limit r I b v hv j).congr'
  apply Eventually.of_forall
  intro k
  dsimp only
  unfold tailGame
  have he := recastSourceGame_conditional
    (show I.toNativeFamilyData.M (I.toNativeFamilyData.offset+k-I.toNativeFamilyData.offset)=
      I.toNativeFamilyData.offset+k by rw [I.toNativeFamilyData.M_eq]; omega)
    (completedGame r I (I.toNativeFamilyData.offset+k-I.toNativeFamilyData.offset))
    (lt_of_lt_of_le (by decide : 0<2) (I.toNativeFamilyData.market_valid _).1)
    (by dsimp [NativeFamilyData.offset]; omega) v
  convert! (congrArg (fun P : CountLaw 2 => P.mass j) he).symm using 1
  exact hindex _ _ (by omega) _ _

def family : NativeFamily r :=
  sourceFamily_from_producer_tail r I.toNativeFamilyData.offset
    (by dsimp [NativeFamilyData.offset]; omega)
    (tailGame r I) (tail_parameters r I) (tail_native r I)
    (fun b v hv _ j => tail_conditional r I b v hv j)

end Native02Source

theorem source_native_family (r : Partition) : Nonempty (NativeFamily r) := by
  obtain ⟨A⟩ := sourceNative02_frozenActiveFamily r
  obtain ⟨I⟩ := Hybrid.Native02.native_affine_implementation_of_active_family
    (sourceNative02Input r) A
  exact ⟨Native02Source.family r I⟩

theorem common_conull_across_native_markets
    (Γ : Partition → ∀ m, MultipleGame m) (N : ℕ)
    (hF : ∀ r m, (Γ r m).F=sourceValueLaw)
    (hu : ∀ r m, N≤ m → ∀ᵐ v ∂(Γ r m).F, ∀ᵐ a ∂(Γ r m).σ v,
      ∀ i, ∀ dev : JointAction 2,
        (problem (Γ r m) i).payoff v dev≤(problem (Γ r m) i).payoff v a) :
    ∀ᵐ v ∂sourceValueLaw, ∀ r m, N≤ m → ∀ᵐ a ∂(Γ r m).σ v,
      ∀ i, ∀ dev : JointAction 2,
        (problem (Γ r m) i).payoff v dev≤(problem (Γ r m) i).payoff v a := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro m
  by_cases hm : N≤ m
  · have h := hu r m hm
    rw [hF r m] at h
    filter_upwards [h] with v hv
    exact fun _ => hv
  · exact ae_of_all _ (fun _ h => False.elim (hm h))

end FCAppendix.Affine.Multiple07
