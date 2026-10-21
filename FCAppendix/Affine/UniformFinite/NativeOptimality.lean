import FCAppendix.Affine.UniformFinite.NativeContext

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Uniform05 SourceContinuity
open scoped BigOperators

namespace NativeContext
variable {M : ℕ} [NeZero M]

theorem extend_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A S : Finset ι) (c : ℕ) (r : ι → ℝ)
    (hz : ∀ a, a∉A → r a=0) (hS : Finite.Optimal (min A.card c) r S) :
    Finite.Optimal c r S := by
  refine ⟨hS.1.trans (min_le_right _ _),?_⟩
  intro D hD
  have hcap : (D∩A).card ≤ min A.card c :=
    le_min (Finset.card_le_card Finset.inter_subset_right)
      ((Finset.card_le_card Finset.inter_subset_left).trans hD)
  have hh := hS.2 (D∩A) hcap
  have he : (∑ a∈D∩A,r a) = ∑ a∈D,r a :=
    Finset.sum_subset Finset.inter_subset_left (fun a ha hn => hz a
      (fun hA => hn (Finset.mem_inter.mpr ⟨ha,hA⟩)))
  rwa [he] at hh

theorem acceptance_on_valid (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (X : Hybrid.ClassifiedContext M) (hX : Valid X) (j : Fin 2) (a : Fin M) :
    (∫ s : unitInterval, if a∈(contextPolicy i G μseed).select j X s then (1:ℝ) else 0) =
      NativeRow.acceptance i (decode X) j (state i G X) (common i μseed X) a := by
  simp only [contextPolicy, select, if_pos hX, sourceSelect, NativeRow.acceptance]

theorem lower_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    (X : Hybrid.ClassifiedContext M) (hX : Valid X)
    (h0 : NonnegativeList X.1) (hU : ∀ a, entryBid (X.1 a) ≤ cap i)
    (j : Fin 2) (s : unitInterval) :
    Finite.Optimal (Uniform07.capacity M-Hybrid.contextUpper j X)
      (Hybrid.lowerContextReceipt ((contextPolicy i G μseed).nativeGame Γ (cap i))
        (contextPolicy i G μseed) (xi i) j X)
      ((contextPolicy i G μseed).select j X s) := by
  let C := contextPolicy (M:=M) i G μseed
  let r : Fin M→ℝ := fun a => Source.lowerBids (decode X) (bids i (state i G X)) a *
    (1-xi i*NativeRow.acceptance i (decode X) (Hybrid.otherProposer j)
      (state i G X) (common i μseed X) a)
  have hreceipt : Hybrid.lowerContextReceipt (C.nativeGame Γ (cap i)) C (xi i) j X = r := by
    funext a
    rw [Hybrid.lowerContextReceipt, Hybrid.contextAcceptance]
    change entryBid (X.1 a) *
      (1-xi i*(∫ s : unitInterval, if a∈C.select (Hybrid.otherProposer j) X s then (1:ℝ) else 0
        ∂Γ.seedLaw)) = r a
    rw [hseed, acceptance_on_valid i G μseed X hX]
    dsimp [r]
    rw [state_lowerBids i G X h0 hU]
  have hs := NativeRow.select_optimal i (decode X) j (state i G X) (common i μseed X) s
  have hc : Source.residual (decode X) j =
      min (present X.1).card (Uniform07.capacity M-Hybrid.contextUpper j X) := by
    unfold Source.residual
    rw [decode_upper X hX j]
    rfl
  rw [hc] at hs
  have he := extend_budget (present X.1)
    (NativeRow.select i (decode X) j (state i G X) (common i μseed X) s)
    (Uniform07.capacity M-Hybrid.contextUpper j X) r
    (fun a ha => by simp [r, Source.lowerBids, decode, ha]) hs
  change Finite.Optimal (Uniform07.capacity M-Hybrid.contextUpper j X)
    (Hybrid.lowerContextReceipt (C.nativeGame Γ (cap i)) C (xi i) j X) (C.select j X s)
  rw [hreceipt]
  simpa only [C,contextPolicy,select,if_pos hX,sourceSelect] using he

theorem observed_lower_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) (hseed : Γ.seedLaw=volume)
    (j : Fin 2) (L : LocalList M) (hL : FeasibleObservedList j L) (s : unitInterval) :
    Finite.Optimal (Uniform07.capacity M-TaggedLocal.localCount (cap i) (cap i) L 2)
      (Hybrid.lowerContextReceipt ((contextPolicy i G μseed).nativeGame Γ (cap i))
        (contextPolicy i G μseed) (xi i) j (Hybrid.observedContext (cap i) j L))
      ((contextPolicy i G μseed).select j (Hybrid.observedContext (cap i) j L) s) := by
  obtain ⟨h0,hU⟩ := observed_bid_box i j L ((feasibleObservedList_iff_nonnegative j L).mp hL)
  simpa only [Hybrid.contextUpper_observed] using
    lower_optimal i G μseed Γ hseed (Hybrid.observedContext (cap i) j L)
      (observed_valid (cap i) j L) h0 hU j s

def localPolicy (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) (j : Fin 2) :
    LocalPolicy M (Uniform07.capacity M) unitInterval :=
  (contextPolicy i G μseed).localPolicy (cap i) j

theorem localPolicy_measurable (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ) (j : Fin 2) :
    Measurable (fun x : LocalList M × unitInterval => (localPolicy i G μseed j x.1 x.2).val) :=
  (contextPolicy i G μseed).measurable_selection (cap i) j

def nativeGame (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) :
    FiniteGame M 2 (Uniform07.capacity M) unitInterval :=
  (contextPolicy i G μseed).nativeGame Γ (cap i)

theorem original_laws_retained (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval) :
    (nativeGame i G μseed Γ).F=Γ.F ∧ (nativeGame i G μseed Γ).σ=Γ.σ ∧
      (nativeGame i G μseed Γ).seedLaw=Γ.seedLaw ∧
      userLaw (nativeGame i G μseed Γ)=userLaw Γ ∧
      backgroundLaw (nativeGame i G μseed Γ)=backgroundLaw Γ := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem proposer_optimal (i : Row) (G : RestrictedLaw i) (μseed : Measure ℝ)
    (Γ : FiniteGame M 2 (Uniform07.capacity M) unitInterval)
    (hseed : Γ.seedLaw=volume) {R : ℝ} (hR : cap i< R)
    (hA : Γ.A=Schedule.affine 2 (eta i) (eta_range i).1.le (eta_range i).2.le)
    (hfull : ∀ᵐ d ∂userProfileLaw (nativeGame i G μseed Γ), d∈Hybrid.classifiedProfiles M (cap i)) :
    ∀ j L, FeasibleObservedList j L → ∀ s,
      Finite.Optimal (Uniform07.capacity M)
        (beliefReceipts (nativeGame i G μseed Γ).A
          (posteriorCountBelief (nativeGame i G μseed Γ)
            (Hybrid.classifiedPosterior (nativeGame i G μseed Γ) (R:=R) hfull) j L) L)
        ((nativeGame i G μseed Γ).policy j L s).val := by
  apply Hybrid.ContextPolicy.nativeGame_proposer_optimal
    (contextPolicy i G μseed) Γ (cap_pos i).le hR (eta_range i).1.le (eta_range i).2.le hA hfull
  intro j L hL s
  exact observed_lower_optimal i G μseed Γ hseed j L hL s

end NativeContext
end FCAppendix.Affine.UniformFinite
