import FCAppendix.Affine.Tail04.PartialNativeSeed
import FCAppendix.Affine.Tail04.PartialNativeSeedReplacement
import FCAppendix.Affine.Tail04.NativeActiveFiberCoordinates
import FCAppendix.Affine.Tail04.OriginalFlagCompression

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativePublicWeight
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativeObservationPair NativePartialReports NativeMenuReports
open PartialNativeCoordinates PartialNativeEvents PartialNativeSeed
open NativeActiveFiberCoordinates LocalCoordinates SortedCoordinates Hybrid
open EqualPrivateSignal JoinedHighPolicy LocalHighCommon MenuError
open scoped BigOperators

variable {m N c : ℕ}

def orderedPrivateFin (D : Data m c) (j : Fin 2) (L : LocalList m) : Fin (m+1)×Fin (m+1) :=
  if j=0 then (D.finiteCount (ids D.E 2 L),D.finiteCount (ids D.E 3 L))
  else (D.finiteCount (ids D.E 3 L),D.finiteCount (ids D.E 2 L))

lemma orderedPrivateFin_val (D : Data (N+1) c) (j : Fin 2) (L : LocalList (N+1)) :
    ((orderedPrivateFin D j L).1.val,(orderedPrivateFin D j L).2.val)=orderedCounts D j L := by
  by_cases hj : j=0 <;> simp only [orderedPrivateFin,orderedCounts,hj,if_true,if_false,Data.finiteCount]

def partialPrivateFin (_D : Data (N+1) c) (i : Fin (N+1)) (kind : Fin N→ Fin 4)
    (side j : Fin 2) : Fin (N+2) :=
  ⟨(rivalSet i kind (NativeContinuation.upperTag j)).card+partialOffset side j,by
    have hc : (rivalSet i kind (NativeContinuation.upperTag j)).card≤ N := by
      rw [rivalSet_card_filter]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    have ho := partialOffset_le_one side j
    omega⟩

lemma partial_orderedPrivateFin (D : Data (N+1) c) (i : Fin (N+1))
    (kind : Fin N→ Fin 4) (ω : Background (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r,MenuAction D.E (ω.1 (i.succAbove r)).1.2)
    (hk : rivalKinds D.E i ω=kind) (b : Icc D.E.R D.E.Rp) (side : Fin 2) :
    orderedPrivateFin D side (presentList ω i b side)=
      (partialPrivateFin D i kind side 0,partialPrivateFin D i kind side 1) := by
  have h := partial_orderedCounts D.E i ω hr D rfl b side
  rw [hk,←orderedPrivateFin_val] at h
  have hu0 : NativeContinuation.upperTag 0 = (2 : Fin 4) := by decide
  have hu1 : NativeContinuation.upperTag 1 = (3 : Fin 4) := by decide
  apply Prod.ext
  · apply Fin.ext
    have h0 := congrArg Prod.fst h
    simpa only [partialPrivateFin,hu0,rivalSet_card] using h0
  · apply Fin.ext
    have h1 := congrArg Prod.snd h
    simpa only [partialPrivateFin,hu1,rivalSet_card] using h1

def drawnParameter (D : Data m c) (Q : PublicScenario.Data) (A : ℕ)
    (H0 H1 : Fin (m+1)) (b : TypicalGuard.BidBox A D.E.U) (u : unitInterval) :
    Parameters A H0.val D.E.R D.E.Rp D.E.U :=
  let q := PublicScenario.draw Q A (TypicalGuard.bids b,(H0.val,H1.val)) u
  ((q.1,b),(D.signalLaw H0,q.2))

lemma measurable_drawnParameter (D : Data m c) (Q : PublicScenario.Data) (A : ℕ)
    (H0 H1 : Fin (m+1)) :
    Measurable (fun z : TypicalGuard.BidBox A D.E.U×unitInterval =>
      drawnParameter D Q A H0 H1 z.1 z.2) := by
  have hi : Measurable (fun z : TypicalGuard.BidBox A D.E.U × unitInterval =>
      ((TypicalGuard.bids z.1,(H0.val,H1.val)),z.2)) :=
    ((TypicalGuard.continuous_bids.measurable.comp measurable_fst).prodMk
      measurable_const).prodMk measurable_snd
  have hq := (PublicScenario.measurable_draw Q A).comp hi
  exact (hq.fst.prodMk measurable_fst).prodMk (measurable_const.prodMk hq.snd)

lemma localWeight_of_seed (D : Data m c) (Q : PublicScenario.Data) (μL : Measure ℝ)
    (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
    (j : Fin 2) (L : LocalList m) (u : unitInterval)
    (hu : seedOnList μL (D.E.roleList 0 L)=some u) :
    localWeight D j L=
      publicWeight (ids D.E 1 L).card (orderedPrivateFin D j L).1.val
        (orderedPrivateFin D j L).2.val c D.ξ D.E.U D.E.R D.E.Rp D.width
        (D.marksLaw (orderedPrivateFin D j L).1) (D.marksLaw (orderedPrivateFin D j L).2)
        (drawnParameter D Q (ids D.E 1 L).card (orderedPrivateFin D j L).1
          (orderedPrivateFin D j L).2 (activeBids D.E (ids D.E 1 L) L) u) := by
  simp only [localWeight]
  rw [D.key_self L]
  fin_cases j <;>
    simp [weightAtKey,orderedPrivateFin,
      Data.parameter,hpublic,PublicScenario.localChoice,hu,drawnParameter,Data.finiteCount] <;> rfl

def fiberParameter (D : Data (N+1) c) (Q : PublicScenario.Data) (i : Fin (N+1))
    (kind : Fin N→ Fin 4) (side : Fin 2)
    (z : (Fin N→ UserDraw 2)×unitInterval) :
    Parameters (commonSize i kind) (partialPrivateFin D i kind side 0).val
      D.E.R D.E.Rp D.E.U :=
  drawnParameter D Q (commonSize i kind) (partialPrivateFin D i kind side 0)
    (partialPrivateFin D i kind side 1)
    (SortedAllNoise.sortedBox (NativeActiveFiberCoordinates.commonRow D.E i kind z.1)) z.2

def fiberWeight (D : Data (N+1) c) (Q : PublicScenario.Data) (i : Fin (N+1))
    (kind : Fin N→ Fin 4) (side : Fin 2) (z : (Fin N→ UserDraw 2)×unitInterval) : ℝ :=
  publicWeight (commonSize i kind) (partialPrivateFin D i kind side 0).val
    (partialPrivateFin D i kind side 1).val c D.ξ D.E.U D.E.R D.E.Rp D.width
    (D.marksLaw (partialPrivateFin D i kind side 0))
    (D.marksLaw (partialPrivateFin D i kind side 1)) (fiberParameter D Q i kind side z)

lemma measurable_fiberParameter (D : Data (N+1) c) (Q : PublicScenario.Data)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (side : Fin 2) :
    Measurable (fiberParameter D Q i kind side) :=
  (measurable_drawnParameter D Q (commonSize i kind) _ _).comp
    (((SortedAllNoise.continuous_sortedBox.measurable).comp
      ((measurable_commonRow D.E i kind).comp measurable_fst)).prodMk measurable_snd)

lemma measurable_fiberWeight (D : Data (N+1) c) (Q : PublicScenario.Data)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (side : Fin 2) :
    Measurable (fiberWeight D Q i kind side) :=
  (measurable_publicWeight _ _ _ _ _ _ _ _ _ _ _).comp
    (measurable_fiberParameter D Q i kind side)

theorem partial_weight_tuple (D : Data (N+1) c) (Q : PublicScenario.Data) (μL : Measure ℝ)
    (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (ω : Background (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r,MenuAction D.E (ω.1 (i.succAbove r)).1.2)
    (hk : rivalKinds D.E i ω=kind) (b : Icc D.E.R D.E.Rp) (side : Fin 2)
    (u : unitInterval) (hu : seedOnList μL (D.E.roleList 0 (presentList ω i b side))=some u) :
    localWeight D side (presentList ω i b side)=
      fiberWeight D Q i kind side ((fun r => ω.1 (i.succAbove r)),u) := by
  rw [localWeight_of_seed D Q μL hpublic side _ u hu,
    partial_orderedPrivateFin D i kind ω hr hk b side]
  have hA : ids D.E 1 (presentList ω i b side)=rivalSet i kind 1 := by
    simpa only [hk] using (partial_ids D.E i ω hr b side).2.1
  rw [hA,common_bids D.E i kind ω hr hk b side]
  rfl

lemma fiberWeight_eraseLow (D : Data (N+1) c) (Q : PublicScenario.Data)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (side : Fin 2)
    (row : Fin N→ UserDraw 2) (u : unitInterval) :
    fiberWeight D Q i kind side (PartialNativeSeedReplacement.eraseLow kind row,u)=
      fiberWeight D Q i kind side (row,u) := by
  have he : NativeActiveFiberCoordinates.commonRow D.E i kind
      (PartialNativeSeedReplacement.eraseLow kind row)=
      NativeActiveFiberCoordinates.commonRow D.E i kind row := by
    funext q
    have hq := (NativeFiberEnumerations.categoryEnumeration i kind 1 q).property
    simp only [NativeActiveFiberCoordinates.commonRow,PartialNativeSeedReplacement.eraseLow,hq,
      show ¬(1:Fin 4)=0 by decide,if_false]
  simp only [fiberWeight,fiberParameter,he]

theorem native_fiber_guard_replacement
    (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed) (D : Data (N+1) c)
    (Q : PublicScenario.Data)
    (hpublic : ∀ n z,D.publicChoice n z=
      PublicScenario.localChoice D.E Q (NativeFlag.nativeLowBidLaw Γ D.E) n z)
    (hcat : ∀ k : Fin 4,(userLaw Γ) (D.E.coarseTag ⁻¹' {k})≠0)
    (hlow : ∀ b,NativeFlag.nativeLowBidLaw Γ D.E {b}=0)
    (hmenu : ∀ᵐ x ∂Γ.F⊗ₘΓ.σ,MenuAction D.E x.2)
    (i : Fin (N+1)) (kind : Fin N→ Fin 4) (n : ℕ)
    (e : Fin (n+1)≃{r : Fin N // kind r=0}) (side : Fin 2) :
    (fiber Γ D kind).real (restoreBackground i ⁻¹' guardEvent D i side)=
      ((fiber Γ D kind).prod (volume : Measure unitInterval)).real
        {z | fiberWeight D Q i kind side (z.1.1,z.2)≠1} := by
  let b : Icc D.E.R D.E.Rp := ⟨D.E.R,le_rfl,D.E.R_le_Rp⟩
  have he : (restoreBackground i ⁻¹' guardEvent D i side)=ᵐ[fiber Γ D kind]
      {z | fiberWeight D Q i kind side (z.1,fiberMinimum Γ D kind n e z)≠1} := by
    filter_upwards [fiber_shape Γ D kind,fiber_menu Γ D hmenu kind,
      fiber_seed_on_present Γ D hmenu i kind n e b side] with z hz hmz hs
    have hk : rivalKinds D.E i (restoreBackground i z)=kind := by
      funext r;simpa only [rivalKinds,restoreBackground_rival] using hz r
    have hr : ∀ r,MenuAction D.E ((restoreBackground i z).1 (i.succAbove r)).1.2 := by
      intro r;simpa only [restoreBackground_rival] using hmz r
    have hw := partial_weight_tuple D Q _ hpublic i kind (restoreBackground i z) hr hk b side _ hs
    simp only [restoreBackground_rival] at hw
    apply propext
    change (_≠1 ↔ _≠1)
    rw [hw]
  rw [measureReal_def,measure_congr he]
  change (fiber Γ D kind).real {z | fiberWeight D Q i kind side (z.1,fiberMinimum Γ D kind n e z)≠1}=_
  exact PartialNativeSeedReplacement.event_replacement Γ D hcat hlow kind n e
    {z | fiberWeight D Q i kind side z≠1}
    (measurableSet_eq_fun (measurable_fiberWeight D Q i kind side) measurable_const).compl
    (fun row u => by
      change fiberWeight D Q i kind side
        (PartialNativeSeedReplacement.eraseLow kind row,u)≠1 ↔
          fiberWeight D Q i kind side (row,u)≠1
      rw [fiberWeight_eraseLow])

end FCAppendix.Affine.Tail04.PartialNativePublicWeight
