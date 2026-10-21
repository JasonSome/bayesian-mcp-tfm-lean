import FCAppendix.Affine.Tail04.PartialNativeCoordinates
import FCAppendix.Affine.Tail04.PublicScenario
import FCAppendix.Affine.Tail04.NativeLowCoordinates

noncomputable section
namespace FCAppendix.Affine.Tail04.PartialNativeEvents
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy NativePartialReports NativeObservationPair
open PartialNativeCoordinates LocalCoordinates SortedCoordinates Hybrid
open JoinedHighPolicy LocalHighCommon EqualPrivateSignal
open scoped BigOperators

local instance (α : Type*) : TopologicalSpace (Finset α) := ⊥
local instance (α : Type*) : DiscreteTopology (Finset α) := ⟨rfl⟩
local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤
local instance (α : Type*) : BorelSpace (Finset α) := ⟨borel_eq_top_of_discrete.symm⟩

variable {m c : ℕ} (D : Data m c)

def weightAtKey (j : Fin 2) (K : Key m) (L : LocalList m) : ℝ :=
  if j=0 then publicWeight K.1.1.card K.1.2.card K.2.val c D.ξ D.E.U D.E.R D.E.Rp D.width
    (D.marksLaw (D.finiteCount K.1.2)) (D.marksLaw K.2)
    (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L)
  else publicWeight K.1.1.card K.2.val K.1.2.card c D.ξ D.E.U D.E.R D.E.Rp D.width
    (D.marksLaw K.2) (D.marksLaw (D.finiteCount K.1.2))
    (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L)

def branchAtKey (j : Fin 2) (K : Key m) (L : LocalList m) : unitInterval :=
  if j=0 then (D.parameter K.1.1 (D.finiteCount K.1.2) K.2 L).2.2
  else (D.parameter K.1.1 K.2 (D.finiteCount K.1.2) L).2.2

def localWeight (j : Fin 2) (L : LocalList m) : ℝ := weightAtKey D j (key D.E L) L
def localBranch (j : Fin 2) (L : LocalList m) : unitInterval := branchAtKey D j (key D.E L) L

lemma measurable_weightAtKey (j : Fin 2) (K : Key m) : Measurable (weightAtKey D j K) := by
  change Measurable (fun L : LocalList m=>weightAtKey D j K L)
  by_cases hj : j=0
  · simp only [weightAtKey,if_pos hj]
    exact (measurable_publicWeight _ _ _ _ _ _ _ _ _ _ _).comp
      (D.parameter_measurable K.1.1 (D.finiteCount K.1.2) K.2)
  · simp only [weightAtKey,if_neg hj]
    exact (measurable_publicWeight _ _ _ _ _ _ _ _ _ _ _).comp
      (D.parameter_measurable K.1.1 K.2 (D.finiteCount K.1.2))

lemma measurable_branchAtKey (j : Fin 2) (K : Key m) : Measurable (branchAtKey D j K) := by
  change Measurable (fun L : LocalList m=>branchAtKey D j K L)
  by_cases hj : j=0
  · simp only [branchAtKey,if_pos hj]
    exact (D.parameter_measurable K.1.1 (D.finiteCount K.1.2) K.2).snd.snd
  · simp only [branchAtKey,if_neg hj]
    exact (D.parameter_measurable K.1.1 K.2 (D.finiteCount K.1.2)).snd.snd

attribute [local irreducible] weightAtKey branchAtKey

lemma measurable_localWeight (j : Fin 2) : Measurable (localWeight D j) := by
  have h : Measurable (fun p : Key m×LocalList m=>weightAtKey D j p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_weightAtKey D j)
  change Measurable (fun L : LocalList m=>weightAtKey D j (key D.E L) L)
  exact h.comp ((measurable_key D.E).prodMk measurable_id)

lemma measurable_localBranch (j : Fin 2) : Measurable (localBranch D j) := by
  have h : Measurable (fun p : Key m×LocalList m=>branchAtKey D j p.1 p.2) :=
    measurable_from_prod_countable_right (measurable_branchAtKey D j)
  change Measurable (fun L : LocalList m=>branchAtKey D j (key D.E L) L)
  exact h.comp ((measurable_key D.E).prodMk measurable_id)

lemma localGood_iff (j : Fin 2) (L : LocalList m) :
    localGood D j L ↔ D.offCommon L=∅ ∧
      (ids D.E 2 L).card≠(ids D.E 3 L).card ∧
        (localBranch D j L:ℝ)< localWeight D j L := by
  have hn : D.finiteCount (ids D.E 2 L)≠D.finiteCount (ids D.E 3 L) ↔
      (ids D.E 2 L).card≠(ids D.E 3 L).card := by
    constructor
    · intro h he;exact h (Fin.ext he)
    · intro h he;exact h (congrArg Fin.val he)
  simp only [localGood,goodAtKey,localBranch,localWeight,branchAtKey,weightAtKey,
    D.key_self L,hn]
  by_cases hj : j=0 <;> simp only [hj,if_true,if_false,UseTypical] <;>
    rw [D.key_self L]

lemma localGood_of_unit_weight (j : Fin 2) (L : LocalList m)
    (hmenu : D.offCommon L=∅) (hne : (ids D.E 2 L).card≠(ids D.E 3 L).card)
    (hw : localWeight D j L=1) (hu : (localBranch D j L:ℝ)<1) : localGood D j L := by
  exact (localGood_iff D j L).mpr ⟨hmenu,hne,by simpa only [hw] using hu⟩

section Public
variable (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hpublic : ∀ N z,D.publicChoice N z=PublicScenario.localChoice D.E Q μL N z)

lemma localChoice_shared (N : ℕ) (L : LocalList m)
    (b b' : TypicalGuard.BidBox N D.E.U) (H H' : ℕ×ℕ) :
    (PublicScenario.localChoice D.E Q μL N (L,(b,H))).1.1=
      (PublicScenario.localChoice D.E Q μL N (L,(b',H'))).1.1 ∧
    (PublicScenario.localChoice D.E Q μL N (L,(b,H))).2=
      (PublicScenario.localChoice D.E Q μL N (L,(b',H'))).2 := by
  unfold PublicScenario.localChoice
  cases hu : Hybrid.seedOnList μL L
  · exact ⟨rfl,rfl⟩
  · exact ⟨PublicScenario.draw_regime_independent_counts Q N _ _ H H' _,
      PublicScenario.draw_branch_independent_counts Q N _ _ H H' _⟩

include Q μL hpublic in
theorem common_controls (L K : LocalList m)
    (hA : ids D.E 1 L=ids D.E 1 K)
    (hL : D.E.roleList 0 L=D.E.roleList 0 K) :
    localRegime D 0 L=localRegime D 1 K ∧ localBranch D 0 L=localBranch D 1 K := by
  let A := ids D.E 1 L
  let b := activeBids D.E A L
  let b' := activeBids D.E A K
  have h := localChoice_shared D Q μL A.card (D.E.roleList 0 L) b b'
    ((ids D.E 2 L).card,(ids D.E 3 L).card)
    ((ids D.E 3 K).card,(ids D.E 2 K).card)
  simp only [localRegime,regimeAtKey,localBranch,branchAtKey,
    if_neg (by decide : (1:Fin 2)≠0),Data.parameter,hpublic,key,Data.finiteCount,ite_true,regime]
  simp only [←hL,NativeLowCoordinates.otherPrivateCount_eq_absent,←ids_card]
  rw [←hA]
  exact h

theorem partial_common_controls {N : ℕ} (D : Data (N+1) c)
    (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
    (i : Fin (N+1)) (ω : Background (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,NativeMenuReports.MenuAction D.E (ω.1 (i.succAbove r)).1.2)
    (b : Icc D.E.R D.E.Rp) :
    localRegime D 0 (presentList ω i b 0)=localRegime D 1 (presentList ω i b 1) ∧
      localBranch D 0 (presentList ω i b 0)=localBranch D 1 (presentList ω i b 1) := by
  apply common_controls D Q μL hpublic
  · exact (partial_ids D.E i ω hr b 0).2.1.trans (partial_ids D.E i ω hr b 1).2.1.symm
  · simpa [otherProposer] using
      PartialNativeCoordinates.common_roleList D.E i ω hr b 0 0 (Or.inl rfl)

end Public

section Exceptions
variable (Γ : FiniteGame m 2 c NativeLocalPolicy.Seed)

def tieEvent (i : Fin m) (j : Fin 2) : Set (Background m 2 NativeLocalPolicy.Seed) :=
  {ω | (ids D.E 2 (presentList ω i D.E.R j)).card=
    (ids D.E 3 (presentList ω i D.E.R j)).card}

def guardEvent (i : Fin m) (j : Fin 2) : Set (Background m 2 NativeLocalPolicy.Seed) :=
  {ω | localWeight D j (presentList ω i D.E.R j)≠1}

def endpointEvent (i : Fin m) : Set (Background m 2 NativeLocalPolicy.Seed) :=
  {ω | localBranch D 0 (presentList ω i D.E.R 0)=1}

lemma measurableSet_tieEvent (i : Fin m) (j : Fin 2) : MeasurableSet (tieEvent D i j) := by
  have hc (k : Fin 4) : Measurable (fun ω : Background m 2 NativeLocalPolicy.Seed =>
      (ids D.E k (presentList ω i D.E.R j)).card) :=
    (measurable_of_countable Finset.card).comp ((measurable_ids D.E k).comp
      (measurable_presentList i D.E.R j))
  exact measurableSet_eq_fun (hc 2) (hc 3)

lemma measurableSet_guardEvent (i : Fin m) (j : Fin 2) : MeasurableSet (guardEvent D i j) :=
  (measurableSet_eq_fun ((measurable_localWeight D j).comp
    (measurable_presentList i D.E.R j)) measurable_const).compl

lemma measurableSet_endpointEvent (i : Fin m) : MeasurableSet (endpointEvent D i) :=
  measurableSet_eq_fun ((measurable_localBranch D 0).comp
    (measurable_presentList i D.E.R 0)) measurable_const

lemma bad_subset_at {N : ℕ} (D : Data (N+1) c)
    (Q : PublicScenario.Data) (μL : Measure ℝ)
    (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
    (i : Fin (N+1)) (ω : Background (N+1) 2 NativeLocalPolicy.Seed)
    (hr : ∀ r : Fin N,NativeMenuReports.MenuAction D.E (ω.1 (i.succAbove r)).1.2)
    (hbad : ¬goodBackground D i ω) :
    ω∈tieEvent D i 0 ∪ tieEvent D i 1 ∪ guardEvent D i 0 ∪ guardEvent D i 1 ∪
      endpointEvent D i := by
  by_contra hn
  have hR : D.E.R∈Icc D.E.R D.E.Rp := ⟨le_rfl,D.E.R_le_Rp⟩
  let b : Icc D.E.R D.E.Rp := ⟨D.E.R,hR⟩
  have hc := partial_common_controls Q μL D hpublic i ω hr b
  have ht0 : ω∉tieEvent D i 0 := fun h => hn (Or.inl (Or.inl (Or.inl (Or.inl h))))
  have ht1 : ω∉tieEvent D i 1 := fun h => hn (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hg0 : ω∉guardEvent D i 0 := fun h => hn (Or.inl (Or.inl (Or.inr h)))
  have hg1 : ω∉guardEvent D i 1 := fun h => hn (Or.inl (Or.inr h))
  have hu : localBranch D 0 (presentList ω i D.E.R 0)≠1 := fun h => hn (Or.inr h)
  have hu0 : (localBranch D 0 (presentList ω i D.E.R 0):ℝ)<1 := by
    apply lt_of_le_of_ne (localBranch D 0 (presentList ω i D.E.R 0)).property.2
    exact fun he => hu (Subtype.ext he)
  apply hbad
  refine ⟨?_,hc.1⟩
  intro j
  apply localGood_of_unit_weight D j _
  · exact partial_on_menu D.E i ω hr D rfl b j
  · fin_cases j <;> assumption
  · fin_cases j
    · exact not_not.mp hg0
    · exact not_not.mp hg1
  · fin_cases j
    · exact hu0
    · change (localBranch D 1 (presentList ω i D.E.R 1):ℝ)<1
      have he : localBranch D 0 (presentList ω i D.E.R 0)=
          localBranch D 1 (presentList ω i D.E.R 1) := hc.2
      rw [←he]
      exact hu0

lemma real_mono_ae {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {A B : Set X} (h : A≤ᵐ[μ] B) : μ.real A≤ μ.real B :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

theorem badMass_union_bound {N : ℕ} (D : Data (N+1) c)
    (Γ : FiniteGame (N+1) 2 c NativeLocalPolicy.Seed)
    (Q : PublicScenario.Data) (μL : Measure ℝ)
    (hpublic : ∀ n z,D.publicChoice n z=PublicScenario.localChoice D.E Q μL n z)
    (i : Fin (N+1))
    (hr : ∀ᵐ ω ∂backgroundLaw Γ,∀ r : Fin N,NativeMenuReports.MenuAction D.E (ω.1 (i.succAbove r)).1.2) :
    NativePartialDeviation.badMass D Γ i≤
      (backgroundLaw Γ).real (tieEvent D i 0)+(backgroundLaw Γ).real (tieEvent D i 1)+
      (backgroundLaw Γ).real (guardEvent D i 0)+(backgroundLaw Γ).real (guardEvent D i 1)+
      (backgroundLaw Γ).real (endpointEvent D i) := by
  have hs := real_mono_ae (backgroundLaw Γ) (hr.mono fun ω hω hbad =>
    bad_subset_at D Q μL hpublic i ω hω hbad)
  have h0 := measureReal_union_le (μ:=backgroundLaw Γ) (tieEvent D i 0) (tieEvent D i 1)
  have h1 := measureReal_union_le (μ:=backgroundLaw Γ)
    (tieEvent D i 0∪tieEvent D i 1) (guardEvent D i 0)
  have h2 := measureReal_union_le (μ:=backgroundLaw Γ)
    (tieEvent D i 0∪tieEvent D i 1∪guardEvent D i 0) (guardEvent D i 1)
  have h3 := measureReal_union_le (μ:=backgroundLaw Γ)
    (tieEvent D i 0∪tieEvent D i 1∪guardEvent D i 0∪guardEvent D i 1) (endpointEvent D i)
  change (backgroundLaw Γ).real {ω | ¬goodBackground D i ω} ≤ _
  change (backgroundLaw Γ).real {ω | ¬goodBackground D i ω} ≤
    (backgroundLaw Γ).real (tieEvent D i 0∪tieEvent D i 1∪guardEvent D i 0∪
      guardEvent D i 1∪endpointEvent D i) at hs
  linarith

end Exceptions
end FCAppendix.Affine.Tail04.PartialNativeEvents
