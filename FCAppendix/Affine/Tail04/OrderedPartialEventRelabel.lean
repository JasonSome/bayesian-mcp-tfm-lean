import FCAppendix.Affine.Tail04.OrderedNativePartialDeviation
import FCAppendix.Affine.Tail04.PartialNativeEvents
import FCAppendix.Exclusive.OnceBayes

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedPartialEventRelabel
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy

variable {m c : ℕ}

def swap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

def reroute (ω : Background m 2 Seed) : Background m 2 Seed :=
  (fun i => Bayes.rerouteDraw swap (ω.1 i),ω.2)

lemma measurePreserving_reroute (Γ : FiniteGame m 2 c Seed) :
    MeasurePreserving reroute (backgroundLaw Γ) (backgroundLaw Γ) := by
  have hp := measurePreserving_pi (fun _ : Fin m => userLaw Γ)
    (fun _ : Fin m => userLaw Γ)
    (f:=fun _ => Bayes.rerouteDraw swap)
    (fun _ => Bayes.measurePreserving_rerouteDraw Γ swap)
  exact hp.prod (MeasurePreserving.id _)

lemma presentList_reroute (ω : Background m 2 Seed) (i : Fin m) (b : ℝ)
    (j : Fin 2) : presentList (reroute ω) i b j=presentList ω i b (swap j) := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [presentList_self]
  · simp [presentList,reroute,Bayes.rerouteDraw,hk,observe,drawsRealization,
      mem_firstK,Equiv.Perm.mul_apply]

variable (D : Data m c) (Q : PublicScenario.Data) (μL : Measure ℝ)
  (hpublic : ∀ N z,D.publicChoice N z=PublicScenario.localChoice D.E Q μL N z)

include Q μL hpublic in
lemma regime_label_independent (j k : Fin 2) (L : LocalList m) :
    NativePartialReports.localRegime D j L=NativePartialReports.localRegime D k L := by
  have h := (PartialNativeEvents.common_controls D Q μL hpublic L L rfl rfl).1
  fin_cases j <;> fin_cases k
  · rfl
  · exact h
  · exact h.symm
  · rfl

include Q μL hpublic in
lemma localRegime_eq (j : Fin 2) (L : LocalList m) :
    OrderedNativePartialReports.localRegime D j L=NativePartialReports.localRegime D j L :=
  regime_label_independent D Q μL hpublic _ _ L

include Q μL hpublic in
lemma backgroundRegime_eq (i : Fin m) (ω : Background m 2 Seed) :
    OrderedNativePartialReports.backgroundRegime D i ω=
      NativePartialReports.backgroundRegime D i ω :=
  localRegime_eq D Q μL hpublic 0 _

include Q μL hpublic in
lemma good_of_both (i : Fin m) (ω : Background m 2 Seed)
    (h : NativePartialReports.goodBackground D i ω)
    (hr : NativePartialReports.goodBackground D i (reroute ω)) :
    OrderedNativePartialReports.goodBackground D i ω := by
  constructor
  · intro j
    let r := OrderedNativePolicy.role D.E j (presentList ω i D.E.R j)
    have hall (r j : Fin 2) : r=j ∨ r=swap j := by
      fin_cases r <;> fin_cases j <;> simp [swap]
    have he : r=j ∨ r=swap j := hall r j
    change NativePartialReports.localGood D r (presentList ω i D.E.R j)
    rcases he with he|he
    · rw [he]
      exact h.1 j
    · have hh := hr.1 (swap j)
      rw [presentList_reroute] at hh
      simpa [he,swap] using hh
  · rw [localRegime_eq D Q μL hpublic,localRegime_eq D Q μL hpublic]
    exact h.2

include Q μL hpublic in
lemma bad_subset (i : Fin m) :
    {ω : Background m 2 Seed | ¬OrderedNativePartialReports.goodBackground D i ω} ⊆
      {ω | ¬NativePartialReports.goodBackground D i ω} ∪
      reroute ⁻¹' {ω | ¬NativePartialReports.goodBackground D i ω} := by
  intro ω hω
  by_contra hn
  have h1 : NativePartialReports.goodBackground D i ω := by
    by_contra hh
    exact hn (Or.inl hh)
  have h2 : NativePartialReports.goodBackground D i (reroute ω) := by
    by_contra hh
    exact hn (Or.inr hh)
  exact hω (good_of_both D Q μL hpublic i ω h1 h2)

include Q μL hpublic in
theorem badMass_le_twice (Γ : FiniteGame m 2 c Seed) (i : Fin m) :
    OrderedNativePartialDeviation.badMass D Γ i≤2*NativePartialDeviation.badMass D Γ i := by
  let A : Set (Background m 2 Seed) := {ω | ¬NativePartialReports.goodBackground D i ω}
  have hA : MeasurableSet A := (NativePartialReports.measurableSet_goodBackground D i).compl
  have hp := measurePreserving_reroute Γ
  have he : (backgroundLaw Γ).real (reroute ⁻¹' A)=(backgroundLaw Γ).real A := by
    exact congrArg ENNReal.toReal (hp.measure_preimage hA.nullMeasurableSet)
  have hm : (backgroundLaw Γ).real
      {ω | ¬OrderedNativePartialReports.goodBackground D i ω}≤
        (backgroundLaw Γ).real (A∪reroute ⁻¹' A) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (bad_subset D Q μL hpublic i))
  have hu := measureReal_union_le (μ:=backgroundLaw Γ) A (reroute ⁻¹' A)
  rw [he] at hu
  change (backgroundLaw Γ).real {ω | ¬OrderedNativePartialReports.goodBackground D i ω}≤
    2*(backgroundLaw Γ).real A
  linarith

include Q μL hpublic in
theorem serviceProb_eq (Γ : FiniteGame m 2 c Seed) (i : Fin m) :
    OrderedNativePartialDeviation.serviceProb D Γ i=
      NativePartialDeviation.serviceProb D Γ i := by
  have he : OrderedNativePartialReports.backgroundRegime D i=
      NativePartialReports.backgroundRegime D i :=
    funext (backgroundRegime_eq D Q μL hpublic i)
  unfold OrderedNativePartialDeviation.serviceProb OrderedNativePartialDeviation.actualRegimeLaw
    NativePartialDeviation.serviceProb NativePartialDeviation.actualRegimeLaw
  simp only [he]

end FCAppendix.Affine.Tail04.OrderedPartialEventRelabel
