import FCAppendix.Affine.Tail04.LocalCoordinates
import FCAppendix.Affine.Tail04.AtypicalOriginalPosterior

noncomputable section
namespace FCAppendix.Affine.Tail04.PrivateRowSorting
open MeasureTheory ProbabilityTheory Set Classical Filter
open scoped BigOperators Topology
open EqualPrivateSignal EqualPrivateUpper SortedCoordinates LocalCoordinates

local instance (H : ℕ) : TopologicalSpace (Equiv.Perm (Fin H)) := ⊥
local instance (H : ℕ) : DiscreteTopology (Equiv.Perm (Fin H)) := ⟨rfl⟩
local instance (H : ℕ) : MeasurableSpace (Equiv.Perm (Fin H)) := ⊤
local instance (H : ℕ) : BorelSpace (Equiv.Perm (Fin H)) := ⟨borel_eq_top_of_discrete.symm⟩

variable (E : Observable.Regions)

def position {H : ℕ} (b : Fin H → ℝ) (k : Fin H) : Fin H :=
  (enumerate Finset.univ b (Fin.cast (by simp) k)).val

lemma position_injective {H : ℕ} (b : Fin H → ℝ) : Function.Injective (position b) := by
  intro i j he
  have hh := enumerate_injective Finset.univ b (Subtype.ext he)
  exact Fin.ext (congrArg (fun k : Fin (Finset.univ : Finset (Fin H)).card => k.val) hh)

def permutation {H : ℕ} (b : Fin H → ℝ) : Equiv.Perm (Fin H) :=
  Equiv.ofBijective (position b) ⟨position_injective b,
    surjective_of_injective_card _ (position_injective b) rfl⟩

lemma measurable_permutation_apply {Ω : Type*} [MeasurableSpace Ω] {H : ℕ}
    (b : Ω → Fin H → ℝ) (hb : ∀ i, Measurable (fun ω => b ω i)) (k : Fin H) :
    Measurable (fun ω => permutation (b ω) k) :=
  measurable_subtype_coe.comp (measurable_enumerate Finset.univ b hb (Fin.cast (by simp) k))

lemma sorted_antitone {H : ℕ} (b : Fin H → ℝ) : Antitone (fun i => b (permutation b i)) := by
  intro i j hij
  apply enumerate_ordered Finset.univ b
  change i.val ≤ j.val
  exact hij

lemma antitone_perm_le {H : ℕ} (b d : Fin H → ℝ) (σ : Equiv.Perm (Fin H))
    (hb : Antitone b) (hd : Antitone d) (hσ : ∀ i,d i=b (σ i)) (k : Fin H) : d k≤ b k := by
  by_contra hn
  have hlt : b k< d k := lt_of_not_ge hn
  let inc : Fin (k.val+1) → Fin H := fun i => ⟨i.val,by omega⟩
  have hinc (i : Fin (k.val+1)) : inc i≤ k := by change i.val≤ k.val;omega
  have hsmall (i : Fin (k.val+1)) : (σ (inc i)).val< k.val := by
    by_contra h
    have hk : k≤ σ (inc i) := by change k.val≤(σ (inc i)).val;omega
    have ha := hb hk
    have hd' := hd (hinc i)
    rw [hσ (inc i)] at hd'
    linarith
  let f : Fin (k.val+1) → Fin k.val := fun i => ⟨(σ (inc i)).val,hsmall i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have he : σ (inc i)=σ (inc j) := Fin.ext (congrArg (fun u : Fin k.val => u.val) hij)
    have hi := σ.injective he
    exact Fin.ext (congrArg (fun k : Fin H => k.val) hi)
  have hh := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hh
  omega

theorem antitone_perm_unique {H : ℕ} (b d : Fin H → ℝ) (σ : Equiv.Perm (Fin H))
    (hb : Antitone b) (hd : Antitone d) (hσ : ∀ i,d i=b (σ i)) : b=d := by
  funext k
  apply le_antisymm
  · exact antitone_perm_le d b σ.symm hd hb (fun i => by simpa using (hσ (σ.symm i)).symm) k
  · exact antitone_perm_le b d σ hb hd hσ k

lemma continuous_reindex {H : ℕ} {X : Type*} [TopologicalSpace X] :
    Continuous (fun z : (Fin H → X)×Equiv.Perm (Fin H) => fun i => z.1 (z.2 i)) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro z
  have hs : ∀ᶠ w : (Fin H → X)×Equiv.Perm (Fin H) in 𝓝 z,w.2=z.2 := by
    have ho : IsOpen {w : (Fin H → X)×Equiv.Perm (Fin H) | w.2=z.2} :=
      (isOpen_discrete ({z.2} : Set (Equiv.Perm (Fin H)))).preimage continuous_snd
    exact ho.mem_nhds rfl
  apply ((continuous_apply (z.2 i)).comp continuous_fst).continuousAt.congr_of_eventuallyEq
  exact hs.mono (fun w hw => by
    change w.1 (w.2 i) = w.1 (z.2 i)
    rw [hw])

def sortSignal (H : ℕ) (t : Signal H E.R E.Rp) : Signal H E.R E.Rp :=
  fun i => t (permutation (fun k => signalKey E (t k)) i)

lemma sortSignal_antitone (H : ℕ) (t : Signal H E.R E.Rp) :
    Antitone (fun i => signalKey E (sortSignal E H t i)) :=
  sorted_antitone (fun i => signalKey E (t i))

theorem continuous_sortSignal (H : ℕ) : Continuous (sortSignal E H) := by
  let value : Signal H E.R E.Rp×Equiv.Perm (Fin H) → Signal H E.R E.Rp :=
    fun z i => z.1 (z.2 i)
  have hv : Continuous value := continuous_reindex
  let G : Set (Signal H E.R E.Rp×Equiv.Perm (Fin H)) :=
    {z | Antitone (fun i => signalKey E (value z i))}
  have hG : IsClosed G := by
    have he : G=⋂ i : Fin H,⋂ j : Fin H,⋂ (_ : i≤ j),
        {z | signalKey E (value z j)≤ signalKey E (value z i)} := by
      ext z
      simp only [Set.mem_iInter]
      rfl
    rw [he]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hij
    exact isClosed_le ((continuous_signalKey E).comp ((continuous_apply j).comp hv))
      ((continuous_signalKey E).comp ((continuous_apply i).comp hv))
  apply EqualPrivateContinuity.continuous_unique_compact_response G hG value hv (sortSignal E H)
  · intro t
    exact ⟨permutation (fun i => signalKey E (t i)),sortSignal_antitone E H t⟩
  · intro t σ hσ
    let τ := permutation (fun i => signalKey E (t i))
    have he : (fun i => signalKey E (sortSignal E H t i))=
        fun i => signalKey E (t (σ i)) := by
      apply antitone_perm_unique _ _ (σ.trans τ.symm)
        (sortSignal_antitone E H t) hσ
      intro i
      simp [sortSignal,τ,value]
    funext i
    apply signalKey_injective E
    exact (congrFun he i).symm

def sortRow (H : ℕ) (row : Row H E.R E.Rp E.H) : Row H E.R E.Rp E.H :=
  fun i => row (permutation (fun k => signalKey E (signal row k)) i)

lemma measurable_sortRow (H : ℕ) : Measurable (sortRow E H) := by
  apply measurable_pi_iff.mpr
  intro i
  have hp := measurable_permutation_apply (fun row : Row H E.R E.Rp E.H =>
      fun k => signalKey E (signal row k))
    (fun k => (continuous_signalKey E).measurable.comp
      (continuous_signalEntry.measurable.comp (measurable_pi_apply k))) i
  exact measurable_finite_eval (fun row : Row H E.R E.Rp E.H =>
      permutation (fun k => signalKey E (signal row k)) i)
    (fun row k => row k) hp (fun k => measurable_pi_apply k)

@[simp] lemma signal_sortRow (H : ℕ) (row : Row H E.R E.Rp E.H) :
    signal (sortRow E H row)=sortSignal E H (signal row) := rfl

lemma anyUpper_sortRow (H : ℕ) (row : Row H E.R E.Rp E.H) :
    AtypicalOriginalPosterior.anyUpper (marks (signal (sortRow E H row))) ↔
      AtypicalOriginalPosterior.anyUpper (marks (signal row)) := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨permutation (fun k => signalKey E (signal row k)) i,hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨k,hk⟩ := (permutation (fun j => signalKey E (signal row j))).surjective i
    refine ⟨k,?_⟩
    change isUpper (signalEntry (row (permutation (fun j => signalKey E (signal row j)) k)))=true
    rw [hk]
    exact hi

lemma upperCount_sortRow (H : ℕ) (row : Row H E.R E.Rp E.H) :
    upperCount (marks (signal (sortRow E H row)))=upperCount (marks (signal row)) := by
  let σ := permutation (fun k => signalKey E (signal row k))
  have he : (Finset.univ.filter fun i => marks (signal (sortRow E H row)) i=true)=
      (Finset.univ.filter fun i => marks (signal row) i=true).map σ.symm.toEmbedding := by
    ext i
    simp [sortRow,marks,signal,σ]
  unfold upperCount
  rw [he,Finset.card_map]

def sortedLaw (H : ℕ) (θ : ProbabilityMeasure (Row H E.R E.Rp E.H)) :
    ProbabilityMeasure (Row H E.R E.Rp E.H) :=
  ProbabilityMeasure.map θ ((measurable_sortRow E H).aemeasurable (μ := (θ : Measure (Row H E.R E.Rp E.H))))

lemma sorted_signal_law (H : ℕ) (θ : ProbabilityMeasure (Row H E.R E.Rp E.H)) :
    (sortedLaw E H θ : Measure (Row H E.R E.Rp E.H)).map signal =
      ((θ : Measure (Row H E.R E.Rp E.H)).map signal).map (sortSignal E H) := by
  change ((θ : Measure (Row H E.R E.Rp E.H)).map (sortRow E H)).map signal=_
  rw [Measure.map_map continuous_signal.measurable (measurable_sortRow E H),
    Measure.map_map (continuous_sortSignal E H).measurable continuous_signal.measurable]
  rfl

lemma sorted_anyUpper (H : ℕ) (θ : ProbabilityMeasure (Row H E.R E.Rp E.H)) :
    (AtypicalOriginalPosterior.markLaw (sortedLaw E H θ : Measure (Row H E.R E.Rp E.H))).prob AtypicalOriginalPosterior.anyUpper=
      (AtypicalOriginalPosterior.markLaw (θ : Measure (Row H E.R E.Rp E.H))).prob AtypicalOriginalPosterior.anyUpper := by
  rw [FiniteLaw.prob_eq_expect,FiniteLaw.prob_eq_expect,
    AtypicalOriginalPosterior.markLaw_expect,AtypicalOriginalPosterior.markLaw_expect]
  let f : Row H E.R E.Rp E.H → ℝ := fun row =>
    if AtypicalOriginalPosterior.anyUpper (marks (signal row)) then 1 else 0
  have hf : Measurable f := by
    convert! (measurable_of_countable (fun z : Marks H =>
      if AtypicalOriginalPosterior.anyUpper z then (1:ℝ) else 0)).comp
        AtypicalOriginalPosterior.continuous_rowMarks.measurable using 1
  have hmap := integral_map (μ := (θ : Measure (Row H E.R E.Rp E.H)))
    (φ := sortRow E H) (f := f) (measurable_sortRow E H).aemeasurable hf.aestronglyMeasurable
  calc
    _ = ∫row, f (sortRow E H row) ∂(θ : Measure (Row H E.R E.Rp E.H)) := by
      convert! hmap using 1
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro row
      change (if AtypicalOriginalPosterior.anyUpper (marks (signal (sortRow E H row))) then (1:ℝ) else 0) =
        (if AtypicalOriginalPosterior.anyUpper (marks (signal row)) then 1 else 0)
      rw [anyUpper_sortRow]

lemma sorted_upperCount_mean (H : ℕ) (θ : ProbabilityMeasure (Row H E.R E.Rp E.H)) :
    (AtypicalOriginalPosterior.markLaw (sortedLaw E H θ : Measure (Row H E.R E.Rp E.H))).expect (fun z => (upperCount z:ℝ))=
      (AtypicalOriginalPosterior.markLaw (θ : Measure (Row H E.R E.Rp E.H))).expect (fun z => (upperCount z:ℝ)) := by
  rw [AtypicalOriginalPosterior.markLaw_expect,AtypicalOriginalPosterior.markLaw_expect]
  let f : Row H E.R E.Rp E.H → ℝ := fun row => (upperCount (marks (signal row)):ℝ)
  have hf : Measurable f := by
    convert! (measurable_of_countable (fun z : Marks H => (upperCount z:ℝ))).comp
      AtypicalOriginalPosterior.continuous_rowMarks.measurable using 1
  have hmap := integral_map (μ := (θ : Measure (Row H E.R E.Rp E.H)))
    (φ := sortRow E H) (f := f) (measurable_sortRow E H).aemeasurable hf.aestronglyMeasurable
  calc
    _ = ∫row, f (sortRow E H row) ∂(θ : Measure (Row H E.R E.Rp E.H)) := by
      convert! hmap using 1
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro row
      change (upperCount (marks (signal (sortRow E H row))):ℝ) = (upperCount (marks (signal row)):ℝ)
      rw [upperCount_sortRow]

def originalIid (H : ℕ) (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp)) :
    ProbabilityMeasure (Row H E.R E.Rp E.H) :=
  ⟨Measure.pi (fun _ : Fin H => (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))),inferInstance⟩

def sortedOriginalIid (H : ℕ) (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp)) :
    ProbabilityMeasure (Row H E.R E.Rp E.H) := sortedLaw E H (originalIid E H ρ)

def upperProbability (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp)) : ℝ :=
  ∫ x,if isUpper (signalEntry x)=true then (1:ℝ) else 0 ∂(ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))

lemma original_mark_probability (H : ℕ) (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp))
    (i : Fin H) :
    (AtypicalOriginalPosterior.markLaw (originalIid E H ρ : Measure (Row H E.R E.Rp E.H))).prob (fun z => z i=true)=
      upperProbability E ρ := by
  rw [FiniteLaw.prob_eq_expect,AtypicalOriginalPosterior.markLaw_expect]
  let f : Ici E.H ⊕ Icc E.R E.Rp → ℝ :=
    fun x => if isUpper (signalEntry x)=true then 1 else 0
  have hf : Measurable f := (measurable_of_countable (fun b : Bool => if b=true then (1:ℝ) else 0)).comp
    (continuous_isUpper.measurable.comp continuous_signalEntry.measurable)
  have hp := measurePreserving_eval (fun _ : Fin H => (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))) i
  change (∫ row,f (row i) ∂Measure.pi (fun _ : Fin H => (ρ : Measure (Ici E.H ⊕ Icc E.R E.Rp))))=_
  rw [←integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable,hp.map_eq]
  rfl

theorem sortedOriginalIid_anyUpper (H : ℕ)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp)) :
    (AtypicalOriginalPosterior.markLaw (sortedOriginalIid E H ρ : Measure (Row H E.R E.Rp E.H))).prob
      AtypicalOriginalPosterior.anyUpper ≤ (H:ℝ)*upperProbability E ρ := by
  rw [sortedOriginalIid,sorted_anyUpper]
  exact AtypicalOriginalPosterior.anyUpper_bound_of_coordinate _ _
    (fun i => (original_mark_probability E H ρ i).le)

theorem sortedOriginalIid_countMean (H : ℕ)
    (ρ : ProbabilityMeasure (Ici E.H ⊕ Icc E.R E.Rp)) :
    (AtypicalOriginalPosterior.markLaw (sortedOriginalIid E H ρ : Measure (Row H E.R E.Rp E.H))).expect
      (fun z => (upperCount z:ℝ))=(H:ℝ)*upperProbability E ρ := by
  rw [sortedOriginalIid,sorted_upperCount_mean]
  exact TypicalHighPolicy.expected_upperCount H _ _ (original_mark_probability E H ρ)

theorem continuous_sortedSignalLaw (H : ℕ) :
    Continuous (fun μ : ProbabilityMeasure (Signal H E.R E.Rp) =>
      μ.map (continuous_sortSignal E H).measurable.aemeasurable) :=
  ProbabilityMeasure.continuous_map (continuous_sortSignal E H)

end FCAppendix.Affine.Tail04.PrivateRowSorting
