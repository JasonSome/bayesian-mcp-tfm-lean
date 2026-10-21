import FCAppendix.Affine.Tail04.AtypicalActiveNoisy
import FCAppendix.Affine.Tail04.PrivateRowSorting

noncomputable section
namespace FCAppendix.Affine.Tail04.SortedAllNoise
open MeasureTheory Set Filter Topology Classical
open AllNoiseFiniteSelector AtypicalActiveNoisy PrivateRowSorting SortedCoordinates

local instance (N : ℕ) : TopologicalSpace (Equiv.Perm (Fin N)) := ⊥
local instance (N : ℕ) : DiscreteTopology (Equiv.Perm (Fin N)) := ⟨rfl⟩
local instance (N : ℕ) : MeasurableSpace (Equiv.Perm (Fin N)) := ⊤
local instance (N : ℕ) : BorelSpace (Equiv.Perm (Fin N)) := ⟨borel_eq_top_of_discrete.symm⟩

def sorted {N : ℕ} (b : Fin N → ℝ) : Fin N → ℝ := b ∘ permutation b
def focalRank {N : ℕ} (b : Fin N → ℝ) (i : Fin N) : Fin N := (permutation b).symm i

lemma permutation_eq_of_comparisons {N : ℕ} (a b : Fin N → ℝ)
    (h : ∀ i j, a i< a j ↔ b i< b j) : permutation a=permutation b := by
  have he (i j : Fin N) : a i=a j ↔ b i=b j := by
    constructor
    · intro hij
      apply le_antisymm
      · exact le_of_not_gt (fun hlt => (ne_of_lt ((h j i).mpr hlt)) hij.symm)
      · exact le_of_not_gt (fun hlt => (ne_of_lt ((h i j).mpr hlt)) hij)
    · intro hij
      apply le_antisymm
      · exact le_of_not_gt (fun hlt => (ne_of_lt ((h j i).mp hlt)) hij.symm)
      · exact le_of_not_gt (fun hlt => (ne_of_lt ((h i j).mp hlt)) hij)
  have hr : rankFin Finset.univ a=rankFin Finset.univ b := by
    funext i
    apply Fin.ext
    change (preceding Finset.univ a i).card = (preceding Finset.univ b i).card
    apply congrArg Finset.card
    ext j
    simp only [preceding,Finset.mem_filter,before,h i j,he j i]
  have hE : rankEquiv Finset.univ a=rankEquiv Finset.univ b :=
    Equiv.ext (fun i => congrFun hr i)
  apply Equiv.ext
  intro i
  change (SortedCoordinates.enumerate Finset.univ a (Fin.cast (by simp) i)).val=
    (SortedCoordinates.enumerate Finset.univ b (Fin.cast (by simp) i)).val
  simp only [SortedCoordinates.enumerate,hE]

lemma permutation_eventually_eq {N : ℕ} (b : Fin N → ℝ)
    (hno : ∀ i j, i≠j → b i≠b j) :
    ∀ᶠ a in 𝓝 b, permutation a=permutation b :=
  (comparisons_eventually_eq b hno).mono (fun a ha => permutation_eq_of_comparisons a b ha)

lemma measurable_permutation {N : ℕ} :
    Measurable (permutation : (Fin N → ℝ) → Equiv.Perm (Fin N)) := by
  apply measurable_to_countable'
  intro σ
  have he : (permutation : (Fin N → ℝ) → Equiv.Perm (Fin N)) ⁻¹' {σ}=
      ⋂ i : Fin N,{b | permutation b i=σ i} := by
    ext b
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter]
    exact ⟨fun h i => congrArg (fun e : Equiv.Perm (Fin N) => e i) h,
      fun h => Equiv.ext h⟩
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
    (measurable_permutation_apply (fun b : Fin N → ℝ => b)
      (fun j => measurable_pi_apply j) i) measurable_const)

lemma measurable_sorted {N : ℕ} : Measurable (sorted : (Fin N → ℝ) → (Fin N → ℝ)) := by
  apply measurable_pi_iff.mpr
  intro i
  exact LocalCoordinates.measurable_finite_eval (fun b : Fin N → ℝ => permutation b i)
    (fun b j => b j) (measurable_permutation_apply (fun b : Fin N → ℝ => b)
      (fun j => measurable_pi_apply j) i) (fun j => measurable_pi_apply j)

lemma measurable_focalRank {N : ℕ} (i : Fin N) :
    Measurable (fun b : Fin N → ℝ => focalRank b i) :=
  (measurable_of_countable (fun σ : Equiv.Perm (Fin N) => σ.symm i)).comp measurable_permutation

lemma continuous_reindex_fixed {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (fun b : Fin N → ℝ => b ∘ σ) :=
  continuous_pi (fun i => continuous_apply (σ i))

theorem continuous_sorted {N : ℕ} : Continuous (sorted : (Fin N → ℝ) → (Fin N → ℝ)) := by
  let value : (Fin N → ℝ)×Equiv.Perm (Fin N) → Fin N → ℝ := fun p => p.1 ∘ p.2
  have hv : Continuous value := PrivateRowSorting.continuous_reindex
  let G : Set ((Fin N → ℝ)×Equiv.Perm (Fin N)) := {p | Antitone (value p)}
  have hG : IsClosed G := by
    have he : G=⋂ i : Fin N,⋂ j : Fin N,⋂ (_ : i≤ j),{p | value p j≤ value p i} := by
      ext p
      simp only [Set.mem_iInter]
      rfl
    rw [he]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => isClosed_iInter
      (fun _ => isClosed_le ((continuous_apply j).comp hv) ((continuous_apply i).comp hv))))
  apply EqualPrivateContinuity.continuous_unique_compact_response G hG value hv sorted
  · intro b
    exact ⟨permutation b,PrivateRowSorting.sorted_antitone b⟩
  · intro b σ hσ
    let τ := permutation b
    have h := PrivateRowSorting.antitone_perm_unique (sorted b) (b ∘ σ)
      (σ.trans τ.symm) (PrivateRowSorting.sorted_antitone b) hσ
      (fun i => by simp [sorted,τ])
    exact h.symm

def sortedBox {N : ℕ} {L U : ℝ} (b : Fin N → Icc L U) : Fin N → Icc L U :=
  fun i => b (permutation (fun j => (b j:ℝ)) i)

theorem continuous_sortedBox {N : ℕ} {L U : ℝ} :
    Continuous (sortedBox : (Fin N → Icc L U) → (Fin N → Icc L U)) := by
  apply continuous_pi
  intro i
  apply Continuous.subtype_mk
  exact (continuous_apply i).comp
    (continuous_sorted.comp (continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)))

lemma ae_activeRule_all_permutations (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (b : Fin N → ℝ) (hb : ∀ i, 0< b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ σ : Equiv.Perm (Fin N), ∀ᶠ a in 𝓝 b, ∀ side k i,
        (AtypicalActiveRanks.activeRule N H0 H1 c ξ side
          (noisyBids eps a z ∘ σ) k i ↔
         AtypicalActiveRanks.activeRule N H0 H1 c ξ side
          (noisyBids eps b z ∘ σ) k i) := by
  apply ae_all_iff.mpr
  intro σ
  have hm := measurePreserving_piCongrLeft
    (fun _ : Fin N => (volume : Measure unitInterval)) σ.symm
  have hh := hm.quasiMeasurePreserving.ae
    (ae_activeRule_locally_constant N H0 H1 c ξ heps (b ∘ σ) (fun i => hb (σ i)))
  filter_upwards [hh] with z hz
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin N => unitInterval) σ.symm) z=z ∘ σ := by
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  rw [he] at hz
  have ht := (continuous_reindex_fixed σ).continuousAt.tendsto.eventually hz
  convert! ht using 1

theorem ae_sorted_activeRule_locally_constant (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (b : Fin N → ℝ) (hb : ∀ i, 0< b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b, ∀ side k i,
        (AtypicalActiveRanks.activeRule N H0 H1 c ξ side
          (sorted (noisyBids eps a z)) k (focalRank (noisyBids eps a z) i) ↔
         AtypicalActiveRanks.activeRule N H0 H1 c ξ side
          (sorted (noisyBids eps b z)) k (focalRank (noisyBids eps b z) i)) := by
  filter_upwards [ae_activeRule_all_permutations N H0 H1 c ξ heps b hb,
    ae_noisyBids_distinct heps.ne' b (fun i => (hb i).ne')] with z hz hn
  have hp := (((continuous_noisyBids eps).comp
    (continuous_id.prodMk continuous_const)).continuousAt.tendsto).eventually
      (permutation_eventually_eq (noisyBids eps b z) hn)
  dsimp only [Function.comp_def,id_eq] at hp
  filter_upwards [hz (permutation (noisyBids eps b z)),hp] with a ha hp
  intro side k i
  simpa only [sorted,focalRank,hp] using ha side k ((permutation (noisyBids eps b z)).symm i)

def sortedFallback (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (EqualPrivateSignal.Marks H0))
    (ν1 : FiniteLaw (EqualPrivateSignal.Marks H1)) (b : Fin N → ℝ) (i : Fin N) : CountLaw 2 :=
  AtypicalActiveNoisy.countLaw N H0 H1 c ξ ν0 ν1 (sorted b) (focalRank b i)

theorem ae_sortedFallback_locally_constant (N H0 H1 c : ℕ) (ξ : ℝ) {eps : ℝ}
    (heps : 0< eps) (ν0 : FiniteLaw (EqualPrivateSignal.Marks H0))
    (ν1 : FiniteLaw (EqualPrivateSignal.Marks H1)) (b : Fin N → ℝ) (hb : ∀ i, 0< b i) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ∀ᶠ a in 𝓝 b, ∀ i,
        sortedFallback N H0 H1 c ξ ν0 ν1 (noisyBids eps a z) i=
          sortedFallback N H0 H1 c ξ ν0 ν1 (noisyBids eps b z) i := by
  filter_upwards [ae_sorted_activeRule_locally_constant N H0 H1 c ξ heps b hb,
    ae_noisyBids_distinct heps.ne' b (fun i => (hb i).ne')] with z hz hn
  have hp := (((continuous_noisyBids eps).comp
    (continuous_id.prodMk continuous_const)).continuousAt.tendsto).eventually
      (permutation_eventually_eq (noisyBids eps b z) hn)
  dsimp only [Function.comp_def,id_eq] at hp
  filter_upwards [hz,hp] with a ha hp
  intro i
  unfold sortedFallback
  have hi : focalRank (noisyBids eps a z) i=focalRank (noisyBids eps b z) i := by
    simp only [focalRank,hp]
  rw [hi]
  apply countLaw_congr_rules
  intro side k
  simpa only [hi] using ha side k i

lemma measurable_sortedFallback_mass (N H0 H1 c : ℕ) (ξ : ℝ)
    (ν0 : FiniteLaw (EqualPrivateSignal.Marks H0))
    (ν1 : FiniteLaw (EqualPrivateSignal.Marks H1)) (i : Fin N) (r : Fin 3) :
    Measurable (fun b : Fin N → ℝ => (sortedFallback N H0 H1 c ξ ν0 ν1 b i).mass r) :=
  LocalCoordinates.measurable_finite_eval (fun b : Fin N → ℝ => focalRank b i)
    (fun b j => (AtypicalActiveNoisy.countLaw N H0 H1 c ξ ν0 ν1 (sorted b) j).mass r)
    (measurable_focalRank i)
    (fun j => (measurable_countLaw_mass N H0 H1 c ξ ν0 ν1 j r).comp measurable_sorted)

end FCAppendix.Affine.Tail04.SortedAllNoise
