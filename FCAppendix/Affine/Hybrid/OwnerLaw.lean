import FCAppendix.Affine.Hybrid.Sampling
import FCAppendix.Affine.Hybrid.SupportSampler

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory
open scoped BigOperators

lemma finiteMix_support {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (w : FiniteLaw Ω) (laws : Ω → FiniteLaw Ξ) (x : Ξ)
    (hx : (FiniteLaw.finiteMix w laws).mass x ≠ 0) :
    ∃ i, w.mass i ≠ 0 ∧ (laws i).mass x ≠ 0 := by
  by_contra h
  apply hx
  unfold FiniteLaw.finiteMix FiniteLaw.expect
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : w.mass i=0
  · rw [hi,zero_mul]
  · have hix : (laws i).mass x=0 := by
      by_contra hn
      exact h ⟨i,hi,hn⟩
    change w.mass i * (laws i).mass x=0
    rw [hix,mul_zero]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma rankLaw_relabel [Nonempty ι] (b : ι → ℝ) (e : Equiv.Perm ι) :
    rankLaw (b ∘ e.symm) = (rankLaw b).map e := by
  apply FiniteLaw.ext_expect
  intro f
  rw [FiniteLaw.expect_map]
  unfold FiniteLaw.expect
  calc
    _ = ∑ i, (rankLaw (b ∘ e.symm)).mass (e i)*f (e i) :=
      (Equiv.sum_comp e _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      change averageRank (b ∘ e.symm) (e i)/rankDenominator ι*f (e i)=_
      rw [averageRank_relabel]
      rfl

lemma favoredSetLaw_relabel [Nonempty ι] (b : ι → ℝ) (K : ℕ) (e : Equiv.Perm ι) :
    favoredSetLaw (b ∘ e.symm) K =
      (favoredSetLaw b K).map (fun S => S.map e.toEmbedding) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [favoredSetLaw,FiniteLaw.expect_finiteMix,rankLaw_relabel,FiniteLaw.expect_map,
    FiniteLaw.expect_map, favoredSetLaw, FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro i
  rw [conditionalFill_relabel,FiniteLaw.expect_map]

lemma favoredSetLaw_support [Nonempty ι] (b : ι → ℝ) {K : ℕ}
    (hN : 2 ≤ Fintype.card ι) (hK : 1 ≤ K) (hKN : K ≤ Fintype.card ι)
    (S : Finset ι) (hS : (favoredSetLaw b K).mass S ≠ 0) : S.card=K := by
  obtain ⟨i,_,hi⟩ := finiteMix_support (rankLaw b) (conditionalFill K) S hS
  exact (conditionalFill_implements hN hK hKN i).1 S hi

omit [Fintype ι] in
lemma ownerMarginal_relabel (E : Finset ι) (K : ℕ) (e : Equiv.Perm ι) :
    ownerMarginal (E.map e.toEmbedding) K = ownerMarginal E K ∘ e.symm := by
  funext i
  simp only [ownerMarginal,Finset.mem_map_equiv,Finset.card_map,Function.comp_apply]

lemma ownerDivision_relabel (E : Finset ι) (K : ℕ) (e : Equiv.Perm ι) :
    ownerDivision (E.map e.toEmbedding) K =
      (ownerDivision E K).map (fun AB => (AB.1.map e.toEmbedding,AB.2.map e.toEmbedding)) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [ownerDivision,ownerMarginal_relabel,ExactCapacity.symmetricLottery_equivariant,
    FiniteLaw.expect_map,FiniteLaw.expect_map,FiniteLaw.expect_map,ownerDivision,FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro S
  congr 1
  simp only [Finset.map_sdiff]

lemma exclusiveOwnersLaw_relabel [Nonempty ι] (b : ι → ℝ) (K₁ K₂ : ℕ) (e : Equiv.Perm ι) :
    exclusiveOwnersLaw (b ∘ e.symm) K₁ K₂ =
      (exclusiveOwnersLaw b K₁ K₂).map
        (fun AB => (AB.1.map e.toEmbedding,AB.2.map e.toEmbedding)) := by
  apply FiniteLaw.ext_expect
  intro f
  rw [exclusiveOwnersLaw,FiniteLaw.expect_finiteMix,favoredSetLaw_relabel,FiniteLaw.expect_map,
    FiniteLaw.expect_map,exclusiveOwnersLaw,FiniteLaw.expect_finiteMix]
  apply FiniteLaw.expect_congr
  intro E
  rw [ownerDivision_relabel,FiniteLaw.expect_map]

def sourceOwnersLaw [Nonempty ι] (b : ι → ℝ) (K₁ K₂ : ℕ) :
    FiniteLaw (Finset ι × Finset ι) :=
  if K₁+K₂=0 then FiniteLaw.dirac (∅,∅) else exclusiveOwnersLaw b K₁ K₂

lemma sourceOwnersLaw_support [Nonempty ι] (b : ι → ℝ) (K₁ K₂ : ℕ)
    (hN : 2 ≤ Fintype.card ι) (hK : K₁+K₂ ≤ Fintype.card ι)
    (A B : Finset ι) (hAB : (sourceOwnersLaw b K₁ K₂).mass (A,B) ≠ 0) :
    A.card=K₁ ∧ B.card=K₂ ∧ Disjoint A B := by
  unfold sourceOwnersLaw at hAB
  split_ifs at hAB with hz
  · have hK₁ : K₁=0 := by omega
    have hK₂ : K₂=0 := by omega
    have he : (A,B)=(∅,∅) := by
      by_contra hn
      apply hAB
      simp only [FiniteLaw.dirac]
      exact if_neg hn
    cases he
    simp [hK₁,hK₂]
  · obtain ⟨E,hE,hpair⟩ := finiteMix_support (favoredSetLaw b (K₁+K₂))
      (fun E=>ownerDivision E K₁) (A,B) hAB
    have hcard := favoredSetLaw_support b hN (by omega) hK E hE
    have hne : E.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨hsub,hA,hB,hdisj,_⟩ := ownerDivision_support hne (by omega) A B hpair
    refine ⟨hA,?_,hdisj⟩
    rw [hB,Finset.card_sdiff_of_subset hsub,hcard,hA]
    omega

lemma sourceOwnersLaw_relabel [Nonempty ι] (b : ι → ℝ) (K₁ K₂ : ℕ) (e : Equiv.Perm ι) :
    sourceOwnersLaw (b ∘ e.symm) K₁ K₂ =
      (sourceOwnersLaw b K₁ K₂).map
        (fun AB => (AB.1.map e.toEmbedding,AB.2.map e.toEmbedding)) := by
  unfold sourceOwnersLaw
  split_ifs
  · apply FiniteLaw.ext_expect
    intro f
    simp only [FiniteLaw.expect_dirac,FiniteLaw.expect_map,Finset.map_empty]
  · exact exclusiveOwnersLaw_relabel b K₁ K₂ e

lemma measurable_sourceOwnersLaw_mass [Nonempty ι] (K₁ K₂ : ℕ) (AB : Finset ι × Finset ι) :
    Measurable (fun b : ι → ℝ => (sourceOwnersLaw b K₁ K₂).mass AB) := by
  unfold sourceOwnersLaw
  split_ifs
  · exact measurable_const
  · unfold exclusiveOwnersLaw FiniteLaw.finiteMix FiniteLaw.expect
    exact Finset.measurable_sum _ (fun E _ =>
      (measurable_favoredSetLaw_mass (K₁+K₂) E).mul_const _)

theorem exists_sourceOwners_sampler [Nonempty ι] (K₁ K₂ : ℕ) :
    ∃ f : (ι → ℝ) → unitInterval → Finset ι × Finset ι,
      Measurable (Function.uncurry f) ∧
      (∀ b u,0 < (sourceOwnersLaw b K₁ K₂).mass (f b u)) ∧
      ∀ b,(volume : Measure unitInterval).map (f b)=
        FiniteLaw.probabilityMeasure (sourceOwnersLaw b K₁ K₂) :=
  exists_support_sampler (fun b=>sourceOwnersLaw b K₁ K₂) (measurable_sourceOwnersLaw_mass K₁ K₂)

end FCAppendix.Affine.Hybrid
