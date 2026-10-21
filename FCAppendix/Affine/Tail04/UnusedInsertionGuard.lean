import FCAppendix.Affine.Tail04.FocalInsertionGuard
import FCAppendix.Affine.Tail04.SourceMenuPopulation
import FCAppendix.Affine.Tail04.ActualGuardMarginals

noncomputable section
namespace FCAppendix.Affine.Tail04.UnusedInsertionGuard
open MeasureTheory ProbabilityTheory Set Classical
open EqualPrivateSignal LocalHighCommon JoinedHighPolicy
open MenuError SourceMenuPopulation TypicalGuardEndpoints
open scoped BigOperators

lemma weight_one_margin (A H0 H1 c : ℕ) (ξ B R Rp γ : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin A)) (b : Fin A→ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (hγ : 0< γ)
    (h : TypicalGuard.weight A H0 H1 c ξ B R Rp γ reg I O0 O1 b ν0 ν1=1) :
    TypicalHighPolicy.Structural A H0 H1 c I O0 O1 ∧
      γ≤ TypicalGuard.margin A H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1 := by
  have hs : TypicalHighPolicy.Structural A H0 H1 c I O0 O1 := by
    by_contra hn
    simp only [TypicalGuard.weight,if_neg hn] at h
    norm_num at h
  have hp : probabilityClip (TypicalGuard.margin A H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1/γ)=1 := by
    simpa only [TypicalGuard.weight,if_pos hs,probabilityClip] using h
  have hh := (ActualGuardMarginals.probabilityClip_eq_one_iff _).mp hp
  exact ⟨hs,by simpa only [one_mul] using (le_div_iff₀ hγ).mp hh⟩

lemma realization_bounds (A H c : ℕ) (ξ B γ : ℝ) (reg : Bool)
    (O I : Finset (Fin A)) (b : Fin A→ℝ)
    (hm : γ≤ TypicalGuard.realizationMargin A H c ξ B reg O I b) (z : Marks H) :
    (1-ξ)*B+γ≤ TypicalHighPolicy.multiplier A H c ξ reg O I b z ∧
      TypicalHighPolicy.multiplier A H c ξ reg O I b z+γ≤1 := by
  have hh := hm.trans (TypicalGuard.finiteMinimum_le _ z)
  have hl := hh.trans (min_le_left _ _)
  have hu := hh.trans (min_le_right _ _)
  constructor <;> linarith

lemma margin_mono_cap (A H0 H1 c : ℕ) (ξ B B0 R Rp γ : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin A)) (b : Fin A→ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (hξ : ξ≤1) (hB : B≤ B0) (hγ1 : γ≤1)
    (hm : γ≤ TypicalGuard.margin A H0 H1 c ξ B0 R Rp reg I O0 O1 b ν0 ν1) :
    γ≤ TypicalGuard.margin A H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1 := by
  have hκ : 0≤1-ξ := by linarith
  have hBB := mul_le_mul_of_nonneg_left hB hκ
  have h0 := hm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have h1 := hm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hp := hm.trans (min_le_right _ _)
  apply le_min
  · apply le_min
    · apply TypicalGuard.le_finiteMinimum _ γ hγ1
      intro z
      have hz := realization_bounds A H0 c ξ B0 γ reg O0 I b h0 z
      exact le_min (by linarith [hz.1]) (by linarith [hz.2])
    · apply TypicalGuard.le_finiteMinimum _ γ hγ1
      intro z
      have hz := realization_bounds A H1 c ξ B0 γ reg O1 I b h1 z
      exact le_min (by linarith [hz.1]) (by linarith [hz.2])
  · exact hp

theorem guard_of_wide_weight (A H0 H1 c : ℕ) (ξ B B0 R Rp width γ : ℝ) (reg : Bool)
    (I O0 O1 : Finset (Fin A)) (b : Fin A→ℝ)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1))
    (_hξ : 0≤ ξ) (hξ1 : ξ≤1) (hB : B≤ B0) (hw : 0< width) (hwγ : width≤ γ) (hγ1 : γ≤1)
    (hstep : ξ/mixedReciprocalSum I b≤ γ)
    (hone : TypicalGuard.weight A H0 H1 c ξ B0 R Rp γ reg I O0 O1 b ν0 ν1=1) :
    FocalInsertion.Guard A H0 H1 c ξ B R Rp reg I O0 O1 b ν0 ν1 ∧
      TypicalGuard.weight A H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1=1 := by
  have hγ : 0< γ := hw.trans_le hwγ
  obtain ⟨hs,hm⟩ := weight_one_margin A H0 H1 c ξ B0 R Rp γ reg I O0 O1 b ν0 ν1 hγ hone
  have hm' := margin_mono_cap A H0 H1 c ξ B B0 R Rp γ reg I O0 O1 b ν0 ν1 hξ1 hB hγ1 hm
  have hr0 := hm'.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr1 := hm'.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hp := hm'.trans (min_le_right _ _)
  have hg0 : FocalInsertion.LocalGuard A H0 c ξ B reg O0 I b := by
    intro z
    have hz:=realization_bounds A H0 c ξ B γ reg O0 I b hr0 z
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hg1 : FocalInsertion.LocalGuard A H1 c ξ B reg O1 I b := by
    intro z
    have hz:=realization_bounds A H1 c ξ B γ reg O1 I b hr1 z
    exact ⟨by linarith [hz.1],by linarith [hz.2]⟩
  have hp0 : FocalInsertion.PartialGuard A H0 c ξ R Rp reg O0 I b ν0 := by
    cases reg
    · have hh := hp.trans (min_le_left _ _)
      change TypicalHighPolicy.meanMultiplier A H0 c ξ false O0 I b ν0+ξ/mixedReciprocalSum I b≤ R
      linarith
    · have hh := hp.trans (min_le_left _ _)
      change Rp≤ TypicalHighPolicy.meanMultiplier A H0 c ξ true O0 I b ν0
      linarith
  have hp1 : FocalInsertion.PartialGuard A H1 c ξ R Rp reg O1 I b ν1 := by
    cases reg
    · have hh := hp.trans (min_le_right _ _)
      change TypicalHighPolicy.meanMultiplier A H1 c ξ false O1 I b ν1+ξ/mixedReciprocalSum I b≤ R
      linarith
    · have hh := hp.trans (min_le_right _ _)
      change Rp≤ TypicalHighPolicy.meanMultiplier A H1 c ξ true O1 I b ν1
      linarith
  exact ⟨⟨hs,hg0,hg1,hp0,hp1⟩,
    TypicalGuard.weight_eq_one A H0 H1 c ξ B R Rp width reg I O0 O1 b ν0 ν1 hw hs
      (hwγ.trans hm')⟩

lemma insertion_step {N : ℕ} {ξ W wbar γ δ Z : ℝ}
    (hN : 0< N) (hξ : 0≤ ξ) (hδ : 0< δ) (hδw : δ≤ wbar/2)
    (hW : |W-wbar|≤ Z) (hZ : Z< δ) (hroom : 2*ξ/((N:ℝ)*wbar)≤ γ) :
    0< W ∧ ξ/((N:ℝ)*W)≤ γ := by
  have hwbar : 0< wbar := by linarith
  have hWlo : wbar/2≤ W := by linarith [(abs_le.mp hW).1]
  have hw : 0< W := (half_pos hwbar).trans_le hWlo
  have hn : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  refine ⟨hw,?_⟩
  calc
    ξ/((N:ℝ)*W)≤ ξ/((N:ℝ)*(wbar/2)) :=
      div_le_div_of_nonneg_left hξ (mul_pos hn (half_pos hwbar))
        (mul_le_mul_of_nonneg_left hWlo hn.le)
    _=2*ξ/((N:ℝ)*wbar) := by ring
    _≤ γ := hroom

end FCAppendix.Affine.Tail04.UnusedInsertionGuard
