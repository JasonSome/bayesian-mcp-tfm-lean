import FCAppendix.Affine.Tail04.OriginalFlagMeasure
import FCAppendix.Affine.Tail04.ActualActiveFiniteGain
import FCAppendix.Affine.Tail04.ActualFallbackPromotion
import FCAppendix.Affine.Tail04.PartialNativeGuardIntegration

noncomputable section
namespace FCAppendix.Affine.Tail04.TwoFocalFlagExpectation
open MeasureTheory ProbabilityTheory Set Classical
open OriginalFlagCompression OriginalFlagMeasure ActualActiveFiniteGain ActualFallbackPromotion
open PartialNativeGuardIntegration
open scoped BigOperators

private theorem flag_expect_exact {ι : Type*} [Fintype ι] [d : DecidableEq ι]
    (p : ι→unitInterval) (f : (ι→Bool)→ℝ) :
    (independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2)).expect f=
      ∫ u,f (flags p u) ∂Measure.pi (fun _ : ι => (volume : Measure unitInterval)) := by
  have hd : d=Classical.decEq ι := Subsingleton.elim _ _
  subst d
  exact flag_expect p f

def suffix {X : Type*} (N : ℕ) (r : Fin (N+2)→ X) : Fin N→ X := fun j => r j.succ.succ

lemma suffix_preserving (N : ℕ) :
    MeasurePreserving (suffix (X:=unitInterval) N)
      (Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval)))
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))) := by
  have h0 := measurePreserving_snd.comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (N+2) => (volume : Measure unitInterval)) 0)
  have h1 := measurePreserving_snd.comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (N+1) => (volume : Measure unitInterval)) 0)
  convert! h1.comp h0 using 1

section FixedRow
variable {N A : ℕ} (active : Fin (N+2)→ Bool) (e : Fin A≃Active active)
  (p : Fin (N+2)→ unitInterval)

def compressedLaw : FiniteLaw (Fin A→ Bool) :=
  independentFlagLaw (fun j => (p (e j).val:ℝ))
    (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2)

def failure (phi : ℕ→ℝ→ unitInterval) (b : Fin A→ℝ) : ℝ :=
  (compressedLaw active e p).prob (fun z => ¬WeightFlags phi b z)

lemma failure_bounds (phi : ℕ→ℝ→ unitInterval) (b : Fin A→ℝ) :
    failure active e p phi b∈Icc (0:ℝ) 1 :=
  ⟨FiniteLaw.prob_nonneg _ _,FiniteLaw.prob_le_one _ _⟩

theorem failure_le_suffix_event (phi : ℕ→ℝ→ unitInterval) (b : Fin A→ℝ)
    (bad : Set (Fin N→ unitInterval)) (hbad : MeasurableSet bad)
    (hgood : ∀ z : Fin (N+2)→ unitInterval,suffix N z∉bad →
      ∀ target,targetTypicalWeight phi b target
        (compressedFlags active e (flags p z))=1) :
    failure active e p phi b≤
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real bad := by
  classical
  let f : (Fin A→Bool)→ℝ := fun z =>
    @ite ℝ (¬WeightFlags phi b z) (Classical.propDecidable _) 1 0
  have hexact : failure active e p phi b=
      ∫ z,f (compressedFlags active e (flags p z))
        ∂Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval)) :=
    (@flag_expect_compression (Fin (N+2)) inferInstance (instDecidableEqFin _) active A e p f).trans
      (@flag_expect_exact (Fin (N+2)) inferInstance (instDecidableEqFin _) p
        (fun z => f (compressedFlags active e z)))
  let g : (Fin (N+2)→ unitInterval)→ℝ := fun z => if suffix N z∈bad then 1 else 0
  have hm : Measurable g := Measurable.ite
    (hbad.preimage (suffix_preserving N).measurable) measurable_const measurable_const
  have hi : Integrable g (Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval))) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun z => by
      dsimp only [g];split_ifs <;> norm_num)
  have hbound := integral_mono_of_nonneg
    (μ:=Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval)))
    (f:=fun z => f (compressedFlags active e (flags p z)))
    (g:=g) (ae_of_all _ fun z => by
      change (0:ℝ) ≤ f (compressedFlags active e (flags p z))
      dsimp only [f]
      split_ifs <;> norm_num) hi
    (ae_of_all _ fun z => by
      by_cases hz : suffix N z∈bad
      · dsimp only [g,f]
        rw [if_pos hz]
        split_ifs <;> norm_num
      · have hg : WeightFlags phi b (compressedFlags active e (flags p z)) := hgood z hz
        simp only [f,g,if_neg hz,not_true_eq_false,hg,if_false,le_refl])
  have hsmall : Measurable (fun z : Fin N→ unitInterval => if z∈bad then (1:ℝ) else 0) :=
    Measurable.ite hbad measurable_const measurable_const
  have he := integral_map (μ:=Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval)))
    (suffix_preserving N).measurable.aemeasurable
    hsmall.aestronglyMeasurable
  rw [(suffix_preserving N).map_eq] at he
  have hmass : (∫ z : Fin (N+2)→ unitInterval,g z
      ∂Measure.pi (fun _ : Fin (N+2) => (volume : Measure unitInterval)))=
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real bad := by
    exact he.symm.trans (by
      simpa only [Set.indicator,Set.mem_setOf_eq,Pi.one_apply] using
        integral_indicator_one (μ:=Measure.pi
          (fun _ : Fin N => (volume : Measure unitInterval))) hbad)
  exact (hexact.trans_le hbound).trans_eq hmass

theorem effective_failure_le (low : Bool) (phi : ℕ→ℝ→ unitInterval) (b : Fin A→ℝ)
    (bad : Set (Fin N→ unitInterval)) (hbad : MeasurableSet bad)
    (hgood : ∀ z : Fin (N+2)→ unitInterval,suffix N z∉bad →
      ∀ target,targetTypicalWeight phi b target
        (compressedFlags active e (flags p z))=1) :
    failure active e p (effectivePhi low phi) b≤
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real bad+
        (if low then 0 else 1) := by
  cases low
  · have hf := (failure_bounds active e p (effectivePhi false phi) b).2
    have hm : 0≤(Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))).real bad :=
      measureReal_nonneg
    simp only [Bool.false_eq_true,if_false]
    linarith
  · simpa only [effectivePhi,Bool.true_eq,if_true,add_zero] using
      failure_le_suffix_event active e p phi b bad hbad hgood

theorem failure_eq_actual (phi : ℕ→ℝ→ unitInterval) (b : Fin A→ℝ) (e0 F : ℝ)
    (hp : ∀ j,sourceFlagProb e0 F b j=(p (e j).val:ℝ)) :
    failure active e p phi b=badWeightProbability phi e0 F b := by
  have he : sourceFlagProb e0 F b=(fun j => (p (e j).val:ℝ)) := funext hp
  unfold failure compressedLaw badWeightProbability
  simp only [he]

theorem compressedLaw_eq_source (b : Fin A→ℝ) (e0 F : ℝ)
    (hp : ∀ j,sourceFlagProb e0 F b j=(p (e j).val:ℝ)) :
    compressedLaw active e p=
      independentFlagLaw (sourceFlagProb e0 F b) (sourceFlagProb_nonneg e0 F b)
        (sourceFlagProb_le_one e0 F b) := by
  have he : sourceFlagProb e0 F b=(fun j => (p (e j).val:ℝ)) := funext hp
  unfold compressedLaw
  simp only [he]

end FixedRow

theorem prob_le_prob_add_variation {ι : Type*} [Fintype ι] (μ ν : FiniteLaw ι)
    (Q : ι→ Prop) [hQ : DecidablePred Q] :
    μ.prob Q≤ ν.prob Q+∑ z,|μ.mass z-ν.mass z| := by
  have hdec : hQ=(fun z => Classical.propDecidable (Q z)) := Subsingleton.elim _ _
  subst hQ
  have hp (z : ι) : μ.mass z*(if Q z then (1:ℝ) else 0)≤
      ν.mass z*(if Q z then (1:ℝ) else 0)+|μ.mass z-ν.mass z| := by
    by_cases hz : Q z
    · simp only [if_pos hz,mul_one]
      linarith [le_abs_self (μ.mass z-ν.mass z)]
    · simp only [if_neg hz,mul_zero,zero_add]
      exact abs_nonneg _
  simpa only [FiniteLaw.prob,FiniteLaw.expect,Finset.sum_add_distrib] using!
    Finset.sum_le_sum (s:=Finset.univ) (fun z _ => hp z)

end FCAppendix.Affine.Tail04.TwoFocalFlagExpectation
