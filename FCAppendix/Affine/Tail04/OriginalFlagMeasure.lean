import FCAppendix.Affine.Tail04.OriginalFlagCompression
import FCAppendix.Affine.Tail04.OriginalNoiseProduct
import FCAppendix.Game.CommonListSeeds

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalFlagMeasure
open MeasureTheory ProbabilityTheory Set Classical
open OriginalFlagCompression
open scoped BigOperators

section Finite
variable {ι : Type*} [Fintype ι] (p : ι→ unitInterval)

def flags (u : ι→ unitInterval) : ι→ Bool := fun i => Empirical.flag (p i) (u i)

omit [Fintype ι] in
lemma measurable_flags : Measurable (flags p) :=
  measurable_pi_lambda _ fun i => (Empirical.measurable_flag_fixed (p i)).comp (measurable_pi_apply i)

private theorem ofMeasure_flags_with_decidable [DecidableEq ι] :
    FiniteLaw.ofMeasure (Measure.pi fun _ : ι => (volume : Measure unitInterval))
      (flags p) (measurable_flags p)=
      independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2) := by
  apply FiniteLaw.ext
  intro z
  rw [FiniteLaw.ofMeasure_mass]
  have he : {u : ι→ unitInterval | flags p u=z}=
      Set.univ.pi (fun i => {v : unitInterval | Empirical.flag (p i) v=z i}) := by
    ext u
    simp only [flags,Set.mem_setOf_eq,Set.mem_univ_pi,funext_iff]
  rw [he,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ i,_) = ∏ i,(IndependentCounts.bernoulli (p i) (p i).2.1 (p i).2.2).mass (z i)
  apply Finset.prod_congr rfl
  intro i _
  rw [←FiniteLaw.ofMeasure_mass (volume : Measure unitInterval) (Empirical.flag (p i))
    (Empirical.measurable_flag_fixed (p i)),Empirical.uniform_flag_law]

theorem ofMeasure_flags :
    FiniteLaw.ofMeasure (Measure.pi fun _ : ι => (volume : Measure unitInterval))
      (flags p) (measurable_flags p)=
      independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2) := by
  exact ofMeasure_flags_with_decidable p

private theorem flag_expect_with_decidable [DecidableEq ι] (f : (ι→ Bool)→ℝ) :
    (independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2)).expect f=
      ∫ u,f (flags p u) ∂Measure.pi (fun _ : ι => (volume : Measure unitInterval)) := by
  exact (congrArg (fun law : FiniteLaw (ι→ Bool) => law.expect f)
    (ofMeasure_flags_with_decidable p).symm).trans
      (FiniteLaw.expect_ofMeasure _ _ (measurable_flags p) f)

theorem flags_law :
    (Measure.pi fun _ : ι => (volume : Measure unitInterval)).map (flags p)=
      FiniteLaw.probabilityMeasure
        (independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2)) := by
  rw [←ofMeasure_flags p,FiniteLaw.probabilityMeasure_ofMeasure]

theorem flag_expect (f : (ι→ Bool)→ℝ) :
    (independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2)).expect f=
      ∫ u,f (flags p u) ∂Measure.pi (fun _ : ι => (volume : Measure unitInterval)) := by
  rw [←ofMeasure_flags p,FiniteLaw.expect_ofMeasure]

end Finite

section Compression
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (active : ι→ Bool)
    {A : ℕ} (e : Fin A≃Active active)

def restrictUniforms (u : ι→ unitInterval) : Fin A→ unitInterval := fun j => u (e j).val

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_restrictUniforms : Measurable (restrictUniforms active e) :=
  measurable_pi_lambda _ fun j => measurable_pi_apply (e j).val

omit [DecidableEq ι] in
theorem restrictUniforms_preserving :
    MeasurePreserving (restrictUniforms active e)
      (Measure.pi fun _ : ι => (volume : Measure unitInterval))
      (Measure.pi fun _ : Fin A => (volume : Measure unitInterval)) := by
  have hs := measurePreserving_fst.comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => (volume : Measure unitInterval))
      (fun i => active i=true))
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin A => (volume : Measure unitInterval)) e.symm
  have hall := hr.comp hs
  convert! hall using 1
  · funext u j
    simp [restrictUniforms,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']

theorem flagLaw_compression (p : ι→ unitInterval) :
    (independentFlagLaw (fun i => (p i:ℝ)) (fun i => (p i).2.1) (fun i => (p i).2.2)).map
      (compressedFlags active e)=
      independentFlagLaw (fun j => (p (e j).val:ℝ))
        (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2) := by
  have hm := FiniteLaw.ofMeasure_map
    (Measure.pi fun _ : ι => (volume : Measure unitInterval)) (flags p)
    (measurable_flags p) (compressedFlags active e) (measurable_of_countable _)
  have hp := FiniteLaw.ofMeasure_comp_measurePreserving _ _ (restrictUniforms active e)
    (restrictUniforms_preserving active e) (flags (fun j => p (e j).val))
      (measurable_flags (fun j => p (e j).val))
  exact (congrArg (fun law : FiniteLaw (ι→ Bool) => law.map (compressedFlags active e))
    (ofMeasure_flags_with_decidable p).symm).trans (hm.trans (hp.trans (ofMeasure_flags_with_decidable (fun j => p (e j).val))))

theorem flag_expect_compression (p : ι→ unitInterval) (f : (Fin A→ Bool)→ℝ) :
    (independentFlagLaw (fun j => (p (e j).val:ℝ))
      (fun j => (p (e j).val).2.1) (fun j => (p (e j).val).2.2)).expect f=
      (independentFlagLaw (fun i => (p i:ℝ))
        (fun i => (p i).2.1) (fun i => (p i).2.2)).expect
          (fun z => f (compressedFlags active e z)) := by
  rw [←flagLaw_compression active e p,FiniteLaw.expect_map]

end Compression

section Original
variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] (N : ℕ)
    (p : X→ unitInterval) (hp : Measurable p)

def mark (r : Fin N→ X) (u : Fin N→ unitInterval) : Fin N→ Bool :=
  flags (fun i => p (r i)) u

include hp in
lemma measurable_mark : Measurable (Function.uncurry (mark N p)) :=
  measurable_pi_lambda _ fun i => Empirical.measurable_flag.comp
    ((hp.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      ((measurable_pi_apply i).comp measurable_snd))

include hp in
theorem original_flag_event (E : Set ((Fin N→ X)×(Fin N→ Bool))) (hE : MeasurableSet E) :
    (∫ r,(independentFlagLaw (fun i => (p (r i):ℝ))
      (fun i => (p (r i)).2.1) (fun i => (p (r i)).2.2)).prob (fun z => (r,z)∈E)
        ∂Measure.pi (fun _ : Fin N => μ))=
      (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))).real
        {r | ((fun i => (r i).1),(fun i => Empirical.flag (p (r i).1) (r i).2))∈E} := by
  let f : (Fin N→ X×unitInterval)→ℝ := fun r =>
    if ((fun i => (r i).1),(fun i => Empirical.flag (p (r i).1) (r i).2))∈E then 1 else 0
  have he : Measurable (fun r : Fin N→ X×unitInterval =>
      ((fun i => (r i).1),(fun i => Empirical.flag (p (r i).1) (r i).2))) :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst).prodMk
      (measurable_pi_lambda _ fun i => Empirical.measurable_flag.comp
        ((hp.comp (measurable_pi_apply i).fst).prodMk (measurable_pi_apply i).snd))
  have hf : Measurable f := Measurable.ite (hE.preimage he) measurable_const measurable_const
  have hi : Integrable f (Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval))) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun r => by
      dsimp only [f];split_ifs <;> norm_num)
  have hzip := OriginalNoiseProduct.zipRow_preserves μ (volume : Measure unitInterval) N
  have hi' : Integrable (fun z => f (OriginalNoiseProduct.zipRow N z))
      ((Measure.pi (fun _ : Fin N => μ)).prod
        (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)))) :=
    hzip.integrable_comp_of_integrable hi
  have hmap := integral_map
    (μ := (Measure.pi (fun _ : Fin N => μ)).prod
      (Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))))
    hzip.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hzip.map_eq,integral_prod _ hi'] at hmap
  calc
    _ = ∫ r,∫ u,f (OriginalNoiseProduct.zipRow N (r,u))
        ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))
        ∂Measure.pi (fun _ : Fin N => μ) := by
      apply integral_congr_ae
      exact ae_of_all _ fun r => by
        simpa only [FiniteLaw.prob,OriginalNoiseProduct.zipRow,f,flags]
          using! flag_expect_with_decidable (fun i => p (r i)) (fun z => if (r,z)∈E then (1:ℝ) else 0)
    _ = ∫ r,f r ∂Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval)) := hmap.symm
    _ = _ := by
      simpa only [f,Set.indicator,Set.mem_setOf_eq,Pi.one_apply,Set.preimage] using!
        integral_indicator_one (μ:=Measure.pi (fun _ : Fin N => μ.prod (volume : Measure unitInterval)))
          (hE.preimage he)

end Original
end FCAppendix.Affine.Tail04.OriginalFlagMeasure
