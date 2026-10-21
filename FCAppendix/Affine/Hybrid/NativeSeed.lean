import FCAppendix.Affine.Hybrid.CategoryFibers

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

def bidBlockSplit (p : ι → Prop) [DecidablePred p] (n : ℕ)
    (e : Fin (n+1) ≃ Subtype p) (bid : X → ℝ) (x : ι → X) :
    (Fin (n+1) → ℝ) × ({i : ι // ¬p i} → X) :=
  (fun j => bid (x (e j)),fun i => x i)

omit [Fintype ι] in
lemma measurable_bidBlockSplit (p : ι → Prop) [DecidablePred p] (n : ℕ)
    (e : Fin (n+1) ≃ Subtype p) (bid : X → ℝ) (hb : Measurable bid) :
    Measurable (bidBlockSplit p n e bid) :=
  (measurable_pi_lambda _ (fun j => hb.comp (measurable_pi_apply ((e j):ι)))).prodMk
    (measurable_pi_lambda _ (fun i : {i : ι // ¬p i} => measurable_pi_apply (i:ι)))

theorem bidBlockSplit_law (ν : ι → Measure X) [∀ i, IsProbabilityMeasure (ν i)]
    (p : ι → Prop) [DecidablePred p] (n : ℕ) (e : Fin (n+1) ≃ Subtype p)
    (bid : X → ℝ) (hb : Measurable bid) (μB : Measure ℝ) [IsProbabilityMeasure μB]
    (hbid : ∀ j, (ν (e j)).map bid = μB) :
    (Measure.pi ν).map (bidBlockSplit p n e bid) =
      (lowVectorLaw μB n).prod (Measure.pi fun i : {i : ι // ¬p i} => ν i) := by
  let f : (Subtype p → X) → (Fin (n+1) → ℝ) := fun x j => bid (x (e j))
  have hf : Measurable f := measurable_pi_lambda _
    (fun j => hb.comp (measurable_pi_apply (e j)))
  have hreindex :
      (Measure.pi (fun i : Subtype p => ν i)).map
        (fun x : Subtype p → X => fun j : Fin (n+1) => x (e j)) =
        Measure.pi (fun j : Fin (n+1) => ν (e j)) := by
    have h := (measurePreserving_piCongrLeft
      (fun j : Fin (n+1) => ν (e j)) e.symm).map_eq
    simp only [Equiv.apply_symm_apply] at h
    convert h using 1
    congr 1
    funext x j
    simp [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft']
  have hr : Measurable (fun x : Subtype p → X => fun j : Fin (n+1) => x (e j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (e j))
  have hc : Measurable (fun x : Fin (n+1) → X => fun j => bid (x j)) :=
    measurable_pi_lambda _ (fun j => hb.comp (measurable_pi_apply j))
  have hfLaw : (Measure.pi (fun i : Subtype p => ν i)).map f = lowVectorLaw μB n := by
    calc
      _ = ((Measure.pi (fun i : Subtype p => ν i)).map
          (fun x : Subtype p → X => fun j : Fin (n+1) => x (e j))).map
          (fun x : Fin (n+1) → X => fun j => bid (x j)) :=
        (Measure.map_map hc hr).symm
      _ = _ := by
        rw [hreindex,Measure.pi_map_pi (fun _ => hb.aemeasurable)]
        simp only [hbid,lowVectorLaw]
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) p
  have hsplit := (measurePreserving_piEquivPiSubtypeProd ν p).map_eq
  calc
    _ = ((Measure.pi ν).map E).map (Prod.map f id) := by
      rw [Measure.map_map (hf.prodMap measurable_id) E.measurable]
      rfl
    _ = ((Measure.pi (fun i : Subtype p => ν i)).prod
        (Measure.pi fun i : {i : ι // ¬p i} => ν i)).map (Prod.map f id) := by rw [hsplit]
    _ = _ := by
      rw [←Measure.map_prod_map _ _ hf measurable_id,hfLaw,Measure.map_id]

variable {K Y : Type*} [MeasurableSpace K] [MeasurableSingletonClass K]
  [DecidableEq K] [MeasurableSpace Y]

theorem conditional_low_seed_joint (μ : Measure X) [IsProbabilityMeasure μ]
    (tag : X → K) (htag : Measurable tag) (k : ι → K) (low : K)
    (hmass : ∀ i, μ (tag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : ι // k i=low})
    (bid : X → ℝ) (hb : Measurable bid)
    (hnoatoms : ∀ b : ℝ, ((cond μ (tag ⁻¹' {low})).map bid) {b}=0)
    (ω : Measure Y) [IsProbabilityMeasure ω] :
    ((cond (Measure.pi (fun _ : ι => μ)) (categoryFiber tag k)).prod ω).map
      (fun x => (conditionalMinimumSeed ((cond μ (tag ⁻¹' {low})).map bid) n
          (fun j => bid (x.1 (e j))),
        ((fun i : {i : ι // k i≠low} => x.1 i),x.2))) =
      (volume : Measure unitInterval).prod
        ((Measure.pi (fun i : {i : ι // k i≠low} => cond μ (tag ⁻¹' {k i}))).prod ω) := by
  let ν : ι → Measure X := fun i => cond μ (tag ⁻¹' {k i})
  letI (i : ι) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hmass i)
  have hlow : μ (tag ⁻¹' {low}) ≠ 0 := by
    have h := hmass (e 0)
    simpa only [(e 0).property] using h
  letI : IsProbabilityMeasure (cond μ (tag ⁻¹' {low})) := cond_isProbabilityMeasure hlow
  let μB := (cond μ (tag ⁻¹' {low})).map bid
  letI : IsProbabilityMeasure μB := Measure.isProbabilityMeasure_map hb.aemeasurable
  have hbid (j : Fin (n+1)) : (ν (e j)).map bid = μB := by
    simp only [ν,(e j).property,μB]
  have hsplit := bidBlockSplit_law ν (fun i => k i=low) n e bid hb μB hbid
  let rest := Measure.pi (fun i : {i : ι // k i≠low} => ν i)
  let split : (ι → X) × Y → (Fin (n+1) → ℝ) × (({i : ι // k i≠low} → X) × Y) :=
    fun x => ((bidBlockSplit (fun i => k i=low) n e bid x.1).1,
      ((bidBlockSplit (fun i => k i=low) n e bid x.1).2,x.2))
  have hsplitMeas : Measurable split :=
    (((measurable_bidBlockSplit (fun i => k i=low) n e bid hb).comp measurable_fst).fst).prodMk
      ((((measurable_bidBlockSplit (fun i => k i=low) n e bid hb).comp measurable_fst).snd).prodMk
        measurable_snd)
  have hsplitJoint : ((Measure.pi ν).prod ω).map split = (lowVectorLaw μB n).prod (rest.prod ω) := by
    have h := Measure.map_prod_map (Measure.pi ν) ω
      (measurable_bidBlockSplit (fun i => k i=low) n e bid hb) measurable_id
    have hassoc := (measurePreserving_prodAssoc (lowVectorLaw μB n) rest ω).map_eq
    calc
      _ = (((Measure.pi ν).prod ω).map
          (Prod.map (bidBlockSplit (fun i => k i=low) n e bid) id)).map
          MeasurableEquiv.prodAssoc := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable
          ((measurable_bidBlockSplit (fun i => k i=low) n e bid hb).prodMap measurable_id)]
        rfl
      _ = _ := by rw [←h,hsplit,Measure.map_id]; exact hassoc
  rw [conditional_categoryFiber μ tag htag k]
  change ((Measure.pi ν).prod ω).map
    ((fun z : (Fin (n+1) → ℝ) × (({i : ι // k i≠low} → X) × Y) =>
      (conditionalMinimumSeed μB n z.1,z.2)) ∘ split) = _
  calc
    _ = (((Measure.pi ν).prod ω).map split).map
        (Prod.map (conditionalMinimumSeed μB n) id) :=
      (Measure.map_map ((measurable_conditionalMinimumSeed μB n).prodMap measurable_id) hsplitMeas).symm
    _ = _ := by
      rw [hsplitJoint]
      exact conditionalMinimumSeed_joint μB hnoatoms n (rest.prod ω)

lemma cond_prod_left {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (S : Set A) : cond (μ.prod ν) (S ×ˢ Set.univ) = (cond μ S).prod ν := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod,measure_univ,mul_one,←Measure.restrict_prod_eq_prod_univ,
    Measure.prod_smul_left]

theorem native_background_minimum_seed {m c : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (Γ : Bayes.FiniteGame m 2 c Seed)
    (tag : Bayes.UserDraw 2 → K) (htag : Measurable tag)
    (k : Fin m → K) (low : K)
    (hmass : ∀ i, Bayes.userLaw Γ (tag ⁻¹' {k i}) ≠ 0)
    (n : ℕ) (e : Fin (n+1) ≃ {i : Fin m // k i=low})
    (hnoatoms : ∀ b : ℝ,
      ((cond (Bayes.userLaw Γ) (tag ⁻¹' {low})).map
        (fun d : Bayes.UserDraw 2 => d.1.2.bid)) {b}=0) :
    (cond (Bayes.backgroundLaw Γ) ((categoryFiber tag k) ×ˢ Set.univ)).map
      (fun x => (conditionalMinimumSeed
          ((cond (Bayes.userLaw Γ) (tag ⁻¹' {low})).map
            (fun d : Bayes.UserDraw 2 => d.1.2.bid)) n
          (fun j => (x.1 (e j)).1.2.bid),
        ((fun i : {i : Fin m // k i≠low} => x.1 i),x.2))) =
      (volume : Measure unitInterval).prod
        ((Measure.pi (fun i : {i : Fin m // k i≠low} =>
          cond (Bayes.userLaw Γ) (tag ⁻¹' {k i}))).prod
            (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))) := by
  rw [Bayes.backgroundLaw,cond_prod_left]
  exact conditional_low_seed_joint (Bayes.userLaw Γ) tag htag k low hmass n e
    (fun d : Bayes.UserDraw 2 => d.1.2.bid)
    ((Game.measurable_bid 2).comp measurable_fst.snd) hnoatoms _

end FCAppendix.Affine.Hybrid
