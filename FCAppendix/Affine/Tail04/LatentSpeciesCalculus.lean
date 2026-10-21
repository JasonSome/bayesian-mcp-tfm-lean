import FCAppendix.Affine.Tail04.LatentNoisyPopulation

noncomputable section
namespace FCAppendix.Affine.Tail04.LatentSpeciesCalculus
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint NativeNoisySource LatentNoisyPopulation
open OriginalFiniteFibers
open scoped BigOperators

lemma restrict_mapped {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (hf : Measurable f)
    (S : Set Y) (hS : MeasurableSet S) :
    (μ.map f).restrict S=(μ.restrict (f ⁻¹' S)).map f := by
  ext B hB
  rw [Measure.restrict_apply hB,Measure.map_apply hf (hB.inter hS),
    Measure.map_apply hf hB,Measure.restrict_apply (hB.preimage hf)]
  rfl

abbrev ComponentDraw := ((ℝ×JointAction 2)×unitInterval)×Equiv.Perm (Fin 2)

def mark (r : Fin 5) (z : ComponentDraw) : Draw := (((r,z.1.1),z.1.2),z.2)

lemma measurable_mark (r : Fin 5) : Measurable (mark r) :=
  ((measurable_const.prodMk measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd

def label (z : Draw) : Fin 5 := z.1.1.1
def baseBid (z : Draw) : ℝ := z.1.1.2.2.bid
def value (z : Draw) : ℝ := z.1.1.2.1

lemma measurable_label : Measurable label := measurable_fst.fst.fst
lemma measurable_baseBid : Measurable baseBid :=
  (measurable_bid 2).comp measurable_fst.fst.snd.snd
lemma measurable_value : Measurable value := measurable_fst.fst.snd.fst

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)

def componentDrawLaw (r : Fin 5) : Measure ComponentDraw :=
  ((baseComponent D P t ht πL π upperBid hupperBid r : Measure _).prod
    (volume : Measure unitInterval)).prod (permLaw 2)

instance componentDrawLaw_probability (r : Fin 5) :
    IsProbabilityMeasure (componentDrawLaw D P t ht πL π upperBid hupperBid r) := by
  unfold componentDrawLaw
  infer_instance

theorem drawLaw_species_sum :
    drawLaw D P t ht πL π upperBid hupperBid=
      ∑ r,ENNReal.ofReal ((species P t ht).mass r) •
        (componentDrawLaw D P t ht πL π upperBid hupperBid r).map (mark r) := by
  change (((∑ r,ENNReal.ofReal ((species P t ht).mass r) •
    (taggedComponent D P t ht πL π upperBid hupperBid r : Measure Tagged)).prod
      (volume : Measure unitInterval)).prod (permLaw 2))=_
  rw [prod_finsetSum,prod_finsetSum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Measure.prod_smul_left,Measure.prod_smul_left]
  congr 1
  unfold taggedComponent componentDrawLaw
  let μ : Measure (ℝ×JointAction 2) :=
    (baseComponent D P t ht πL π upperBid hupperBid r : Measure (ℝ×JointAction 2))
  let f : ℝ×JointAction 2→Tagged := fun x => (r,x)
  have hf : Measurable f := measurable_const.prodMk measurable_id
  change ((μ.map f).prod (volume : Measure unitInterval)).prod (permLaw 2)=
    ((μ.prod (volume : Measure unitInterval)).prod (permLaw 2)).map (mark r)
  have h0 : (μ.map f).prod (volume : Measure unitInterval)=
      (μ.prod volume).map (Prod.map f id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map μ volume hf measurable_id
  rw [h0]
  simpa only [Measure.map_id] using!
    Measure.map_prod_map (μ.prod (volume : Measure unitInterval)) (permLaw 2)
      (hf.prodMap measurable_id) measurable_id

lemma restrict_mark (r s : Fin 5) (μ : Measure ComponentDraw) :
    (μ.map (mark r)).restrict {z | label z=s}=
      if r=s then μ.map (mark r) else 0 := by
  rw [restrict_mapped μ (mark r) (measurable_mark r) _
    (measurableSet_eq_fun measurable_label measurable_const)]
  by_cases h : r=s
  · simp only [h,mark,label,preimage_setOf_eq,Set.setOf_true,Measure.restrict_univ,ite_true]
  · simp only [mark,label,h,preimage_setOf_eq,Set.setOf_false,Measure.restrict_empty,
      Measure.map_zero,ite_false]

theorem drawLaw_restrict_label (r : Fin 5) :
    (drawLaw D P t ht πL π upperBid hupperBid).restrict {z | label z=r}=
      ENNReal.ofReal ((species P t ht).mass r) •
        (componentDrawLaw D P t ht πL π upperBid hupperBid r).map (mark r) := by
  rw [drawLaw_species_sum]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,add_zero,
    Measure.restrict_add,Measure.restrict_smul,restrict_mark]
  fin_cases r <;> simp

def bandSpecies : Fin 3 → Fin 5 := ![2,3,1]
def bandRoutes : Fin 3 → ℕ := ![2,2,1]

lemma bandRoutes_le (i : Fin 3) : bandRoutes i≤2 := by fin_cases i <;> norm_num [bandRoutes]

def bandBase (i : Fin 3)
    (x : Icc (valueLo P i) (valueHi P t i)×Icc (bidLo D i) (bidHi D i)) : ℝ×JointAction 2 :=
  ((x.1:ℝ),bandAction (bidLo_pos D i).le (bandRoutes i) (bandRoutes_le i) x.2)

lemma measurable_bandBase (i : Fin 3) : Measurable (bandBase D P t i) :=
  measurable_fst.subtype_val.prodMk
    ((measurable_bandAction (bidLo_pos D i).le (bandRoutes i) (bandRoutes_le i)).comp measurable_snd)

abbrev BandDraw (i : Fin 3) :=
  ((Icc (valueLo P i) (valueHi P t i)×Icc (bidLo D i) (bidHi D i))×unitInterval)×Equiv.Perm (Fin 2)

def bandDraw (i : Fin 3) (z : BandDraw D P t i) : Draw :=
  mark (bandSpecies i) ((bandBase D P t i z.1.1,z.1.2),z.2)

lemma measurable_bandDraw (i : Fin 3) : Measurable (bandDraw D P t i) :=
  (measurable_mark (bandSpecies i)).comp
    (((measurable_bandBase D P t i).prodMap measurable_id).prodMap measurable_id)

def bandDrawLaw (i : Fin 3) : Measure (BandDraw D P t i) :=
  (((π i).1 : Measure _).prod (volume : Measure unitInterval)).prod (permLaw 2)

instance bandDrawLaw_probability (i : Fin 3) :
    IsProbabilityMeasure (bandDrawLaw D P t ht π i) := by unfold bandDrawLaw;infer_instance

lemma component_band (i : Fin 3) :
    (componentDrawLaw D P t ht πL π upperBid hupperBid (bandSpecies i)).map (mark (bandSpecies i))=
      (bandDrawLaw D P t ht π i).map (bandDraw D P t i) := by
  have hbase : (baseComponent D P t ht πL π upperBid hupperBid (bandSpecies i) : Measure _)=
      ((π i).1 : Measure _).map (bandBase D P t i) := by
    fin_cases i <;> rfl
  unfold componentDrawLaw bandDrawLaw
  rw [hbase]
  rw [show (((π i).1 : Measure _).map (bandBase D P t i)).prod volume=
      (((π i).1 : Measure _).prod volume).map (Prod.map (bandBase D P t i) id) by
        simpa only [Measure.map_id] using
          Measure.map_prod_map _ _ (measurable_bandBase D P t i) measurable_id]
  rw [show ((((π i).1 : Measure _).prod volume).map (Prod.map (bandBase D P t i) id)).prod
      (permLaw 2)=((((π i).1 : Measure _).prod volume).prod (permLaw 2)).map
        (Prod.map (Prod.map (bandBase D P t i) id) id) by
          simpa only [Measure.map_id] using Measure.map_prod_map _ _
            ((measurable_bandBase D P t i).prodMap measurable_id) measurable_id]
  rw [Measure.map_map (measurable_mark (bandSpecies i))
    (((measurable_bandBase D P t i).prodMap measurable_id).prodMap measurable_id)]
  rfl

def bandCluster (i : Fin 3) (J : Set ℝ) : Set Draw :=
  {z | label z=bandSpecies i ∧ baseBid z∈J}

lemma measurableSet_bandCluster (i : Fin 3) (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (bandCluster i J) :=
  (measurableSet_eq_fun measurable_label measurable_const).inter (hJ.preimage measurable_baseBid)

def typedCluster (i : Fin 3) (J : Set ℝ) :
    Set (Icc (valueLo P i) (valueHi P t i)×Icc (bidLo D i) (bidHi D i)) :=
  {x | (x.2:ℝ)∈J}

lemma measurableSet_typedCluster (i : Fin 3) (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (typedCluster D P t i J) := hJ.preimage measurable_snd.subtype_val

theorem drawLaw_restrict_bandCluster (i : Fin 3) (J : Set ℝ) (hJ : MeasurableSet J) :
    (drawLaw D P t ht πL π upperBid hupperBid).restrict (bandCluster i J)=
      ENNReal.ofReal ((species P t ht).mass (bandSpecies i)) •
        (((((π i).1 : Measure _).restrict (typedCluster D P t i J)).prod
          (volume : Measure unitInterval)).prod (permLaw 2)).map (bandDraw D P t i) := by
  have hlabel : MeasurableSet {z : Draw | label z=bandSpecies i} :=
    measurableSet_eq_fun measurable_label measurable_const
  have hbid : MeasurableSet {z : Draw | baseBid z∈J} := hJ.preimage measurable_baseBid
  change (drawLaw D P t ht πL π upperBid hupperBid).restrict
    ({z | label z=bandSpecies i}∩{z | baseBid z∈J})=_
  rw [Set.inter_comm,←Measure.restrict_restrict hbid,drawLaw_restrict_label,
    Measure.restrict_smul,component_band]
  rw [restrict_mapped _ _ (measurable_bandDraw D P t i) _ hbid]
  have hp : bandDraw D P t i ⁻¹' {z | baseBid z∈J}=
      ((typedCluster D P t i J)×ˢ univ)×ˢ univ := by
    ext z
    simp only [bandDraw,mark,baseBid,bandBase,bandAction,typedCluster,mem_preimage,
      mem_setOf_eq,mem_prod,mem_univ,and_true]
  rw [hp,bandDrawLaw,←Measure.restrict_prod_eq_prod_univ,
    ←Measure.restrict_prod_eq_prod_univ]

theorem original_band_cluster_mass (i : Fin 3) (J : Set ℝ) (hJ : MeasurableSet J) :
    (drawLaw D P t ht πL π upperBid hupperBid).real (bandCluster i J)=
      (species P t ht).mass (bandSpecies i)*
        ((π i).1 : Measure _).real (typedCluster D P t i J) := by
  have h := congrArg (fun μ : Measure Draw => μ univ)
    (drawLaw_restrict_bandCluster D P t ht πL π upperBid hupperBid i J hJ)
  rw [Measure.restrict_apply MeasurableSet.univ,univ_inter,Measure.smul_apply,
    Measure.map_apply (measurable_bandDraw D P t i) MeasurableSet.univ,preimage_univ] at h
  have hvolume : (volume : Measure unitInterval) univ=1 := by simp
  have hperm : permLaw 2 univ=1 := measure_univ
  simp only [←univ_prod_univ,Measure.prod_prod] at h
  simp only [univ_prod_univ,hvolume,hperm,mul_one,
    Measure.restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul] at h
  exact congrArg ENNReal.toReal h |>.trans (by
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal ((species P t ht).nonneg (bandSpecies i))]
    rfl)

theorem original_band_cluster_recipient_mass (i : Fin 3) (J : Set ℝ) (hJ : MeasurableSet J)
    (j : Fin 2) :
    (drawLaw D P t ht πL π upperBid hupperBid).real
      {z | z∈bandCluster i J ∧ j∈firstK z.2 1}=
      (species P t ht).mass (bandSpecies i)*
        ((π i).1 : Measure _).real (typedCluster D P t i J)/2 := by
  let S : Set Draw := {z | j∈firstK z.2 1}
  have hS : MeasurableSet S :=
    (show MeasurableSet {τ : Equiv.Perm (Fin 2) | j∈firstK τ 1} from
      MeasurableSet.of_discrete).preimage measurable_snd
  have h := congrArg (fun μ : Measure Draw => μ S)
    (drawLaw_restrict_bandCluster D P t ht πL π upperBid hupperBid i J hJ)
  rw [Measure.restrict_apply hS,Measure.smul_apply,
    Measure.map_apply (measurable_bandDraw D P t i) hS] at h
  have hp : bandDraw D P t i ⁻¹' S=univ×ˢ {τ | j∈firstK τ 1} := by ext z;simp [S,bandDraw,mark]
  have hvolume : (volume : Measure unitInterval) univ=1 := by simp
  rw [hp,Measure.prod_prod,←univ_prod_univ,Measure.prod_prod,hvolume,mul_one,
    Measure.restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul] at h
  have hh := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ((species P t ht).nonneg (bandSpecies i))] at hh
  have hf := permLaw_mem_firstK 2 1 (by norm_num) (by norm_num) j
  simp only [measureReal_def,Nat.cast_one,Nat.cast_ofNat] at hf
  rw [hf] at hh
  have hs : S∩bandCluster i J={z | z∈bandCluster i J ∧ j∈firstK z.2 1} := by
    ext z;simp only [S,mem_inter_iff,mem_setOf_eq,and_comm]
  simpa only [hs,measureReal_def,div_eq_mul_inv,mul_assoc,one_mul] using hh

end FCAppendix.Affine.Tail04.LatentSpeciesCalculus
