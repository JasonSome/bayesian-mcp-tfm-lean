import FCAppendix.Affine.Hybrid.Finishing01MenusFullRow

noncomputable section
namespace FCAppendix.Affine.Hybrid.Finishing01Menus
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

variable {N : ℕ}

theorem measurePreserving_row_map {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
    (N : ℕ) (μ : ProbabilityMeasure X) (f : X→ℝ) (hf : Measurable f) :
    MeasurePreserving (fun x : Fin N→ X => fun j => f (x j))
      (rowLaw N μ : Measure (Fin N→ X))
      (Measure.pi (fun _ : Fin N => (μ:Measure X).map f)) := by
  refine ⟨measurable_pi_lambda _ (fun j => hf.comp (measurable_pi_apply j)),?_⟩
  rw [LowBody.rowLaw_eq_measure_pi]
  exact Measure.pi_map_pi (fun _ : Fin N => hf.aemeasurable)

theorem patternInterim_map {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [CompactSpace X]
    [TopologicalSpace.MetrizableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [BorelSpace Y]
    {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (z L U : ℝ) (c : ℕ) (kind : Fin N→ Fin 4)
    (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y)
    (f : X→ℝ) (g : Y→ℝ) (hf : Measurable f) (hg : Measurable g)
    (v b : ℝ) :
    patternInterim ξ z L U c kind ((μ:Measure X).map f) ((ν:Measure Y).map g) v b=
      ∫xy : (Fin N→ X)×(Fin N→ Y),
        activePhysicalPatternPayoff ξ z L U c kind
          (v,b,(fun j => f (xy.1 j)),fun j => g (xy.2 j))
        ∂(rowLaw N μ : Measure (Fin N→ X)).prod (rowLaw N ν : Measure (Fin N→ Y)) := by
  have hp := (measurePreserving_row_map N μ f hf).prod
    (measurePreserving_row_map N ν g hg)
  have hm : Measurable (fun xy : (Fin N→ℝ)×(Fin N→ℝ) =>
      activePhysicalPatternPayoff ξ z L U c kind (v,b,xy)) :=
    (measurable_activePhysicalPatternPayoff hξ hξ1 z L U c kind).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hi := integral_map
    (μ:=(rowLaw N μ : Measure (Fin N→ X)).prod (rowLaw N ν : Measure (Fin N→ Y)))
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi

variable (P : Finish01.Primitives)

def lowReal (low : ProbabilityMeasure P.Low) : Measure ℝ :=
  (low:Measure P.Low).map Subtype.val

def baseReal (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : Measure ℝ :=
  ((pi.1.map measurable_snd.aemeasurable : ProbabilityMeasure P.Bid):Measure P.Bid).map Subtype.val

def implementedReal {ε : ℝ} (hε : 0≤ε)
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : Measure ℝ :=
  (activeImplementedBidLaw P.L_pos hε mu pi : Measure (ActivePhysicalBid P.L P.U ε)).map Subtype.val

instance lowReal_isProbability (low : ProbabilityMeasure P.Low) :
    IsProbabilityMeasure (lowReal P low) := Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

instance baseReal_isProbability (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : IsProbabilityMeasure (baseReal P mu pi) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

instance implementedReal_isProbability {ε : ℝ} (hε : 0≤ε)
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : IsProbabilityMeasure (implementedReal P hε mu pi) :=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

theorem baseReal_box (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) : ∀ᵐb∂baseReal P mu pi,b∈ Icc P.L P.U := by
  exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
    (ae_of_all _ Subtype.property)

theorem implementedReal_box {ε : ℝ} (hε : 0≤ε)
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) :
    ∀ᵐb∂implementedReal P hε mu pi,b∈ Icc P.L (P.U*(1+ε)) := by
  exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
    (ae_of_all _ Subtype.property)

theorem exactUtility_eq_actualRowInterim (N c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (t : P.Value×P.Bid) :
    P.exactUtility N c low mu pi t=
      actualRowInterim (N:=N) P.xi P.z P.L P.U c P.categories
        (lowReal P low) (baseReal P mu pi) t.1 t.2 := by
  unfold Finish01.Primitives.exactUtility actualRowInterim FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  exact (patternInterim_map P.xi_pos P.xi_lt_one P.z P.L P.U c kind
    low (pi.1.map measurable_snd.aemeasurable) Subtype.val Subtype.val
    measurable_subtype_coe measurable_subtype_coe t.1 t.2).symm

theorem noisyExpectedUtility_eq_actualRow_noise {ε : ℝ} (hε : 0≤ε)
    (c : ℕ) (low : ProbabilityMeasure P.Low)
    (mu : Measure P.Value) [IsProbabilityMeasure mu]
    (pi : Law (A:=P.Bid) mu) (v : P.Value) (b : P.Bid) :
    activeNoisyExpectedUtility (N:=N) P.L_pos hε P.xi P.z c P.categories low mu (pi,(v,b))=
      ∫z : unitInterval,
        actualRowInterim (N:=N) P.xi P.z P.L (P.U*(1+ε)) c P.categories
          (lowReal P low) (implementedReal P hε mu pi) v (activeNoisyRealBid ε b z) := by
  let G := activeImplementedBidLaw P.L_pos hε mu pi
  let Q := productLaw (rowLaw N low) (rowLaw N G)
  let f (kind : Fin N→ Fin 4)
      (tz : ((Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε))×unitInterval) : ℝ :=
    activePhysicalPatternPayoff P.xi P.z P.L (P.U*(1+ε)) c kind
      (v,activeNoisyRealBid ε b tz.2,
        (fun j => (tz.1.1 j:ℝ)),fun j => (tz.1.2 j:ℝ))
  have hm (kind : Fin N→ Fin 4) : Measurable (f kind) := by
    apply (measurable_activePhysicalPatternPayoff P.xi_pos P.xi_lt_one
      P.z P.L (P.U*(1+ε)) c kind).comp
    dsimp [f,activeNoisyRealBid]
    fun_prop
  have hi (kind : Fin N→ Fin 4) : Integrable (f kind)
      ((Q:Measure ((Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε))).prod volume) := by
    apply Integrable.of_bound (hm kind).aestronglyMeasurable (|(v:ℝ)|+3*(P.U*(1+ε)))
    filter_upwards [] with tz
    rw [Real.norm_eq_abs]
    exact abs_physicalPatternPayoff_le P.xi_pos P.xi_lt_one P.L_pos
      P.z c kind v (activeNoisyRealBid ε b tz.2)
      (fun j => (tz.1.1 j:ℝ)) (fun j => (tz.1.2 j:ℝ))
      (activeNoisyRealBid_mem P.L_pos hε b tz.2) (fun j => (tz.1.2 j).property)
  have hp (kind : Fin N→ Fin 4) (z : unitInterval) :
      (∫r, f kind (r,z) ∂(Q:Measure ((Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε))))=
        patternInterim P.xi P.z P.L (P.U*(1+ε)) c kind
          (lowReal P low) (implementedReal P hε mu pi) v (activeNoisyRealBid ε b z) := by
    exact (patternInterim_map P.xi_pos P.xi_lt_one P.z P.L (P.U*(1+ε)) c kind
      low G Subtype.val Subtype.val measurable_subtype_coe measurable_subtype_coe
      v (activeNoisyRealBid ε b z)).symm
  have hpat (kind : Fin N→ Fin 4) :
      (∫r,activePatternSmoothedPayoff P.L_pos hε P.xi P.z c kind ((v,b),r)
        ∂(Q:Measure ((Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε))))=
        ∫z : unitInterval,patternInterim P.xi P.z P.L (P.U*(1+ε)) c kind
          (lowReal P low) (implementedReal P hε mu pi) v (activeNoisyRealBid ε b z) := by
    have heq (r : (Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε)) :
        activePatternSmoothedPayoff P.L_pos hε P.xi P.z c kind ((v,b),r)=
          ∫z : unitInterval,f kind (r,z) := by
      rw [activePatternSmoothedPayoff_eq_integral]
      apply integral_congr_ae
      filter_upwards [] with z
      exact activePatternNoisyPayoff_eq_physical P.L_pos hε P.xi P.z c kind ((v,b),r) z
    simp_rw [heq]
    rw [integral_integral_swap (hi kind)]
    simp_rw [hp]
  have hiz (kind : Fin N→ Fin 4) : Integrable
      (fun z : unitInterval => patternInterim P.xi P.z P.L (P.U*(1+ε)) c kind
        (lowReal P low) (implementedReal P hε mu pi) v (activeNoisyRealBid ε b z)) volume := by
    have hh := (hi kind).swap.integral_prod_left
    simpa only [Function.comp_def,Prod.swap_prod_mk,hp] using hh
  change (∑kind : Fin N→ Fin 4,(CommonList.iid P.categories N).mass kind*
    ∫r,activePatternSmoothedPayoff P.L_pos hε P.xi P.z c kind ((v,b),r)
      ∂(Q:Measure ((Fin N→ P.Low)×(Fin N→ ActivePhysicalBid P.L P.U ε))))=
    ∫z : unitInterval,∑kind : Fin N→ Fin 4,(CommonList.iid P.categories N).mass kind*
      patternInterim P.xi P.z P.L (P.U*(1+ε)) c kind
        (lowReal P low) (implementedReal P hε mu pi) v (activeNoisyRealBid ε b z)
  rw [integral_finsetSum _ (fun kind _ => (hiz kind).const_mul _)]
  apply Finset.sum_congr rfl
  intro kind _
  rw [hpat,integral_const_mul]

end FCAppendix.Affine.Hybrid.Finishing01Menus
