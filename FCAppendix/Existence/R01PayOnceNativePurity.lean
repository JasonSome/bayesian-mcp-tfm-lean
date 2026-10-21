import FCAppendix.Existence.R01PayOncePhysicalService

noncomputable section
namespace FCAppendix.Bayes.PayOnceConstruction
open MeasureTheory ProbabilityTheory Game Set Filter
open Existence.PayOnceBounded

theorem mixedGame_physical_monotone_purity {W : ℝ} (hW : 0<W)
    (N n c : ℕ) (hn : 2≤n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ) (hg : 0≤g) (hbounded : ∀ᵐv ∂F,max 0 (v-g)≤W)
    (π : ProbabilityMeasure (Value W × FloorAction 0 W))
    (σ : Kernel (Value W) (FloorAction 0 W)) [IsMarkovKernel σ]
    (hIC : ∀ᵐw ∂physicalNetLaw W g hW.le F,∀ᵐa ∂σ w,∀a' : FloorAction 0 W,
      positivePayoff N n c π (w,a')≤positivePayoff N n c π (w,a))
    (hpositive : ∀ᵐw ∂physicalNetLaw W g hW.le F,∀ᵐa ∂σ w,0<w.1→0<bid a)
    (hservice : ∀ᵐw ∂physicalNetLaw W g hW.le F,∀ᵐa ∂σ w,0<w.1→0<positiveQ N n c π a)
    (hatom : ∀v,g<v→F {v}=0) :
    ∃ (b : ℝ→ℝ) (hb : ∀v,0≤b v),Measurable b ∧ Monotone b ∧
      (∀ᵐv ∂F,g<v→
        (mixedGame (N+1) n c hn F (physicalKernel W g hW.le σ) (Schedule.once n) g hg).σ v=
          Measure.dirac (fullBid n (b v) (hb v))) := by
  obtain ⟨b,hbmeas,hbmono,hbbound,hpure⟩ := actual_bounded_monotone_bid_representative
    hW.le N n c hn (physicalNetLaw W g hW.le F)
    (physicalNetLaw_positive_atomless W g hW F hbounded hatom) π σ hIC hpositive hservice
  let B : ℝ→ℝ := fun v=>b (v-g)
  have hB : ∀v,0≤B v := fun v=>(hbbound (v-g)).1
  refine ⟨B,hB,hbmeas.comp (measurable_id.sub measurable_const),?_,?_⟩
  · intro v v' h
    exact hbmono (sub_le_sub_right h g)
  · have hphys := ae_of_ae_map (continuous_physicalNetType W g hW.le).measurable.aemeasurable hpure
    filter_upwards [hphys,hbounded] with v hv hvbound
    intro hvpos
    have hnet := physicalNetType_eq_sub_of_positive W g hW.le v hvpos hvbound
    obtain ⟨bp,hbid,hdir,hbest⟩ := hv (by rw [hnet]; exact sub_pos.mpr hvpos)
    have hBv : B v=bp.1 := by change b (v-g)=bp.1; rw [←hnet]; exact hbid
    change ((physicalKernel W g hW.le σ).map (nativeAction n)) v=_
    rw [Kernel.map_apply _ (measurable_nativeAction n W)]
    change (σ (physicalNetType W g hW.le v)).map (nativeAction n)=_
    rw [hdir,Measure.map_dirac' (measurable_nativeAction n W)]
    apply congrArg Measure.dirac
    change (⟨bp.1,bp.2.1.le,n,le_rfl⟩ : JointAction n)=⟨B v,hB v,n,le_rfl⟩
    congr 1
    exact hBv.symm

end FCAppendix.Bayes.PayOnceConstruction
