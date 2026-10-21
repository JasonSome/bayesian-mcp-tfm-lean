import FCAppendix.Affine.Hybrid.Native02.SourceResponse
import FCAppendix.Affine.Hybrid.Native02.NativeSourceIC

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional

namespace PrimitiveInput
variable (p : PrimitiveInput)

theorem reciprocalMean_bidReal_eq (pi : Law (A:=p.Bid) (p.activeValues : Measure p.Value)) :
    reciprocalMean (p.bidReal pi)=
      ∫x : p.Value×p.Bid,(x.2.1)⁻¹ ∂(pi.1 : Measure (p.Value×p.Bid)) := by
  unfold reciprocalMean bidReal
  rw [Measure.map_map measurable_subtype_coe measurable_snd]
  rw [integral_map (measurable_subtype_coe.comp measurable_snd).aemeasurable
    measurable_inv.aestronglyMeasurable]
  rfl

end PrimitiveInput

namespace FrozenActiveFamily
variable (p : PrimitiveInput)

def of_compact_numeric
    (start : ℕ) (low : ℕ→ ProbabilityMeasure p.Low)
    (joint : ℕ→ Law (A:=p.Bid) (p.activeValues : Measure p.Value))
    (hlow : ∀ m≥ start,∃W : LowBody.ActualAtomlessLowLimit (m-1) p.d p.xi
      (p.capacity m) p.categories (p.lowValues : Measure p.Low),
        low m=W.joint.1.map measurable_snd.aemeasurable)
    (hatom : ∀ m≥ start,NullSingletonClass
      ((joint m).1.map measurable_snd.aemeasurable : Measure p.Bid))
    (hIC : ∀ m≥ start,∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),∀ b : p.Bid,
      p.compactSourceUtility (m-1) (p.capacity m) (low m) (joint m) (x.1,b)≤
        p.compactSourceUtility (m-1) (p.capacity m) (low m) (joint m) x)
    (hprice : Tendsto (fun m=> p.h0/
      (∫x : p.Value×p.Bid,(x.2.1)⁻¹ ∂((joint m).1 : Measure (p.Value×p.Bid))))
      atTop (𝓝 p.lam))
    (hgraph : ∀ eps>0,∀ᶠm in atTop,
      ∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),|x.2.1-p.beta x.1|< eps) :
    FrozenActiveFamily p where
  start := start
  low := low
  joint := joint
  low_witness := hlow
  atomless := hatom
  numeric_IC := fun m hm => p.compact_source_IC_to_physical (m-1) (p.capacity m)
    (low m) (joint m) (hIC m hm)
  price_limit := by simpa only [p.reciprocalMean_bidReal_eq] using hprice
  supported_graph := hgraph
  response_measurable := p.source_response_measurable
  response_boxed := p.source_response_boxed

def of_inversePhi_numeric
    (q01 : ℝ→ℝ→ℝ)
    (hphi : ∀(v : p.Value)(lam : ℝ),lam∈ Icc (p.h0*p.L) (p.h0*p.U)→
      q01 v.1 lam∈ Icc (0:ℝ) 1 ∧ phi p.xi p.z (q01 v.1 lam)=lam/v.1)
    (lam01 : ℝ)
    (hunique : ∀ lam',lam'∈ Icc (p.h0*p.L) (p.h0*p.U)→
      (∫v : p.Value,q01 v.1 lam' ∂(p.activeValues : Measure p.Value))=p.qbar→ lam'=lam01)
    (start : ℕ) (low : ℕ→ ProbabilityMeasure p.Low)
    (joint : ℕ→ Law (A:=p.Bid) (p.activeValues : Measure p.Value))
    (hlow : ∀ m≥ start,∃W : LowBody.ActualAtomlessLowLimit (m-1) p.d p.xi
      (p.capacity m) p.categories (p.lowValues : Measure p.Low),
        low m=W.joint.1.map measurable_snd.aemeasurable)
    (hatom : ∀ m≥ start,NullSingletonClass
      ((joint m).1.map measurable_snd.aemeasurable : Measure p.Bid))
    (hIC : ∀ m≥ start,∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),∀ b : p.Bid,
      p.compactSourceUtility (m-1) (p.capacity m) (low m) (joint m) (x.1,b)≤
        p.compactSourceUtility (m-1) (p.capacity m) (low m) (joint m) x)
    (hprice : Tendsto (fun m=> p.h0/
      (∫x : p.Value×p.Bid,(x.2.1)⁻¹ ∂((joint m).1 : Measure (p.Value×p.Bid))))
      atTop (𝓝 lam01))
    (hgraph : ∀ eps>0,∀ᶠm in atTop,
      ∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),
        |x.2.1-lam01/(1-p.xi*q01 x.1.1 lam01)|< eps) :
    FrozenActiveFamily p := by
  have hlam : p.lam∈ Icc (p.h0*p.L) (p.h0*p.U) :=
    ⟨p.source_price_box.1.le,p.source_price_box.2.le⟩
  have hq (v : p.Value) : q01 v.1 p.lam=p.q v :=
    p.source_q_eq_of_phi v _ (hphi v p.lam hlam).1 (hphi v p.lam hlam).2
  have hclear : (∫v : p.Value,q01 v.1 p.lam ∂(p.activeValues : Measure p.Value))=p.qbar := by
    rw [integral_congr_ae (ae_of_all _ hq)]
    exact p.clearing
  have heq : p.lam=lam01 := hunique p.lam hlam hclear
  have hprice' : Tendsto (fun m=> p.h0/
      (∫x : p.Value×p.Bid,(x.2.1)⁻¹ ∂((joint m).1 : Measure (p.Value×p.Bid))))
      atTop (𝓝 p.lam) := by simpa only [heq] using hprice
  have hgraph' : ∀ eps>0,∀ᶠm in atTop,
      ∀ᵐx ∂((joint m).1 : Measure (p.Value×p.Bid)),|x.2.1-p.beta x.1|< eps := by
    intro eps heps
    filter_upwards [hgraph eps heps] with m hm
    filter_upwards [hm] with x hx
    simpa only [←heq,hq,PrimitiveInput.beta] using hx
  exact of_compact_numeric p start low joint hlow hatom hIC hprice' hgraph'

end FrozenActiveFamily
end FCAppendix.Affine.Hybrid.Native02
