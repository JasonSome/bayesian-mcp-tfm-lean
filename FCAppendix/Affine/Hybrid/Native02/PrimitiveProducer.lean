import FCAppendix.Affine.Hybrid.Finishing01
import FCAppendix.Affine.Hybrid.Native02.FrozenActiveAdapter

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional

namespace PrimitiveInput

def activePrimitives (p : PrimitiveInput) : Finish01.Primitives where
  s := p.s
  a := p.a
  h := p.h
  rho := p.rho
  d := p.d
  vlo := p.vlo
  vhi := p.vhi
  L := p.L
  U := p.U
  xi := p.xi
  z := p.z
  s_pos := p.s_pos
  a_pos := p.a_pos
  h_pos := p.h_pos
  mass := p.mass
  xi_pos := p.xi_pos
  xi_half := p.xi_half
  z_nonneg := p.z_nonneg
  z_lt_one := p.z_lt_one
  d_nonneg := p.d_nonneg
  L_pos := p.L_pos
  value_order := p.value_order
  rho_lower := p.rho_lower
  rho_upper := p.rho_upper
  qbar_pos := p.qbar_pos
  qbar_lt_one := p.qbar_lt_one
  box_lower := p.box_lower
  box_upper := p.box_upper
  low_receipt := p.low_receipt
  value_surplus := p.value_surplus
  inward_lower := p.inward_lower
  inward_upper := p.inward_upper
  low_rate_gap := p.low_rate_gap

end PrimitiveInput

theorem primitive_active_producer : ActiveProducer := by
  intro p
  let P := p.activePrimitives
  let muLow : Measure P.Low := (p.lowValues : Measure p.Low)
  let mu : Measure P.Value := (p.activeValues : Measure p.Value)
  letI : IsProbabilityMeasure muLow := p.lowValues.prop
  letI : IsProbabilityMeasure mu := p.activeValues.prop
  let E := Classical.choice (P.exists_primitive_active p.capacity p.capacity_limit
    muLow p.low_positive mu)
  let F := E.numeric
  have hlam : (F.multiplier : ℝ) = p.lam :=
    (E.global_unique p.lam p.q p.q_interior p.source_q_phi p.clearing).symm
  have hq (v : p.Value) : P.qResponse v F.multiplier = p.q v := by
    apply p.source_q_eq_of_phi v _
      ⟨(P.qResponse_spec v F.multiplier).1.1.le,
        (P.qResponse_spec v F.multiplier).1.2.le⟩
    simpa only [P, PrimitiveInput.activePrimitives, hlam] using P.qResponse_phi v F.multiplier
  have hlow : ∀ m ≥ F.threshold, ∃ W : LowBody.ActualAtomlessLowLimit
      (m-1) p.d p.xi (p.capacity m) p.categories (p.lowValues : Measure p.Low),
      F.low m = W.joint.1.map measurable_snd.aemeasurable := by
    intro m hm
    exact ⟨(F.lowWitness m hm).witness, F.low_eq m hm⟩
  have hIC : ∀ m ≥ F.threshold,
      ∀ᵐ x ∂((F.joint m).1 : Measure P.Latent), ∀ b : p.Bid,
        p.compactSourceUtility (m-1) (p.capacity m) (F.low m) (F.joint m) (x.1,b) ≤
          p.compactSourceUtility (m-1) (p.capacity m) (F.low m) (F.joint m) x := by
    intro m hm
    exact F.all_bid_IC m hm
  have hprice : Tendsto (fun m => p.h0 /
      (∫ x : p.Value × p.Bid, (x.2.1)⁻¹
        ∂((F.joint m).1 : Measure P.Latent))) atTop (𝓝 p.lam) := by
    convert! F.price_tendsto using 1
    rw [hlam]
  have hgraph : ∀ eps > 0, ∀ᶠ m in atTop,
      ∀ᵐ x ∂((F.joint m).1 : Measure P.Latent),
        |x.2.1 - p.beta x.1| < eps := by
    intro eps heps
    filter_upwards [F.supported_graph eps heps] with m hm
    filter_upwards [hm] with x hx
    change |x.2.1 - (F.multiplier:ℝ)/(1-P.xi*P.qResponse x.1 F.multiplier)| < eps at hx
    rw [hq] at hx
    simpa only [hlam, PrimitiveInput.beta, P, PrimitiveInput.activePrimitives] using hx
  exact ⟨FrozenActiveFamily.of_compact_numeric p F.threshold F.low F.joint
    hlow F.atomless hIC hprice hgraph⟩

end FCAppendix.Affine.Hybrid.Native02
