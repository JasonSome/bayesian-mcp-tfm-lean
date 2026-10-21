import FCAppendix.Affine.Hybrid.Native02.SourceFamily
import FCAppendix.Affine.Hybrid.Native02.ExceptionalOriginalRows
import FCAppendix.Affine.Hybrid.Native02.ReferenceMenus

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes Set Filter Topology

namespace SourceFamily
variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

lemma exceptionalReference_factor_pos (_S : SourceFamily p A) : 0< p.h0 := by
  have hq0 : 0< p.qbar := p.qbar_pos
  have hq1 : p.qbar<1 := p.qbar_lt_one
  dsimp only [PrimitiveInput.h0]
  nlinarith [p.xi_pos,p.xi_lt_one]

lemma exceptionalReference_box (k : ℕ) : S.price k∈ Icc (p.h0*p.L) (p.h0*p.U) :=
  reciprocal_reference_bounds (S.activeLaw k) p.L_pos p.L_lt_U.le
    (S.activeLaw_supported k) S.exceptionalReference_factor_pos.le

include S in
lemma exceptionalReference_source_box : p.lam∈ Icc (p.h0*p.L) (p.h0*p.U) :=
  isClosed_Icc.mem_of_tendsto S.price_limit
    (Eventually.of_forall (fun k => S.exceptionalReference_box k))

lemma exceptionalReference_intervals (k : ℕ) {v : ℝ} (hv : p.vlo≤ v) :
    S.price k∈ Icc (0:ℝ) v ∧ p.lam∈ Icc (0:ℝ) v := by
  have h0 : 0< p.h0*p.L := mul_pos S.exceptionalReference_factor_pos p.L_pos
  have hupper : p.h0*p.U< p.L := p.box_upper
  have hLv : p.L< v := p.L_lt_U.trans (p.value_surplus.trans_le hv)
  have hf := S.exceptionalReference_box k
  have hs := S.exceptionalReference_source_box
  exact ⟨⟨h0.le.trans hf.1,hf.2.trans (hupper.trans hLv).le⟩,
    ⟨p.lam_pos.le,hs.2.trans (hupper.trans hLv).le⟩⟩

theorem exceptional_menus (W : ℝ) (hW : 0≤ W) (eps : ℝ) (heps : 0< eps) :
    ∀ᶠ k : ℕ in atTop,∀ v : ℝ,p.vlo≤ v → |v|≤ W →
      ∀ (i : Fin (S.M k)) (act : JointAction 2),
      p.d< act.bid → act.bid< p.R → act.bid∉Icc p.L p.U →
      (act.routeCount=1 → (problem (S.game k) i).payoff v act<
        Menus.M1 p.xi_pos p.xi_lt_one p.lam v+eps) ∧
      (act.routeCount=2 → (problem (S.game k) i).payoff v act< outsideTwo v p.lam+eps) := by
  have heta : p.eta=1-2*p.xi := by dsimp [PrimitiveInput.xi]; ring
  have hm := FullContext.eventually_original_game_exceptional_menus
    p.s p.a p.h p.rho p.z p.xi p.eta p.d p.L p.U p.R W
    p.s_pos p.a_pos p.h_pos p.mass p.z_nonneg p.z_lt_one p.xi_pos p.xi_lt_one
    heta p.eta_pos.le p.eta_lt_one.le p.d_nonneg p.L_pos p.L_lt_U.le p.upper_floor hW
    p.low_receipt p.rho_lower p.rho_upper p.qbar_pos p.qbar_lt_one p.box_lower p.box_upper
    p.capacity p.capacity_limit (eps/2) (half_pos heps)
  have hm' := S.N_tendsto.eventually hm
  let K := 1/(1-p.xi)+2
  have hκ : 0<1-p.xi := sub_pos.mpr p.xi_lt_one
  have hK : 0< K := by dsimp [K]; positivity
  have hp : Tendsto (fun k => K*|S.price k-p.lam|) atTop (nhds 0) := by
    simpa only [sub_self,abs_zero,mul_zero] using ((S.price_limit.sub_const p.lam).abs).const_mul K
  have hsmall := hp.eventually (Iio_mem_nhds (half_pos heps))
  filter_upwards [hm',hsmall] with k hk hpk
  intro v hv hvW i act hb hbR hout
  have hv0 : 0< v := p.vlo_pos.trans_le hv
  have facts := S.context_facts k
  have hmenus :
      (act.routeCount=1 → (problem (S.game k) i).payoff v act<
        Menus.M1 p.xi_pos p.xi_lt_one (S.price k) v+eps/2) ∧
      (act.routeCount=2 → (problem (S.game k) i).payoff v act< outsideTwo v (S.price k)+eps/2) := by
    rw [S.game_eq_closed k]
    exact hk (S.lowLaw k) (S.activeLaw k) (S.lowLaw_singletons k)
      (S.lowLaw_supported k) (S.activeLaw_supported k) (S.baseGame k) rfl rfl rfl
      facts.1 facts.2.1 facts.2.2 i act hb hbR hout v hv0 hvW
  have hM1 := M1_price_bound (lam:=S.price k) (lam':=p.lam) (v:=v) p.xi_pos p.xi_lt_one
  have hM2 := M2_price_bound hv0 (S.exceptionalReference_intervals k hv).1
    (S.exceptionalReference_intervals k hv).2
  have hprice1 : |S.price k-p.lam|/(1-p.xi)≤ K*|S.price k-p.lam| := by
    dsimp [K]
    have he : |S.price k-p.lam|/(1-p.xi)=(1/(1-p.xi))*|S.price k-p.lam| := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hprice2 : 2*|S.price k-p.lam|≤ K*|S.price k-p.lam| := by
    exact mul_le_mul_of_nonneg_right
      (by dsimp [K]; linarith [one_div_pos.mpr hκ]) (abs_nonneg _)
  constructor
  · intro hroute
    have hfinite := hmenus.1 hroute
    have hd := (abs_le.mp hM1).2
    linarith
  · intro hroute
    have hfinite := hmenus.2 hroute
    have hd := (abs_le.mp hM2).2
    linarith

theorem exceptional_null_error (W : ℝ) (hW : 0≤ W) :
    ∃ err : ℕ → ℝ,(∀ k,0< err k) ∧ Tendsto err atTop (nhds 0) ∧
      ∀ᶠ k : ℕ in atTop,∀ v : ℝ,p.vlo≤ v → |v|≤ W →
      ∀ (i : Fin (S.M k)) (act : JointAction 2),
      p.d< act.bid → act.bid< p.R → act.bid∉Icc p.L p.U →
      (act.routeCount=1 → (problem (S.game k) i).payoff v act<
        Menus.M1 p.xi_pos p.xi_lt_one p.lam v+err k) ∧
      (act.routeCount=2 → (problem (S.game k) i).payoff v act< outsideTwo v p.lam+err k) := by
  exact FullContext.exists_positive_null_error_of_eventually _
    (fun eps heps => S.exceptional_menus W hW eps heps)

include S in
lemma exceptional_inwardScale_zero (hz : p.z=0) :
    inwardScale p.xi p.z p.qbar=(1-p.qbar)/(1-p.xi*p.qbar) := by
  have hh0 : 1-p.xi*p.qbar≠0 := S.exceptionalReference_factor_pos.ne'
  rw [hz]
  unfold inwardScale
  simp only [zero_mul,zero_div,add_zero]
  field_simp [hh0]

theorem zero_exceptional_reduced_M2 (hz : p.z=0) :
    ∃ delta>0,∀ᶠ k : ℕ in atTop,∀ v∈ Icc p.vlo p.vhi,
      ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.routeCount=2 → p.d< act.bid → act.bid< p.R → act.bid∉Icc p.L p.U →
        (problem (S.game k) i).payoff v act< outsideTwo v p.lam-delta := by
  have heta : p.eta=1-2*p.xi := by dsimp [PrimitiveInput.xi]; ring
  have hq0 : 0< sourceExposure p.a p.h p.rho 0 := by simpa only [hz] using p.qbar_pos
  have hq1 : sourceExposure p.a p.h p.rho 0<1 := by simpa only [hz] using p.qbar_lt_one
  have hlo : (1-p.xi)*p.U<(1-p.xi*sourceExposure p.a p.h p.rho 0)*p.L := by
    simpa only [hz, PrimitiveInput.xi] using p.box_lower
  have hhi : (1-p.xi*sourceExposure p.a p.h p.rho 0)*p.U< p.L := by
    simpa only [hz, PrimitiveInput.xi] using p.box_upper
  have hleft : p.L<(1-sourceExposure p.a p.h p.rho 0)/
      (1-p.xi*sourceExposure p.a p.h p.rho 0)*p.vlo := by
    have hh : p.L< inwardScale p.xi p.z p.qbar*p.vlo := p.inward_lower
    rw [S.exceptional_inwardScale_zero hz] at hh
    simpa only [PrimitiveInput.qbar,hz] using hh
  have hright : (1-sourceExposure p.a p.h p.rho 0)/
      (1-p.xi*sourceExposure p.a p.h p.rho 0)*p.vhi< p.U := by
    have hh : inwardScale p.xi p.z p.qbar*p.vhi< p.U := p.inward_upper
    rw [S.exceptional_inwardScale_zero hz] at hh
    simpa only [PrimitiveInput.qbar,hz] using hh
  have ht := FullContext.eventually_original_game_exceptional_zero_strict
    p.s p.a p.h p.rho p.xi p.eta p.d p.L p.U p.R p.vlo p.vhi
    p.s_pos p.a_pos p.h_pos p.mass p.xi_pos p.xi_lt_one heta p.eta_pos.le p.eta_lt_one.le
    p.L_pos p.L_lt_U.le p.upper_floor p.value_surplus p.value_order p.low_receipt
    p.rho_lower p.rho_upper hq0 hq1 hlo hhi hleft hright p.capacity p.capacity_limit
  dsimp only at ht
  let delta := FullContext.zeroSourceLoss p.xi (sourceExposure p.a p.h p.rho 0)
    p.L p.U p.vlo p.vhi/4
  have hd : 0< delta := by dsimp [delta]; linarith [ht.1]
  have hfinite := S.N_tendsto.eventually ht.2
  have hp : Tendsto (fun k => 2*|S.price k-p.lam|) atTop (nhds 0) := by
    simpa only [sub_self,abs_zero,mul_zero] using ((S.price_limit.sub_const p.lam).abs).const_mul 2
  have hprice := hp.eventually (Iio_mem_nhds hd)
  refine ⟨delta,hd,?_⟩
  filter_upwards [hfinite,hprice] with k hk hpk
  intro v hv i act hroute hb hbR hout
  have facts := S.context_facts k
  have hfinitePay := hk (S.lowLaw k) (S.activeLaw k) (S.lowLaw_singletons k)
    (S.lowLaw_supported k) (S.activeLaw_supported k) (S.baseGame k) rfl rfl rfl
    facts.1 facts.2.1 facts.2.2 i act hb hbR hout hroute v hv
  have hgame : S.game k=ClosedPolicy.nativeGame
      (FullContext.contextPolicy p.xi_pos p.xi_lt_one p.d p.L p.U 0 (S.C k) (S.lowLaw k))
      (S.baseGame k) p.R := by rw [S.game_eq_closed k,hz]
  have hlam : (1-p.xi*sourceExposure p.a p.h p.rho 0)/reciprocalMean (S.activeLaw k)=S.price k := by
    simp only [price,PrimitiveInput.h0,PrimitiveInput.qbar,hz]
  have hfinitePay' : (problem (S.game k) i).payoff v act <
      outsideTwo v (S.price k) - FullContext.zeroSourceLoss p.xi
        (sourceExposure p.a p.h p.rho 0) p.L p.U p.vlo p.vhi/2 := by
    rw [hgame]
    convert! hfinitePay using 1
    rw [hlam]

  have hv0 : 0< v := p.vlo_pos.trans_le hv.1
  have hM := M2_price_bound hv0 (S.exceptionalReference_intervals k hv.1).1
    (S.exceptionalReference_intervals k hv.1).2
  have hdiff := (abs_le.mp hM).2
  dsimp only [delta] at hpk ⊢
  linarith

theorem active_exceptional_broadcast_gap :
    ∃ delta>0,∀ᶠ k : ℕ in atTop,∀ v∈ p.activeSupport,
      ∀ (i : Fin (S.M k)) (act : JointAction 2),
      act.routeCount=2 → p.d< act.bid → act.bid< p.R → act.bid∉Icc p.L p.U →
        (problem (S.game k) i).payoff v act<
          Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam v-delta := by
  by_cases hz : p.z=0
  · obtain ⟨delta,hdelta,hfinite⟩ := S.zero_exceptional_reduced_M2 hz
    refine ⟨delta,hdelta,?_⟩
    filter_upwards [hfinite] with k hk
    intro v hv i act hroute hb hbR hout
    have hvband := p.active_band hv
    have hlv : p.lam< v := (S.exceptionalReference_source_box.2.trans_lt
      (show p.h0*p.U< p.L from p.box_upper)).trans
        (p.L_lt_U.trans (p.value_surplus.trans_le hvband.1))
    rw [hz,Menus.U2_zero_eq p.xi_pos p.xi_lt_one p.lam p.lam_pos v hlv]
    exact hk v hvband i act hroute hb hbR hout
  · have hzpos : 0< p.z := lt_of_le_of_ne p.z_nonneg (Ne.symm hz)
    obtain ⟨delta,hdelta,hmargin⟩ := Menus.active_M2_compact_margin
      p.xi_pos p.xi_lt_one p.z p.lam p.z_nonneg p.z_lt_one.le
      p.activeSupport p.active_compact p.active_nonempty
      (fun v hv => p.vlo_pos.trans_le (p.active_band hv).1) (p.active_menu_M2 hzpos)
    have hW : 0≤ p.vhi := (p.vlo_pos.trans_le p.value_order).le
    have hfinite := S.exceptional_menus p.vhi hW (delta/2) (half_pos hdelta)
    refine ⟨delta/2,half_pos hdelta,?_⟩
    filter_upwards [hfinite] with k hk
    intro v hv i act hroute hb hbR hout
    have hvband := p.active_band hv
    have hv0 : 0< v := p.vlo_pos.trans_le hvband.1
    have hvW : |v|≤ p.vhi := by rw [abs_of_pos hv0]; exact hvband.2
    have hpay := (hk v hvband.1 hvW i act hb hbR hout).2 hroute
    have hm := hmargin v hv
    linarith

end SourceFamily
end FCAppendix.Affine.Hybrid.Native02
