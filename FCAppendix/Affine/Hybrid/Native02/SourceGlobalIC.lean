import FCAppendix.Affine.Hybrid.Native02.SourceFamilyService
import FCAppendix.Affine.Hybrid.Native02.SourceFamilyEstimates
import FCAppendix.Affine.Hybrid.Native02.SourceFamilyExceptional
import FCAppendix.Affine.Hybrid.Native02.FiniteGlobalIC

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Existence.RankEnvelope

namespace SourceFamily
variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

theorem eventually_activeUsersOptimal : ∀ᶠk in atTop,
    ∀ i : Fin (S.M k),∀ᵐx ∂(S.PA k : Measure (ℝ×JointAction 2)),
      (problem (S.game k) i).BestResponse x.1 x.2 := by
  obtain ⟨delta,hd,hgap⟩:=Menus.active_compact_margin p.xi_pos p.xi_lt_one p.z p.lam
    p.z_nonneg p.z_lt_one.le p.activeSupport p.active_compact p.active_nonempty p.R
    (by convert! p.active_menu_one using 1) (by convert! p.active_menu_M1 using 1)
    (by convert! p.active_menu_upper using 1)
  obtain ⟨egap,heg,hexgap⟩:=S.active_exceptional_broadcast_gap
  let D:=min delta egap
  let eps:=D/4
  have hD : 0< D := lt_min hd heg
  have heps : 0< eps := by dsimp [eps];positivity
  have hsmall : 2*eps< D := by dsimp [eps];linarith
  have hDdelta : D≤ delta := min_le_left _ _
  have hDegap : D≤ egap := min_le_right _ _
  filter_upwards [S.eventually_boxed_menus S.H S.H_pos.le eps heps,
    S.exceptional_menus S.H S.H_pos.le eps heps,
    S.eventually_low_payoff_small S.H S.H_pos.le eps heps,hexgap]
    with k hbox hex hlo hexc
  intro i
  filter_upwards [S.PA_source_support k,S.PA_support k,S.boxed_incumbent_IC k]
    with x hxK hx hxIC
  let v : p.Value:=⟨x.1,hx.1⟩
  let test : JointAction 2:=activeBroadcast p.L_pos.le (A.targetBid v)
  have htbox : test.bid∈ Icc p.L p.U := A.response_boxed v
  have hvW:=S.active_value_bound x.1 hxK
  have htest := (hbox i test htbox x.1 hvW.2).1 rfl
  have htestref : broadcastReference p.eta p.xi p.z x.1 p.lam test.bid=
      Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam x.1 := p.broadcastReference_beta v
  rw [htestref] at htest
  have hbase:=hgap x.1 hxK
  have hMnonneg:=Menus.M1_nonneg p.xi_pos p.xi_lt_one p.lam x.1
  have h1le : Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1≤
      max (Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1)
        (max (Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1) (x.1-p.R)) := le_max_left _ _
  have hMle : Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1≤
      max (Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1)
        (max (Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1) (x.1-p.R)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hRle : x.1-p.R≤
      max (Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1)
        (max (Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1) (x.1-p.R)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  apply active_finite_global_IC (S.game k) rfl i x.1 p.d p.L p.U p.R
    (Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam x.1)
    (Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1)
    (Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1)
    (Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam x.1-egap) D eps
    p.d_lt_L p.L_lt_U.le p.upper_floor heps.le hsmall
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    x.2 test htbox rfl
  · exact fun a ha hk=> hxIC i a ha hk
  · have hh := (abs_lt.mp htest).1
    linarith
  · intro a ha
    exact (hlo i x.1 ⟨hvW.1.le,by simpa only [abs_of_pos hvW.1] using hvW.2⟩ a ha).le
  · intro a hk ha
    have hh := (abs_lt.mp ((hbox i a ha x.1 hvW.2).2 hk)).2
    have hr := singletonReference_le_U1 (z:=p.z) (v:=x.1) p.xi_pos p.xi_lt_one
      (p.L_pos.trans_le ha.1) (S.limiting_exposure_mem a.bid ha)
    linarith
  · intro a hk hd' hR' hnot
    exact ((hex x.1 hx.1.1 hvW.2 i a hd' hR' hnot).1 hk).le
  · intro a hk hd' hR' hnot
    have hh := hexc x.1 hxK i a hk hd' hR' hnot
    linarith

theorem eventually_upperUsersOptimal : ∀ᶠk in atTop,
    ∀ i : Fin (S.M k),∀ᵐx ∂(S.PH k : Measure (ℝ×JointAction 2)),
      (problem (S.game k) i).BestResponse x.1 x.2 := by
  obtain ⟨delta,hd,hgap⟩:=Menus.upper_compact_margin p.xi_pos p.xi_lt_one p.z p.lam
    p.z_nonneg p.z_lt_one.le p.upperSupport p.upper_compact p.upper_nonempty
    (fun v hv=>(S.upper_value_bound v hv).1) p.R
    (by convert! p.upper_menu_two using 1) (by convert! p.upper_menu_one using 1)
    (by convert! p.upper_menu_M1 using 1) (by convert! p.upper_menu_M2 using 1)
  let eps:=delta/4
  have heps : 0< eps := by dsimp [eps];positivity
  have hsmall : 2*eps< delta := by dsimp [eps];linarith
  have herror : ∀ᶠk in atTop,error (S.upperRank k) S.t p.R< eps :=
    S.upper_limits.2.eventually (Iio_mem_nhds heps)
  filter_upwards [S.eventually_boxed_menus S.H S.H_pos.le eps heps,
    S.exceptional_menus S.H S.H_pos.le eps heps,
    S.eventually_low_payoff_small S.H S.H_pos.le eps heps,herror]
    with k hbox hex hlo hE
  intro i
  filter_upwards [S.PH_source_support k,(S.upperPackage k).joint_shape,
    (S.upperPackage k).joint_upper_IC i] with x hxK hx hxhigh
  have hvW:=S.upper_value_bound x.1 hxK
  have hvlo : p.vlo≤ x.1 := p.value_order.trans (S.vhi_lt_t.le.trans hx.1.1)
  have hbase:=hgap x.1 hxK
  have hM0:=Menus.M1_nonneg p.xi_pos p.xi_lt_one p.lam x.1
  let U2:=Menus.U2 p.xi_pos p.xi_lt_one p.z p.lam x.1
  let U1:=Menus.U1 p.xi_pos p.xi_lt_one p.z p.lam x.1
  let M1:=Menus.M1 p.xi_pos p.xi_lt_one p.lam x.1
  let M2:=outsideTwo x.1 p.lam
  change max U2 (max U1 (max M1 M2))+delta≤ x.1-p.R at hbase
  change 0≤ M1 at hM0
  have h2le : U2≤ max U2 (max U1 (max M1 M2)) := le_max_left _ _
  have h1le : U1≤ max U2 (max U1 (max M1 M2)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hMle : M1≤ max U2 (max U1 (max M1 M2)) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hEle : M2≤ max U2 (max U1 (max M1 M2)) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hinc := (S.upperPackage k).utility_floor i x.1 hx.1.1
  rw [←hx.2.1] at hinc
  apply upper_finite_global_IC (S.game k) rfl i x.1 p.d p.L p.U p.R U2 U1 M1 M2 delta eps
    p.d_lt_L p.L_lt_U.le p.upper_floor heps.le hsmall
    (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) x.2 (by linarith)
  · intro a ha
    exact (hlo i x.1 ⟨hvW.1.le,by simpa only [abs_of_pos hvW.1] using hvW.2⟩ a ha).le
  · intro a hk ha
    have hh := (abs_lt.mp ((hbox i a ha x.1 hvW.2).2 hk)).2
    have hr := singletonReference_le_U1 (z:=p.z) (v:=x.1) p.xi_pos p.xi_lt_one
      (p.L_pos.trans_le ha.1) (S.limiting_exposure_mem a.bid ha)
    dsimp only [U1]
    linarith
  · intro a hk ha
    have hh := (abs_lt.mp ((hbox i a ha x.1 hvW.2).1 hk)).2
    have hr := broadcastReference_le_U2 (z:=p.z) (v:=x.1)
      (by dsimp only [PrimitiveInput.xi];ring : p.eta=1-2*p.xi)
      p.xi_pos p.xi_lt_one (p.L_pos.trans_le ha.1) (S.limiting_exposure_mem a.bid ha)
    dsimp only [U2]
    linarith
  · intro a hk hd' hR' hnot
    exact ((hex x.1 hvlo hvW.2 i a hd' hR' hnot).1 hk).le
  · intro a hk hd' hR' hnot
    exact ((hex x.1 hvlo hvW.2 i a hd' hR' hnot).2 hk).le
  · intro a _ ha
    exact hxhigh a ha
  · intro a _ ha
    exact hxhigh a ha

theorem eventually_usersOptimal : ∀ᶠk in atTop,UsersOptimal (S.game k) := by
  filter_upwards [S.eventually_activeUsersOptimal,S.eventually_upperUsersOptimal]
    with k hA hH
  exact original_population_mixture_IC (S.game k) p.s p.a p.h
    (S.PL k) (S.PA k) (S.PH k) (S.joint_original_components k)
    (fun i=>(S.lowUsersOptimal k i).mono (fun _ hx=> hx.1)) hA hH

end SourceFamily
end FCAppendix.Affine.Hybrid.Native02
