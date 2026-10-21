import FCAppendix.Affine.Tail04.NativeExceptionalCounts
import FCAppendix.Affine.Hybrid.Native02.SourceFamilyExceptional

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeSourceExceptionalCounts
open MeasureTheory ProbabilityTheory Set Filter Topology Game Bayes
open Hybrid Hybrid.Native02 Hybrid.Native02.FullContext
open NativeExceptionalCounts

variable {p : PrimitiveInput} {A : FrozenActiveFamily p} (S : SourceFamily p A)

theorem eventually_exceptional_count_zero (eps : ℝ) (heps : 0< eps) :
    ∀ᶠk in atTop,∀(i : Fin (S.M k)) (act : JointAction 2),
      p.d< act.bid→ act.bid< p.R→ act.bid∉Icc p.L p.U→ act.routeCount=2→
      |((problem (S.game k) i).outcome act).mass 0-
        (1-EqualCapacity.demand p.xi act.bid (S.price k))^2|< eps := by
  have he:=eventually_exceptional_fullrow_failure p.s p.a p.h p.rho p.z p.xi p.d p.L p.U
    p.s_pos p.a_pos p.h_pos p.mass p.z_nonneg p.z_lt_one p.xi_pos p.xi_lt_one
    p.d_pos p.L_pos p.L_lt_U.le p.low_receipt p.rho_lower p.rho_upper
    p.qbar_pos p.qbar_lt_one p.box_lower p.box_upper p.capacity p.capacity_limit eps heps
  filter_upwards [S.N_tendsto.eventually he] with k hk
  intro i act hb hbR hout hroute
  have facts:=S.context_facts k
  have hf:=hk (S.lowLaw k) (S.activeLaw k) (S.lowLaw_singletons k)
    (S.lowLaw_supported k) (S.activeLaw_supported k)
    (NativeContinuation.focalIndex i).symm act.bid hb hout
  have heq := closed_broadcast_failure_fullrows
    (contextPolicy p.xi_pos p.xi_lt_one p.d p.L p.U p.z (S.C k) (S.lowLaw k)) (S.baseGame k)
    (p.d_lt_L.le.trans p.L_lt_U.le) p.upper_floor rfl
    facts.1 facts.2.1 p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
    (S.lowLaw k) (S.activeLaw k) facts.2.2 i act hbR hroute
  have heq' : ((problem (S.game k) i).outcome act).mass 0 =
      (CommonList.iid (LowBody.categoryLaw p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le
        p.mass (S.activeLaw k)) (S.N k)).expect
          (patternFailure
            (contextPolicy p.xi_pos p.xi_lt_one p.d p.L p.U p.z (S.C k) (S.lowLaw k))
            (NativeContinuation.focalIndex i).symm (S.lowLaw k) (S.activeLaw k) act.bid) := by
    rw [S.game_eq_closed k]
    exact heq
  rw [heq']
  exact hf

theorem exceptional_count_null_error :
    ∃err : ℕ→ℝ,(∀k,0< err k)∧Tendsto err atTop (nhds 0)∧
      ∀ᶠk in atTop,∀(i : Fin (S.M k)) (act : JointAction 2),
        p.d< act.bid→ act.bid< p.R→ act.bid∉Icc p.L p.U→ act.routeCount=2→
        |((problem (S.game k) i).outcome act).mass 0-
          (1-EqualCapacity.demand p.xi act.bid (S.price k))^2|< err k :=
  exists_positive_null_error_of_eventually _ (eventually_exceptional_count_zero S)

end FCAppendix.Affine.Tail04.NativeSourceExceptionalCounts
