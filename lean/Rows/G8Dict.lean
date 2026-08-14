import Rows.G6

open TM Term Trans Rows Rows.Selected

namespace Rows.Selected.G8Dict

abbrev Z0 : Term := Z zero
abbrev Z1 : Term := Z one

def t : Term := psi Z0 (phi zero (add Z1 Z0))

/-- The term-side iteration exposed by the fundamental sequence of `t`. -/
def F : Nat → Term
  | 0 => psi Z0 Z1
  | n+1 => psi Z0 (phi zero (add Z1 (F n)))

/-- The complete-block Buchholz reader output, before the outer selected-row shift. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0, b => b
  | n+1, b => .D 0 (.D 2 (W n b))

theorem fsN_t : ∀ n : Nat, fsN t n=F n
  | 0 => by
    rw [t,fsN]
    rfl
  | n+1 => by
    rw [t,fsN]
    simp only [show kindT (phi zero (add Z1 Z0))=KindT.isLim from rfl,
      show cofT (phi zero (add Z1 Z0))=Z0 from rfl,
      show ((Z0:Term)==omega)=false from rfl,
      Bool.false_eq_true,if_false,
      show lt Z0 Z0=false from Evidence.WF.lt_irrefl Z0]
    rw [← t,fsN_t n]
    cases n <;> rfl

theorem psi_lt_Z2 (x : Term) :
    lt (psi Z0 x) (Z (ofNat 2))=true := by
  unfold lt
  cases h:fuelOf (psi Z0 x) (Z (ofNat 2)) with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_psi_Z]
    apply if_pos
    simp only [Bool.or_eq_true]
    right
    have hf : Z0.deg+(Z (ofNat 2)).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF Z0 (Z (ofNat 2)) f hf]
    decide

theorem psi_lt_Z1 (x : Term) : lt (psi Z0 x) Z1=true := by
  unfold lt
  cases h:fuelOf (psi Z0 x) Z1 with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_psi_Z]
    apply if_pos
    simp only [Bool.or_eq_true]
    right
    have hf : Z0.deg+Z1.deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF Z0 Z1 f hf]
    decide

theorem F_isAP (n : Nat) : (F n).isAP=true := by cases n <;> rfl

theorem F_bne_one (n : Nat) : ((F n)==one)=false := by cases n <;> rfl

theorem plus_Z1_F (n : Nat) : plus Z1 (F n)=add Z1 (F n) := by
  unfold plus
  rw [show Z1.toList=[Z1] from rfl,
    show (F n).toList=[F n] from by cases n <;> rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (F n) Z1=true from Evidence.WF.le_of_lt (by
    cases n <;> exact psi_lt_Z1 _)]
  rfl

theorem lt_M_add_Z1_F (n : Nat) : lt M (add Z1 (F n))=false := by
  unfold lt
  rw [show fuelOf M (add Z1 (F n))=
      (2*(M.deg+(add Z1 (F n)).deg)+6)+1+1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_M_add]
  simp only [show ((M:Term)==Z1)=false from rfl,Bool.false_or,
    Evidence.WF.ltF_succ_M_Z]

theorem psi_lt_Z0 (x : Term) : lt (psi Z0 x) Z0=true := by
  unfold lt
  rw [show fuelOf (psi Z0 x) Z0=
      (2*((psi Z0 x).deg+Z0.deg)+7)+1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_psi_Z,if_pos]
  simp only [show ((Z0:Term)==Z0)=true from rfl,Bool.true_or]

theorem F_lt_Z0 (n : Nat) : lt (F n) Z0=true := by
  cases n <;> exact psi_lt_Z0 _

theorem omegaNF_psi (x : Term) : omegaNF (psi Z0 x)=psi Z0 x := by
  unfold omegaNF
  rw [show lt M (psi Z0 x)=false from by
    unfold lt
    rw [show fuelOf M (psi Z0 x)=(2*(M.deg+(psi Z0 x).deg)+7)+1 from by
      unfold fuelOf; omega,
      Evidence.WF.ltF_succ_M_psi]]
  simp only [Bool.false_eq_true,if_false]
  simp only [show ((psi Z0 x:Term)==M)=false from rfl,
    Bool.false_eq_true,if_false]
  unfold phiNF
  have hn : psi Z0 x≠zero := by intro h; cases h
  have hlt : lt zero (psi Z0 x)=true := Rows.ProofsB.lt_zero_ne hn
  rw [show ((psi Z0 x).isSC && lt zero (psi Z0 x))=true from by
    rw [hlt]
    rfl]
  simp only [if_true]

theorem omegaNF_F (n : Nat) : omegaNF (F n)=F n := by
  cases n <;> exact omegaNF_psi _

theorem add_Z1_F_not_lt_Z0 (n : Nat) : lt (add Z1 (F n)) Z0=false := by
  unfold lt
  rw [show fuelOf (add Z1 (F n)) Z0=
      (2*((add Z1 (F n)).deg+Z0.deg)+7)+1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_add_nsum _ (by exact Term.noConfusion) (by rfl)]
  rw [← Evidence.WF.lt_eq_ltF Z1 Z0 _ (by
    simp only [Term.deg]
    omega)]
  decide

theorem pow_Z1_F_not_lt_Z0 (n : Nat) :
    lt (phi zero (add Z1 (F n))) Z0=false := by
  unfold lt
  rw [show fuelOf (phi zero (add Z1 (F n))) Z0=
      (2*((phi zero (add Z1 (F n))).deg+Z0.deg)+7)+1 from by
        unfold fuelOf; omega,
    Evidence.WF.ltF_succ_phi_Z]
  rw [← Evidence.WF.lt_eq_ltF (add Z1 (F n)) Z0 _ (by
    simp only [Term.deg]
    omega),add_Z1_F_not_lt_Z0]
  simp only [Bool.and_false]

theorem phiShifted_add_Z1_F (n : Nat) :
    phiShifted zero (add Z1 (F n))=false := by
  unfold phiShifted
  rw [Evidence.StageB.splitFin_add_pair (F_isAP n) (F_bne_one n)]
  rfl

theorem logOm_pow_Z1_F (n : Nat) :
    Trans.Dict.logOm (phi zero (add Z1 (F n)))=add Z1 (F n) := by
  unfold Trans.Dict.logOm
  change (if phiShifted zero (add Z1 (F n)) then
    plus (add Z1 (F n)) one else add Z1 (F n))=add Z1 (F n)
  rw [phiShifted_add_Z1_F]
  rfl

theorem toList_add_Z1_F (n : Nat) :
    (add Z1 (F n)).toList=[Z1,F n] := by
  change Z1::(F n).toList=[Z1,F n]
  rw [show (F n).toList=[F n] from by cases n <;> rfl]

theorem wcnf_pow_Z1_F (n : Nat) : Trans.Dict.wcnf Z0
    [phi zero (add Z1 (F n))]=([(Z1,F n)],zero) := by
  unfold Trans.Dict.wcnf
  rw [pow_Z1_F_not_lt_Z0]
  simp only [Bool.false_eq_true,if_false,logOm_pow_Z1_F]
  rw [toList_add_Z1_F]
  simp only [List.filter_cons,List.filter_nil,
    show lt Z1 Z0=false from by decide,F_lt_Z0,
    Bool.not_false,Bool.not_true,Bool.false_eq_true,if_true,if_false,
    List.map_cons,List.map_nil,
    show Trans.Dict.divAP Z0 Z1=Z1 from rfl,TM.Term.ofList,
    omegaNF_F,Trans.Dict.wcnf]

theorem omegaNF_add_Z1_F (n : Nat) :
    omegaNF (add Z1 (F n))=phi zero (add Z1 (F n)) := by
  rw [omegaNF_of_le_M (lt_M_add_Z1_F n)]
  exact Evidence.StageB.phiNF_add_pair rfl (F_isAP n) (F_bne_one n)

theorem collapse_two_F (n : Nat) :
    Trans.Dict.collapse 2 (F n)=phi zero (add Z1 (F n)) := by
  have hw : Trans.Dict.wcnf (Z (ofNat 2)) [F n]=([],F n) := by
    rw [Trans.Dict.wcnf,if_pos (by cases n <;> exact psi_lt_Z2 _)]
    rfl
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (2+1)=Z (ofNat 2) from rfl,
    show Trans.Dict.reg 2=Z1 from rfl,
    show ((2:Nat)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (F n).toList=[F n] from by cases n <;> rfl,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (F_isAP n),plus_Z1_F]
  exact omegaNF_add_Z1_F n

theorem mulL_Z1_F (n : Nat) :
    Trans.Dict.mulL Z1 (F n)=phi zero (add Z1 (F n)) := by
  unfold Trans.Dict.mulL
  rw [show (F n).toList=[F n] from by cases n <;> rfl]
  simp only [List.map_cons,List.map_nil,TM.Term.ofList]
  rw [show Trans.Dict.logOm (F n)=F n from by cases n <;> rfl,
    plus_Z1_F,omegaNF_add_Z1_F]

theorem sub1_pow_Z1_F (n : Nat) :
    Trans.Dict.sub1 (phi zero (add Z1 (F n)))=
      phi zero (add Z1 (F n)) := by
  unfold Trans.Dict.sub1
  simp only [TM.Term.toList]
  rw [show ((phi zero (add Z1 (F n)):Term)==one)=false from rfl]
  simp only [Bool.false_eq_true,if_false]

theorem collapse_zero_pow_Z1_F (n : Nat) :
    Trans.Dict.collapse 0 (phi zero (add Z1 (F n)))=
      psi Z0 (phi zero (add Z1 (F n))) := by
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (0+1)=Z0 from rfl,
    show Trans.Dict.reg 0=zero from rfl,
    show ((0:Nat)==0)=true from rfl]
  simp only [if_true]
  rw [show (phi zero (add Z1 (F n))).toList=
      [phi zero (add Z1 (F n))] from rfl,
    wcnf_pow_Z1_F]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z0 Z1=true from by decide,
    show Trans.Dict.subAP Z0 Z1=Z1 from rfl,
    show Trans.Dict.mulL Z0 Z1=Z1 from rfl,
    mulL_Z1_F,sub1_pow_Z1_F]
  simp only [if_pos True.intro,Option.getD_some,TM.Term.plus_zero]
  rw [Rows.ProofsB.plus_zero_left (show (psi Z0
    (phi zero (add Z1 (F n)))).isAP=true from rfl),omegaNF_psi]

theorem dict_W : ∀ n : Nat,
    Trans.Dict.dict (W (n+1) .zero)=F n
  | 0 => rfl
  | n+1 => by
    rw [show n+1+1=(n+1)+1 by omega,W,
      Trans.Dict.dict_D,Trans.Dict.dict_D,dict_W n,
      collapse_two_F,collapse_zero_pow_Z1_F]
    rfl

theorem dict_W_fsN (n : Nat) :
    Trans.Dict.dict (W (n+1) .zero)=fsN t n := by
  rw [dict_W,fsN_t]

#print axioms dict_W_fsN

end Rows.Selected.G8Dict
