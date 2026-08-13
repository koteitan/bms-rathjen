import Rows.G4Dict

open TM Term Trans Rows Rows.Selected

namespace Rows.Selected.G5Dict

abbrev Om : Term := Z zero
abbrev Z1 : Term := Z one

def J (n : Nat) : Term := plus Z1 (G4Dict.I n)

theorem toList_J_succ (n : Nat) :
    (J (n+1)).toList=[Z1,G4Dict.I (n+1)] := by
  unfold J plus
  rw [show Z1.toList=[Z1] from rfl,
    show (G4Dict.I (n+1)).toList=[G4Dict.I (n+1)] from by
      rw [G4Dict.I_succ]
      rfl]
  change (ofList (([Z1].filter (fun a=>le (G4Dict.I (n+1)) a))++
    [G4Dict.I (n+1)])).toList=_
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (G4Dict.I (n+1)) Z1=true from
    Evidence.WF.le_of_lt (G4Dict.I_lt_Z1 (n+1))]
  rfl

theorem lt_Z1_Om : lt Z1 Om=false := by decide

theorem divAP_Om_Z1 : Trans.Dict.divAP Om Z1=Z1 := rfl

theorem ne_Z1_I (n : Nat) : (Z1==G4Dict.I n)=false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hi:=G4Dict.I_lt_Z1 n
  rw [← h,Evidence.WF.lt_irrefl] at hi
  exact Bool.noConfusion hi

theorem wcnf_J (n : Nat) :
    Trans.Dict.wcnf Om [Z1,G4Dict.I (n+3)]=
      ([(Z1,one),(G4Dict.I (n+2),one)],zero) := by
  unfold Trans.Dict.wcnf
  rw [lt_Z1_Om]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.logOm Z1=Z1 from rfl,
    show Z1.toList=[Z1] from rfl]
  simp only [List.filter_cons,List.filter_nil,lt_Z1_Om,Bool.not_false,if_true,
    List.map_cons,List.map_nil,divAP_Om_Z1,TM.Term.ofList]
  rw [G4Dict.wcnf_I n]
  simp only
  rw [ne_Z1_I]
  simp only [Bool.false_eq_true,if_false,TM.Term.ofList]
  rfl

theorem subAP_Om_Z1 : Trans.Dict.subAP Om Z1=Z1 := rfl
theorem mulL_Om_Z1 : Trans.Dict.mulL Om Z1=Z1 := rfl
theorem mulL_Z1_one : Trans.Dict.mulL Z1 one=Z1 := rfl
theorem sub1_Z1 : Trans.Dict.sub1 Z1=Z1 := rfl

theorem collapse_zero_J (n : Nat) :
    Trans.Dict.collapse 0 (J (n+3))=psi Om (J (n+3)) := by
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (J (n+3)).toList=[Z1,G4Dict.I (n+3)] from by
    simpa only [show n+3=(n+2)+1 by omega] using toList_J_succ (n+2),
    wcnf_J]
  simp only [List.foldl_cons,List.foldl_nil,
    show le Om Z1=true from by decide,if_true,
    show le Om (G4Dict.I (n+2))=true from G4Dict.le_Om_I (n+2)]
  rw [subAP_Om_Z1,mulL_Om_Z1,mulL_Z1_one,sub1_Z1,
    G4Dict.subAP_I (n+1),G4Dict.mulL_Om_I n,G4Dict.mulL_I_one n]
  rfl

theorem dict_D0_sum_rep1_fE (n : Nat) :
    Trans.Dict.dict (.D 0 (.sum (.D 2 .zero) (G4Dict.rep1 (n+1))))=
      Rows.Selected.fE n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        rw [Trans.Dict.dict_D,Trans.Dict.dict,
          show Trans.Dict.dict (.D 2 .zero)=Z1 from rfl,
          show Trans.Dict.dict (G4Dict.rep1 (n+1+1+1+1))=G4Dict.I (n+3) from by
            simpa only [show n+1+1+1+1=n+2+2 by omega,
              show n+3=(n+2)+1 by omega] using G4Dict.dict_rep1_succ (n+2)]
        change Trans.Dict.collapse 0 (J (n+3))=Rows.Selected.fE (n+3)
        rw [collapse_zero_J]
        change psi Om (J (n+3))=Rows.Selected.fE (n+1+1+1)
        rw [Rows.Selected.fE]
        unfold J
        change psi Om (plus Z1 (G4Dict.I (n+3)))=
          psi Om (plus Z1 (iterPhiAt zero G4Dict.base (n+3)))
        rw [G4Dict.iterPhiAt_eq_I]

#print axioms dict_D0_sum_rep1_fE

end Rows.Selected.G5Dict
