import Rows.G8

open TM Term Trans Rows Rows.Selected

namespace Rows.Selected.G9Dict

abbrev Z0 : Term := Z zero
abbrev B : Term := Rows.Selected.Bph

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev C : Trans.Dict.BT := .sum D1z (.sum D1z D0z)
abbrev A0 : Trans.Dict.BT := .D 1 C

/-- The fixed uncountable head contributed by one complete block. -/
def H : Term := phi zero
  (add Z0 (add Z0 (add Z0 TM.Term.one)))

/-- The term-side tower above the doubled family-four base. -/
def I : Nat → Term
  | 0 => plus B B
  | n+1 => phi zero (I n)

def F : Nat → Term
  | 0 => B
  | n+1 => I (n+1)

/-- The complete-block Buchholz reader output, before the outer collapse. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum A0 (.D 0 (W n b))

theorem iterPhiAt_eq_I : ∀ n : Nat,
    iterPhiAt zero (plus B B) n=I n
  | 0 => rfl
  | n+1 => by
    rw [iterPhiAt,iterPhiAt_eq_I n,I]
    cases n with
    | zero => rfl
    | succ n => exact Rows.ProofsB.phiNF_phi_arg (by rfl)

theorem fA_eq_F (n : Nat) : Rows.Selected.fA n=F n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [Rows.Selected.fA,F,iterPhiAt_eq_I]

theorem I_cnv : ∀ n : Nat, Evidence.WF.CNV (I n)=true
  | 0 => by decide
  | n+1 => by
    show (Evidence.WF.CNV zero && Evidence.WF.CNV (I n))=true
    rw [I_cnv n]
    rfl

theorem I_inT (n : Nat) : inT (I n)=true :=
  Evidence.WF.inT_of_cnv _ (I_cnv n)

theorem I_lt_Z : ∀ n : Nat, lt (I n) Z0=true
  | 0 => by decide
  | n+1 => by
    rw [I]
    unfold lt
    cases h:fuelOf (phi zero (I n)) Z0 with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hi:=Evidence.WF.deg_pos (I n)
      have hz:=Evidence.WF.deg_pos Z0
      have h0:=Evidence.WF.deg_pos zero
      have hf : zero.deg+Z0.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      have hfi : (I n).deg+Z0.deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      constructor
      · exact Evidence.WF.ltF_left_zero (by omega) (by simp)
      · rw [← Evidence.WF.lt_eq_ltF (I n) Z0 f hfi]
        exact I_lt_Z n

theorem I_lt_I_succ (n : Nat) : lt (I n) (I (n+1))=true := by
  rw [I]
  exact Evidence.WF.lt_phi_self (I_cnv n) zero

theorem B_lt_I_succ : ∀ n : Nat, lt B (I (n+1))=true
  | 0 => by decide
  | n+1 => Evidence.WF.lt_trans_inT
      (by decide) (I_inT (n+1)) (I_inT (n+2))
      (B_lt_I_succ n) (I_lt_I_succ (n+1))

theorem I_lt_H (n : Nat) : lt (I n) H=true := by
  exact Evidence.WF.lt_trans_inT (I_inT n) (by decide) (by decide)
    (I_lt_Z n) (by decide)

theorem I_succ_toList (n : Nat) : (I (n+1)).toList=[I (n+1)] := by
  rw [I]
  rfl

theorem plus_H_I_succ (n : Nat) :
    plus H (I (n+1))=add H (I (n+1)) := by
  unfold plus
  rw [show H.toList=[H] from rfl,I_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (I (n+1)) H=true from Evidence.WF.le_of_lt (I_lt_H (n+1))]
  rfl

theorem plus_B_I_succ (n : Nat) : plus B (I (n+1))=I (n+1) := by
  unfold plus
  rw [show B.toList=[B] from rfl,I_succ_toList]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (I (n+1)) B=false from by
    unfold le
    rw [show ((I (n+1)==B))=false from beq_eq_false_iff_ne.mpr
      (Ne.symm (Evidence.WF.ne_of_ltF (B_lt_I_succ n)))]
    simp only [Bool.false_or]
    exact Evidence.WF.lt_asymm_inT (by decide) (I_inT (n+1))
      (B_lt_I_succ n)]
  rfl

theorem omegaNF_I_succ (n : Nat) : omegaNF (I (n+1))=I (n+2) := by
  rw [I,I]
  exact (Rows.ProofsB.omegaNF_phi zero (I n)).trans
    (Rows.ProofsB.phiNF_phi_arg (by rfl))

theorem wcnf_H_I_succ (n : Nat) :
    Trans.Dict.wcnf Z0 [H,I (n+1)]=
      ([(TM.Term.ofNat 3,TM.Term.omega)],I (n+1)) := by
  rw [Trans.Dict.wcnf,if_neg (by decide)]
  simp only [H,Trans.Dict.logOm,TM.Term.phiShifted,TM.Term.splitFin,
    Bool.false_or,Bool.false_eq_true,if_false,TM.Term.toList,List.filter_cons,
    List.filter_nil,List.map_cons,List.map_nil,Trans.Dict.divAP,
    Trans.Dict.subAP,Trans.Dict.wcnf]
  rw [if_pos (I_lt_Z (n+1))]
  rfl

theorem collapse_H_I_succ (n : Nat) :
    Trans.Dict.collapse 0 (plus H (I (n+1)))=I (n+2) := by
  rw [plus_H_I_succ]
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (add H (I (n+1))).toList=[H,I (n+1)] from by
    rw [H,I]
    rfl,wcnf_H_I_succ]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z0 (TM.Term.ofNat 3)=false from by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.sub1 TM.Term.omega=TM.Term.omega from rfl]
  simp only [Option.getD_some]
  rw [show (if (0==0) then zero else plus zero TM.Term.one)=zero from rfl,
    show phiNF (TM.Term.ofNat 3) (plus zero TM.Term.omega)=B from rfl,
    plus_B_I_succ,
    Rows.ProofsB.plus_zero_left (show (I (n+1)).isAP=true from by rw [I]; rfl),
    omegaNF_I_succ]

theorem dict_A0 : Trans.Dict.dict A0=H := rfl

theorem collapse_H_B :
    Trans.Dict.collapse 0 (plus H B)=I 1 := rfl

theorem dict_D0_W : ∀ n : Nat,
    Trans.Dict.dict (.D 0 (W n A0))=F n
  | 0 => rfl
  | n+1 => by
    rw [W,Trans.Dict.dict_D,Trans.Dict.dict_sum,dict_A0,
      dict_D0_W n]
    cases n with
    | zero => exact collapse_H_B
    | succ n => exact collapse_H_I_succ n

theorem dict_D0_W_fA (n : Nat) :
    Trans.Dict.dict (.D 0 (W n A0))=Rows.Selected.fA n := by
  rw [dict_D0_W,← fA_eq_F]

#print axioms dict_D0_W_fA

end Rows.Selected.G9Dict
