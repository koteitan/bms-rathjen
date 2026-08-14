import Rows.G9Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G9

def M : BMS.Matrix := [[0,0],[1,1],[2,1],[2,1],[2,0],[1,1]]
def t : Term := phi (phi zero zero)
  (phi (add (phi zero zero) (add (phi zero zero) (phi zero zero)))
    (phi zero (phi zero zero)))

/-- Row-zero value of the `0,1,1,1,0` five-column tail. -/
def p (k : Nat) : Int :=
  if k%5=0 then ((k/5+1:Nat):Int)
  else if k%5=1 then ((k/5+2:Nat):Int)
  else ((k/5+3:Nat):Int)

/-- Row-one value of the five-column tail. -/
def q (k : Nat) : Int := if k%5=0 ∨ k%5=4 then 0 else 1

def T (m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => (p k,q k)

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS :=
  [(0,0),(1,1),(2,1),(2,1),(2,0)]++T m

abbrev D0z : Trans.Dict.BT := .D 0 .zero
abbrev D1z : Trans.Dict.BT := .D 1 .zero
abbrev D11z : Trans.Dict.BT := .D 1 D1z
abbrev D1ss : Trans.Dict.BT := .D 1 (.sum D1z D1z)
abbrev C : Trans.Dict.BT := .sum D1z (.sum D1z D0z)
abbrev A0 : Trans.Dict.BT := .D 1 C
abbrev Anchor : Trans.Dict.BT := .D 0 A0

/-- A complete block wraps the unfinished suffix in the reader output. -/
def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0,b => b
  | n+1,b => .sum A0 (.D 0 (W n b))

def Part : Nat → Trans.Dict.BT
  | 0 => A0
  | 1 => .sum A0 D0z
  | 2 => .sum A0 (.D 0 D1z)
  | 3 => .sum A0 (.D 0 D11z)
  | _ => .sum A0 (.D 0 D1ss)

/-- Reader output on every one-column prefix of the five-phase ladder. -/
def LBT (m : Nat) : Trans.Dict.BT := .D 0 (W (m/5) (Part (m%5)))

theorem T_succ (m : Nat) : T (m+1)=T m++[(p m,q m)] := by
  unfold T
  rw [List.range_succ,List.map_append]
  rfl

theorem L_succ (m : Nat) : L (m+1)=L m++[(p m,q m)] := by
  unfold L
  rw [T_succ,List.append_assoc]

theorem length_T (m : Nat) : (T m).length=m := by simp [T]

theorem length_L (m : Nat) : (L m).length=m+5 := by simp [L,length_T]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+5 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m++[(p m,q m)]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,1],[2,1],[2,0]]++
      ((List.range n).map fun a =>
        ([[1+a,0],[2+a,1],[3+a,1],[3+a,1],[3+a,0]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*1*1,0+a*0*1],[1+a*1*1,1+a*0*1],
          [2+a*1*1,1+a*0*1],[2+a*1*1,1+a*0*1],
          [2+a*1*1,0+a*0*1]] : BMS.Matrix)).flatten) := rfl
  have hf : (fun a : Nat =>
      ([[0+a*1*1,0+a*0*1],[1+a*1*1,1+a*0*1],
        [2+a*1*1,1+a*0*1],[2+a*1*1,1+a*0*1],
        [2+a*1*1,0+a*0*1]] : BMS.Matrix))=
      fun a => [[a,0],[1+a,1],[2+a,1],[2+a,1],[2+a,0]] := by
    funext a
    simp
  rw [h,hf,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append,List.nil_append]
  have hb : ((fun a : Nat =>
      ([[a,0],[1+a,1],[2+a,1],[2+a,1],[2+a,0]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[1+a,0],[2+a,1],[3+a,1],[3+a,1],[3+a,0]] := by
    funext a
    simp [Function.comp_apply,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  rw [hb]

theorem p_phase0 (a : Nat) : p (5*a)=((a+1:Nat):Int) := by simp [p]
theorem p_phase1 (a : Nat) : p (5*a+1)=((a+2:Nat):Int) := by simp [p]; omega
theorem p_phase2 (a : Nat) : p (5*a+2)=((a+3:Nat):Int) := by simp [p]; omega
theorem p_phase3 (a : Nat) : p (5*a+3)=((a+3:Nat):Int) := by simp [p]; omega
theorem p_phase4 (a : Nat) : p (5*a+4)=((a+3:Nat):Int) := by simp [p]; omega
theorem q_phase0 (a : Nat) : q (5*a)=0 := by simp [q]
theorem q_phase1 (a : Nat) : q (5*a+1)=1 := by simp [q]
theorem q_phase2 (a : Nat) : q (5*a+2)=1 := by simp [q]
theorem q_phase3 (a : Nat) : q (5*a+3)=1 := by simp [q]
theorem q_phase4 (a : Nat) : q (5*a+4)=0 := by simp [q]

theorem T_five_mul (n : Nat) :
    T (5*n)=((List.range n).map fun a =>
      ([(((a+1:Nat):Int),(0:Int)),(((a+2:Nat):Int),(1:Int)),
        (((a+3:Nat):Int),(1:Int)),(((a+3:Nat):Int),(1:Int)),
        (((a+3:Nat):Int),(0:Int))] : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 5*(n+1)=5*n+5 by omega,T_succ,T_succ,T_succ,T_succ,T_succ,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [show 5*n+1=5*n+1 by rfl,show 5*n+2=5*n+2 by rfl,
      show 5*n+3=5*n+3 by rfl,show 5*n+4=5*n+4 by rfl,
      p_phase0 n,q_phase0 n,p_phase1 n,q_phase1 n,p_phase2 n,q_phase2 n,
      p_phase3 n,q_phase3 n,p_phase4 n,q_phase4 n]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[1+a,0],[2+a,1],[3+a,1],[3+a,1],[3+a,0]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=T (5*n) := by
  rw [T_five_mul,List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp
  constructor
  · omega
  · constructor <;> omega

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[1+a,0],[2+a,1],[3+a,1],[3+a,1],[3+a,0]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a five-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (5*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,1],[2,1],[2,0]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[1+a,0],[2+a,1],[3+a,1],[3+a,1],[3+a,0]]:BMS.Matrix)).flatten).isEmpty=false
      from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (5*n))
#guard (List.range 18).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Row-zero parent structure. -/

theorem getD_T (m k : Nat) (hk : k<m) :
    (T m).getD k (0,0)=(p k,q k) := by
  unfold T
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (T m) (k:Int)=p k := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem gp1_T (m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (T m) (k:Int)=q k := by
  show (if (k:Int)<0 then 0 else ((T m).getD k (0,0)).2)=_
  rw [if_neg (by omega),getD_T m k hk]

theorem gp0_L (m k : Nat) (hk : k<m+5) :
    Trans.Recal.gp0 (L m) (k:Int)=
      if k<5 then ([0,1,2,2,2].getD k 0:Int) else p (k-5) := by
  by_cases h5:k<5
  · simp only [if_pos h5]
    have hc:k=0∨k=1∨k=2∨k=3∨k=4:=by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp only [if_neg h5]
    obtain ⟨j,rfl⟩ : ∃ j,k=j+5 := ⟨k-5,by omega⟩
    show (if (((j+5:Nat):Int)<0) then 0 else ((L m).getD (j+5) (0,0)).1)=p j
    rw [if_neg (by omega)]
    change ((T m).getD j (0,0)).1=p j
    rw [getD_T m j (by omega)]

theorem gp1_L (m k : Nat) (hk : k<m+5) :
    Trans.Recal.gp1 (L m) (k:Int)=
      if k<5 then ([0,1,1,1,0].getD k 0:Int) else q (k-5) := by
  by_cases h5:k<5
  · simp only [if_pos h5]
    have hc:k=0∨k=1∨k=2∨k=3∨k=4:=by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> rfl
  · simp only [if_neg h5]
    obtain ⟨j,rfl⟩ : ∃ j,k=j+5 := ⟨k-5,by omega⟩
    show (if (((j+5:Nat):Int)<0) then 0 else ((L m).getD (j+5) (0,0)).2)=q j
    rw [if_neg (by omega)]
    change ((T m).getD j (0,0)).2=q j
    rw [getD_T m j (by omega)]

theorem fpar_L_base_one (m : Nat) : Trans.Recal.fpar (L m) 0 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_two (m : Nat) : Trans.Recal.fpar (L m) 0 2 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_three (m : Nat) : Trans.Recal.fpar (L m) 0 3 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_base_four (m : Nat) : Trans.Recal.fpar (L m) 0 4 0=1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rfl

theorem fpar_L_phase0_zero (m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (L m) 0 5 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) 5) 4 0=0
  rw [show (5:Int)=((5:Nat):Int) from rfl,gp0_L m 5 (by omega),
    if_neg (by omega),p_phase0 0]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) 4=2 from by
      simpa using gp0_L m 4 (by omega),if_neg (by omega),if_neg (by omega),
    show (4:Int)-1=3 by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) 3=2 from by
      simpa using gp0_L m 3 (by omega),if_neg (by omega),if_neg (by omega),
    show (3:Int)-1=2 by omega]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) 2=2 from by
      simpa using gp0_L m 2 (by omega),if_neg (by omega),if_neg (by omega),
    show (2:Int)-1=1 by omega]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) 1=1 from by
      simpa using gp0_L m 1 (by omega),if_neg (by omega),if_neg (by omega),
    show (1:Int)-1=0 by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) 0=0 from by
      simpa using gp0_L m 0 (by omega),if_neg (by omega),if_pos (by omega)]

theorem fpar_L_phase0_succ (a m : Nat) (h : 5*(a+1)<m) :
    Trans.Recal.fpar (L m) 0 ((5*(a+1)+5:Nat):Int) 0=(5*a+5:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((5*(a+1)+5:Nat):Int)-1=((5*a+9:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) ((5*(a+1)+5:Nat):Int)) ((5*a+9:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (L m) ((5*(a+1)+5:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*(a+1)+5) (by omega),if_neg (by omega)]
      simpa only [show 5*(a+1)+5-5=5*(a+1) by omega] using p_phase0 (a+1)]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+9:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+9) (by omega),if_neg (by omega)]
      simpa only [show 5*a+9-5=5*a+4 by omega] using p_phase4 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+9:Nat):Int)-1=((5*a+8:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+8:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+8) (by omega),if_neg (by omega)]
      simpa only [show 5*a+8-5=5*a+3 by omega] using p_phase3 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+8:Nat):Int)-1=((5*a+7:Nat):Int) by omega]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+7) (by omega),if_neg (by omega)]
      simpa only [show 5*a+7-5=5*a+2 by omega] using p_phase2 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+6:Nat):Int)-1=((5*a+5:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (L m) ((5*a+5:Nat):Int)=((a+1:Nat):Int) from by
      rw [gp0_L m (5*a+5) (by omega),if_neg (by omega)]
      simpa only [show 5*a+5-5=5*a by omega] using p_phase0 a,
    if_pos (by omega)]

theorem fpar_L_phase1 (a m : Nat) (h : 5*a+1<m) :
    Trans.Recal.fpar (L m) 0 ((5*a+6:Nat):Int) 0=(5*a+5:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((5*a+6:Nat):Int)-1=((5*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)) ((5*a+5:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (L m) ((5*a+5:Nat):Int)=((a+1:Nat):Int) from by
      rw [gp0_L m (5*a+5) (by omega),if_neg (by omega)]
      simpa only [show 5*a+5-5=5*a by omega] using p_phase0 a,
    if_pos (by omega)]

theorem fpar_L_phase2 (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.fpar (L m) 0 ((5*a+7:Nat):Int) 0=(5*a+6:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)) ((5*a+6:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+7) (by omega),if_neg (by omega)]
      simpa only [show 5*a+7-5=5*a+2 by omega] using p_phase2 a]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a,
    if_pos (by omega)]

theorem fpar_L_phase3 (a m : Nat) (h : 5*a+3<m) :
    Trans.Recal.fpar (L m) 0 ((5*a+8:Nat):Int) 0=(5*a+6:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((5*a+8:Nat):Int)-1=((5*a+7:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) ((5*a+8:Nat):Int)) ((5*a+7:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (L m) ((5*a+8:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+8) (by omega),if_neg (by omega)]
      simpa only [show 5*a+8-5=5*a+3 by omega] using p_phase3 a]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+7) (by omega),if_neg (by omega)]
      simpa only [show 5*a+7-5=5*a+2 by omega] using p_phase2 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a,
    if_pos (by omega)]

theorem fpar_L_phase4 (a m : Nat) (h : 5*a+4<m) :
    Trans.Recal.fpar (L m) 0 ((5*a+9:Nat):Int) 0=(5*a+6:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),length_L]
  rw [show ((5*a+9:Nat):Int)-1=((5*a+8:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+6) (L m)
    (Trans.Recal.gp0 (L m) ((5*a+9:Nat):Int)) ((5*a+8:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (L m) ((5*a+9:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+9) (by omega),if_neg (by omega)]
      simpa only [show 5*a+9-5=5*a+4 by omega] using p_phase4 a]
  rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+8:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+8) (by omega),if_neg (by omega)]
      simpa only [show 5*a+8-5=5*a+3 by omega] using p_phase3 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+8:Nat):Int)-1=((5*a+7:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+7) (by omega),if_neg (by omega)]
      simpa only [show 5*a+7-5=5*a+2 by omega] using p_phase2 a,
    if_neg (by omega),if_neg (by omega),
    show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a,
    if_pos (by omega)]

def parentL (k : Nat) : Nat :=
  if k=0 then 0 else if k=1 then 0 else if k<5 then 1
  else
    let j:=k-5
    if j%5=0 then if j=0 then 0 else k-5
    else if j%5=1 ∨ j%5=2 then k-1
    else if j%5=3 then k-2 else k-3

theorem parentL_lt (k : Nat) (hk : 0<k) : parentL k<k := by
  unfold parentL
  split <;> rename_i h0
  · omega
  split <;> rename_i h1
  · omega
  split <;> rename_i h5
  · omega
  dsimp only
  split <;> rename_i hp0
  · split <;> omega
  split <;> rename_i hp12
  · omega
  split <;> omega

theorem parentL_phase0_zero : parentL 5=0 := rfl
theorem parentL_phase0_succ (a : Nat) :
    parentL (5*(a+1)+5)=5*a+5 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_pos (by simp),if_neg (by omega)]
  omega
theorem parentL_phase1 (a : Nat) : parentL (5*a+6)=5*a+5 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_pos (by omega)]
  omega
theorem parentL_phase2 (a : Nat) : parentL (5*a+7)=5*a+6 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_pos (by omega)]
  omega
theorem parentL_phase3 (a : Nat) : parentL (5*a+8)=5*a+6 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  omega
theorem parentL_phase4 (a : Nat) : parentL (5*a+9)=5*a+6 := by
  unfold parentL
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  dsimp only
  rw [if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  omega

theorem fpar_L_parent (m k : Nat) (hk0 : 0<k) (hk : k<m+5) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0=(parentL k:Nat) := by
  by_cases h5:k<5
  · have hc:k=0∨k=1∨k=2∨k=3∨k=4:=by omega
    rcases hc with h0|h1|h2|h3|h4
    · omega
    · subst k
      change Trans.Recal.fpar (L m) 0 1 0=0
      exact fpar_L_base_one m
    · subst k
      change Trans.Recal.fpar (L m) 0 2 0=1
      exact fpar_L_base_two m
    · subst k
      change Trans.Recal.fpar (L m) 0 3 0=1
      exact fpar_L_base_three m
    · subst k
      change Trans.Recal.fpar (L m) 0 4 0=1
      exact fpar_L_base_four m
  · obtain ⟨j,rfl⟩ : ∃ j,k=j+5 := ⟨k-5,by omega⟩
    have hj : j<m := by omega
    have hm : j%5=0 ∨ j%5=1 ∨ j%5=2 ∨ j%5=3 ∨ j%5=4 := by omega
    rcases hm with h0|h1|h2|h3|h4
    · have heq:j=5*(j/5):=by omega
      by_cases jz:j=0
      · subst j
        simpa [parentL] using fpar_L_phase0_zero m hj
      · have ha : 5*((j/5-1)+1)<m := by omega
        have hf:=fpar_L_phase0_succ (j/5-1) m ha
        rw [heq]
        have hp : parentL (5*(j/5)+5)=5*(j/5-1)+5 := by
          simpa only [show 5*(j/5)+5=5*((j/5-1)+1)+5 by omega] using
            parentL_phase0_succ (j/5-1)
        rw [hp]
        simpa only [show j/5-1+1=j/5 by omega] using hf
    · have heq:j=5*(j/5)+1:=by omega
      rw [heq]
      rw [show 5*(j/5)+1+5=5*(j/5)+6 by omega]
      rw [parentL_phase1]
      exact fpar_L_phase1 (j/5) m (by omega)
    · have heq:j=5*(j/5)+2:=by omega
      rw [heq]
      rw [show 5*(j/5)+2+5=5*(j/5)+7 by omega]
      rw [parentL_phase2]
      exact fpar_L_phase2 (j/5) m (by omega)
    · have heq:j=5*(j/5)+3:=by omega
      rw [heq]
      rw [show 5*(j/5)+3+5=5*(j/5)+8 by omega]
      rw [parentL_phase3]
      exact fpar_L_phase3 (j/5) m (by omega)
    · have heq:j=5*(j/5)+4:=by omega
      rw [heq]
      rw [show 5*(j/5)+4+5=5*(j/5)+9 by omega]
      rw [parentL_phase4]
      exact fpar_L_phase4 (j/5) m (by omega)

theorem isAncAux_L (m k : Nat) : ∀ f : Nat, k<m+5 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k=>∀ f:Nat,k<m+5→k<f→
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_L_parent m k (by omega) hkm]
      rw [show (((parentL k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hp:=parentL_lt k (by omega)
      exact ih (parentL k) hp f (by omega) (by omega)

theorem isAnc_L (m k : Nat) (hk : k<m+5) :
    Trans.Recal.isAnc (L m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  exact isAncAux_L m k (m+6) hk (by omega)

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  rw [show Trans.Recal.lenI (L m)-1=((m+4:Nat):Int) from by rw [lenI_L]; omega]
  exact isAnc_L m (m+4) (by omega)

/-! ### Principal decomposition of the periodic tail. -/

theorem lenI_T (m : Nat) : Trans.Recal.lenI (T m)=(m:Int) := by
  unfold Trans.Recal.lenI
  rw [length_T]

theorem fpar_T_phase0 (a m : Nat) (h : 5*(a+1)<m) :
    Trans.Recal.fpar (T m) 0 ((5*(a+1):Nat):Int) 0=(5*a:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((5*(a+1):Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((5*(a+1):Nat):Int)) ((5*a+4:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (T m) ((5*(a+1):Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase0 (a+1)] using gp0_T m (5*(a+1)) h]
  rw [show m+1=m+1 by rfl,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (T m) ((5*a+4:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase4 a] using gp0_T m (5*a+4) (by omega),
    if_neg (by omega),if_neg (by omega),
    show ((5*a+4:Nat):Int)-1=((5*a+3:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show m-1+1=m by omega]
  rw [show Trans.Recal.gp0 (T m) ((5*a+3:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase3 a] using gp0_T m (5*a+3) (by omega),
    if_neg (by omega),if_neg (by omega),
    show ((5*a+3:Nat):Int)-1=((5*a+2:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (T m) ((5*a+2:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase2 a] using gp0_T m (5*a+2) (by omega),
    if_neg (by omega),if_neg (by omega),
    show ((5*a+2:Nat):Int)-1=((5*a+1:Nat):Int) by omega]
  rw [show m-2=(m-3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase1 a] using gp0_T m (5*a+1) (by omega),
    if_neg (by omega),if_neg (by omega),
    show ((5*a+1:Nat):Int)-1=((5*a:Nat):Int) by omega]
  rw [show m-3=(m-4)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (T m) ((5*a:Nat):Int)=((a+1:Nat):Int) from by
      simpa only [p_phase0 a] using gp0_T m (5*a) (by omega),if_pos (by omega)]

theorem fpar_T_phase1 (a m : Nat) (h : 5*a+1<m) :
    Trans.Recal.fpar (T m) 0 ((5*a+1:Nat):Int) 0=(5*a:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((5*a+1:Nat):Int)-1=((5*a:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)) ((5*a:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase1 a] using gp0_T m (5*a+1) h,
    Trans.Recal.fpar0Aux,if_neg (by omega),
    show Trans.Recal.gp0 (T m) ((5*a:Nat):Int)=((a+1:Nat):Int) from by
      simpa only [p_phase0 a] using gp0_T m (5*a) (by omega),if_pos (by omega)]

theorem fpar_T_phase2 (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.fpar (T m) 0 ((5*a+2:Nat):Int) 0=(5*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((5*a+2:Nat):Int)-1=((5*a+1:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((5*a+2:Nat):Int)) ((5*a+1:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (T m) ((5*a+2:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase2 a] using gp0_T m (5*a+2) h,
    Trans.Recal.fpar0Aux,if_neg (by omega),
    show Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase1 a] using gp0_T m (5*a+1) (by omega),if_pos (by omega)]

theorem fpar_T_phase3 (a m : Nat) (h : 5*a+3<m) :
    Trans.Recal.fpar (T m) 0 ((5*a+3:Nat):Int) 0=(5*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((5*a+3:Nat):Int)-1=((5*a+2:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((5*a+3:Nat):Int)) ((5*a+2:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (T m) ((5*a+3:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase3 a] using gp0_T m (5*a+3) h]
  rw [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),
    show Trans.Recal.gp0 (T m) ((5*a+2:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase2 a] using gp0_T m (5*a+2) (by omega),
    if_neg (by omega),
    show ((5*a+2:Nat):Int)-1=((5*a+1:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show m-1+1=m by omega]
  rw [if_neg (by omega),show Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase1 a] using gp0_T m (5*a+1) (by omega),if_pos (by omega)]

theorem fpar_T_phase4 (a m : Nat) (h : 5*a+4<m) :
    Trans.Recal.fpar (T m) 0 ((5*a+4:Nat):Int) 0=(5*a+1:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl),length_T]
  rw [show ((5*a+4:Nat):Int)-1=((5*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+1) (T m)
    (Trans.Recal.gp0 (T m) ((5*a+4:Nat):Int)) ((5*a+3:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (T m) ((5*a+4:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase4 a] using gp0_T m (5*a+4) h]
  rw [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),
    show Trans.Recal.gp0 (T m) ((5*a+3:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase3 a] using gp0_T m (5*a+3) (by omega),
    if_neg (by omega),
    show ((5*a+3:Nat):Int)-1=((5*a+2:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show m-1+1=m by omega]
  rw [show Trans.Recal.gp0 (T m) ((5*a+2:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [p_phase2 a] using gp0_T m (5*a+2) (by omega),
    if_neg (by omega),if_neg (by omega),
    show ((5*a+2:Nat):Int)-1=((5*a+1:Nat):Int) by omega]
  rw [show m-1=(m-2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (T m) ((5*a+1:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase1 a] using gp0_T m (5*a+1) (by omega),if_pos (by omega)]

def parentT (k : Nat) : Nat :=
  if k%5=0 then k-5 else if k%5=1 ∨ k%5=2 then k-1
  else if k%5=3 then k-2 else k-3

theorem parentT_lt (k : Nat) (hk : 0<k) : parentT k<k := by
  unfold parentT
  split <;> rename_i h0
  · have : 5≤k := by omega
    omega
  split <;> rename_i h12
  · omega
  split <;> rename_i h3
  · have : 2≤k := by omega
    omega
  · have : 3≤k := by omega
    omega

theorem fpar_T_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (T m) 0 (k:Int) 0=(parentT k:Nat) := by
  have hm : k%5=0 ∨ k%5=1 ∨ k%5=2 ∨ k%5=3 ∨ k%5=4 := by omega
  rcases hm with h0|h1|h2|h3|h4
  · have heq : k=5*((k/5-1)+1) := by omega
    rw [heq]
    rw [show parentT (5*((k/5-1)+1))=5*(k/5-1) from by
      simp [parentT]; omega]
    exact fpar_T_phase0 (k/5-1) m (by omega)
  · have heq : k=5*(k/5)+1 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+1)=5*(k/5) from by simp [parentT]]
    exact fpar_T_phase1 (k/5) m (by omega)
  · have heq : k=5*(k/5)+2 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+2)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_T_phase2 (k/5) m (by omega)
  · have heq : k=5*(k/5)+3 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+3)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_T_phase3 (k/5) m (by omega)
  · have heq : k=5*(k/5)+4 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+4)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_T_phase4 (k/5) m (by omega)

theorem isAncAux_T (k : Nat) : ∀ m f : Nat, k<m → k<f →
    Trans.Recal.isAncAux f (T m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, k<m → k<f →
    Trans.Recal.isAncAux f (T m) 0 (k:Int) 0=true) k ?_
  intro k ih m f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · have hkpos:0<k:=by omega
      rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_T_pos m k hkpos hkm]
      rw [show (((parentT k:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf))

theorem isAnc_T (m k : Nat) (hk : k<m) :
    Trans.Recal.isAnc (T m) 0 (k:Int) 0=true := by
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_T]; omega),length_T]
  exact isAncAux_T k m (m+1) hk (by omega)

theorem fAncAux_T_last (k : Nat) : ∀ m f : Nat, ∀ acc : List Int,
    k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (T m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (T m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      have hp:Trans.Recal.fpar (T m) 0 0 0=-1:=by
        unfold Trans.Recal.fpar
        rw [if_neg (by rw [lenI_T]; omega),if_pos (by rfl)]
        simp only [Trans.Recal.fpar0Aux]
        rw [if_pos (by omega)]
      rw [show ((0:Nat):Int)=0 from rfl,hp,if_neg (by omega)]
      exact hlast
    · have hkpos:0<k:=by omega
      rw [fpar_T_pos m k hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f (acc++[((parentT k:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm)
        (Nat.lt_of_lt_of_le hpk (Nat.le_of_lt_succ hkf)) (by simp)

theorem fAnc_T_last (m : Nat) (hm : 0<m) :
    (Trans.Recal.fAnc (T m) 0 ((m-1:Nat):Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_T]; omega),length_T]
  exact fAncAux_T_last (m-1) m (m+1) [((m-1:Nat):Int)]
    (by omega) (by omega) (by simp)

theorem slice_T_full (m : Nat) :
    Trans.Recal.slice (T m) 0 (m:Int)=T m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show ((m:Int)-0).toNat=m from by omega]
  simpa only [length_T] using (List.take_length (l:=T m))

theorem ppair_T : ∀ m : Nat,
    Trans.Recal.ppair (T m)=if m=0 then [] else [T m]
  | 0 => rfl
  | m+1 => by
    unfold Trans.Recal.ppair
    rw [length_T]
    simp only [show ¬m+1=0 by omega,if_false,Trans.Recal.ppairAux]
    rw [show Trans.Recal.lenI (T (m+1))-1=(m:Int) by rw [lenI_T]; omega,
      if_neg (by omega)]
    have hf:(Trans.Recal.fAnc (T (m+1)) 0 (m:Int) 0).getLast?=some 0 := by
      simpa only [Nat.add_sub_cancel] using fAnc_T_last (m+1) (by omega)
    rw [hf]
    simp only [Option.getD_some]
    rw [show (0:Int)-1=-1 by omega,if_pos (by omega),
      show (m:Int)+1=((m+1:Nat):Int) by omega,slice_T_full]

/-! ### Reduction structure of the complete ladder. -/

def R (m : Nat) : Trans.Recal.PS := [(2,1),(2,1),(2,0)]++T m

theorem length_R (m : Nat) : (R m).length=m+3 := by simp [R,length_T]

theorem lenI_R (m : Nat) : Trans.Recal.lenI (R m)=(m:Int)+3 := by
  unfold Trans.Recal.lenI
  rw [length_R]
  omega

theorem drop_two_L (m : Nat) : (L m).drop 2=R m := rfl

theorem fpar0_L_one (m : Nat) : Trans.Recal.fpar0 (L m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_two (m : Nat) : Trans.Recal.fpar0 (L m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_one_lb (m : Nat) : Trans.Recal.fpar0 (L m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_one (m : Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 1 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+4) (L m) 1 j1 0)=0
  rw [fpar0_L_one]
  rfl

theorem fpar1_L_two_lb (m : Nat) : Trans.Recal.fpar (L m) 1 2 1=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 2 1
    if j1<1 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+6) (L m) 1 j1 1)=-1
  rw [fpar0_L_two]
  simp only [show ¬((1:Int)<1) by omega,if_false]
  rw [show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_one_lb,if_pos (by omega)]

theorem trMax_L (m : Nat) : Trans.Recal.trMax (L m)=1 := by
  show Trans.Recal.trMaxAux ((L m).length+1) (L m) 0=1
  rw [length_L]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1) 0=0 from by simpa using fpar1_L_one m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)<((m+5:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1) (0+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1) (0+1)=-1 from by
      simpa using fpar1_L_two_lb m]
    simp,if_pos (by rfl)]
  omega

theorem gp0_R_tail (m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (R m) ((k+3:Nat):Int)=p k := by
  show (if (((k+3:Nat):Int)<0) then 0 else ((R m).getD (k+3) (0,0)).1)=p k
  rw [if_neg (by omega)]
  change ((T m).getD k (0,0)).1=p k
  rw [getD_T m k hk]

theorem fpar_R_root (m : Nat) (hm : 0<m) :
    Trans.Recal.fpar (R m) 0 3 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 3=1 from by
    simpa only [p_phase0 0] using gp0_R_tail m 0 hm]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (3:Int)-1=2 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 2=2 from rfl,if_neg (by omega),
    show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 1=2 from rfl,if_neg (by omega),
    show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fpar_R_phase0 (a m : Nat) (h : 5*(a+1)<m) :
    Trans.Recal.fpar (R m) 0 ((5*(a+1)+3:Nat):Int) 0=(5*a+3:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show ((5*(a+1)+3:Nat):Int)-1=((5*a+7:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+4) (R m)
    (Trans.Recal.gp0 (R m) ((5*(a+1)+3:Nat):Int)) ((5*a+7:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (R m) ((5*(a+1)+3:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [p_phase0 (a+1)] using gp0_R_tail m (5*(a+1)) h]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+7=5*a+4+3 by omega,p_phase4 a] using
        gp0_R_tail m (5*a+4) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+6:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+6=5*a+3+3 by omega,p_phase3 a] using
        gp0_R_tail m (5*a+3) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+6:Nat):Int)-1=((5*a+5:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+5:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+5=5*a+2+3 by omega,p_phase2 a] using
        gp0_R_tail m (5*a+2) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  rw [show m+1=m+1 by rfl,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [show 5*a+4=5*a+1+3 by omega,p_phase1 a] using
        gp0_R_tail m (5*a+1) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+4:Nat):Int)-1=((5*a+3:Nat):Int) by omega]
  rw [show m=(m-1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show m-1+1=m by omega]
  rw [if_neg (by omega),show Trans.Recal.gp0 (R m) ((5*a+3:Nat):Int)=((a+1:Nat):Int) from by
      simpa only [show 5*a+3=5*a+3 by rfl,p_phase0 a] using
        gp0_R_tail m (5*a) (by omega),if_pos (by omega)]

theorem fpar_R_phase1 (a m : Nat) (h : 5*a+1<m) :
    Trans.Recal.fpar (R m) 0 ((5*a+4:Nat):Int) 0=(5*a+3:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show ((5*a+4:Nat):Int)-1=((5*a+3:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+4) (R m)
    (Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)) ((5*a+3:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [show 5*a+4=5*a+1+3 by omega,p_phase1 a] using
        gp0_R_tail m (5*a+1) h,
    Trans.Recal.fpar0Aux,if_neg (by omega),
    show Trans.Recal.gp0 (R m) ((5*a+3:Nat):Int)=((a+1:Nat):Int) from by
      simpa only [p_phase0 a] using gp0_R_tail m (5*a) (by omega),if_pos (by omega)]

theorem fpar_R_phase2 (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.fpar (R m) 0 ((5*a+5:Nat):Int) 0=(5*a+4:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+4) (R m)
    (Trans.Recal.gp0 (R m) ((5*a+5:Nat):Int)) ((5*a+4:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (R m) ((5*a+5:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+5=5*a+2+3 by omega,p_phase2 a] using
        gp0_R_tail m (5*a+2) h,
    Trans.Recal.fpar0Aux,if_neg (by omega),
    show Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [show 5*a+4=5*a+1+3 by omega,p_phase1 a] using
        gp0_R_tail m (5*a+1) (by omega),if_pos (by omega)]

theorem fpar_R_phase3 (a m : Nat) (h : 5*a+3<m) :
    Trans.Recal.fpar (R m) 0 ((5*a+6:Nat):Int) 0=(5*a+4:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show ((5*a+6:Nat):Int)-1=((5*a+5:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+4) (R m)
    (Trans.Recal.gp0 (R m) ((5*a+6:Nat):Int)) ((5*a+5:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (R m) ((5*a+6:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+6=5*a+3+3 by omega,p_phase3 a] using
        gp0_R_tail m (5*a+3) h]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+5:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+5=5*a+2+3 by omega,p_phase2 a] using
        gp0_R_tail m (5*a+2) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [show 5*a+4=5*a+1+3 by omega,p_phase1 a] using
        gp0_R_tail m (5*a+1) (by omega),if_pos (by omega)]

theorem fpar_R_phase4 (a m : Nat) (h : 5*a+4<m) :
    Trans.Recal.fpar (R m) 0 ((5*a+7:Nat):Int) 0=(5*a+4:Nat) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega]
  change Trans.Recal.fpar0Aux (m+4) (R m)
    (Trans.Recal.gp0 (R m) ((5*a+7:Nat):Int)) ((5*a+6:Nat):Int) 0=_
  rw [show Trans.Recal.gp0 (R m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+7=5*a+4+3 by omega,p_phase4 a] using
        gp0_R_tail m (5*a+4) h]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+6:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+6=5*a+3+3 by omega,p_phase3 a] using
        gp0_R_tail m (5*a+3) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+6:Nat):Int)-1=((5*a+5:Nat):Int) by omega]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.fpar0Aux]
  rw [show Trans.Recal.gp0 (R m) ((5*a+5:Nat):Int)=((a+3:Nat):Int) from by
      simpa only [show 5*a+5=5*a+2+3 by omega,p_phase2 a] using
        gp0_R_tail m (5*a+2) (by omega),if_neg (by omega),if_neg (by omega),
    show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show Trans.Recal.gp0 (R m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) from by
      simpa only [show 5*a+4=5*a+1+3 by omega,p_phase1 a] using
        gp0_R_tail m (5*a+1) (by omega),if_pos (by omega)]

theorem fpar_R_tail_pos (m k : Nat) (hk0 : 0<k) (hk : k<m) :
    Trans.Recal.fpar (R m) 0 ((k+3:Nat):Int) 0=((parentT k+3:Nat):Int) := by
  have hm : k%5=0 ∨ k%5=1 ∨ k%5=2 ∨ k%5=3 ∨ k%5=4 := by omega
  rcases hm with h0|h1|h2|h3|h4
  · have heq : k=5*((k/5-1)+1) := by omega
    rw [heq]
    rw [show parentT (5*((k/5-1)+1))=5*(k/5-1) from by
      simp [parentT]; omega]
    exact fpar_R_phase0 (k/5-1) m (by omega)
  · have heq : k=5*(k/5)+1 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+1)=5*(k/5) from by simp [parentT]]
    exact fpar_R_phase1 (k/5) m (by omega)
  · have heq : k=5*(k/5)+2 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+2)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_R_phase2 (k/5) m (by omega)
  · have heq : k=5*(k/5)+3 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+3)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_R_phase3 (k/5) m (by omega)
  · have heq : k=5*(k/5)+4 := by omega
    rw [heq]
    rw [show parentT (5*(k/5)+4)=5*(k/5)+1 from by simp [parentT]]
    exact fpar_R_phase4 (k/5) m (by omega)

theorem fAncAux_R_tail_last (k : Nat) : ∀ m f : Nat, ∀ acc : List Int,
    k<m → k+3<f → acc.getLast?=some ((k+3:Nat):Int) →
    (Trans.Recal.fAncAux f (R m) 0 ((k+3:Nat):Int) 0 acc).getLast?=some 3 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ m f:Nat, ∀ acc:List Int,
    k<m → k+3<f → acc.getLast?=some ((k+3:Nat):Int) →
    (Trans.Recal.fAncAux f (R m) 0 ((k+3:Nat):Int) 0 acc).getLast?=some 3) k ?_
  intro k ih m f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show ((0+3:Nat):Int)=3 from by omega,fpar_R_root m (by omega),
        if_neg (by omega)]
      simpa using hlast
    · have hkpos:0<k:=by omega
      rw [fpar_R_tail_pos m k hkpos hkm,if_pos (by omega)]
      have hpk:=parentT_lt k hkpos
      exact ih (parentT k) hpk m f
        (acc++[((parentT k+3:Nat):Int)])
        (by exact Nat.lt_trans hpk hkm) (by omega) (by simp)

theorem fAnc_R_tail_last (m : Nat) (hm : 0<m) :
    (Trans.Recal.fAnc (R m) 0 ((m+2:Nat):Int) 0).getLast?=some 3 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  have h:=fAncAux_R_tail_last (m-1) m (m+4) [((m-1+3:Nat):Int)]
    (by omega) (by omega) (by simp)
  simpa only [show m-1+3=m+2 by omega] using h

theorem slice_R_tail (m : Nat) :
    Trans.Recal.slice (R m) 3 ((m+3:Nat):Int)=T m := by
  unfold Trans.Recal.slice R
  change (T m).take ((((m+3:Nat):Int)-3).toNat)=T m
  rw [show ((((m+3:Nat):Int)-3).toNat)=m by omega]
  simpa only [length_T] using (List.take_length (l:=T m))

theorem fpar_R_zero (m : Nat) : Trans.Recal.fpar (R m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar_R_one (m : Nat) : Trans.Recal.fpar (R m) 0 1 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 1=2 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fpar_R_two (m : Nat) : Trans.Recal.fpar (R m) 0 2 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_R]; omega),if_pos (by rfl),length_R]
  rw [show Trans.Recal.gp0 (R m) 2=2 from rfl]
  simp only [Trans.Recal.fpar0Aux]
  rw [show (2:Int)-1=1 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 1=2 from rfl,if_neg (by omega),
    show (1:Int)-1=0 by omega,if_neg (by omega),
    show Trans.Recal.gp0 (R m) 0=2 from rfl,if_neg (by omega),
    show (0:Int)-1=-1 by omega,if_pos (by omega)]

theorem fAnc_R_zero (m : Nat) : Trans.Recal.fAnc (R m) 0 0 0=[0] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_zero,if_neg (by omega)]

theorem fAnc_R_one (m : Nat) : Trans.Recal.fAnc (R m) 0 1 0=[1] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_one,if_neg (by omega)]

theorem fAnc_R_two (m : Nat) : Trans.Recal.fAnc (R m) 0 2 0=[2] := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_R]; omega),length_R]
  simp only [Trans.Recal.fAncAux]
  rw [fpar_R_two,if_neg (by omega)]

theorem slice_R_zero (m : Nat) : Trans.Recal.slice (R m) 0 1=[(2,1)] := by rfl
theorem slice_R_one (m : Nat) : Trans.Recal.slice (R m) 1 2=[(2,1)] := by rfl
theorem slice_R_two (m : Nat) : Trans.Recal.slice (R m) 2 3=[(2,0)] := by rfl

theorem ppair_R_zero : Trans.Recal.ppair (R 0)=[[(2,1)],[(2,1)],[(2,0)]] := by
  decide

theorem ppair_R_succ (m : Nat) :
    Trans.Recal.ppair (R (m+1))=[[(2,1)],[(2,1)],[(2,0)],T (m+1)] := by
  unfold Trans.Recal.ppair
  rw [length_R,lenI_R]
  rw [show m+1+3+1=m+5 by omega]
  rw [show ((m+1:Nat):Int)+3-1=((m+3:Nat):Int) by omega]
  rw [show m+5=(m+4)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega)]
  dsimp only
  have hf : (Trans.Recal.fAnc (R (m+1)) 0 ((m+3:Nat):Int) 0).getLast?=some 3 := by
    simpa only [show m+1+2=m+3 by omega] using
      fAnc_R_tail_last (m+1) (by omega)
  rw [hf]
  simp only [Option.getD_some]
  have hs : Trans.Recal.slice (R (m+1)) 3 (((m+3:Nat):Int)+1)=T (m+1) := by
    simpa only [show ((m+3:Nat):Int)+1=((m+1+3:Nat):Int) by omega] using
      slice_R_tail (m+1)
  rw [show (3:Int)-1=2 by omega,hs]
  rw [show m+4=(m+3)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_two]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (2:Int)-1=1 by omega,show (2:Int)+1=3 by omega,slice_R_two]
  rw [show m+3=(m+2)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_one]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (1:Int)-1=0 by omega,show (1:Int)+1=2 by omega,slice_R_one]
  rw [show m+2=(m+1)+1 by omega,Trans.Recal.ppairAux,if_neg (by omega),
    fAnc_R_zero]
  simp only [List.getLast?_singleton,Option.getD_some]
  rw [show (0:Int)-1=-1 by omega,show (0:Int)+1=1 by omega,slice_R_zero]
  rw [Trans.Recal.ppairAux,if_pos (by omega)]

theorem brF_L_zero :
    Trans.Recal.brF (L 0)=[[(2,1)],[(2,1)],[(2,0)]] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  change Trans.Recal.ppair ((L 0).drop 2)=_
  rw [drop_two_L]
  exact ppair_R_zero

theorem brF_L_succ (m : Nat) :
    Trans.Recal.brF (L (m+1))=[[(2,1)],[(2,1)],[(2,0)],T (m+1)] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  change Trans.Recal.ppair ((L (m+1)).drop 2)=_
  rw [drop_two_L]
  exact ppair_R_succ m

theorem firstNodes_L_zero : Trans.Recal.firstNodes (L 0)=[2,3,4,5] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L_zero,trMax_L]
  rfl

theorem firstNodes_L_succ (m : Nat) :
    Trans.Recal.firstNodes (L (m+1))=[2,3,4,5,((m+6:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L_succ,trMax_L]
  simp only [List.foldl_cons,List.foldl_nil,length_T,List.map_cons,List.map_nil]
  simp
  push_cast
  omega

theorem joints_L_zero : Trans.Recal.joints (L 0)=[1,1,1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L_zero]
  change [Trans.Recal.fpar (L 0) 0 2 0,Trans.Recal.fpar (L 0) 0 3 0,
    Trans.Recal.fpar (L 0) 0 4 0]=[1,1,1]
  rw [fpar_L_base_two,fpar_L_base_three,fpar_L_base_four]

theorem joints_L_succ (m : Nat) :
    Trans.Recal.joints (L (m+1))=[1,1,1,0] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L_succ]
  change [Trans.Recal.fpar (L (m+1)) 0 2 0,
    Trans.Recal.fpar (L (m+1)) 0 3 0,
    Trans.Recal.fpar (L (m+1)) 0 4 0,
    Trans.Recal.fpar (L (m+1)) 0 5 0]=[1,1,1,0]
  rw [fpar_L_base_two,fpar_L_base_three,fpar_L_base_four,
    fpar_L_phase0_zero (m+1) (by omega)]

theorem fpar1_L_two (m : Nat) : Trans.Recal.fpar (L m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 2=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 2 0=1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rfl]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from rfl,if_pos (by omega)]

theorem fpar1_L_three (m : Nat) : Trans.Recal.fpar (L m) 1 3 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 3=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 3 0=1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rfl]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),
    show Trans.Recal.gp1 (L m) 0=0 from rfl,if_pos (by omega)]

/-! ### Period-five reduction. -/

def S (m : Nat) : Trans.Recal.PS := Trans.Recal.incrFirst (T m) (-1)

theorem p_add_five (k : Nat) : p (k+5)=p k+1 := by
  unfold p
  rw [show (k+5)%5=k%5 by omega,show (k+5)/5=k/5+1 by omega]
  split <;> rename_i h0
  · push_cast
    omega
  split <;> push_cast <;> omega

theorem q_add_five (k : Nat) : q (k+5)=q k := by
  unfold q
  rw [show (k+5)%5=k%5 by omega]

theorem S_succ (m : Nat) : S (m+1)=S m++[(p m-1,q m)] := by
  unfold S Trans.Recal.incrFirst
  rw [T_succ,List.map_append]
  rfl

theorem S_zero : S 0=[] := rfl
theorem S_one : S 1=Trans.Recal.zeroPS := rfl
theorem S_two : S 2=G1.LG 0 := rfl
theorem S_three : S 3=G1.LG 1 := rfl
theorem S_four : S 4=G1.LG 2 := rfl

theorem S_add_five : ∀ m : Nat, S (m+5)=L m
  | 0 => rfl
  | m+1 => by
    rw [show m+1+5=(m+5)+1 by omega,S_succ,S_add_five m,L_succ]
    congr 1
    apply congrArg (fun x => [x])
    apply Prod.ext
    · rw [p_add_five]
      omega
    · exact q_add_five m

theorem red_LG (m f : Nat) :
    Trans.Recal.red (f+3) (G1.LG m)=G1.LG m := by
  cases m with
  | zero =>
    simpa only [show f+3=(f+2)+1 by omega] using G8.red_A_zero_two (f+2)
  | succ m =>
    rw [show f+3=(f+2)+1 by omega,Trans.Recal.red]
    rw [show Trans.Recal.isZeroP (G1.LG (m+1))=false from by
          unfold Trans.Recal.isZeroP
          rw [G1.len_LG]
          simp,
      G1.isPrincipalP_LG]
    simp only [Bool.false_eq_true,if_false,if_true]
    rw [show (Trans.Recal.gp0 (G1.LG (m+1)) 0==0 &&
        Trans.Recal.gp1 (G1.LG (m+1)) 0==0)=true from by rfl]
    simp only [if_true,G1.trMax_LG,G1.lenI_LG]
    rw [show ((1:Int)==(((m+1:Nat):Int)+2-1))=false from
      beq_eq_false_iff_ne.mpr (by omega)]
    simp only [Bool.false_eq_true,if_false,G1.brF_LG,G1.firstNodes_LG,
      G1.joints_LG,List.length_replicate]
    rw [show ((List.range (m+1)).foldl
        (init:=Trans.Recal.jjSeq 0 1)
        (fun (r:Trans.Recal.PS) (J:Nat) =>
          let bJ:=(List.replicate (m+1) [G1.CC]).getD J []
          let nJ:Int:=if Trans.Recal.gp1 bJ 0==0 then -1 else
            Trans.Recal.fpar (G1.LG (m+1)) 1
              (((List.range (m+2)).map fun k:Nat=>(k:Int)+2).getD J 0) 0
          let jnJ:=(List.replicate (m+1) (1:Int)).getD J 0
          let NJ:Trans.Recal.PS:=(jnJ+1,nJ+1)::Trans.Recal.derp bJ
          r++Trans.Recal.incrFirst (Trans.Recal.red (f+2) NJ) (jnJ-nJ)))=
        (List.range (m+1)).foldl (fun r (_:Nat)=>r++[G1.CC])
          (Trans.Recal.jjSeq 0 1) from by
      refine G1.foldl_congr_mem _ _ _ _ (fun J hJ r=>?_)
      have hJ':J<m+1:=List.mem_range.mp hJ
      rw [G1.getD_repl (m+1) J [G1.CC] [] hJ',
        G1.getD_repl (m+1) J (1:Int) 0 hJ',
        G1.getD_map_range (m+2) J (fun k:Nat=>(k:Int)+2) (by omega)]
      dsimp only
      rw [show (Trans.Recal.gp1 [G1.CC] 0==0)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      rw [G1.fpar_LG_1_e (m+1) ((J:Int)+2) (by omega) (by push_cast; omega)]
      change r++Trans.Recal.incrFirst (Trans.Recal.red (f+2) G1.X1) 1=_
      rw [G1.red_X1 f]
      rfl]
    rw [show Trans.Recal.jjSeq 0 1=[((0:Int),(0:Int)),((1:Int),(1:Int))] from rfl,
      G1.foldStep (m+1)]

theorem red_single_zero (f : Nat) :
    Trans.Recal.red (f+1) [(2,0)]=[(0,0)] := by rfl

theorem isPrincipalP_T (m : Nat) (hm : 2≤m) :
    Trans.Recal.isPrincipalP (T m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (T m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_T]
    rw [show (m==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
    rfl]
  simp only [Bool.not_false,Bool.true_and]
  rw [show Trans.Recal.lenI (T m)-1=((m-1:Nat):Int) from by rw [lenI_T]; omega]
  exact isAnc_T m (m-1) (by omega)

theorem red_L_zero (f : Nat) : Trans.Recal.red (f+4) (L 0)=L 0 := by
  rw [show f+4=(f+3)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L 0)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L 0) 0==0 &&
      Trans.Recal.gp1 (L 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  rw [show Trans.Recal.lenI (L 0)-1=4 from by rw [lenI_L]; omega]
  rw [show ((1:Int)==4)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L_zero,firstNodes_L_zero,joints_L_zero]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 3=[0,1,2] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 0 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 1 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)]]:List Trans.Recal.PS).getD 2 []=[(2,0)] from rfl,
    show ([2,3,4,5]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5]:List Int).getD 2 0=4 from rfl,
    show ([1,1,1]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1]:List Int).getD 2 0=1 from rfl]
  rw [show Trans.Recal.gp1 [(2,1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  rw [show Trans.Recal.gp1 [(2,0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_L_three]
  change ((Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,0)]) 2=L 0
  have hx : Trans.Recal.red (f+3) [(2,1)]=[(1,1)] := by
    change Trans.Recal.red (f+3) G1.X1=[(1,1)]
    simpa only [show f+3=(f+1)+2 by omega] using G1.red_X1 (f+1)
  have hz : Trans.Recal.red (f+3) [(2,0)]=[(0,0)] := by
    simpa only [show f+3=(f+2)+1 by omega] using red_single_zero (f+2)
  rw [hx,hz]
  rfl

theorem T_head (m : Nat) :
    T (m+1)=(1,0)::((List.range m).map fun k=>(p (k+1),q (k+1))) := by
  unfold T
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  rfl

theorem cons_derp_T (m : Nat) :
    (1,0)::Trans.Recal.derp (T (m+1))=T (m+1) := by
  rw [T_head]
  rfl

theorem incrFirst_S (m : Nat) : Trans.Recal.incrFirst (S m) 1=T m := by
  unfold S Trans.Recal.incrFirst T
  rw [List.map_map,List.map_map]
  apply List.map_congr_left
  intro k _
  change (p k+(-1)+1,q k)=(p k,q k)
  apply Prod.ext
  · omega
  · rfl

theorem red_T_one (f : Nat) : Trans.Recal.red (f+1) (T 1)=S 1 := by rfl

theorem red_T_step (m f : Nat) (hm : 2≤m)
    (hred : Trans.Recal.red f (S m)=S m) :
    Trans.Recal.red (f+1) (T m)=S m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (T m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_T]
      rw [show (m==1)=false from beq_eq_false_iff_ne.mpr (by omega)]
      rfl,
    isPrincipalP_T m hm]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (T m) 0==0 && Trans.Recal.gp1 (T m) 0==0)=false from by
    rw [show Trans.Recal.gp0 (T m) 0=1 from by
        simpa only [p_phase0 0] using gp0_T m 0 (by omega),
      show Trans.Recal.gp1 (T m) 0=0 from by
        simpa only [q_phase0 0] using gp1_T m 0 (by omega)]
    rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (T m) 0==0)=true from by
    rw [show Trans.Recal.gp1 (T m) 0=0 from by
      simpa only [q_phase0 0] using gp1_T m 0 (by omega)]
    rfl]
  simp only [if_true]
  rw [show Trans.Recal.incrFirst (T m) (-Trans.Recal.gp0 (T m) 0)=S m from by
    rw [show Trans.Recal.gp0 (T m) 0=1 from by
      simpa only [p_phase0 0] using gp0_T m 0 (by omega)]
    rfl]
  exact hred

theorem red_L_succ_from_tail (m f : Nat)
    (htail : Trans.Recal.red (f+3) (T (m+1))=S (m+1)) :
    Trans.Recal.red (f+4) (L (m+1))=L (m+1) := by
  rw [show f+4=(f+3)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L (m+1))=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,
    isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L (m+1)) 0==0 &&
      Trans.Recal.gp1 (L (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L]
  rw [show Trans.Recal.lenI (L (m+1))-1=((m+5:Nat):Int) from by
    rw [lenI_L]; omega]
  rw [show ((1:Int)==((m+5:Nat):Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L_succ,firstNodes_L_succ,joints_L_succ]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 4=[0,1,2,3] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 0 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 1 []=[(2,1)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 2 []=[(2,0)] from rfl,
    show ([[(2,1)],[(2,1)],[(2,0)],T (m+1)]:List Trans.Recal.PS).getD 3 []=T (m+1) from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 1 0=3 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 2 0=4 from rfl,
    show ([2,3,4,5,((m+6:Nat):Int)]:List Int).getD 3 0=5 from rfl,
    show ([1,1,1,0]:List Int).getD 0 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 1 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 2 0=1 from rfl,
    show ([1,1,1,0]:List Int).getD 3 0=0 from rfl]
  rw [show Trans.Recal.gp1 [(2,1)] 0=1 from rfl,
    show ((1:Int)==0)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  rw [show Trans.Recal.gp1 [(2,0)] 0=0 from rfl,
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  rw [fpar1_L_three]
  rw [show Trans.Recal.gp1 (T (m+1)) 0=0 from by
      simpa only [q_phase0 0] using gp1_T (m+1) 0 (by omega),
    show ((0:Int)==0)=true from rfl]
  simp only [if_true]
  change (((Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,1)]) 1)++
    Trans.Recal.incrFirst (Trans.Recal.red (f+3) [(2,0)]) 2)++
    Trans.Recal.incrFirst
      (Trans.Recal.red (f+3) ((1,0)::Trans.Recal.derp (T (m+1)))) 1=L (m+1)
  rw [cons_derp_T,htail,incrFirst_S]
  have hx : Trans.Recal.red (f+3) [(2,1)]=[(1,1)] := by
    change Trans.Recal.red (f+3) G1.X1=[(1,1)]
    simpa only [show f+3=(f+1)+2 by omega] using G1.red_X1 (f+1)
  have hz : Trans.Recal.red (f+3) [(2,0)]=[(0,0)] := by
    simpa only [show f+3=(f+2)+1 by omega] using red_single_zero (f+2)
  rw [hx,hz]
  rfl

theorem red_L_bound : ∀ m f : Nat, 4*m+8≤f →
    Trans.Recal.red f (L m)=L m := by
  intro m
  refine Nat.strongRecOn (motive:=fun m=>∀ f:Nat,4*m+8≤f→
    Trans.Recal.red f (L m)=L m) m ?_
  intro m ih f hf
  cases m with
  | zero =>
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    exact red_L_zero g
  | succ m =>
    obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
    apply red_L_succ_from_tail m g
    by_cases h1:m+1=1
    · have hm:m=0:=by omega
      subst m
      simpa only [show g+3=(g+2)+1 by omega] using red_T_one (g+2)
    · have hm2:2≤m+1:=by omega
      apply red_T_step (m+1) (g+2) hm2
      by_cases h5:m+1<5
      · have hc:m+1=2∨m+1=3∨m+1=4:=by omega
        rcases hc with hc|hc|hc
        · rw [hc,S_two]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 0 u
        · rw [hc,S_three]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 1 u
        · rw [hc,S_four]
          obtain ⟨u,hu⟩ : ∃ u,g+2=u+3 := ⟨g-1,by omega⟩
          rw [hu]
          exact red_LG 2 u
      · obtain ⟨k,hk⟩ : ∃ k,m+1=k+5 := ⟨m+1-5,by omega⟩
        rw [hk,S_add_five]
        exact ih k (by omega) (g+2) (by omega)

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  apply red_L_bound
  unfold Trans.Recal.redFuel
  rw [length_L]
  omega

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

/-! ### Five-phase reader data. -/

theorem gp1_L_tail (m k : Nat) (hk : 5≤k) (hkm : k<m+5) :
    Trans.Recal.gp1 (L m) (k:Int)=q (k-5) := by
  rw [gp1_L m k hkm,if_neg (by omega)]

theorem gp0_L_tail_phase0 (a m : Nat) (h : 5*a<m) :
    Trans.Recal.gp0 (L m) ((5*a+5:Nat):Int)=((a+1:Nat):Int) := by
  rw [gp0_L m (5*a+5) (by omega),if_neg (by omega)]
  simpa only [show 5*a+5-5=5*a by omega] using p_phase0 a

theorem gp0_L_before_phase0 (a m : Nat) (h : 5*a<m) :
    Trans.Recal.gp0 (L m) ((5*a+4:Nat):Int)=((a+2:Nat):Int) := by
  cases a with
  | zero => rfl
  | succ a =>
    rw [gp0_L m (5*(a+1)+4) (by omega),if_neg (by omega)]
    simpa only [show 5*(a+1)+4-5=5*a+4 by omega] using p_phase4 a

theorem gp1_L_phase0_tail (a m : Nat) (h : 5*a<m) :
    Trans.Recal.gp1 (L m) ((5*a+5:Nat):Int)=0 := by
  rw [gp1_L_tail m (5*a+5) (by omega) (by omega)]
  simpa only [show 5*a+5-5=5*a by omega] using q_phase0 a

theorem gp1_L_phase1_tail (a m : Nat) (h : 5*a+1<m) :
    Trans.Recal.gp1 (L m) ((5*a+6:Nat):Int)=1 := by
  rw [gp1_L_tail m (5*a+6) (by omega) (by omega)]
  simpa only [show 5*a+6-5=5*a+1 by omega] using q_phase1 a

theorem gp1_L_phase2_tail (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.gp1 (L m) ((5*a+7:Nat):Int)=1 := by
  rw [gp1_L_tail m (5*a+7) (by omega) (by omega)]
  simpa only [show 5*a+7-5=5*a+2 by omega] using q_phase2 a

theorem gp1_L_phase3_tail (a m : Nat) (h : 5*a+3<m) :
    Trans.Recal.gp1 (L m) ((5*a+8:Nat):Int)=1 := by
  rw [gp1_L_tail m (5*a+8) (by omega) (by omega)]
  simpa only [show 5*a+8-5=5*a+3 by omega] using q_phase3 a

theorem gp1_L_phase4_tail (a m : Nat) (h : 5*a+4<m) :
    Trans.Recal.gp1 (L m) ((5*a+9:Nat):Int)=0 := by
  rw [gp1_L_tail m (5*a+9) (by omega) (by omega)]
  simpa only [show 5*a+9-5=5*a+4 by omega] using q_phase4 a

theorem fpar1_L_phase0_lb (a m : Nat) (h : 5*a<m) :
    Trans.Recal.fpar (L m) 1 ((5*a+5:Nat):Int) ((5*a+4:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L,gp1_L_phase0_tail a m h]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) ((5*a+5:Nat):Int) ((5*a+4:Nat):Int)=-1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L_tail_phase0 a m h]
    change Trans.Recal.fpar0Aux (m+6) (L m) ((a+1:Nat):Int)
      (((5*a+5:Nat):Int)-1) ((5*a+4:Nat):Int)=-1
    rw [show m+6=(m+5)+1 by omega,Trans.Recal.fpar0Aux,
      show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega,
      if_neg (by omega),gp0_L_before_phase0 a m h,if_neg (by omega)]
    rw [show m+5=(m+4)+1 by omega,Trans.Recal.fpar0Aux,if_pos (by omega)],
    if_pos (by omega)]

theorem fpar1_L_phase2_lb (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.fpar (L m) 1 ((5*a+7:Nat):Int) ((5*a+6:Nat):Int)=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L,gp1_L_phase2_tail a m h]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) ((5*a+7:Nat):Int) ((5*a+6:Nat):Int)=
      ((5*a+6:Nat):Int) from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    rw [show Trans.Recal.gp0 (L m) ((5*a+7:Nat):Int)=((a+3:Nat):Int) from by
      rw [gp0_L m (5*a+7) (by omega),if_neg (by omega)]
      simpa only [show 5*a+7-5=5*a+2 by omega] using p_phase2 a]
    simp only [Trans.Recal.fpar0Aux]
    rw [show ((5*a+7:Nat):Int)-1=((5*a+6:Nat):Int) by omega,
      if_neg (by omega)]
    rw [show Trans.Recal.gp0 (L m) ((5*a+6:Nat):Int)=((a+2:Nat):Int) from by
      rw [gp0_L m (5*a+6) (by omega),if_neg (by omega)]
      simpa only [show 5*a+6-5=5*a+1 by omega] using p_phase1 a,
      if_pos (by omega)],
    if_neg (by omega),gp1_L_phase1_tail a m (by omega),if_neg (by omega)]
  rw [show Trans.Recal.fpar0 (L m) ((5*a+6:Nat):Int) ((5*a+6:Nat):Int)=-1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_pos (by omega)],if_pos (by omega)]

theorem isAdm_L_phase0_at (a m : Nat) (h : 5*a<m) :
    Trans.Recal.isAdm (L m) ((5*a+5:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((5*a+5:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [show ((5*a+5:Nat):Int)-1=((5*a+4:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L m) 1 ((5*a+5:Nat):Int)
      ((5*a+4:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [fpar1_L_phase0_lb a m h,lenI_L]
    rw [show decide (0≤((5*a+4:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((5*a+4:Nat):Int)<(m:Int)+5)=true from decide_eq_true (by omega),
      show (((5*a+4:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
    rfl
  rw [hp,Bool.false_and]
  rfl

theorem isAdm_L_phase1_at (a m : Nat) (h : 5*a+2<m) :
    Trans.Recal.isAdm (L m) ((5*a+6:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((5*a+6:Nat):Int)>Trans.Recal.lenI (L m))=false from
    decide_eq_false (by rw [lenI_L]; omega)]
  simp only [Bool.false_or]
  rw [show ((5*a+6:Nat):Int)+1=((5*a+7:Nat):Int) by omega]
  have hp : Trans.Recal.isParentP (L m) 1 ((5*a+7:Nat):Int)
      ((5*a+6:Nat):Int)=false := by
    unfold Trans.Recal.isParentP
    rw [fpar1_L_phase2_lb a m h,lenI_L]
    rw [show decide (0≤((5*a+6:Nat):Int))=true from decide_eq_true (by omega),
      show decide (((5*a+6:Nat):Int)<(m:Int)+5)=true from decide_eq_true (by omega),
      show (((5*a+6:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
    rfl
  rw [hp,Bool.and_false]
  rfl

theorem adm_L_new1 (a : Nat) :
    Trans.Recal.adm (L (5*a+1)) ((5*a:Nat):Int)=((5*a:Nat):Int) := by
  cases a with
  | zero => rfl
  | succ a =>
    unfold Trans.Recal.adm
    rw [length_L]
    simp only [Trans.Recal.admAux]
    rw [if_neg (by omega)]
    have ha:=isAdm_L_phase0_at a (5*(a+1)+1) (by omega)
    rw [show ((5*(a+1):Nat):Int)=((5*a+5:Nat):Int) by omega]
    rw [show Trans.Recal.isAdm (L (5*(a+1)+1)) ((5*a+5:Nat):Int)=true from ha,
      if_pos rfl]

theorem adm_L_new2 (a : Nat) :
    Trans.Recal.adm (L (5*a+2)) ((5*a+5:Nat):Int)=((5*a+5:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase0_at a (5*a+2) (by omega),if_pos rfl]

theorem adm_L_new3 (a : Nat) :
    Trans.Recal.adm (L (5*a+3)) ((5*a+6:Nat):Int)=((5*a+6:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (5*a+3) (by omega),if_pos rfl]

theorem adm_L_new4 (a : Nat) :
    Trans.Recal.adm (L (5*a+4)) ((5*a+6:Nat):Int)=((5*a+6:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (5*a+4) (by omega),if_pos rfl]

theorem adm_L_new5 (a : Nat) :
    Trans.Recal.adm (L (5*a+5)) ((5*a+6:Nat):Int)=((5*a+6:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_phase1_at a (5*a+5) (by omega),if_pos rfl]

theorem j0_L_new1 (a : Nat) :
    Trans.Recal.fpar (L (5*a+1)) 0 ((5*a+5:Nat):Int) 0=((5*a:Nat):Int) := by
  cases a with
  | zero => simpa using fpar_L_phase0_zero 1 (by omega)
  | succ a =>
    simpa only [show 5*(a+1)+5=5*(a+1)+5 by rfl,
      show 5*a+5=5*a+5 by rfl] using
      fpar_L_phase0_succ a (5*(a+1)+1) (by omega)

theorem j0_L_new2 (a : Nat) :
    Trans.Recal.fpar (L (5*a+2)) 0 ((5*a+6:Nat):Int) 0=((5*a+5:Nat):Int) :=
  fpar_L_phase1 a (5*a+2) (by omega)

theorem j0_L_new3 (a : Nat) :
    Trans.Recal.fpar (L (5*a+3)) 0 ((5*a+7:Nat):Int) 0=((5*a+6:Nat):Int) :=
  fpar_L_phase2 a (5*a+3) (by omega)

theorem j0_L_new4 (a : Nat) :
    Trans.Recal.fpar (L (5*a+4)) 0 ((5*a+8:Nat):Int) 0=((5*a+6:Nat):Int) :=
  fpar_L_phase3 a (5*a+4) (by omega)

theorem j0_L_new5 (a : Nat) :
    Trans.Recal.fpar (L (5*a+5)) 0 ((5*a+9:Nat):Int) 0=((5*a+6:Nat):Int) :=
  fpar_L_phase4 a (5*a+5) (by omega)

theorem transType_L_new1 (a : Nat) :
    Trans.Recal.transTypeMain (L (5*a+1)) ((5*a:Nat):Int)
      ((5*a+5:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase0_tail a (5*a+1) (by omega)]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  cases a with
  | zero => rfl
  | succ a =>
    rw [show Trans.Recal.isAdm (L (5*(a+1)+1)) ((5*(a+1):Nat):Int)=true from by
      simpa only [show 5*(a+1)=5*a+5 by omega] using
        isAdm_L_phase0_at a (5*(a+1)+1) (by omega),if_pos rfl]

theorem transType_L_new2 (a : Nat) :
    Trans.Recal.transTypeMain (L (5*a+2)) ((5*a+5:Nat):Int)
      ((5*a+6:Nat):Int)=6 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase1_tail a (5*a+2) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase0_tail a (5*a+2) (by omega),if_neg (by omega),if_neg (by omega)]

theorem transType_L_new3 (a : Nat) :
    Trans.Recal.transTypeMain (L (5*a+3)) ((5*a+6:Nat):Int)
      ((5*a+7:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase2_tail a (5*a+3) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase1_tail a (5*a+3) (by omega),if_pos (by omega),
    isAdm_L_phase1_at a (5*a+3) (by omega),if_pos rfl]

theorem transType_L_new4 (a : Nat) :
    Trans.Recal.transTypeMain (L (5*a+4)) ((5*a+6:Nat):Int)
      ((5*a+8:Nat):Int)=3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase3_tail a (5*a+4) (by omega)]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [gp1_L_phase1_tail a (5*a+4) (by omega),if_pos (by omega),
    isAdm_L_phase1_at a (5*a+4) (by omega),if_pos rfl]

theorem transType_L_new5 (a : Nat) :
    Trans.Recal.transTypeMain (L (5*a+5)) ((5*a+6:Nat):Int)
      ((5*a+9:Nat):Int)=1 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_phase4_tail a (5*a+5) (by omega)]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  rw [isAdm_L_phase1_at a (5*a+5) (by omega),if_pos rfl]

theorem mkC2_L_new1 (a : Nat) :
    Trans.Recal.mkC2 (L (5*a+1)) ((5*a:Nat):Int) ((5*a+5:Nat):Int)
      1 Anchor=.D 0 (Part 1) := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus Part
  rw [gp1_L_phase0_tail a (5*a+1) (by omega)]
  rfl

theorem mkC2_L_new2 (a : Nat) :
    Trans.Recal.mkC2 (L (5*a+2)) ((5*a+5:Nat):Int) ((5*a+6:Nat):Int)
      6 D0z=.D 0 D1z := by
  unfold Trans.Recal.mkC2
  rw [gp1_L_phase1_tail a (5*a+2) (by omega)]
  rfl

theorem mkC2_L_new3 (a : Nat) :
    Trans.Recal.mkC2 (L (5*a+3)) ((5*a+6:Nat):Int) ((5*a+7:Nat):Int)
      3 D1z=D11z := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase2_tail a (5*a+3) (by omega)]
  rfl

theorem mkC2_L_new4 (a : Nat) :
    Trans.Recal.mkC2 (L (5*a+4)) ((5*a+6:Nat):Int) ((5*a+8:Nat):Int)
      3 D11z=D1ss := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase3_tail a (5*a+4) (by omega)]
  rfl

theorem mkC2_L_new5 (a : Nat) :
    Trans.Recal.mkC2 (L (5*a+5)) ((5*a+6:Nat):Int) ((5*a+9:Nat):Int)
      1 D1ss=A0 := by
  unfold Trans.Recal.mkC2 Trans.Recal.bplus
  rw [gp1_L_phase4_tail a (5*a+5) (by omega)]
  rfl

theorem LBT_phase0 (a : Nat) : LBT (5*a)=.D 0 (W a (Part 0)) := by
  unfold LBT
  rw [show 5*a/5=a by omega,show 5*a%5=0 by omega]

theorem LBT_phase1 (a : Nat) : LBT (5*a+1)=.D 0 (W a (Part 1)) := by
  unfold LBT
  rw [show (5*a+1)/5=a by omega,show (5*a+1)%5=1 by omega]

theorem LBT_phase2 (a : Nat) : LBT (5*a+2)=.D 0 (W a (Part 2)) := by
  unfold LBT
  rw [show (5*a+2)/5=a by omega,show (5*a+2)%5=2 by omega]

theorem LBT_phase3 (a : Nat) : LBT (5*a+3)=.D 0 (W a (Part 3)) := by
  unfold LBT
  rw [show (5*a+3)/5=a by omega,show (5*a+3)%5=3 by omega]

theorem LBT_phase4 (a : Nat) : LBT (5*a+4)=.D 0 (W a (Part 4)) := by
  unfold LBT
  rw [show (5*a+4)/5=a by omega,show (5*a+4)%5=4 by omega]

theorem LBT_phase5 (a : Nat) : LBT (5*a+5)=.D 0 (W (a+1) (Part 0)) := by
  simpa only [show 5*a+5=5*(a+1) by omega] using LBT_phase0 (a+1)

theorem repl_D0W : ∀ (a f r : Nat) (b bb c cc : Trans.Dict.BT),
    (∀ g : Nat, r≤g → Trans.Recal.replMark g (.D 0 b) c cc=some (.D 0 bb)) →
    (∀ n : Nat, ((Trans.Dict.BT.D 0 (W (n+1) b))==c)=false) →
    3*a+r≤f →
    Trans.Recal.replMark f (.D 0 (W a b)) c cc=some (.D 0 (W a bb))
  | 0,f,r,b,bb,c,cc,hbase,_,hf => hbase f (by simpa using hf)
  | a+1,f,r,b,bb,c,cc,hbase,hne,hf => by
    obtain ⟨g,rfl⟩ : ∃ g,f=g+3 := ⟨f-3,by omega⟩
    change Trans.Recal.replMark (g+3) (.D 0 (.sum A0 (.D 0 (W a b)))) c cc=
      some (.D 0 (.sum A0 (.D 0 (W a bb))))
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark]
    have hn:=hne a
    change ((Trans.Dict.BT.D 0 (.sum A0 (.D 0 (W a b))))==c)=false at hn
    rw [hn]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [show Trans.Dict.BT.toL (.sum A0 (.D 0 (W a b)))=
      [A0,.D 0 (W a b)] from rfl]
    change ((Trans.Recal.replMark (g+1) (.D 0 (W a b)) c cc).map
      (fun ll=>Trans.Dict.BT.sum A0 ll)).map (fun aa=>Trans.Dict.BT.D 0 aa)=
        some (Trans.Dict.BT.D 0 (Trans.Dict.BT.sum A0 (.D 0 (W a bb))))
    rw [repl_D0W a (g+1) r b bb c cc hbase hne (by omega)]
    rfl

theorem W_add (a b : Nat) (c : Trans.Dict.BT) : W a (W b c)=W (a+b) c := by
  induction a with
  | zero => simp [W]
  | succ a ih =>
    simp only [W,ih]
    rw [show a+1+b=(a+b)+1 by omega,W]

theorem repl_LBT_phase0 (a f : Nat) (hf : 3*a+1≤f) :
    Trans.Recal.replMark f (LBT (5*a)) Anchor (.D 0 (Part 1))=
      some (LBT (5*a+1)) := by
  rw [LBT_phase0,LBT_phase1]
  exact repl_D0W a f 1 (Part 0) (Part 1) Anchor (.D 0 (Part 1))
    (fun g hg => G1.replMark_self g 0 A0 (.D 0 (Part 1)) hg)
    (fun n => by cases n <;> rfl) hf

theorem repl_LBT_phase1 (a f : Nat) (hf : 3*a+3≤f) :
    Trans.Recal.replMark f (LBT (5*a+1)) D0z (.D 0 D1z)=
      some (LBT (5*a+2)) := by
  rw [LBT_phase1,LBT_phase2]
  apply repl_D0W a f 3 (Part 1) (Part 2) D0z (.D 0 D1z) ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+3 := ⟨g-3,by omega⟩
    change Trans.Recal.replMark (h+3) (.D 0 (.sum A0 D0z)) D0z (.D 0 D1z)=
      some (.D 0 (.sum A0 (.D 0 D1z)))
    rw [show h+3=(h+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 D0z))==D0z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [Trans.Recal.replMark]
    change ((Trans.Recal.replMark (h+1) D0z D0z (.D 0 D1z)).map
      (fun q=>Trans.Dict.BT.sum A0 q)).map (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 0 .zero (.D 0 D1z) (by omega)]
    rfl
  · intro n
    cases n <;> rfl

theorem repl_LBT_phase2 (a f : Nat) (hf : 3*a+4≤f) :
    Trans.Recal.replMark f (LBT (5*a+2)) D1z D11z=
      some (LBT (5*a+3)) := by
  rw [LBT_phase2,LBT_phase3]
  apply repl_D0W a f 4 (Part 2) (Part 3) D1z D11z ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
    change Trans.Recal.replMark (h+4) (.D 0 (.sum A0 (.D 0 D1z))) D1z D11z=
      some (.D 0 (.sum A0 (.D 0 D11z)))
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 0 D1z)))==D1z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [Trans.Recal.replMark]
    change (((Trans.Recal.replMark (h+1) D1z D1z D11z).map
      (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 1 .zero D11z (by omega)]
    rfl
  · intro n
    cases n <;> rfl

theorem repl_LBT_phase3 (a f : Nat) (hf : 3*a+4≤f) :
    Trans.Recal.replMark f (LBT (5*a+3)) D11z D1ss=
      some (LBT (5*a+4)) := by
  rw [LBT_phase3,LBT_phase4]
  apply repl_D0W a f 4 (Part 3) (Part 4) D11z D1ss ?_ ?_ hf
  · intro g hg
    obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
    change Trans.Recal.replMark (h+4) (.D 0 (.sum A0 (.D 0 D11z))) D11z D1ss=
      some (.D 0 (.sum A0 (.D 0 D1ss)))
    rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 0 D11z)))==D11z)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [Trans.Recal.replMark]
    change (((Trans.Recal.replMark (h+1) D11z D11z D1ss).map
      (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.sum A0 q)).map
        (fun q=>Trans.Dict.BT.D 0 q)=_
    rw [G1.replMark_self (h+1) 1 D1z D1ss (by omega)]
    rfl
  · intro n
    cases n <;> rfl

theorem repl_LBT_phase4 (a f : Nat) (hf : 3*a+4≤f) :
    Trans.Recal.replMark f (LBT (5*a+4)) D1ss A0=
      some (LBT (5*a+5)) := by
  rw [LBT_phase4,LBT_phase5]
  have h := repl_D0W a f 4 (Part 4) (W 1 (Part 0)) D1ss A0
    (fun g hg => by
      obtain ⟨h,rfl⟩ : ∃ h,g=h+4 := ⟨g-4,by omega⟩
      change Trans.Recal.replMark (h+4) (.D 0 (.sum A0 (.D 0 D1ss))) D1ss A0=
        some (.D 0 (.sum A0 (.D 0 A0)))
      rw [show h+4=(h+3)+1 by omega,Trans.Recal.replMark]
      rw [show ((Trans.Dict.BT.D 0 (.sum A0 (.D 0 D1ss)))==D1ss)=false from rfl]
      simp only [Bool.false_eq_true,if_false]
      rw [Trans.Recal.replMark]
      change (((Trans.Recal.replMark (h+1) D1ss D1ss A0).map
        (fun q=>Trans.Dict.BT.D 0 q)).map (fun q=>Trans.Dict.BT.sum A0 q)).map
          (fun q=>Trans.Dict.BT.D 0 q)=_
      rw [G1.replMark_self (h+1) 1 (.sum D1z D1z) A0 (by omega)]
      rfl)
    (fun n => by cases n <;> rfl) hf
  rw [W_add] at h
  simpa only [show a+1=a+1 by rfl] using h

/-! ### Memo invariant. -/

def Allowed (k : Nat) (req : Option Int) : Prop :=
  if k%5=0 then req=none ∨ req=some (k:Int)
  else if k%5=1 then req=none ∨ req=some ((k+4:Nat):Int)
  else if k%5=2 then
    req=none ∨ req=some ((k+3:Nat):Int) ∨ req=some ((k+4:Nat):Int)
  else if k%5=3 then
    req=none ∨ req=some ((k+2:Nat):Int) ∨ req=some ((k+3:Nat):Int)
  else req=none ∨ req=some ((k+1:Nat):Int) ∨ req=some ((k+2:Nat):Int)

def Val (k : Nat) (req : Option Int) : Trans.Dict.BT :=
  if req=none then LBT k
  else if k%5=0 then Anchor
  else if k%5=1 then D0z
  else if k%5=2 then
    if req=some ((k+3:Nat):Int) then .D 0 D1z else D1z
  else if k%5=3 then
    if req=some ((k+2:Nat):Int) then .D 0 D11z else D11z
  else if req=some ((k+1:Nat):Int) then .D 0 D1ss else D1ss

theorem Allowed_none (k : Nat) : Allowed k none := by
  unfold Allowed
  split <;> first | exact Or.inl rfl | split <;>
    first | exact Or.inl rfl | split <;>
      first | exact Or.inl rfl | split <;> exact Or.inl rfl

theorem Val_none (k : Nat) : Val k none=LBT k := by rw [Val,if_pos rfl]

theorem Allowed_phase0 (a : Nat) : Allowed (5*a) (some ((5*a:Nat):Int)) := by
  rw [Allowed,if_pos (by omega)]
  exact Or.inr rfl

theorem Allowed_phase1 (a : Nat) : Allowed (5*a+1) (some ((5*a+5:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_pos (by omega)]
  exact Or.inr (by congr 2 <;> omega)

theorem Allowed_phase2 (a : Nat) : Allowed (5*a+2) (some ((5*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase2carry (a : Nat) :
    Allowed (5*a+2) (some ((5*a+5:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_phase3 (a : Nat) : Allowed (5*a+3) (some ((5*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase3carry (a : Nat) :
    Allowed (5*a+3) (some ((5*a+5:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Allowed_phase4 (a : Nat) : Allowed (5*a+4) (some ((5*a+6:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  exact Or.inr (Or.inr (by congr 2 <;> omega))

theorem Allowed_phase4carry (a : Nat) :
    Allowed (5*a+4) (some ((5*a+5:Nat):Int)) := by
  rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
  exact Or.inr (Or.inl (by congr 2 <;> omega))

theorem Val_phase0 (a : Nat) : Val (5*a) (some ((5*a:Nat):Int))=Anchor := by
  rw [Val,if_neg (by intro h; cases h),if_pos (by omega)]

theorem Val_phase1 (a : Nat) : Val (5*a+1) (some ((5*a+5:Nat):Int))=D0z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_pos (by omega)]

theorem Val_phase2 (a : Nat) : Val (5*a+2) (some ((5*a+6:Nat):Int))=D1z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_pos (by omega),if_neg (by intro h; injection h with h; omega)]

theorem Val_phase2carry (a : Nat) :
    Val (5*a+2) (some ((5*a+5:Nat):Int))=.D 0 D1z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_pos (by omega),if_pos (by congr 2 <;> omega)]

theorem Val_phase3 (a : Nat) : Val (5*a+3) (some ((5*a+6:Nat):Int))=D11z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_pos (by omega),if_neg (by intro h; injection h with h; omega)]

theorem Val_phase3carry (a : Nat) :
    Val (5*a+3) (some ((5*a+5:Nat):Int))=.D 0 D11z := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_pos (by omega),if_pos (by congr 2 <;> omega)]

theorem Val_phase4 (a : Nat) : Val (5*a+4) (some ((5*a+6:Nat):Int))=D1ss := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),
    if_neg (by intro h; injection h with h; omega)]

theorem Val_phase4carry (a : Nat) :
    Val (5*a+4) (some ((5*a+5:Nat):Int))=.D 0 D1ss := by
  rw [Val,if_neg (by intro h; cases h),if_neg (by omega),if_neg (by omega),
    if_neg (by omega),if_neg (by omega),
    if_pos (by congr 2 <;> omega)]

theorem L_inj (a b : Nat) (h : L a=L b) : a=b := by
  have hl:=congrArg List.length h
  rw [length_L,length_L] at hl
  omega

theorem L_ne_LG (k j : Nat) : L k≠G1.LG j := by
  intro h
  have hd:=congrArg (fun z=>z.getD 4 ((9:Int),(9:Int))) h
  rcases j with _|j
  · simp [L,G1.LG] at hd
  · rcases j with _|j
    · simp [L,G1.LG] at hd
    · rcases j with _|j
      · simp [L,G1.LG] at hd
      · simp [L,G1.LG,List.replicate_succ] at hd

theorem L_ne_base (k : Nat) : L k≠G1.Base := by
  intro h
  have hl:=congrArg List.length h
  rw [length_L] at hl
  simp [G1.Base] at hl

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  G1.Good p ∧
    (∀ j, p.1=(G1.LG j,some 0) → p.2=G1.LBT j) ∧
    ∀ k req, p.1=(L k,req) → Allowed k req → p.2=Val k req

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem good_L_entry (k : Nat) (req : Option Int) (hr : Allowed k req) :
    Good ((L k,req),Val k req) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · intro h
      exact absurd (congrArg Prod.fst h) (L_ne_base k)
  · constructor
    · intro j h
      exact absurd (congrArg Prod.fst h) (L_ne_LG k j)
    · intro j r h _
      have hL:L k=L j:=congrArg Prod.fst h
      have hkj:=L_inj k j hL
      subst hkj
      have hreq:req=r:=by simpa using congrArg Prod.snd h
      subst hreq
      rfl

theorem good_LG_entry (k : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 1) : Good ((G1.LG k,req),G1.Val k req) := by
  constructor
  · have hs:=G1.Sound_cons [] G1.Sound_nil k req
    exact hs _ (by simp)
  · constructor
    · intro j h
      have hk:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hk
      have hreq:req=some 0:=by simpa using congrArg Prod.snd h
      rcases hr with hr|hr <;> subst hr <;> cases hreq
    · intro j r h _
      exact absurd (congrArg Prod.fst h).symm (L_ne_LG j k)

theorem good_base_entry :
    Good ((G1.Base,(none:Option Int)),Trans.Dict.BT.zero) := by
  constructor
  · have hs:=G1.Sound_cons_base [] G1.Sound_nil
    exact hs _ (by simp)
  · constructor
    · intro j h
      exact absurd (congrArg Prod.fst h).symm (G1.LG_ne_base j)
    · intro j r h _
      exact absurd (congrArg Prod.fst h).symm (L_ne_base j)

theorem good_LG_zero_entry (k : Nat) :
    Good ((G1.LG k,some 0),G1.LBT k) := by
  constructor
  · refine ⟨?_,?_,?_⟩
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      have hr:(some (0:Int))=none:=by simpa using congrArg Prod.snd h
      cases hr
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      have hr:(some (0:Int))=some 1:=by simpa using congrArg Prod.snd h
      cases hr
    · intro h
      exact absurd (congrArg Prod.fst h) (G1.LG_ne_base k)
  · constructor
    · intro j h
      have hj:k=j:=G1.LG_inj k j (congrArg Prod.fst h)
      subst hj
      rfl
    · intro j r h _
      exact absurd (congrArg Prod.fst h).symm (L_ne_LG j k)

theorem Sound_cons_L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : Allowed k req) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_L_entry k req hr
  · exact hs p h

theorem Sound_cons_LG (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : req=none ∨ req=some 1) :
    Sound (((G1.LG k,req),G1.Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_LG_entry k req hr
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((G1.Base,(none:Option Int)),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_base_entry
  · exact hs p h

theorem Sound_cons_LG_zero (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat) :
    Sound (((G1.LG k,some 0),G1.LBT k)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h; exact good_LG_zero_entry k
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun z=>z.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb:p.1==key:=List.find?_some (p:=fun z=>z.1==key) (a:=p) h
  exact eq_of_beq hb

theorem value_L_of_good {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (hg : Good p) (k : Nat) (req : Option Int) (hr : Allowed k req)
    (he : p.1=(L k,req)) : p.2=Val k req := hg.2.2 k req he hr

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) G1.Base none).run tbl).2 := by
  cases hf:tbl.find? (fun z=>z.1==(G1.Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f G1.Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.1.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_LG0 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 1) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) (G1.LG 0) req).run tbl).1=G1.Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+2) (G1.LG 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun z=>z.1==(G1.LG 0,req)) with
  | some p =>
    rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G1.LG 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h; exact hg.1.1 0 he
    · subst h; exact hg.1.2.1 0 he
  | none =>
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,G1.isReducedP_LG 0,G1.isPrincipalP_LG 0,
      Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG 0,
      show (((0:Nat):Int)+2-1==0)=false from by decide,
      show Trans.Recal.predP (G1.LG 0)=G1.Base from rfl]
    cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,if_true]
      rcases hr with h|h
      · subst h; exact ⟨rfl,Sound_cons_LG s hsm 0 none (Or.inl rfl)⟩
      · subst h; exact ⟨rfl,Sound_cons_LG s hsm 0 (some 1) (Or.inr rfl)⟩

theorem runAux_LG : ∀ (k g : Nat) (req : Option Int),
    req=none ∨ req=some 1 → ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+2) (G1.LG k) req).run tbl).1=G1.Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+2) (G1.LG k) req).run tbl).2
  | 0,g,req,hr,tbl,hs => runAux_LG0 g req hr tbl hs
  | k+1,g,req,hr,tbl,hs => by
    cases hf:tbl.find? (fun z=>z.1==(G1.LG (k+1),req)) with
    | some p =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,
        G1.run_hit (k+g+2) (G1.LG (k+1)) req tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      refine ⟨?_,hs⟩
      rcases hr with h|h
      · subst h; exact hg.1.1 (k+1) he
      · subst h; exact hg.1.2.1 (k+1) he
    | none =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG (k+1),G1.isPrincipalP_LG (k+1),
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG (k+1),
        show ((((k+1:Nat):Int)+2-1)==0)=false from by simp; omega,
        G1.predP_LG k]
      cases hrun:(Trans.Recal.runAux (k+g+2) (G1.LG k) none) tbl with
      | mk a s =>
        have ih1:=runAux_LG k g none (Or.inl rfl) tbl hs
        rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) none).run tbl=(a,s)
          from hrun] at ih1
        have ha:a=G1.LBT k:=ih1.1
        have hsm:Sound s:=ih1.2
        subst ha
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show ((G1.LBT k)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (G1.LG (k+1)) 0 (((k+1:Nat):Int)+2-1) 0=1 from
            G1.fpar_LG_0_e (k+1) (((k+1:Nat):Int)+2-1) (by push_cast; omega)
              (by push_cast; omega),G1.adm_LG_1 (k+1)]
        cases hrun2:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s with
        | mk c1 s2 =>
          have ih2:=runAux_LG k g (some 1) (Or.inr rfl) s hsm
          rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s=(c1,s2)
            from hrun2] at ih2
          have hc1:c1=Trans.Dict.BT.D 1 (G1.rep1 k):=ih2.1
          have hsm2:Sound s2:=ih2.2
          subst hc1
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run,
            show Trans.Recal.transTypeMain (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1)=3 from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.transType_LG k,
            show Trans.Recal.mkC2 (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1) 3
                (.D 1 (G1.rep1 k))=.D 1 (G1.rep1 (k+1)) from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.mkC2_LG k]
          rcases hr with h|h
          · subst h
            rw [G1.replMark_LG ((G1.LBT k).size+
              ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4)) k (by omega)]
            simp only [Option.getD_some]
            exact ⟨rfl,Sound_cons_LG s2 hsm2 (k+1) none (Or.inl rfl)⟩
          · subst h
            simp only [show ((1:Int)<((k+1:Nat):Int)+2-1) by push_cast; omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s2 with
            | mk c0 s3 =>
              have ih3:=runAux_LG k g (some 1) (Or.inr rfl) s2 hsm2
              rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s2=(c0,s3)
                from hrun3] at ih3
              have hc0:c0=.D 1 (G1.rep1 k):=ih3.1
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self (.D 1 (G1.rep1 k))),
                G1.replMark_self ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                  ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                    (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4))
                  1 (G1.rep1 k) (.D 1 (G1.rep1 (k+1))) (by omega)]
              simp only [Option.getD_some]
              exact ⟨rfl,Sound_cons_LG s3 hsm3 (k+1) (some 1) (Or.inr rfl)⟩

theorem isMarkedB_LG_inner (k : Nat) :
    Trans.Recal.isMarkedB (G1.LBT k) (.D 1 (G1.rep1 k))=true := by
  unfold Trans.Recal.isMarkedB
  rw [show (G1.LBT k).size+2=
    ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+2)+1 by
      simp only [G1.LBT,Trans.Dict.BT.size]
      omega]
  rw [Trans.Recal.isMarkedBAux]
  rw [show ((G1.LBT k)==(.D 1 (G1.rep1 k)))=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  exact G1.isMarkedB_self (.D 1 (G1.rep1 k))

theorem runAux_LG_zero : ∀ (k g : Nat) (tbl : Trans.Recal.Memo), Sound tbl →
    ((Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run tbl).1=G1.LBT k ∧
      Sound ((Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run tbl).2
  | 0,g,tbl,hs => by
    simp only [Nat.zero_add]
    cases hf:tbl.find? (fun z=>z.1==(G1.LG 0,some 0)) with
    | some p =>
      rw [show g+2=(g+1)+1 by omega,G1.run_hit (g+1) (G1.LG 0) (some 0) tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      exact ⟨hg.2.1 0 he,hs⟩
    | none =>
      rw [show g+2=(g+1)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG 0,G1.isPrincipalP_LG 0,
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG 0,
        show (((0:Nat):Int)+2-1==0)=false from by decide,
        show Trans.Recal.predP (G1.LG 0)=G1.Base from rfl]
      cases hrun:(Trans.Recal.runAux (g+1) G1.Base none) tbl with
      | mk a s =>
        have ih:=run_base_ok g tbl hs
        rw [show (Trans.Recal.runAux (g+1) G1.Base none).run tbl=(a,s) from hrun] at ih
        have ha:a=Trans.Dict.BT.zero:=ih.1
        have hsm:Sound s:=ih.2
        subst ha
        simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,
          if_true,show ((0:Int)==0)=true from rfl]
        exact ⟨rfl,Sound_cons_LG_zero s hsm 0⟩
  | k+1,g,tbl,hs => by
    cases hf:tbl.find? (fun z=>z.1==(G1.LG (k+1),some 0)) with
    | some p =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,
        G1.run_hit (k+g+2) (G1.LG (k+1)) (some 0) tbl p hf]
      obtain ⟨hg,he⟩:=good_of_find hs hf
      exact ⟨hg.2.1 (k+1) he,hs⟩
    | none =>
      rw [show k+1+g+2=(k+g+2)+1 by omega,Trans.Recal.runAux]
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,hf,G1.isReducedP_LG (k+1),G1.isPrincipalP_LG (k+1),
        Bool.not_true,Bool.false_eq_true,if_false,G1.lenI_LG (k+1),
        show ((((k+1:Nat):Int)+2-1)==0)=false from by simp; omega,G1.predP_LG k]
      cases hrun:(Trans.Recal.runAux (k+g+2) (G1.LG k) none) tbl with
      | mk a s =>
        have ih1:=runAux_LG k g none (Or.inl rfl) tbl hs
        rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) none).run tbl=(a,s)
          from hrun] at ih1
        have ha:a=G1.LBT k:=ih1.1
        have hsm:Sound s:=ih1.2
        subst ha
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show ((G1.LBT k)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (G1.LG (k+1)) 0 (((k+1:Nat):Int)+2-1) 0=1 from
            G1.fpar_LG_0_e (k+1) (((k+1:Nat):Int)+2-1) (by push_cast; omega)
              (by push_cast; omega),G1.adm_LG_1 (k+1)]
        cases hrun2:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)) s with
        | mk c1 s2 =>
          have ih2:=runAux_LG k g (some 1) (Or.inr rfl) s hsm
          rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 1)).run s=(c1,s2)
            from hrun2] at ih2
          have hc1:c1=.D 1 (G1.rep1 k):=ih2.1
          have hsm2:Sound s2:=ih2.2
          subst hc1
          simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run,
            show Trans.Recal.transTypeMain (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1)=3 from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.transType_LG k,
            show Trans.Recal.mkC2 (G1.LG (k+1)) 1 (((k+1:Nat):Int)+2-1) 3
                (.D 1 (G1.rep1 k))=.D 1 (G1.rep1 (k+1)) from by
              rw [show (((k+1:Nat):Int)+2-1)=(k:Int)+2 by push_cast; omega]
              exact G1.mkC2_LG k,
            show ((0:Int)<((k+1:Nat):Int)+2-1) by push_cast; omega,if_true]
          cases hrun3:(Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_LG_zero k g s2 hsm2
            rw [show (Trans.Recal.runAux (k+g+2) (G1.LG k) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G1.LBT k:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            rw [if_pos (isMarkedB_LG_inner k),
              G1.replMark_LG ((G1.LBT k).size+
                ((Trans.Dict.BT.D 1 (G1.rep1 k)).size+
                  (Trans.Dict.BT.D 1 (G1.rep1 (k+1))).size+4)) k (by omega)]
            simp only [Option.getD_some]
            exact ⟨by trivial,Sound_cons_LG_zero s3 hsm3 (k+1)⟩

theorem adm_L_zero : Trans.Recal.adm (L 0) 1=1 := by rfl
theorem transType_L_zero : Trans.Recal.transTypeMain (L 0) 1 4=1 := by rfl
theorem mkC2_L_zero : Trans.Recal.mkC2 (L 0) 1 4 1 D1ss=A0 := by rfl

theorem repl_L_zero (f : Nat) (hf : 2≤f) :
    Trans.Recal.replMark f (G1.LBT 2) D1ss A0=some (LBT 0) := by
  obtain ⟨g,rfl⟩ : ∃ g,f=g+2:=⟨f-2,by omega⟩
  change Trans.Recal.replMark (g+2) (.D 0 D1ss) D1ss A0=some Anchor
  rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
  rw [show ((Trans.Dict.BT.D 0 D1ss)==D1ss)=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [G1.replMark_self (g+1) 1 (.sum D1z D1z) A0 (by omega)]
  rfl

theorem repl_D0_D1_self (f : Nat) (a cc : Trans.Dict.BT) (hf : 2≤f) :
    Trans.Recal.replMark f (.D 0 (.D 1 a)) (.D 1 a) cc=
      some (.D 0 cc) := by
  obtain ⟨g,rfl⟩ : ∃ g,f=g+2:=⟨f-2,by omega⟩
  rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
  rw [show ((Trans.Dict.BT.D 0 (.D 1 a))==(.D 1 a))=false from rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [G1.replMark_self (g+1) 1 a cc (by omega)]
  rfl

set_option maxHeartbeats 2000000 in
theorem runAux_L0 (g : Nat) (req : Option Int) (hr : Allowed 0 req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+5) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+5) (L 0) req).run tbl).2 := by
  have hr' : req=none ∨ req=some 0 := by
    rw [Allowed,if_pos (by decide)] at hr
    simpa using hr
  cases hf:tbl.find? (fun z=>z.1==(L 0,req)) with
  | some p =>
    rw [show g+5=(g+4)+1 by omega,G1.run_hit (g+4) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg 0 req hr he,hs⟩
  | none =>
    rw [show g+5=(g+4)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L 0,isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L 0,
      show (((0:Int)+5-1)==0)=false from by decide,
      show Trans.Recal.predP (L 0)=G1.LG 2 from rfl]
    cases hrun:(Trans.Recal.runAux (g+4) (G1.LG 2) none) tbl with
    | mk t1 s =>
      have ih1:=runAux_LG 2 g none (Or.inl rfl) tbl hs
      rw [show 2+g+2=g+4 by omega] at ih1
      rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=G1.LBT 2:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux (g+4) (G1.LG 2) (some 1)) s with
      | mk c1 s2 =>
        have ih2:=runAux_LG 2 g (some 1) (Or.inr rfl) s hsm
        rw [show 2+g+2=g+4 by omega] at ih2
        rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) (some 1)).run s=(c1,s2)
          from hrun2] at ih2
        have hc1:c1=D1ss:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((0:Nat):Int)+5-1)=4 by omega,
          show ((4:Int)==0)=false from rfl,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((G1.LBT 2)==Trans.Dict.BT.zero)=false from rfl,
          Bool.false_eq_true,if_false,
          show Trans.Recal.fpar (L 0) 0 4 0=1 from rfl,adm_L_zero,
          hrun2,transType_L_zero,mkC2_L_zero]
        rcases hr' with h|h
        · subst h
          rw [repl_L_zero _ (by omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none 0,?_⟩
          have ht:=Sound_cons_L s2 hsm2 0 none (Allowed_none 0)
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ((0:Int)<4) by omega,if_true]
          cases hrun3:(Trans.Recal.runAux (g+4) (G1.LG 2) (some 0)) s2 with
          | mk c0 s3 =>
            have ih3:=runAux_LG_zero 2 g s2 hsm2
            rw [show 2+g+2=g+4 by omega] at ih3
            rw [show (Trans.Recal.runAux (g+4) (G1.LG 2) (some 0)).run s2=(c0,s3)
              from hrun3] at ih3
            have hc0:c0=G1.LBT 2:=ih3.1
            have hsm3:Sound s3:=ih3.2
            subst hc0
            simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run,hrun3]
            have hm : Trans.Recal.isMarkedB (G1.LBT 2) D1ss=true :=
              isMarkedB_LG_inner 2
            rw [if_pos hm,repl_L_zero _ (by omega)]
            simp only [Option.getD_some]
            refine ⟨(Val_phase0 0).symm,?_⟩
            have ht:=Sound_cons_L s3 hsm3 0 (some 0) (Allowed_phase0 0)
            exact ht

theorem size_W (n : Nat) (b : Trans.Dict.BT) :
    (W n b).size=11*n+b.size := by
  induction n with
  | zero => simp [W]
  | succ n ih =>
    simp only [W,Trans.Dict.BT.size,ih]
    omega

set_option maxHeartbeats 2000000 in
theorem runAux_phase0_step (a g : Nat) (req : Option Int)
    (hr : Allowed (5*a+1) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (5*a) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux (5*a+g+5) (L (5*a)) r).run s).1=Val (5*a) r ∧
          Sound ((Trans.Recal.runAux (5*a+g+5) (L (5*a)) r).run s).2) :
    ((Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) req).run tbl).1=
        Val (5*a+1) req ∧
      Sound ((Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((5*a+5:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_pos (by omega)] at hr
    simpa only [show 5*a+1+4=5*a+5 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (5*a+1),req)) with
  | some p =>
    rw [show (5*a+1)+g+5=(5*a+g+5)+1 by omega,
      G1.run_hit (5*a+g+5) (L (5*a+1)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (5*a+1) req hr he,hs⟩
  | none =>
    rw [show (5*a+1)+g+5=(5*a+g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (5*a+1),isPrincipalP_L (5*a+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (5*a+1),
      show ((((5*a+1:Nat):Int)+5-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (5*a+1))=L (5*a) from by
        simpa only [show 5*a+1=5*a+1 by rfl] using predP_L (5*a)]
    cases hrun:(Trans.Recal.runAux (5*a+g+5) (L (5*a)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (5*a)) tbl hs
      rw [show (Trans.Recal.runAux (5*a+g+5) (L (5*a)) none).run tbl=(t1,s)
        from hrun] at ih1
      have ht1:t1=LBT (5*a):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux (5*a+g+5) (L (5*a))
          (some ((5*a:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((5*a:Nat):Int)) (Allowed_phase0 a) s hsm
        rw [show (Trans.Recal.runAux (5*a+g+5) (L (5*a))
          (some ((5*a:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=Anchor:=ih2.1.trans (Val_phase0 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((5*a+1:Nat):Int)+5-1)=((5*a+5:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (5*a))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase0]; rfl,
          Bool.false_eq_true,if_false,j0_L_new1,adm_L_new1,hrun2,
          transType_L_new1,mkC2_L_new1]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase0 a _ (by
            rw [LBT_phase0]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (5*a+1),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+1) none (Allowed_none (5*a+1))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show ¬(((5*a+5:Nat):Int)<((5*a+5:Nat):Int)) by omega,
            if_false,gp1_L_phase0_tail a (5*a+1) (by omega),
            StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          refine ⟨(Val_phase1 a).symm,?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+1) (some ((5*a+5:Nat):Int))
            (Allowed_phase1 a)
          rw [Val_phase1] at ht
          exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase1_step (a g : Nat) (req : Option Int)
    (hr : Allowed (5*a+2) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (5*a+1) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) r).run s).1=
            Val (5*a+1) r ∧
          Sound ((Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) r).run s).2) :
    ((Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) req).run tbl).1=
        Val (5*a+2) req ∧
      Sound ((Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((5*a+5:Nat):Int) ∨
      req=some ((5*a+6:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_pos (by omega)] at hr
    simpa only [show 5*a+2+3=5*a+5 by omega,
      show 5*a+2+4=5*a+6 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (5*a+2),req)) with
  | some p =>
    rw [show (5*a+2)+g+5=((5*a+1)+g+5)+1 by omega,
      G1.run_hit ((5*a+1)+g+5) (L (5*a+2)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (5*a+2) req hr he,hs⟩
  | none =>
    rw [show (5*a+2)+g+5=((5*a+1)+g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (5*a+2),isPrincipalP_L (5*a+2),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (5*a+2),
      show ((((5*a+2:Nat):Int)+5-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (5*a+2))=L (5*a+1) from by
        simpa only [show 5*a+2=(5*a+1)+1 by omega] using predP_L (5*a+1)]
    cases hrun:(Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (5*a+1)) tbl hs
      rw [show (Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (5*a+1):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1))
          (some ((5*a+5:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((5*a+5:Nat):Int)) (Allowed_phase1 a) s hsm
        rw [show (Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1))
          (some ((5*a+5:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D0z:=ih2.1.trans (Val_phase1 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((5*a+2:Nat):Int)+5-1)=((5*a+6:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (5*a+1))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase1]; rfl,
          Bool.false_eq_true,if_false,j0_L_new2,adm_L_new2,hrun2,
          transType_L_new2,mkC2_L_new2]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase1 a _ (by
            rw [LBT_phase1]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (5*a+2),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+2) none (Allowed_none (5*a+2))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((5*a+5:Nat):Int)<((5*a+6:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1))
                (some ((5*a+5:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((5*a+5:Nat):Int)) (Allowed_phase1 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((5*a+1)+g+5) (L (5*a+1))
                (some ((5*a+5:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D0z:=ih3.1.trans (Val_phase1 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D0z),
                G1.replMark_self (D0z.size+(D0z.size+(Trans.Dict.BT.D 0 D1z).size+4))
                  0 .zero (.D 0 D1z) (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase2carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (5*a+2) (some ((5*a+5:Nat):Int))
                (Allowed_phase2carry a)
              rw [Val_phase2carry] at ht
              exact ht
          · subst h
            simp only [show ¬(((5*a+6:Nat):Int)<((5*a+6:Nat):Int)) by omega,
              if_false,gp1_L_phase1_tail a (5*a+2) (by omega),
              StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            refine ⟨(Val_phase2 a).symm,?_⟩
            have ht:=Sound_cons_L s2 hsm2 (5*a+2) (some ((5*a+6:Nat):Int))
              (Allowed_phase2 a)
            rw [Val_phase2] at ht
            exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase2_step (a g : Nat) (req : Option Int)
    (hr : Allowed (5*a+3) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (5*a+2) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) r).run s).1=
            Val (5*a+2) r ∧
          Sound ((Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) r).run s).2) :
    ((Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) req).run tbl).1=
        Val (5*a+3) req ∧
      Sound ((Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((5*a+5:Nat):Int) ∨
      req=some ((5*a+6:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_pos (by omega)] at hr
    simpa only [show 5*a+3+2=5*a+5 by omega,
      show 5*a+3+3=5*a+6 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (5*a+3),req)) with
  | some p =>
    rw [show (5*a+3)+g+5=((5*a+2)+g+5)+1 by omega,
      G1.run_hit ((5*a+2)+g+5) (L (5*a+3)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (5*a+3) req hr he,hs⟩
  | none =>
    rw [show (5*a+3)+g+5=((5*a+2)+g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (5*a+3),isPrincipalP_L (5*a+3),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (5*a+3),
      show ((((5*a+3:Nat):Int)+5-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (5*a+3))=L (5*a+2) from by
        simpa only [show 5*a+3=(5*a+2)+1 by omega] using predP_L (5*a+2)]
    cases hrun:(Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (5*a+2)) tbl hs
      rw [show (Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (5*a+2):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
          (some ((5*a+6:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((5*a+6:Nat):Int)) (Allowed_phase2 a) s hsm
        rw [show (Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
          (some ((5*a+6:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1z:=ih2.1.trans (Val_phase2 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((5*a+3:Nat):Int)+5-1)=((5*a+7:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (5*a+2))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase2]; rfl,
          Bool.false_eq_true,if_false,j0_L_new3,adm_L_new3,hrun2,
          transType_L_new3,mkC2_L_new3]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase2 a _ (by
            rw [LBT_phase2]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (5*a+3),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+3) none (Allowed_none (5*a+3))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((5*a+5:Nat):Int)<((5*a+7:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
                (some ((5*a+5:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((5*a+5:Nat):Int)) (Allowed_phase2carry a) s2 hsm2
              rw [show (Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
                (some ((5*a+5:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=.D 0 D1z:=ih3.1.trans (Val_phase2carry a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              have hm : Trans.Recal.isMarkedB (.D 0 D1z) D1z=true := by
                exact isMarkedB_LG_inner 0
              rw [if_pos hm,repl_D0_D1_self _ .zero D11z (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase3carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (5*a+3) (some ((5*a+5:Nat):Int))
                (Allowed_phase3carry a)
              rw [Val_phase3carry] at ht
              exact ht
          · subst h
            simp only [show (((5*a+6:Nat):Int)<((5*a+7:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
                (some ((5*a+6:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((5*a+6:Nat):Int)) (Allowed_phase2 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((5*a+2)+g+5) (L (5*a+2))
                (some ((5*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D1z:=ih3.1.trans (Val_phase2 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D1z),
                G1.replMark_self (D1z.size+(D1z.size+D11z.size+4))
                  1 .zero D11z (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase3 a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (5*a+3) (some ((5*a+6:Nat):Int))
                (Allowed_phase3 a)
              rw [Val_phase3] at ht
              exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase3_step (a g : Nat) (req : Option Int)
    (hr : Allowed (5*a+4) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (5*a+3) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) r).run s).1=
            Val (5*a+3) r ∧
          Sound ((Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) r).run s).2) :
    ((Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) req).run tbl).1=
        Val (5*a+4) req ∧
      Sound ((Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((5*a+5:Nat):Int) ∨
      req=some ((5*a+6:Nat):Int) := by
    rw [Allowed,if_neg (by omega),if_neg (by omega),if_neg (by omega),
      if_neg (by omega)] at hr
    simpa only [show 5*a+4+1=5*a+5 by omega,
      show 5*a+4+2=5*a+6 by omega] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (5*a+4),req)) with
  | some p =>
    rw [show (5*a+4)+g+5=((5*a+3)+g+5)+1 by omega,
      G1.run_hit ((5*a+3)+g+5) (L (5*a+4)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (5*a+4) req hr he,hs⟩
  | none =>
    rw [show (5*a+4)+g+5=((5*a+3)+g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (5*a+4),isPrincipalP_L (5*a+4),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (5*a+4),
      show ((((5*a+4:Nat):Int)+5-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (5*a+4))=L (5*a+3) from by
        simpa only [show 5*a+4=(5*a+3)+1 by omega] using predP_L (5*a+3)]
    cases hrun:(Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (5*a+3)) tbl hs
      rw [show (Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (5*a+3):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
          (some ((5*a+6:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((5*a+6:Nat):Int)) (Allowed_phase3 a) s hsm
        rw [show (Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
          (some ((5*a+6:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D11z:=ih2.1.trans (Val_phase3 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((5*a+4:Nat):Int)+5-1)=((5*a+8:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (5*a+3))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase3]; rfl,
          Bool.false_eq_true,if_false,j0_L_new4,adm_L_new4,hrun2,
          transType_L_new4,mkC2_L_new4]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase3 a _ (by
            rw [LBT_phase3]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (5*a+4),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+4) none (Allowed_none (5*a+4))
          rw [Val_none] at ht
          exact ht
        · rcases h with h|h
          · subst h
            simp only [show (((5*a+5:Nat):Int)<((5*a+8:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
                (some ((5*a+5:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((5*a+5:Nat):Int)) (Allowed_phase3carry a) s2 hsm2
              rw [show (Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
                (some ((5*a+5:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=.D 0 D11z:=ih3.1.trans (Val_phase3carry a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              have hm : Trans.Recal.isMarkedB (.D 0 D11z) D11z=true := by
                exact isMarkedB_LG_inner 1
              rw [if_pos hm,repl_D0_D1_self _ D1z D1ss (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase4carry a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (5*a+4) (some ((5*a+5:Nat):Int))
                (Allowed_phase4carry a)
              rw [Val_phase4carry] at ht
              exact ht
          · subst h
            simp only [show (((5*a+6:Nat):Int)<((5*a+8:Nat):Int)) by omega,
              if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
              modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
              MonadStateOf.get,Id.run]
            cases hrun3:(Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
                (some ((5*a+6:Nat):Int))) s2 with
            | mk c0 s3 =>
              have ih3:=ih (some ((5*a+6:Nat):Int)) (Allowed_phase3 a) s2 hsm2
              rw [show (Trans.Recal.runAux ((5*a+3)+g+5) (L (5*a+3))
                (some ((5*a+6:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
              have hc0:c0=D11z:=ih3.1.trans (Val_phase3 a)
              have hsm3:Sound s3:=ih3.2
              subst hc0
              dsimp only
              rw [if_pos (G1.isMarkedB_self D11z),
                G1.replMark_self (D11z.size+(D11z.size+D1ss.size+4))
                  1 D1z D1ss (by omega)]
              simp only [Option.getD_some]
              refine ⟨(Val_phase4 a).symm,?_⟩
              have ht:=Sound_cons_L s3 hsm3 (5*a+4) (some ((5*a+6:Nat):Int))
                (Allowed_phase4 a)
              rw [Val_phase4] at ht
              exact ht

set_option maxHeartbeats 2000000 in
theorem runAux_phase4_step (a g : Nat) (req : Option Int)
    (hr : Allowed (5*a+5) req) (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ r : Option Int, Allowed (5*a+4) r →
      ∀ s : Trans.Recal.Memo, Sound s →
        ((Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) r).run s).1=
            Val (5*a+4) r ∧
          Sound ((Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) r).run s).2) :
    ((Trans.Recal.runAux ((5*a+5)+g+5) (L (5*a+5)) req).run tbl).1=
        Val (5*a+5) req ∧
      Sound ((Trans.Recal.runAux ((5*a+5)+g+5) (L (5*a+5)) req).run tbl).2 := by
  have hr' : req=none ∨ req=some ((5*a+5:Nat):Int) := by
    rw [Allowed,if_pos (by omega)] at hr
    simpa only [show 5*a+5=5*a+5 by rfl] using hr
  cases hf:tbl.find? (fun z=>z.1==(L (5*a+5),req)) with
  | some p =>
    rw [show (5*a+5)+g+5=((5*a+4)+g+5)+1 by omega,
      G1.run_hit ((5*a+4)+g+5) (L (5*a+5)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨value_L_of_good hg (5*a+5) req hr he,hs⟩
  | none =>
    rw [show (5*a+5)+g+5=((5*a+4)+g+5)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (5*a+5),isPrincipalP_L (5*a+5),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (5*a+5),
      show ((((5*a+5:Nat):Int)+5-1)==0)=false from
        beq_eq_false_iff_ne.mpr (by omega),
      show Trans.Recal.predP (L (5*a+5))=L (5*a+4) from by
        simpa only [show 5*a+5=(5*a+4)+1 by omega] using predP_L (5*a+4)]
    cases hrun:(Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) none) tbl with
    | mk t1 s =>
      have ih1:=ih none (Allowed_none (5*a+4)) tbl hs
      rw [show (Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4)) none).run tbl=
        (t1,s) from hrun] at ih1
      have ht1:t1=LBT (5*a+4):=by simpa only [Val_none] using ih1.1
      have hsm:Sound s:=ih1.2
      subst ht1
      cases hrun2:(Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4))
          (some ((5*a+6:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((5*a+6:Nat):Int)) (Allowed_phase4 a) s hsm
        rw [show (Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4))
          (some ((5*a+6:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=D1ss:=ih2.1.trans (Val_phase4 a)
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [show (((5*a+5:Nat):Int)+5-1)=((5*a+9:Nat):Int) by omega,
          StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,hrun,
          show ((LBT (5*a+4))==Trans.Dict.BT.zero)=false from by
            rw [LBT_phase4]; rfl,
          Bool.false_eq_true,if_false,j0_L_new5,adm_L_new5,hrun2,
          transType_L_new5,mkC2_L_new5]
        rcases hr' with h|h
        · subst h
          rw [repl_LBT_phase4 a _ (by
            rw [LBT_phase4]
            simp only [Trans.Dict.BT.size,size_W]
            omega)]
          simp only [Option.getD_some]
          refine ⟨Val_none (5*a+5),?_⟩
          have ht:=Sound_cons_L s2 hsm2 (5*a+5) none (Allowed_none (5*a+5))
          rw [Val_none] at ht
          exact ht
        · subst h
          simp only [show (((5*a+5:Nat):Int)<((5*a+9:Nat):Int)) by omega,
            if_true,StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
            modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
            MonadStateOf.get,Id.run]
          cases hrun3:(Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4))
              (some ((5*a+5:Nat):Int))) s2 with
          | mk c0 s3 =>
            have ih3:=ih (some ((5*a+5:Nat):Int)) (Allowed_phase4carry a) s2 hsm2
            rw [show (Trans.Recal.runAux ((5*a+4)+g+5) (L (5*a+4))
              (some ((5*a+5:Nat):Int))).run s2=(c0,s3) from hrun3] at ih3
            have hc0:c0=.D 0 D1ss:=ih3.1.trans (Val_phase4carry a)
            have hsm3:Sound s3:=ih3.2
            subst hc0
            dsimp only
            have hm : Trans.Recal.isMarkedB (.D 0 D1ss) D1ss=true := by
              show Trans.Recal.isMarkedB (G1.LBT 2) (.D 1 (G1.rep1 2))=true
              exact isMarkedB_LG_inner 2
            rw [if_pos hm,repl_D0_D1_self _ (.sum D1z D1z) A0 (by omega)]
            simp only [Option.getD_some]
            have hv : Val (5*a+5) (some ((5*a+5:Nat):Int))=Anchor := by
              simpa only [show 5*(a+1)=5*a+5 by omega] using Val_phase0 (a+1)
            refine ⟨hv.symm,?_⟩
            have ha : Allowed (5*a+5) (some ((5*a+5:Nat):Int)) := by
              simpa only [show 5*(a+1)=5*a+5 by omega] using Allowed_phase0 (a+1)
            have ht:=Sound_cons_L s3 hsm3 (5*a+5) (some ((5*a+5:Nat):Int)) ha
            rw [hv] at ht
            exact ht

def RunOK (k : Nat) : Prop :=
  ∀ g : Nat, ∀ req : Option Int, Allowed k req →
    ∀ tbl : Trans.Recal.Memo, Sound tbl →
      ((Trans.Recal.runAux (k+g+5) (L k) req).run tbl).1=Val k req ∧
        Sound ((Trans.Recal.runAux (k+g+5) (L k) req).run tbl).2

theorem runOK_zero : RunOK 0 := by
  intro g req hr tbl hs
  simpa only [Nat.zero_add] using runAux_L0 g req hr tbl hs

theorem runOK_phase0 (a : Nat) (ih : RunOK (5*a)) : RunOK (5*a+1) := by
  intro g req hr tbl hs
  exact runAux_phase0_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase1 (a : Nat) (ih : RunOK (5*a+1)) : RunOK (5*a+2) := by
  intro g req hr tbl hs
  exact runAux_phase1_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase2 (a : Nat) (ih : RunOK (5*a+2)) : RunOK (5*a+3) := by
  intro g req hr tbl hs
  exact runAux_phase2_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase3 (a : Nat) (ih : RunOK (5*a+3)) : RunOK (5*a+4) := by
  intro g req hr tbl hs
  exact runAux_phase3_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_phase4 (a : Nat) (ih : RunOK (5*a+4)) : RunOK (5*a+5) := by
  intro g req hr tbl hs
  exact runAux_phase4_step a g req hr tbl hs fun r ha s hsound =>
    ih g r ha s hsound

theorem runOK_quintuple (a : Nat) :
    RunOK (5*a) ∧ RunOK (5*a+1) ∧ RunOK (5*a+2) ∧
      RunOK (5*a+3) ∧ RunOK (5*a+4) := by
  induction a with
  | zero =>
    have h0 : RunOK (5*0) := by simpa only using runOK_zero
    have h1:=runOK_phase0 0 h0
    have h2:=runOK_phase1 0 h1
    have h3:=runOK_phase2 0 h2
    exact ⟨h0,h1,h2,h3,runOK_phase3 0 h3⟩
  | succ a ih =>
    have h0' := runOK_phase4 a ih.2.2.2.2
    have h0 : RunOK (5*(a+1)) := by
      simpa only [show 5*(a+1)=5*a+5 by omega] using h0'
    have h1:=runOK_phase0 (a+1) h0
    have h2:=runOK_phase1 (a+1) h1
    have h3:=runOK_phase2 (a+1) h2
    exact ⟨h0,h1,h2,h3,runOK_phase3 (a+1) h3⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int) (hr : Allowed k req)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+5) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+5) (L k) req).run tbl).2 := by
  have hk : RunOK k := by
    have hm : k%5=0 ∨ k%5=1 ∨ k%5=2 ∨ k%5=3 ∨ k%5=4 := by omega
    have hdiv:=Nat.mod_add_div k 5
    rcases hm with h0|h1|h2|h3|h4
    · have heq:k=5*(k/5):=by omega
      rw [heq]
      exact (runOK_quintuple (k/5)).1
    · have heq:k=5*(k/5)+1:=by omega
      rw [heq]
      exact (runOK_quintuple (k/5)).2.1
    · have heq:k=5*(k/5)+2:=by omega
      rw [heq]
      exact (runOK_quintuple (k/5)).2.2.1
    · have heq:k=5*(k/5)+3:=by omega
      rw [heq]
      exact (runOK_quintuple (k/5)).2.2.2.1
    · have heq:k=5*(k/5)+4:=by omega
      rw [heq]
      exact (runOK_quintuple (k/5)).2.2.2.2
  exact hk g req hr tbl hs

/-- Link 2: the recalibrated reader follows the entire five-phase ladder. -/
theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb : m+5≤Trans.Recal.transFuel (L m) := by
    show m+5≤40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h : Trans.Recal.transFuel (L m)=
      m+(Trans.Recal.transFuel (L m)-m-5)+5 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  simpa only [Val_none] using
    (runAux_L m _ none (Allowed_none m) [] Sound_nil).1

theorem W_eq_dict (n : Nat) (b : Trans.Dict.BT) :
    W n b=G9Dict.W n b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [W,G9Dict.W,ih]

/-- Link 3: every complete five-column block advances the closed family-four tower. -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (5*n))=fA n := by
  rw [LBT_phase0,W_eq_dict]
  simpa only [Part,A0,C,D0z,D1z] using G9Dict.dict_D0_W_fA n

theorem fA_inT (n : Nat) : inT (fA n)=true := by
  rw [G9Dict.fA_eq_F]
  cases n with
  | zero => decide
  | succ n => exact G9Dict.I_inT (n+1)

theorem one_lt_fA (n : Nat) : lt TM.Term.one (fA n)=true := by
  rw [G9Dict.fA_eq_F]
  cases n with
  | zero => decide
  | succ n =>
    exact Evidence.WF.lt_trans_inT (by decide) (by decide)
      (G9Dict.I_inT (n+1)) (by decide) (G9Dict.B_lt_I_succ n)

theorem le_fA_one (n : Nat) : le (fA n) TM.Term.one=false := by
  unfold le
  rw [show ((fA n)==TM.Term.one)=false from beq_eq_false_iff_ne.mpr
    (Ne.symm (Evidence.WF.ne_of_ltF (one_lt_fA n)))]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (fA_inT n) (one_lt_fA n)

theorem fA_toList (n : Nat) : (fA n).toList=[fA n] := by
  rw [G9Dict.fA_eq_F]
  cases n with
  | zero => rfl
  | succ n => exact G9Dict.I_succ_toList n

theorem one_plus_fA (n : Nat) : plus TM.Term.one (fA n)=fA n := by
  unfold plus
  rw [show TM.Term.one.toList=[TM.Term.one] from rfl,fA_toList]
  simp only [List.filter_cons,List.filter_nil,le_fA_one,Bool.false_eq_true,
    if_false,List.nil_append,TM.Term.ofList]

/-- The first disputed family-four row agrees with its five-column expansion sequence. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fA n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map
          Trans.Recal.transPort).map
            (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=some (fA n)
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fA]

#guard (List.range 18).all fun m =>
  Trans.Recal.redP (L m)==L m && Trans.Recal.transPort (L m)==LBT m
#guard (List.range 8).all fun n =>
  Trans.oR (BMS.expand M n)==some (fA n)
#print axioms oR_M

end G9
end Rows.Selected
